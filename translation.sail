$ifdef SYSTEM_TINY_ARM
struct Permissions = {
  allow_write : bool,
  allow_unprivileged_data : bool,
  allow_unprivileged_exec : bool, // also just "allow_exec" in single EL translation regimes
  allow_privileged_exec : bool,
}

function extract_perms_table(descriptor : bits(64)) -> Permissions = {
  let ap_table = descriptor[62..61];

  return struct {
    allow_write = [ap_table[1]] == 0b0,
    allow_unprivileged_data = [ap_table[0]] == 0b0,
    allow_unprivileged_exec = [descriptor[60]] == 0b0,
    allow_privileged_exec = [descriptor[59]] == 0b0,
  }
}

function extract_perms_leaf(descriptor : bits(64)) -> Permissions = {
  let ap = descriptor[7..6];

  return struct {
    allow_write = [ap[1]] == 0b0,
    allow_unprivileged_data = [ap[0]] == 0b1,
    allow_unprivileged_exec = [descriptor[54]] == 0b0,
    allow_privileged_exec = [descriptor[53]] == 0b0,
  }
}

function create_AccessDescriptorTTW (toplevel : bool, varange : VARange) -> AccessDescriptor = {
  var accdesc : AccessDescriptor = base_AccessDescriptor(AccessType_TTW);
  accdesc.el = PSTATE.EL;
  accdesc.read = true;
  accdesc.toplevel = toplevel;
  accdesc.varange = varange;
  return(accdesc)
}

function get_VARange (va : bits(64)) -> VARange = {
  if [va[48]] == 0b0 then {
    VARange_LOWER
  } else {
    VARange_UPPER
  }
}

function va_out_of_range (va : bits(64)) -> bool = {
  not_bool(va[63..48] == 0x0000 | va[63..48] == 0xFFFF)
}

function get_translation_base_address (varange : VARange) -> bits(56) = {
  let ttbr : bits(64) = match varange {
    VARange_LOWER => TTBR0_EL1,
    VARange_UPPER => TTBR1_EL1
  };
  var baddr = sail_zeros(56);
  baddr[47 .. 5] = ttbr[47 .. 5];
  return baddr
}

function ASID_read () -> bits(16) = {
  if slice(TCR_EL1, 22, 1) == sail_zeros(1) then
    slice(TTBR0_EL1, 48, 16)
  else
    slice(TTBR1_EL1, 48, 16)
}

function is_fault (addrdesc : AddressDescriptor) -> bool = {
  match addrdesc.fault.statuscode {
    Fault_None => false,
    _ => true
  }
}

/* If it returns true, the access is allowed */
function check_permission (
  perms : Permissions,
  accdesc : AccessDescriptor
) -> bool = {
  let at_el0 = accdesc.el == 0b00;

  if accdesc.acctype == AccessType_IFETCH then {
    if at_el0 then {
      return perms.allow_unprivileged_exec;
    } else {
      return perms.allow_privileged_exec;
    }
  };

  if accdesc.write & not_bool(perms.allow_write) then {
    return false;
  };

  if at_el0 & not_bool(perms.allow_unprivileged_data) then {
    return false;
  };

  return true;
}

function get_TTEntryAddress (level : range(0, 3), ia : bits(64), baseaddress : bits(56)) -> bits(56) = {
  let 'stride = 9;
  let 'lsb = (3 - level) * stride + 12;
  let 'msb = lsb + stride - 1;
  let index = sail_zero_extend(ia[msb .. lsb] @ sail_zeros(3), 56);
  let descaddress : bits(56) = baseaddress | index;
  return descaddress
}

function decode_desc_type(descriptor : bits(64), level : int) -> DescriptorType = {
  if [descriptor[0]] == 0b0 then {
    return(DescriptorType_Invalid)
  } else {
    if [descriptor[1]] == 0b1 then {
      if level == 3 then {
        DescriptorType_Leaf
      } else {
        DescriptorType_Table
      }
    } else if [descriptor[1]] == 0b0 then { // The descriptor is a block
      if (level == 1 | level == 2) then {
        DescriptorType_Leaf
      } else {
        DescriptorType_Invalid
      }
    } else {
      DescriptorType_Invalid
    }
  }
}

function pgt_walk(va : bits(64), accdesc : AccessDescriptor) -> AddressDescriptor = {
  let varange = get_VARange(va);

  let baseaddress = get_translation_base_address(varange);
  var descaddress = get_TTEntryAddress(0, va, baseaddress);

  // Address descriptor to be returned from the page table walk
  var addrdesc = base_AddressDescriptor(accdesc);
  addrdesc.vaddress = va;
  addrdesc.fault.write = accdesc.write;
  addrdesc.fault.access = accdesc;

  foreach (level from 0 to 3) {
    addrdesc.fault.level = level;

    let walkaccess = create_AccessDescriptorTTW(level == 0, varange);
    let descriptor = read_memory(8, descaddress, walkaccess);

    match decode_desc_type(descriptor, level) {
      DescriptorType_Table => {
        let perms = extract_perms_table(descriptor);
        if not_bool(check_permission(perms, accdesc)) then {
          addrdesc.fault.statuscode = Fault_Permission;
          return addrdesc
        };

        let next_baseaddress = 0x00 @ descriptor[47..12] @ 0x000;
        assert (level < 3, "Table entry at level 3");
        descaddress = get_TTEntryAddress(level + 1, va, next_baseaddress);
        ()
      },
      DescriptorType_Leaf => {
        let perms = extract_perms_leaf(descriptor);
        if not_bool(check_permission(perms, accdesc)) then {
          addrdesc.fault.statuscode = Fault_Permission;
          return addrdesc
        };

        let offset = 12 + (3 - level) * 9;
        let out_pa = 0x00 @ descriptor[47..offset] @ va[offset - 1 .. 0];
        addrdesc.paddress.address = out_pa;
        return addrdesc
      },
      DescriptorType_Invalid => {
        addrdesc.fault.statuscode = Fault_Translation;
        return addrdesc
      }
    }
  };
  exit()
}

function handle_fault (addrdesc : AddressDescriptor) -> unit = {
  let fault : FaultRecord = addrdesc.fault;
  let vaddress = addrdesc.vaddress;
  let source_el = fault.access.el;
  let target_el = 0b01; // We're handling at EL1

  let vect_offset =
    if source_el == target_el then {
      if PSTATE.SP == 0b0 then {
        0x000
      } else {
        0x200
      }
    } else {
      0x400
    };

  // Report the exception
  sail_take_exception(Some(fault));

  // Determine Exception Class (EC)
  var ec = 0b000000;
  let il = 0b1;

  if fault.access.acctype == AccessType_IFETCH then {
    ec = if source_el == target_el then 0b100001 else 0b100000;
  } else if fault.access.acctype == AccessType_GPR then {
    ec = if source_el == target_el then 0b100101 else 0b100100;
  } else {
    exit();
  };

  // Determine Fault Status Code (FSC) based on fault type and level
  let level_bit : bits(2) =
    match fault.level {
      0 => 0b00,
      1 => 0b01,
      2 => 0b10,
      3 => 0b11,
      _ => exit(),
    };
  let dfsc : bits(6) =
    if fault.statuscode == Fault_Translation then {
      // Translation faults: 0b0001xx (where xx is level)
      0b0001 @ level_bit
    } else if fault.statuscode == Fault_Permission then {
      // Permission faults: 0b0011xx (where xx is level)
      0b0011 @ level_bit
    } else {
      // Default/unknown fault
      0b000000
    };

  // Build ISS (Instruction Specific Syndrome)
  let wnr = if fault.write then 0b1 else 0b0;
  let iss = sail_zero_extend(wnr @ dfsc, 25);
  ESR_EL1 = sail_zero_extend((ec @ il) @ iss, 64);
  FAR_EL1 = vaddress;

  /* Save PSTATE to SPSR_EL1 for restoration by ERET */
  SPSR_EL1 = sail_zero_extend(
    PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V @     /* bits 31-28 */
    0b0000000000000000000 @                         /* bits 27-9 (reserved/other) */
    PSTATE.D @                                      /* bit 9 */
    PSTATE.A @                                      /* bit 8 */
    PSTATE.I @                                      /* bit 7 */
    PSTATE.F @                                      /* bit 6 */
    0b00 @                                          /* bits 5-4 (reserved) */
    PSTATE.EL @                                     /* bits 3-2 */
    0b0 @                                           /* bit 1 (reserved) */
    PSTATE.SP,                                      /* bit 0 */
    64
  );

  ELR_EL1 = _PC;

  /* Transition to EL1 and use SP_EL1 */
  PSTATE.EL = 0b01;
  PSTATE.SP = 0b1;

  /* Mask interrupts on exception entry */
  PSTATE.D = 0b1;
  PSTATE.A = 0b1;
  PSTATE.I = 0b1;
  PSTATE.F = 0b1;

  _PC = slice(VBAR_EL1, 12, 52) @ vect_offset;
}

function translate_address(va, accdesc) = {
  // Check SCTLR_EL1.M to check if MMU is enabled
  if slice(SCTLR_EL1, 0, 1) == 0b0 then {
    return Some(truncate(va, addr_size'))
  };

  // Announce translation start
  let cnp =
    if get_VARange(va) == VARange_LOWER then {
      slice(TTBR0_EL1, 0, 1)
    } else {
      slice(TTBR1_EL1, 0, 1)
    };

  let tsi : TranslationStartInfo = struct {
    ss = SS_NonSecure,
    regime = Regime_EL10,
    vmid = 0x0000,
    asid = ASID_read(),
    va = va,
    cnp = cnp,
    accdesc = accdesc,
    size = 0
  };
  sail_translation_start(tsi);

  let addrdesc =
    if va_out_of_range(va) then {
      var addrdesc = base_AddressDescriptor(accdesc);
      addrdesc.fault.statuscode = Fault_Translation;
      addrdesc.fault.write = accdesc.write;
      addrdesc.fault.access = accdesc;
      addrdesc
    } else {
      // Actual translation
      pgt_walk(va, accdesc)
    };

  // Announce result
  sail_translation_end(addrdesc);

  if is_fault(addrdesc) then {
    handle_fault(addrdesc);
    return None()
  };

  return Some(addrdesc.paddress.address)
}
$else
function translate_address(va, accdesc) = {
  return Some(va)
}
$endif
