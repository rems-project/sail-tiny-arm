$ifdef SYSTEM_TINY_ARM
struct Permissions = {
  ap_table : bits(2),
  xn_table : bits(1),
  pxn_table : bits(1),
  uxn_table : bits(1),
  ap : bits(3),
  xn : bits(1),
  uxn : bits(1),
  pxn : bits(1),
}

function base_Permissions() -> Permissions = struct {
  ap_table = sail_zeros(2),
  xn_table = sail_zeros(1),
  pxn_table = sail_zeros(1),
  uxn_table = sail_zeros(1),
  ap = sail_zeros(3),
  xn = sail_zeros(1),
  uxn = sail_zeros(1),
  pxn = sail_zeros(1),
}

struct S1AccessControls = {
  r : bits(1),
  w : bits(1),
  x : bits(1),
}

function base_S1AccessControls () -> S1AccessControls = struct {
  r = 0b0,
  w = 0b0,
  x = 0b0,
}

function extract_perms(descriptor : bits(64), is_table : bool) -> Permissions = {
  var perms : Permissions = base_Permissions();

  if is_table then {
    perms.ap_table = descriptor[62..61];
    perms.xn_table = [descriptor[60]];
    perms.pxn_table = [descriptor[59]];
    perms.uxn_table = [descriptor[60]];
  } else {
    perms.ap  = descriptor[7..6] @ 0b0;
    perms.xn  = [descriptor[54]];
    perms.uxn = [descriptor[54]];
    perms.pxn = [descriptor[53]];
  };

  return perms;
}

function combine_perms(
  prev : Permissions,
  current : Permissions
) -> Permissions = {
  var result = current;

  result.ap_table  = current.ap_table | prev.ap_table;
  result.xn_table  = current.xn_table | prev.xn_table;
  result.pxn_table = current.pxn_table | prev.pxn_table;
  result.uxn_table = current.uxn_table | prev.uxn_table;

  result.ap  = current.ap | prev.ap;
  result.xn  = current.xn | prev.xn;
  result.pxn = current.pxn | prev.pxn;
  result.uxn = current.uxn | prev.uxn;

  return result;
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

function check_table_permission_fault(
  perms : Permissions,
  accdesc : AccessDescriptor
) -> bool = {
  let at_el0 = accdesc.el == 0b00;
  let ap_table = perms.ap_table;

  if at_el0 & ([ap_table[0]] == 0b1) then {
    return true;
  };

  if accdesc.write & ([ap_table[1]] == 0b1) then {
    return true;
  };

  if accdesc.acctype == AccessType_IFETCH then {
    if at_el0 then {
      if perms.uxn_table == 0b1 | perms.xn_table == 0b1 then {
        return true;
      }
    } else {
      if perms.pxn_table == 0b1 | perms.xn_table == 0b1 then {
        return true;
      }
    }
  };

  return false;
}

function decode_leaf_permissions (
  perms : Permissions,
  accdesc : AccessDescriptor
) -> S1AccessControls = {
  var controls : S1AccessControls = base_S1AccessControls();
  let at_el0 = (accdesc.el == 0b00);

  let ap = perms.ap[2..1];
  match ap {
    0b00 => {  // EL1+ read-write
      controls.r = if at_el0 then 0b0 else 0b1;
      controls.w = if at_el0 then 0b0 else 0b1;
    },
    0b01 => {  // EL0/EL1+ read-write
      controls.r = 0b1;
      controls.w = 0b1;
    },
    0b10 => {  // EL1+ read-only
      controls.r = if at_el0 then 0b0 else 0b1;
      controls.w = 0b0;
    },
    0b11 => {  // EL0/EL1+ read-only
      controls.r = 0b1;
      controls.w = 0b0;
    },
    _ => ()
  };

  if at_el0 then {
    controls.x = if (perms.uxn == 0b1 | perms.xn_table == 0b1 | perms.uxn_table == 0b1)
                 then 0b0 else 0b1;
  } else {
    controls.x = if (perms.pxn == 0b1 | perms.xn_table == 0b1 | perms.pxn_table == 0b1)
                 then 0b0 else 0b1;
  };

  let wxn_enabled = [SCTLR_EL1[19]];
  if wxn_enabled == 0b1 & controls.w == 0b1 then {
    controls.x = 0b0;
  };

  return controls;
}

function check_leaf_permission_fault (
  perms : Permissions,
  accdesc : AccessDescriptor
) -> bool = {
  let controls = decode_leaf_permissions(perms, accdesc);
  // Check read permission
  if accdesc.read & (accdesc.acctype != AccessType_IFETCH) then {
    if controls.r == 0b0 then {
      return true;
    }
  };

  // Check write permission
  if accdesc.write then {
    if controls.w == 0b0 then {
      return true;
    }
  };

  // Check execute permission
  if accdesc.acctype == AccessType_IFETCH then {
    if controls.x == 0b0 then {
      return true;
    }
  };

  return false;
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

function pgt_walk(va : bits(64), accdesc : AccessDescriptor) -> (AddressDescriptor, bits(56)) = {
  let varange = get_VARange(va);

  let baseaddress = get_translation_base_address(varange);
  var descaddress = get_TTEntryAddress(0, va, baseaddress);
  var accumulated_perms = base_Permissions();

  foreach (level from 0 to 3) {
    var addrdesc = base_AddressDescriptor(accdesc, level);
    addrdesc.paddress.address = descaddress;
    addrdesc.vaddress = va;

    let walkaccess = create_AccessDescriptorTTW(level == 0, varange);
    let descriptor = read_memory(8, descaddress, walkaccess);

    let perms = extract_perms(descriptor, level == 3);
    accumulated_perms = combine_perms(accumulated_perms, perms);

    match decode_desc_type(descriptor, level) {
      DescriptorType_Table => {
        let next_baseaddress = 0x00 @ descriptor[47..12] @ 0x000;
        if check_table_permission_fault(accumulated_perms, accdesc) then {
          addrdesc.fault.statuscode = Fault_Permission;
          addrdesc.fault.level = level;
          addrdesc.fault.write = accdesc.write;
          addrdesc.fault.access = accdesc;
          return (addrdesc, sail_zeros(56))
        };

        assert (level < 3, "Table entry at level 3");
        descaddress = get_TTEntryAddress(level + 1, va, next_baseaddress);
        ()
      },
      DescriptorType_Leaf => {
        if check_leaf_permission_fault(accumulated_perms, accdesc) then {
          addrdesc.fault.statuscode = Fault_Permission;
          addrdesc.fault.level = level;
          addrdesc.fault.write = accdesc.write;
          addrdesc.fault.access = accdesc;
          return (addrdesc, sail_zeros(56))
        };

        let offset = 12 + (3 - level) * 9;
        let out_pa = 0x00 @ descriptor[47..offset] @ va[offset - 1 .. 0];
        return (addrdesc, out_pa)
      },
      DescriptorType_Invalid => {
        addrdesc.fault.statuscode = Fault_Translation;
        addrdesc.fault.level = level;
        return (addrdesc, sail_zeros(56))
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
    ec = if source_el == target_el then 0b100101 else 0b100100;
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
  ELR_EL1 = _PC;

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

  let (addrdesc, paddress) =
    if va_out_of_range(va) then {
      var addrdesc = base_AddressDescriptor(accdesc, 0);
      addrdesc.fault.statuscode = Fault_Translation;
      addrdesc.fault.write = accdesc.write;
      addrdesc.fault.access = accdesc;
      (addrdesc, sail_zeros(56))
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

  return Some(paddress)
}
$else
function translate_address(va, accdesc) = {
  return Some(va)
}
$endif
