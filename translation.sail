$ifdef SYSTEM_TINY_ARM
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
  va[63..48] == 0x0000 | va[63..48] == sail_ones(16)
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
  let varange : VARange = get_VARange(va);

  let baseaddress = get_translation_base_address(varange);
  var descaddress = get_TTEntryAddress(0, va, baseaddress);

  foreach (level from 0 to 3) {
    let toplevel : bool = level == 0;
    let walkaccess : AccessDescriptor = create_AccessDescriptorTTW(toplevel, varange);
    var walkaddress = base_AddressDescriptor(walkaccess, level);
    walkaddress.paddress.address = descaddress;
    walkaddress.vaddress = va;

    let descriptor = read_memory(8, descaddress, walkaccess);
    match decode_desc_type(descriptor, level) {
      DescriptorType_Table => {
        let next_baseaddress = 0x00 @ descriptor[47..12] @ 0x000;
        assert (level < 3, "Table entry at level 3");
        descaddress = get_TTEntryAddress(level + 1, va, next_baseaddress);
        ()
      },
      DescriptorType_Leaf => {
        let offset = 12 + (3 - level) * 9;
        let out_pa = 0x00 @ descriptor[47..offset] @ va[offset - 1 .. 0];
        return (walkaddress, out_pa)
      },
      DescriptorType_Invalid => {
        walkaddress.fault.statuscode = Fault_Translation;
        return (walkaddress, sail_zeros(56))
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

  var ec = 0b000000;
  let il = 0b1;
  if fault.access.acctype == AccessType_IFETCH then {
    ec = 0b100000;
  } else if fault.access.acctype == AccessType_GPR then {
    ec = 0b100100;
  };

  let wnr = if fault.write then 0b1 else 0b0;
  let dfsc : bits(6) =
    match fault.level {
      0 => 0b000100,
      1 => 0b000101,
      2 => 0b000110,
      3 => 0b000111,
      _ => 0b000000,
    };
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
  let varange = get_VARange(va);
  let cnp =
    if varange == VARange_LOWER then {
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
