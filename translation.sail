
$ifdef SYSTEM_TINY_ARM
instantiation sail_cache_op with
  'cache_op = CacheRecord

instantiation sail_tlbi with
  'tlbi = TLBIInfo

instantiation sail_return_exception

instantiation sail_take_exception with
  'exn = option(FaultRecord)

instantiation sail_translation_start with
  'trans_start = TranslationStartInfo

instantiation sail_translation_end with
  'trans_end = AddressDescriptor

function get_VARange (va : bits(64)) -> VARange = {
  if [va[55]] == sail_zeros(1) then {
    VARange_LOWER
  } else {
    VARange_UPPER
  }
}

function get_translation_base_address (varange : VARange) -> bits(56) = {
  let ttbr : bits(64) = match varange {
    VARange_LOWER => TTBR0_EL1,
    VARange_UPPER => TTBR1_EL1
  };
  var baddr : bits(56) = sail_zeros(56);
  baddr[47 .. 0] = ttbr[47 .. 5] @ sail_zeros(5);
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

function create_AccessDescriptorTTW (toplevel : bool, varange : VARange) -> AccessDescriptor = {
  var accdesc : AccessDescriptor = base_AccessDescriptor(AccessType_TTW);
  accdesc.read = true;
  accdesc.toplevel = toplevel;
  accdesc.varange = varange;
  return(accdesc)
}

function get_TTEntryAddress (level : range(0, 3), ia : bits(64), baseaddress : bits(56)) -> bits(56) = {
  let 'descsizelog2 = 3;
  let 'stride = 9;
  let 'levels = 3 - level;
  let 'lsb = levels * stride + 12;
  let 'msb = lsb + stride - 1;
  let index : bits(56) = sail_zero_extend(ia[msb .. lsb] @ sail_zeros(descsizelog2), 56);
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

  let baseaddress : bits(56) = get_translation_base_address(varange);
  var descaddress : bits(56) = get_TTEntryAddress(0, va, baseaddress);

  // initialize walkaddress
  let walkaccess : AccessDescriptor = create_AccessDescriptorTTW(true, varange);
  var walkaddress = base_AddressDescriptor(walkaccess, 0);
  var desctype = DescriptorType_Table;

  foreach (level from 0 to 3) {
    let toplevel : bool = level == 0;
    let walkaccess : AccessDescriptor = create_AccessDescriptorTTW(toplevel, varange);
    walkaddress = base_AddressDescriptor(walkaccess, level);
    walkaddress.paddress = struct {
      address = descaddress,
      paspace = PAS_NonSecure,
    };
    walkaddress.vaddress = va;

    let memval : bits(64) = read_memory(8, truncate(walkaddress.paddress.address, addr_size'), walkaccess);
    desctype = decode_desc_type(memval, level);
    match desctype {
      DescriptorType_Table => {
        let next_baseaddress : bits(56) = sail_zero_extend(memval[47 .. 12] @ sail_zeros(12), 56);
        assert (0 <= ('loop_level + 1) & ('loop_level + 1) <= 3);
        descaddress = get_TTEntryAddress(level + 1, va, next_baseaddress);
        ()
      },
      DescriptorType_Leaf => {
        let levels : int = 3 - level;
        let 'offset_bits : int = 12 + levels * 9;
        assert((0 <= 'offset_bits - 1) & 56 >= (('offset_bits - 1) + 1));

        let base_pa : bits(56) =
          sail_zero_extend(memval[47 .. 12] @ sail_zeros(12), 56);
        let va_off : bits(56) =
          sail_zero_extend(va[offset_bits - 1 .. 0], 56);
        let out_pa : bits(56) = base_pa | va_off;
        return (walkaddress, out_pa)
      },
      DescriptorType_Invalid => {
        walkaddress.fault.statuscode = Fault_Translation;
        return (walkaddress, sail_zeros(56))
      }
    }
  };
  return (walkaddress, descaddress)
}

function handle_fault (addrdesc : AddressDescriptor) -> unit = {
  let fault : FaultRecord = addrdesc.fault;
  let vaddress : bits(64) = addrdesc.vaddress;
  let source_el : bits(2) = fault.access.el;
  let target_el : bits(2) = 0b01; // We're handling at EL1

  let vect_offset : bits(12) =
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

  var ec : bits(6) = 0b000000;
  let il : bits(1) = 0b1;
  if fault.access.acctype == AccessType_IFETCH then {
    ec = 0b100000;
  } else if fault.access.acctype == AccessType_TTW then {
    ec = 0b100100;
  };

  let wnr : bits(1) = if fault.write then 0b1 else 0b0;
  let dfsc : bits(6) =
    if fault.level == 0 then {
      0b000100
    } else if fault.level == 1 then {
      0b000101
    } else if fault.level == 2 then {
      0b000110
    } else if fault.level == 3 then {
      0b000111
    } else {
      0b000000
    };
  let iss : bits(25) = sail_zero_extend(wnr @ dfsc, 25);
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
  let cnp: bits(1) =
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

  // Actual translation
  let (addrdesc, paddress) = pgt_walk(va, accdesc);

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
