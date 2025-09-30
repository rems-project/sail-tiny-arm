$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>
$include <concurrency_interface/translation.sail>

function mem_acc_is_explicit     (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR
function mem_acc_is_ifetch       (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_IFETCH
function mem_acc_is_ttw          (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_TTW
function mem_acc_is_relaxed      (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.acqpc) & not_bool(acc.acqsc) & not_bool(acc.relsc)
function mem_acc_is_rel_acq_rcpc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.acqpc
function mem_acc_is_rel_acq_rcsc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & (acc.acqsc | acc.relsc)
function mem_acc_is_standalone   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.exclusive) & not_bool(acc.atomicop)
function mem_acc_is_exclusive    (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.exclusive
function mem_acc_is_atomic_rmw   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.atomicop

enum DescriptorType = {
  DescriptorType_Table,
  DescriptorType_Leaf,
  DescriptorType_Invalid
}

function base_AccessDescriptor (acctype : AccessType) -> AccessDescriptor = struct {
  acctype = acctype,
  el = sail_zeros(2),
  ss = SS_NonSecure,
  acqsc = false,
  acqpc = false,
  relsc = false,
  limitedordered = false,
  exclusive = false,
  atomicop = false,
  modop = MemAtomicOp_ADD,
  nontemporal = false,
  read = false,
  write = false,
  cacheop = CacheOp_Clean,
  opscope = CacheOpScope_ALLU,
  cachetype = CacheType_Data,
  pan = false,
  transactional = false,
  nonfault = false,
  firstfault = false,
  first = false,
  contiguous = false,
  streamingsve = false,
  ls64 = false,
  mops = false,
  rcw = false,
  rcws = false,
  toplevel = false,
  varange = VARange_LOWER,
  a32lsmd = false,
  tagchecked = false,
  tagaccess = false,
  mpam = struct {
    mpam_sp = PIdSpace_NonSecure,
    partid = 0x0000,
    pmg = 0x00
  }
}

$ifdef SYSTEM_TINY_ARM
function base_FullAddress () -> FullAddress = struct {
  paspace = PAS_NonSecure,
  address = sail_zeros(56)
}

function base_FaultRecord (accdesc : AccessDescriptor, level : int) -> FaultRecord = struct {
  statuscode = Fault_None,
  access = accdesc,
  ipaddress = base_FullAddress(),
  gpcf = struct {
    gpf = GPCF_None,
    level = 0
  },
  paddress = base_FullAddress(),
  gpcfs2walk = false,
  s2fs1walk = false,
  write = not_bool(accdesc.read) & accdesc.write,
  s1tagnotdata = false,
  tagaccess = false,
  level = level,
  extflag = sail_zeros(1),
  secondstage = false,
  assuredonly = false,
  toplevel = false,
  overlay = false,
  dirtybit = false,
  domain = sail_zeros(4),
  merrorstate = ErrorState_UC,
  debugmoe = sail_zeros(4)
}

function base_MemoryAttributes () -> MemoryAttributes = struct {
  memtype = MemType_Normal,
  device = DeviceType_GRE,
  inner = struct {
    attrs = sail_zeros(2),
    hints = sail_zeros(2),
    transient = false,
  },
  outer = struct {
    attrs = sail_zeros(2),
    hints = sail_zeros(2),
    transient = false,
  },
  shareability = Shareability_ISH,
  tags = MemTag_Untagged,
  notagaccess = false,
  xs = sail_zeros(1),
}

function base_TLBContext () -> TLBContext = struct {
  ss = SS_NonSecure,
  regime = Regime_EL10,
  vmid = sail_zeros(16),
  asid = sail_zeros(16),
  nG = sail_zeros(1),
  ipaspace = PAS_NonSecure,
  includes_s1_name = false,
  includes_s2_name = false,
  includes_gpt_name = false,
  ia = sail_zeros(64),
  tg = TGx_4KB,
  cnp = sail_zeros(1),
  level = 0,
  isd128 = false,
  xs = sail_zeros(1),
}

function base_AddressDescriptor (accdesc: AccessDescriptor, level : int) -> AddressDescriptor = struct {
  fault = base_FaultRecord(accdesc, level),
  memattrs = base_MemoryAttributes(),
  paddress = base_FullAddress(),
  tlbcontext = base_TLBContext(),
  s1assured = false,
  s2fs1mro = false,
  mecid = sail_zeros(16),
  vaddress = sail_zeros(64)
}
$endif

$ifdef SYSTEM_TINY_ARM
let FINAL_LEVEL = 3
$endif

$ifdef SYSTEM_TINY_ARM
type addr_size : Int = 56
let addr_size' : int(56) = 56
$else
type addr_size : Int = 64
let addr_size' : int(64) = 64
$endif

$ifdef SYSTEM_TINY_ARM
type addr_space : Type = PASpace
let addr_space_def = PAS_NonSecure
$else
type addr_space : Type = unit
let addr_space_def = ()
$endif


$ifdef SYSTEM_TINY_ARM
type abort = Fault
$else
type abort = unit
$endif

instantiation sail_mem_read with
  'addr_size = addr_size,
  'addr_space = addr_space,
  'mem_acc = AccessDescriptor,
  'abort = abort,
  'CHERI = false,
  'cap_size_log = 0,
  mem_acc_is_explicit = mem_acc_is_explicit,
  mem_acc_is_ifetch = mem_acc_is_ifetch,
  mem_acc_is_ttw = mem_acc_is_ttw,
  mem_acc_is_relaxed = mem_acc_is_relaxed,
  mem_acc_is_rel_acq_rcpc = mem_acc_is_rel_acq_rcpc,
  mem_acc_is_rel_acq_rcsc = mem_acc_is_rel_acq_rcsc,
  mem_acc_is_standalone = mem_acc_is_standalone,
  mem_acc_is_exclusive = mem_acc_is_exclusive,
  mem_acc_is_atomic_rmw = mem_acc_is_atomic_rmw

instantiation sail_mem_write with
  'addr_size = addr_size,
  'addr_space = addr_space,
  'mem_acc = AccessDescriptor,
  'abort = abort,
  'CHERI = false,
  'cap_size_log = 0,
  mem_acc_is_explicit = mem_acc_is_explicit,
  mem_acc_is_ifetch = mem_acc_is_ifetch,
  mem_acc_is_ttw = mem_acc_is_ttw,
  mem_acc_is_relaxed = mem_acc_is_relaxed,
  mem_acc_is_rel_acq_rcpc = mem_acc_is_rel_acq_rcpc,
  mem_acc_is_rel_acq_rcsc = mem_acc_is_rel_acq_rcsc,
  mem_acc_is_standalone = mem_acc_is_standalone,
  mem_acc_is_exclusive = mem_acc_is_exclusive,
  mem_acc_is_atomic_rmw = mem_acc_is_atomic_rmw

instantiation sail_mem_address_announce with
  'addr_size = addr_size,
  'addr_space = addr_space,
  'mem_acc = AccessDescriptor,
  'abort = abort,
  'CHERI = false,
  'cap_size_log = 0

function rMem(addr) = {
  let req : Mem_read_request(8, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind = base_AccessDescriptor(AccessType_GPR),
    address = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size = 8,
    num_tag = 0
  };
  match sail_mem_read(req) {
    Ok((value, _)) => from_bytes_le(value),
    Err(_) => exit(),
  }
}

function iFetch(addr) = {
  let req : Mem_read_request(4, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind = base_AccessDescriptor(AccessType_IFETCH),
    address = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size = 4,
    num_tag = 0
  };
  match sail_mem_read(req) {
    Ok((value, _)) => from_bytes_le(value),
    Err(_) => exit(),
  }
}

function wMem_Addr(addr) = sail_address_announce(64, sail_zero_extend(addr, 64))

function wMem(addr, value) = {
  let req : Mem_write_request(8, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind = base_AccessDescriptor(AccessType_GPR),
    address = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size = 8,
    num_tag = 0,
    value = to_bytes_le(8, value),
    tags = []
  };
  match sail_mem_write(req) {
    Ok(_) => (),
    Err(_) => exit(),
  }
}

instantiation sail_barrier with
  'barrier = Barrier

function dataMemoryBarrier(types) = sail_barrier(
  Barrier_DMB(struct{
    domain = MBReqDomain_FullSystem,
    types = types,
    nXS = false}))

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
$endif

$ifdef SYSTEM_TINY_ARM
function get_VARange (va : bits(64)) -> VARange = {
  if [va[55]] == sail_zeros(1) then {
    VARange_LOWER
  } else {
    VARange_UPPER
  }
}

function get_baddr (varange : VARange) -> bits(56) = {
  let ttbr : bits(64) = match varange {
    VARange_LOWER => TTBR0_EL1,
    VARange_UPPER => TTBR1_EL1
  };
  var baddr : bits(56) = sail_zeros(56);
  baddr[47 .. 0] = ttbr[47 .. 5] @ sail_zeros(5);
  return baddr
}

function VMID_read () -> bits(16) = {
  // TODO
  return sail_zeros(16)
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

function get_TTEntryAddress (level : int, ia : bits(64), baseaddress : FullAddress) -> FullAddress = {
  let 'descsizelog2 = 3;
  let 'stride = 9;
  let 'levels = FINAL_LEVEL - level;
  let 'lsb = levels * stride + 12;
  let 'msb = lsb + stride - 1;
  assert(constraint((0 <= 'lsb & 'lsb <= 'msb & 'msb < 64)));
  assert(constraint(56 >= 'msb - 'lsb + 1 + 'descsizelog2));
  let index : bits(56) = sail_zero_extend(ia[msb .. lsb] @ sail_zeros(descsizelog2), 56);
  let descaddress : FullAddress = struct {
    address = baseaddress.address | index,
    paspace = baseaddress.paspace,
  };

  return descaddress
}

function decode_desc_type(descriptor : bits(56), level : int) -> DescriptorType = {
  if [descriptor[0]] == sail_zeros(1) then {
    return(DescriptorType_Invalid)
  } else {
    if [descriptor[1]] == 0b1 then {
      if level == FINAL_LEVEL then {
        DescriptorType_Leaf
      } else {
        DescriptorType_Table
      }
    } else if [descriptor[1]] == sail_zeros(1) then {
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
  let startlevel : int = 0;
  let varange : VARange = get_VARange(va);

  let baseaddress : FullAddress = struct {
    address = get_baddr(varange),
    paspace = PAS_NonSecure,
  };
  var descaddress : FullAddress = get_TTEntryAddress(0, va, baseaddress);

  let walkaccess : AccessDescriptor = create_AccessDescriptorTTW(true, varange);
  var walkaddress = base_AddressDescriptor(walkaccess, 0);

  foreach (level from 0 to FINAL_LEVEL)  {
    let toplevel : bool = level == startlevel;
    let walkaccess : AccessDescriptor = create_AccessDescriptorTTW(toplevel, varange);
    walkaddress.fault.level = level;
    walkaddress.paddress = descaddress;
    walkaddress.vaddress = va;

    let req : Mem_read_request(8, 0, addr_size, addr_space, AccessDescriptor) = struct {
      access_kind = walkaccess,
      address = truncate(walkaddress.paddress.address, addr_size'),
      address_space = addr_space_def,
      size = 8,
      num_tag = 0
    };
    let memval : bits(64) = match sail_mem_read(req) {
      Ok((memval, _)) => from_bytes_le(memval),
      Err(_) => exit(),
    };

    let descriptor : bits(56) = slice(memval, 0, 56);
    let desctype = decode_desc_type(descriptor, level);
    match desctype {
      DescriptorType_Table => {
        let next_baseaddress : FullAddress = struct {
          address = sail_zeros(8) @ descriptor[47 .. 12] @ sail_zeros(12),
          paspace = PAS_NonSecure
        };
        descaddress = get_TTEntryAddress(level + 1, va, next_baseaddress);
        ()
      },
      DescriptorType_Leaf => {
        let baseaddress : FullAddress = struct {
          address = sail_zeros(8) @ descriptor[47 .. 12] @ sail_zeros(12),
          paspace = PAS_NonSecure
        };
        descaddress = baseaddress;
      },
      DescriptorType_Invalid => {
        walkaddress.fault.statuscode = Fault_Translation;
        return (walkaddress, sail_zeros(56))
      }
    }
  };
  return (walkaddress, descaddress.address)
}

function handle_fault (addrdesc : AddressDescriptor) -> unit = {
  let fault : FaultRecord = addrdesc.fault;
  let vaddress : bits(64) = addrdesc.vaddress;
  let vect_offset : int = 0;

  var ec : int = 0;
  let il : bits(1) = 0b1;
  if fault.access.acctype == AccessType_IFETCH then {
    ec = 32;
  } else if fault.access.acctype == AccessType_TTW then {
    ec = 36;
  };

  // Report exception
  ESR_EL1 = sail_zero_extend((get_slice_int(6, ec, 0) @ il) @ sail_zeros(25), 64);
  FAR_EL1 = vaddress;
  ELR_EL1 = _PC;

  _PC = slice(VBAR_EL1, 11, 53) @ get_slice_int(11, vect_offset, 0);
  sail_take_exception(Some(fault));
}

function translate_address(va) = {
  let accdesc : AccessDescriptor = base_AccessDescriptor(AccessType_AT);

  // Announce translation start
  let cnp: bits(1) =
    if get_VARange(va) == VARange_LOWER then {
      slice(TTBR0_EL1, 0, 1)
    } else {
      slice(TTBR1_EL1, 0, 1)
    };

  let tsi : TranslationStartInfo = struct {
    ss = accdesc.ss,
    regime = Regime_EL10,
    vmid = VMID_read(),
    asid = ASID_read(),
    va = va,
    cnp = cnp,
    accdesc = accdesc,
    size = 0
  };
  sail_translation_start(tsi);

  // Actual translation
  var (addrdesc, paddress) = pgt_walk(va, accdesc);
  if is_fault(addrdesc) then {
    handle_fault(addrdesc);
    return None()
  };

  // Announce result
  addrdesc.vaddress = sail_zero_extend(va, 64);
  sail_translation_end(addrdesc);

  return Some(paddress)
}
$endif
