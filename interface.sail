$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>
$include <concurrency_interface/translation.sail>

scattered union ast

val decode : bits(32) -> option(ast)
scattered function decode

val execute : ast -> unit
scattered function execute

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit

$ifdef SYSTEM_TINY_ARM
type addr_size : Int = 56
let addr_size' : int(56) = 56
$else
type addr_size : Int = 64
let addr_size' : int(64) = 64
$endif

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

function mem_acc_is_explicit     (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR
function mem_acc_is_ifetch       (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_IFETCH
function mem_acc_is_ttw          (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_TTW
function mem_acc_is_relaxed      (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.acqpc) & not_bool(acc.acqsc) & not_bool(acc.relsc)
function mem_acc_is_rel_acq_rcpc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.acqpc
function mem_acc_is_rel_acq_rcsc (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & (acc.acqsc | acc.relsc)
function mem_acc_is_standalone   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & not_bool(acc.exclusive) & not_bool(acc.atomicop)
function mem_acc_is_exclusive    (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.exclusive
function mem_acc_is_atomic_rmw   (acc : AccessDescriptor) -> bool = acc.acctype == AccessType_GPR & acc.atomicop

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

/* Helper to get current exception level */
$ifdef SYSTEM_TINY_ARM
function current_el() -> bits(2) = PSTATE.EL
$else
function current_el() -> bits(2) = 0b00
$endif

/* Create GPR access descriptor with specified direction and memory ordering */
function create_GPRAccessDescriptor(is_write: bool, ordering: MemoryOrdering) -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_GPR);
  accdesc.write = is_write;
  accdesc.read = not_bool(is_write);
  accdesc.el = current_el();
  match ordering {
    Ordering_Relaxed => (),
    Ordering_Acquire => accdesc.acqsc = true,
    Ordering_AcquireRCpc => accdesc.acqpc = true,
    Ordering_Release => accdesc.relsc = true
  };
  accdesc
}

/* Convenience wrappers for common access patterns */
function create_readAccessDescriptor() -> AccessDescriptor =
  create_GPRAccessDescriptor(false, Ordering_Relaxed)

function create_writeAccessDescriptor() -> AccessDescriptor =
  create_GPRAccessDescriptor(true, Ordering_Relaxed)

function create_readAcquireAccessDescriptor(ordering: MemoryOrdering) -> AccessDescriptor =
  create_GPRAccessDescriptor(false, ordering)

function create_writeReleaseAccessDescriptor() -> AccessDescriptor =
  create_GPRAccessDescriptor(true, Ordering_Release)

function create_iFetchAccessDescriptor() -> AccessDescriptor = {
  var accdesc = base_AccessDescriptor(AccessType_IFETCH);
  accdesc.read = true;
  accdesc.write = false;
  accdesc.el = current_el();
  accdesc
}

$ifdef SYSTEM_TINY_ARM
enum DescriptorType = {
  DescriptorType_Table,
  DescriptorType_Leaf,
  DescriptorType_Invalid
}

function base_FullAddress () -> FullAddress = struct {
  paspace = PAS_NonSecure,
  address = sail_zeros(56)
}

function base_FaultRecord (accdesc : AccessDescriptor) -> FaultRecord = struct {
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
  level = 0,
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

function base_AddressDescriptor (accdesc: AccessDescriptor) -> AddressDescriptor = struct {
  fault = base_FaultRecord(accdesc),
  memattrs = base_MemoryAttributes(),
  paddress = base_FullAddress(),
  tlbcontext = base_TLBContext(),
  s1assured = false,
  s2fs1mro = false,
  mecid = sail_zeros(16),
  vaddress = sail_zeros(64)
}

function base_TLBIRecord (op : TLBIOp) -> TLBIRecord = struct {
  op = op,
  from_aarch64 = true,
  security = SS_NonSecure,
  regime = Regime_EL10,
  vmid = 0x0000,
  asid = 0x0000,
  level = TLBILevel_Any,
  attr = TLBI_AllAttr,
  ipaspace = PAS_NonSecure,
  address = sail_zeros(64),
  end_address_name = sail_zeros(64),
  d64 = true,
  d128 = false,
  ttl = 0b0000,
  tg = 0b00,
}

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

/* See tiny-arm for descriptions, interface for definitions */
val iFetch : (bits(addr_size), AccessDescriptor) -> bits(32)
val rMem : forall 'N, 'N > 0. (int('N), bits(addr_size), AccessDescriptor) -> bits('N * 8)
val wMem_Addr : bits(addr_size) -> unit
val wMem : forall 'N, 'N > 0. (int('N), bits(addr_size), bits('N * 8), AccessDescriptor) -> unit
val dataMemoryBarrier : (MBReqDomain, MBReqTypes) -> unit
val dataSynchronizationBarrer : (MBReqDomain, MBReqTypes) -> unit
val instructionSynchronizationBarrier : unit -> unit

val translate_address : (bits(64), AccessDescriptor) -> option(bits(addr_size))

val read_memory : forall 'N, 'N > 0.
  (int('N), bits(addr_size), AccessDescriptor) -> bits('N * 8)

function read_memory(N, addr, accdesc) = {
  let req : Mem_request('N, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind   = accdesc,
    address       = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size          = N,
    num_tag       = 0
  };

  match sail_mem_read(req) {
    Ok((bytes, _)) => from_bytes_le(bytes),
    Err(_e) => { exit() }
  }
}

function iFetch(addr, accdesc) = read_memory(4, addr, accdesc)

function rMem(N, addr, accdesc) = read_memory(N, addr, accdesc)

function wMem_Addr(addr) = sail_address_announce(64, sail_zero_extend(addr, 64))

function wMem(N, addr, value, accdesc) = {
  let req : Mem_request('N, 0, addr_size, addr_space, AccessDescriptor) = struct {
    access_kind = accdesc,
    address = truncate(addr, addr_size'),
    address_space = addr_space_def,
    size = N,
    num_tag = 0
  };
  match sail_mem_write(req, to_bytes_le(N, value), []) {
    Ok(_) => (),
    Err(_) => exit(),
  }
}

instantiation sail_barrier with
  'barrier = Barrier

function dataMemoryBarrier(domain, types) = sail_barrier(
  Barrier_DMB(struct{
    domain = domain,
    types = types,
    nXS = false}))

function dataSynchronizationBarrer(domain, types) = sail_barrier(
  Barrier_DSB(struct{
    domain = domain,
    types = types,
    nXS = false}))

function instructionSynchronizationBarrier() = sail_barrier(Barrier_ISB())

$ifdef SYSTEM_TINY_ARM
val reportTLBI : (TLBIOp, option(bits(64)), option(bits(16))) -> unit

function reportTLBI(op, addr, asid) = {
  var r = base_TLBIRecord(op);
  r.address = match addr {
    Some(addr) => addr,
    None() => 0x0000000000000000
  };
  r.asid = match asid {
    Some(asid) => asid,
    None() => 0x0000
  };

  sail_tlbi(struct { rec = r, shareability = Shareability_ISH })
}
$endif
