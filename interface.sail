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

function base_AccessDescriptor (acctype : AccessType) -> AccessDescriptor = struct {
  acctype = acctype,
  el = 0b00,
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

function wMem_Addr(addr) = sail_address_announce(64, addr)

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

