$include <concurrency_interface.sail>
$include <concurrency_interface/tlbi.sail>
$include <concurrency_interface/exception.sail>
$include <concurrency_interface/cache_op.sail>
$include <concurrency_interface/translation.sail>

$ifdef SYSTEM_TINY_ARM
type addrsize : Int = 56
$else
type addrsize : Int = 64
$endif

$ifdef SYSTEM_TINY_ARM
type trans_info = option (TranslationInfo)
let trans_info_default : trans_info = None()
$else
type trans_info = unit
let trans_info_default : trans_info = ()
$endif

$ifdef SYSTEM_TINY_ARM
type abort = Fault
$else
type abort = unit
$endif

val pa_bits : bits(addrsize) -> bits(64)

function pa_bits(bv) = sail_zero_extend(bv, 64)

instantiation sail_mem_read with
  'pa = bits(addrsize),
  'translation_summary = trans_info,
  'arch_ak = arm_acc_type,
  'abort = abort,
  pa_bits = pa_bits

instantiation sail_mem_write with
  'pa = bits(addrsize),
  'translation_summary = trans_info,
  'arch_ak = arm_acc_type,
  'abort = abort,
  pa_bits = pa_bits

function rMem(addr) = {
  let req : Mem_read_request(8, 64, bits(addrsize), trans_info, arm_acc_type) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = truncate(addr, sizeof(addrsize)),
    translation = trans_info_default,
    size = 8,
    tag = false
  };
  match sail_mem_read(req) {
    Ok((value, _)) => value,
    Err(_) => exit(),
  }
}

function iFetch(addr) = {
  let req : Mem_read_request(4, 64, bits(addrsize), trans_info, arm_acc_type) = struct {
    access_kind = AK_ifetch(),
    va = Some(addr),
    pa = truncate(addr, sizeof(addrsize)),
    translation = trans_info_default,
    size = 4,
    tag = false
  };
  match sail_mem_read(req) {
    Ok((value, _)) => value,
    Err(_) => exit(),
  }
}

function wMem_Addr(addr) = sail_address_announce(64, addr)

function wMem(addr, value) = {
  let req : Mem_write_request(8, 64, bits(addrsize), trans_info, arm_acc_type) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = truncate(addr, sizeof(addrsize)),
    translation = trans_info_default,
    size = 8,
    value = Some(value),
    tag = None()
  };
  match sail_mem_write(req) {
    Ok(_) => (),
    Err(_) => exit(),
  }
}

instantiation sail_barrier with
  'barrier = Barrier

function dataMemoryBarrier() = sail_barrier(
  Barrier_DMB(struct{
    domain = MBReqDomain_FullSystem,
    types = MBReqTypes_All,
    nXS = false}))

$ifdef SYSTEM_TINY_ARM
instantiation sail_cache_op with
  'cache_op = CacheRecord

instantiation sail_tlbi with
  'tlbi = TLBIInfo

instantiation sail_return_exception

instantiation sail_take_exception with
  'fault = option(FaultRecord)

instantiation sail_translation_start with
  'trans_start = TranslationStartInfo

instantiation sail_translation_end with
  'trans_end = AddressDescriptor
$endif
