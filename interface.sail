$include <concurrency_interface.sail>

function pa_bits(pa : bits(64)) -> bits(64) = pa

instantiation sail_mem_read with
  'pa = bits(64),
  'translation_summary = unit,
  'arch_ak = unit,
  'abort = unit,
  pa_bits = pa_bits

instantiation sail_mem_write with
  'pa = bits(64),
  'translation_summary = unit,
  'arch_ak = unit,
  'abort = unit,
  pa_bits = pa_bits

function rMem(addr) = {
  let req : Mem_read_request(8, 64, bits(64), unit, unit) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = addr,
    translation = (),
    size = 8,
    tag = false
  };
  match sail_mem_read(req) {
    Ok((value, _)) => value,
    Err(_) => exit(),
  }
}

function wMem_Addr(addr) = sail_address_announce(64, addr)

function wMem(addr, value) = {
  let req : Mem_write_request(8, 64, bits(64), unit, unit) = struct {
    access_kind = AK_explicit(struct { variety = AV_plain, strength = AS_normal }),
    va = Some(addr),
    pa = addr,
    translation = (),
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
  'barrier = unit

function dataMemoryBarrier() = sail_barrier(())
