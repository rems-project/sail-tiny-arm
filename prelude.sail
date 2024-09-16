default Order dec

$include <prelude.sail>

/* See simple-arm for descriptions, interface for definitions */
val rMem : bits(64) -> bits(64)
val iFetch : bits(64) -> bits(32)
val wMem_Addr : bits(64) -> unit
val wMem : (bits(64), bits(64)) -> unit
val dataMemoryBarrier : unit -> unit

overload operator ^ = {xor_vec}
