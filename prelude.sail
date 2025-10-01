default Order dec

$define CONCURRENCY_INTERFACE_V2

$include <prelude.sail>

val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", lean: "BEq.beq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)

overload operator == = {eq_any, eq_bits_int}


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

/* See tiny-arm for descriptions, interface for definitions */
val iFetch : bits(addr_size) -> bits(32)
val rMem : bits(addr_size) -> bits(64)
val wMem_Addr : bits(addr_size) -> unit
val wMem : (bits(addr_size), bits(64)) -> unit
$ifdef SYSTEM_TINY_ARM
val translate_address : bits(64) -> option(bits(addr_size))
$endif

overload operator ^ = {xor_vec}
