default Order dec

$define CONCURRENCY_INTERFACE_V2

$include <prelude.sail>

val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", lean: "BEq.beq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)

overload operator == = {eq_any, eq_bits_int}

/* See tiny-arm for descriptions, interface for definitions */
val rMem : bits(64) -> bits(64)
val iFetch : bits(64) -> bits(32)
val wMem_Addr : bits(64) -> unit
val wMem : (bits(64), bits(64)) -> unit

overload operator ^ = {xor_vec}
