default Order dec

$define CONCURRENCY_INTERFACE_V2

$include <prelude.sail>

val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", lean: "BEq.beq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)

overload operator == = {eq_any, eq_bits_int}

overload operator ^ = {xor_vec}

val neq_any = pure {lem: "neq", coq: "generic_neq"} : forall ('a : Type). ('a, 'a) -> bool
function neq_any(x, y) = not_bool(x == y)

overload operator != = {neq_any}
