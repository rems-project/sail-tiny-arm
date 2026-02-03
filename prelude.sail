default Order dec

$define CONCURRENCY_INTERFACE_V2

$include <prelude.sail>

val eq_any = pure {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", lean: "BEq.beq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

val eq_bits_int : forall 'n 'm, 'n >= 0 & 'm >= 0. (bits('n), int('m)) -> bool
function eq_bits_int (x, y) = (unsigned(x) == y)

overload operator == = {eq_any, eq_bits_int}

overload operator ^ = {xor_vec}
overload operator - = {sub_bits}

val fail: forall 'a. string -> 'a
function fail(message) = {
    assert(false, message);
    exit()
}

overload operator == = {eq_bit}

val neq_bit : (bit, bit) -> bool
function neq_bit(x, y) = not_bool(eq_bit(x, y))

overload operator != = {neq_bit}

val not_bit : bit -> bit
function not_bit(b) = if b == bitzero then bitone else bitzero

