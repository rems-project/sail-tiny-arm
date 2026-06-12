/* This file is suppose to contain general utility function and type for Arm
 * (what goes in v8base in the original model) */

enum extend_type = {
  UXTB,
  UXTH,
  UXTW,
  UXTX,
  SXTB,
  SXTH,
  SXTW,
  SXTX,
}

mapping ext_bits : extend_type <-> bits(3) = {
  UXTB <-> 0b000,
  UXTH <-> 0b001,
  UXTW <-> 0b010,
  UXTX <-> 0b011,
  SXTB <-> 0b100,
  SXTH <-> 0b101,
  SXTW <-> 0b110,
  SXTX <-> 0b111,
}

val extend_reg : (bits(64), extend_type) -> bits(64)
function extend_reg(v, ext) = match ext {
  UXTB => sail_zero_extend(v[7..0], 64),
  UXTH => sail_zero_extend(v[15..0], 64),
  UXTW => sail_zero_extend(v[31..0], 64),
  UXTX => v,
  SXTB => sail_sign_extend(v[7..0], 64),
  SXTH => sail_sign_extend(v[15..0], 64),
  SXTW => sail_sign_extend(v[31..0], 64),
  SXTX => v,
}


enum shift_type = {
  shift_LSL,
  shift_LSR,
  shift_ASR,
  shift_ROR,
}

mapping shift_bits : shift_type <-> bits(2) = {
  shift_LSL <-> 0b00,
  shift_LSR <-> 0b01,
  shift_ASR <-> 0b10,
  shift_ROR <-> 0b11,
}

val shift_reg : forall 'N, 'N in {32, 64}. (bits('N), shift_type, range(0,63)) -> bits('N)
function shift_reg(v, sh, amount) = match sh {
  shift_LSL => sail_shiftleft(v, amount),
  shift_LSR => sail_shiftright(v, amount),
  shift_ASR => sail_arith_shiftright(v, amount),
  shift_ROR => fail ("ROR unsupported")
}


/* Operand type: Either a shifted registers, extend registers or a immediate */
union operand = {
  OperandRegExt : (reg_index, extend_type, range (0, 4)),
  OperandRegShift : (reg_index, shift_type, range (0, 63)),
  OperandImm : bits(64)
}

val eval_operand : forall 'N, 'N in {32, 64}. (int('N), operand) -> bits('N)
function eval_operand (size, op) = match op {
  OperandRegExt(n, ext, shift) =>
    sail_shiftleft(extend_reg(X(n), ext)[size-1..0], shift),
  OperandRegShift(n, sh, amount) =>
    shift_reg(X(n, size), sh, amount),
  OperandImm(imm) => imm[size-1..0]
}

let zero_operand = OperandImm(0x0000000000000000)


/* Bitwise operations */
enum bitwise_op = {
  Eor,
  Or,
  And,
}

/* Condition for conditional instructions */
enum cond = {
  EQ,
  NE,
  CS,
  CC,
  MI,
  PL,
  VS,
  VC,
  HI,
  LS,
  GE,
  LT,
  GT,
  LE,
  AL,
  NV,
}

val rotate_right : forall 'n. (bits('n), int) -> bits('n)
function rotate_right (v, r) =
  if r == 0 then v else sail_shiftright(v, r) | sail_shiftleft(v, 'n - r)

// Computes first return value of DecodeBitMasks in official spec
function decode_bitmask(N : bit, imms : bits(6), immr : bits(6), immediate : bool) -> (bits(64), bits(64)) = {
  // Determine the size of the element repetition
  let 'len = if N == bitone then 6 else (5-count_leading_zeros(not_vec(imms)));
  assert(constraint('len > 0), "Invalid immediate encoding for bitwise operation");

  // The mask will have size 2^len and will have (s + 1) ones
  let s = unsigned(imms[len-1..0]);
  let r = unsigned(immr[len-1..0]);
  if immediate then
    assert(s + 1 < 2^len, "All-ones mask is not allowed in immediate bitwise operations");

  let welem = sail_zero_extend(sail_ones(s + 1), 2^len);
  // ROR by r.
  let relem = rotate_right(welem, r);
  let wmask = replicate_bits(relem, 2^(6-len));

  let diff = s - r;
  let d = if diff >= 0 then diff else 2^len + diff;
  let telem = sail_zero_extend(sail_ones(d + 1), 2^len);

  let tmask = replicate_bits(telem, 2^(6-len));
  (wmask, tmask)
}

val smax : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits('n)
function smax(x, y) = if signed(x) > signed(y) then x else y
val smin : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits('n)
function smin(x, y) = if signed(x) < signed(y) then x else y
val umax : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits('n)
function umax(x, y) = if unsigned(x) > unsigned(y) then x else y
val umin : forall 'n, 'n > 0. (bits('n), bits('n)) -> bits('n)
function umin(x, y) = if unsigned(x) < unsigned(y) then x else y


/************* Top level definition start ***************/

// The instruction AST
scattered union ast

// Errors should be reported with [fail], this model doesn't support
// Undefined instruction architectural exceptions
val decode : bits(32) -> ast
scattered function decode

val execute : ast -> unit
scattered function execute

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit


