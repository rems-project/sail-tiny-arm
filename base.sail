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

// Computes first return value of DecodeBitMasks in official spec
function decode_bitmask(N : bit, imms : bits(6), immr : bits(6)) -> bits(64) = {
  // Determine the size of the element repetition
  let 'len = if N == bitone then 6 else (5-count_leading_zeros(not_vec(imms)));
  assert(constraint('len > 0), "Invalid immediate encoding for bitwise operation");

  // The mask will have size 2^len and will have (s + 1) ones
  let s = unsigned(imms[len-1..0]);
  assert(s + 1 < 2^len, "All-ones mask is not allowed in bitwise operations");
  let elem = sail_zero_extend(sail_ones(s + 1), 2^len);

  // ROR by r. Bits above len will rotate by a multiple of 2^len, so are ignored
  let r = unsigned(immr[len-1..0]);
  let relem = if r == 0 then elem else elem[r-1..0]@elem[2^len-1..r];

  replicate_bits(relem, 2^(6-len))
}

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


