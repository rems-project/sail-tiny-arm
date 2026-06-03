
/* The program counter */
register _PC : bits(64)
function rPC() -> bits(64) = _PC
function wPC(pc : bits(64)) -> unit = _PC = pc
overload PC = {rPC, wPC}


/* General purpose registers */
register R30 : bits(64)
register R29 : bits(64)
register R28 : bits(64)
register R27 : bits(64)
register R26 : bits(64)
register R25 : bits(64)
register R24 : bits(64)
register R23 : bits(64)
register R22 : bits(64)
register R21 : bits(64)
register R20 : bits(64)
register R19 : bits(64)
register R18 : bits(64)
register R17 : bits(64)
register R16 : bits(64)
register R15 : bits(64)
register R14 : bits(64)
register R13 : bits(64)
register R12 : bits(64)
register R11 : bits(64)
register R10 : bits(64)
register R9 : bits(64)
register R8 : bits(64)
register R7 : bits(64)
register R6 : bits(64)
register R5 : bits(64)
register R4 : bits(64)
register R3 : bits(64)
register R2 : bits(64)
register R1 : bits(64)
register R0 : bits(64)

let GPRs : vector(31, register(bits(64))) = [
  ref R30,
  ref R29,
  ref R28,
  ref R27,
  ref R26,
  ref R25,
  ref R24,
  ref R23,
  ref R22,
  ref R21,
  ref R20,
  ref R19,
  ref R18,
  ref R17,
  ref R16,
  ref R15,
  ref R14,
  ref R13,
  ref R12,
  ref R11,
  ref R10,
  ref R9,
  ref R8,
  ref R7,
  ref R6,
  ref R5,
  ref R4,
  ref R3,
  ref R2,
  ref R1,
  ref R0,
]

type reg_index = range(0, 31)

val wX : (reg_index, bits(64)) -> unit

function wX(n, value) = {
  if n != 31 then
    *GPRs[n] = value;
}

val rX : reg_index -> bits(64)

function rX(n) = {
  if n != 31 then
    *GPRs[n]
  else
    0x0000000000000000;
}

val rXS : forall 'N, 'N in {8, 16, 32, 64}. (reg_index, int('N)) -> bits('N)
function rXS(n, size) = rX(n)[size-1..0]
val wXS : forall 'N, 'N in {8, 16, 32, 64}. (reg_index, int('N), bits('N)) -> unit
function wXS(n, size, value) = wX(n, sail_zero_extend(value, 64))
overload X = {rX, wX, rXS, wXS}

/* Datasize: 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
type datasize = bit

$ifdef SYSTEM_TINY_ARM
register CurrentEL : bits(2)
$else
let CurrentEL : bits(2) = 0b00
$endif


register NZCV : bits(4)
function rN() -> bit = NZCV[3]
function wN(bit) : bit -> unit = NZCV[3] = bit
overload N = {rN, wN}
function rZ() -> bit = NZCV[2]
function wZ(bit) : bit -> unit = NZCV[2] = bit
overload Z = {rZ, wZ}
function rC() -> bit = NZCV[1]
function wC(bit) : bit -> unit = NZCV[1] = bit
overload C = {rC, wC}
function rV() -> bit = NZCV[0]
function wV(bit) : bit -> unit = NZCV[0] = bit
overload V = {rV, wV}

register SP_EL0 : bits (64)

$ifndef SYSTEM_TINY_ARM
function rSP() -> bits(64) = SP_EL0
function wSP(sp : bits(64)) -> unit = SP_EL0 = sp
$endif

$ifdef SYSTEM_TINY_ARM

register SPSel : bits(1)
register DAIF : bits(4)

register SP_EL1 : bits(64)
register SP_EL2 : bits(64)
register SP_EL3 : bits(64)

function rSP() -> bits(64) = {
  if SPSel == 0b0 then SP_EL0
  else match CurrentEL {
    0b00 => SP_EL0,
    0b01 => SP_EL1,
    0b10 => SP_EL2,
    0b11 => SP_EL3
  }
}
function wSP(sp : bits(64)) -> unit = {
  if SPSel == 0b0 then SP_EL0 = sp
  else match CurrentEL {
    0b00 => SP_EL0 = sp,
    0b01 => SP_EL1 = sp,
    0b10 => SP_EL2 = sp,
    0b11 => SP_EL3 = sp
  }
}

register ELR_EL1 : bits(64)
register ELR_EL2 : bits(64)
register ELR_EL3 : bits(64)

register ESR_EL1 : bits(64)
register ESR_EL2 : bits(64)
register ESR_EL3 : bits(64)

register FAR_EL1 : bits(64)
register FAR_EL2 : bits(64)
register FAR_EL3 : bits(64)

register PAR_EL1 : bits(64)

// We fix the size to 64 and happyly ignore 128 bits register extension for VMSA128
register TTBR0_EL1 : bits(64)
register TTBR1_EL1 : bits(64)
register TTBR0_EL2 : bits(64)
register TTBR1_EL2 : bits(64)
register TTBR0_EL3 : bits(64)
register VTTBR_EL2 : bits(64)

register VBAR_EL1 : bits(64)
register VBAR_EL2 : bits(64)
register VBAR_EL3 : bits(64)

register SPSR_EL1 : bits(64)
register SPSR_EL2 : bits(64)
register SPSR_EL3 : bits(64)

register ID_AA64MMFR0_EL1 : bits(64)
register ID_AA64MMFR1_EL1 : bits(64)
register ID_AA64MMFR2_EL1 : bits(64)
register ID_AA64MMFR3_EL1 : bits(64)
register ID_AA64MMFR4_EL1 : bits(64)

register TCR_EL1 : bits(64)
register TCR_EL2 : bits(64)
register TCR_EL3 : bits(64)
register VTCR_EL2 : bits(64)

register SCTLR_EL1 : bits(64)
register SCTLR_EL2 : bits(64)
register SCTLR_EL3 : bits(64)

$endif

val rSPS : forall 'N, 'N in {8, 16, 32, 64}. (int('N)) -> bits('N)
function rSPS(size) = rSP()[size-1..0]
val wSPS : forall 'N, 'N in {8, 16, 32, 64}. (int('N), bits('N)) -> unit
function wSPS(size, value) = wSP(sail_zero_extend(value, 64))

overload SP = {rSP, wSP, rSPS, wSPS}

/****** Register utilities, operands, ... *********/



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

/* Operand type: either a register or a 64-bit immediate */
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
