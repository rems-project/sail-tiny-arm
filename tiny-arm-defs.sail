type reg_index = range(0, 31)

register _PC : bits(64)

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

overload X = {rX, wX}

function rPC() -> bits(64) = _PC
function wPC(pc : bits(64)) -> unit = _PC = pc

overload PC = {rPC, wPC}

$ifdef SYSTEM_TINY_ARM

// We fix the size to 64 and happyly ignore 128 bits register extension for VMSA128

register SP_EL0 : bits(64)
register SP_EL1 : bits(64)
register SP_EL2 : bits(64)
register SP_EL3 : bits(64)

register ELR_EL1 : bits(64)
register ELR_EL2 : bits(64)
register ELR_EL3 : bits(64)

// TODO: Split into dependency carring components
register PSTATE : bits(64)

register ESR_EL1 : bits(64)
register ESR_EL2 : bits(64)
register ESR_EL3 : bits(64)

register FAR_EL1 : bits(64)
register FAR_EL2 : bits(64)
register FAR_EL3 : bits(64)

register PAR_EL1 : bits(64)

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

$endif
