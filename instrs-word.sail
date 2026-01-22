/* 32-bit ADD/SUB variants */
union clause ast = Add32 : (reg_index, reg_index, reg_index)
union clause ast = Sub32 : (reg_index, reg_index, reg_index)
union clause ast = AddImmediate32 : (reg_index, reg_index, bits(12))
union clause ast = SubImmediate32 : (reg_index, reg_index, bits(12))

/* ADD (shifted register) - 32-bit: 0 00 01011 shift 0 Rm imm6 Rn Rd */
function clause decode (0b0@0b00@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  /* For 32-bit, imm6[5] must be 0 (shift amount 0-31 only) */
  if imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None () /* Simplification: no shift support yet */
  else Some(Add32((d,n,m)))
}

/* SUB (shifted register) - 32-bit: 0 10 01011 shift 0 Rm imm6 Rn Rd */
function clause decode (0b0@0b10@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  if imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None ()
  else Some(Sub32((d,n,m)))
}

/* ADD (immediate) - 32-bit: 0 00 10001 sh imm12 Rn Rd */
function clause decode (0b0@0b00@0b10001@(shift:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  if shift == 0b00 then Some(AddImmediate32((d,n,imm12)))
  else None()
}

/* SUB (immediate) - 32-bit: 0 10 10001 sh imm12 Rn Rd */
function clause decode (0b0@0b10@0b10001@(shift:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  if shift == 0b00 then Some(SubImmediate32((d,n,imm12)))
  else None()
}

/* ADD Wd, Wn, Wm */
function clause execute Add32(d, n, m) = {
  _PC = _PC + 4;
  let op1 : bits(32) = X(n)[31..0];
  let op2 : bits(32) = X(m)[31..0];
  let result : bits(32) = op1 + op2;
  /* Zero-extend 32-bit result to 64 bits */
  X(d) = sail_zero_extend(result, 64);
}

/* SUB Wd, Wn, Wm */
function clause execute Sub32(d, n, m) = {
  _PC = _PC + 4;
  let op1 : bits(32) = X(n)[31..0];
  let op2 : bits(32) = X(m)[31..0];
  let result : bits(32) = op1 + (not_vec(op2) + 1);
  X(d) = sail_zero_extend(result, 64);
}

/* ADD Wd, Wn, #imm */
function clause execute AddImmediate32(d, n, imm12) = {
  _PC = _PC + 4;
  let op1 : bits(32) = X(n)[31..0];
  let op2 : bits(32) = sail_zero_extend(imm12, 32);
  let result : bits(32) = op1 + op2;
  X(d) = sail_zero_extend(result, 64);
}

/* SUB Wd, Wn, #imm */
function clause execute SubImmediate32(d, n, imm12) = {
  _PC = _PC + 4;
  let op1 : bits(32) = X(n)[31..0];
  let op2 : bits(32) = sail_zero_extend(imm12, 32);
  let result : bits(32) = op1 + (not_vec(op2) + 1);
  X(d) = sail_zero_extend(result, 64);
}

/* ========================================================================
 * Logical Instructions: EOR with 32-bit support
 * ========================================================================
 *
 * Encoding (shifted register):
 *   sf 10 01010 shift N Rm imm6 Rn Rd
 *
 * When sf=0: 32-bit operation, imm6[5] must be 0
 * When sf=1: 64-bit operation
 */

union clause ast = ExclusiveOr32 : (reg_index, reg_index, reg_index)

/* EOR (shifted register) - 32-bit: 0 10 01010 shift N Rm imm6 Rn Rd */
function clause decode (0b0@0b10@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  /* For 32-bit, imm6[5] must be 0 */
  if imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None ()
  else Some(ExclusiveOr32((d,n,m)))
}

/* EOR Wd, Wn, Wm */
function clause execute ExclusiveOr32(d, n, m) = {
  _PC = _PC + 4;
  let op1 : bits(32) = X(n)[31..0];
  let op2 : bits(32) = X(m)[31..0];
  let result : bits(32) = op1 ^ op2;
  X(d) = sail_zero_extend(result, 64);
}

/* ========================================================================
 * Move Instructions: MOV with 32-bit support
 * ========================================================================
 *
 * MOV (register) is alias of ORR (shifted register):
 *   sf 0 101010 00 0 Rm 000000 11111 Rd
 *
 * When sf=0: MOV Wd, Wm (zero-extends to 64 bits)
 * When sf=1: MOV Xd, Xm
 */

union clause ast = Move32 : (reg_index, reg_index)

/* MOV Wd, Wm - 32-bit: 0 0 101010 00 0 Rm 000000 11111 Rd */
function clause decode (0b0@0b0@0b101010@0b00@0b0@(Rm:bits(5))@0b000000@0b11111@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let m : reg_index = unsigned(Rm);
  Some(Move32((d,m)))
}

/* MOV Wd, Wm */
function clause execute Move32(d, m) = {
  _PC = _PC + 4;
  let value : bits(32) = X(m)[31..0];
  X(d) = sail_zero_extend(value, 64);
}

/* ========================================================================
 * Move Wide Instructions: MOVZ with 32-bit support
 * ========================================================================
 *
 * Encoding:
 *   sf 10 100101 hw imm16 Rd
 *
 * When sf=0: 32-bit, hw must be 0x or 1x (pos 0 or 16)
 * When sf=1: 64-bit, hw can be 00, 01, 10, or 11
 */

union clause ast = MoveWide32 : (reg_index, bits(16), bits(2))

/* MOVZ - 32-bit: 0 10 100101 hw imm16 Rd */
function clause decode (0b0@0b10@0b100101@(hw:bits(2))@(imm16:bits(16))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  /* For 32-bit, hw[1] must be 0 (only positions 0 and 16 valid) */
  if hw[1] == bitone then None ()
  else Some(MoveWide32(d, imm16, hw))
}

/* MOVZ Wd, #imm, LSL #shift */
function clause execute MoveWide32(d, imm, hw) = {
  _PC = _PC + 4;
  let res : bits(32) = match hw {
    0b00 => sail_zero_extend(imm, 32),       /* imm at bits [15:0] */
    0b01 => imm @ 0x0000,                     /* imm at bits [31:16] */
    _ => sail_zero_extend(imm, 32)            /* Should not happen due to decode constraint */
  };
  X(d) = sail_zero_extend(res, 64);
}

/* ========================================================================
 * Compare and Branch: CBZ/CBNZ with 32-bit support
 * ========================================================================
 *
 * Encoding:
 *   sf 011010 op imm19 Rt
 *
 * When sf=0: Compare lower 32 bits of Wt
 * When sf=1: Compare full 64 bits of Xt
 */

union clause ast = CompareAndBranch32 : (reg_index, bits(64), bool)

/* CBZ - 32-bit: 0 011010 0 imm19 Rt */
function clause decode (0b0@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00, 64);
  Some(CompareAndBranch32(t, offset, false))
}

/* CBNZ - 32-bit: 0 011010 1 imm19 Rt */
function clause decode (0b0@0b011010@0b1@(imm19:bits(19))@(Rt:bits(5))) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00, 64);
  Some(CompareAndBranch32(t, offset, true))
}

/* CBZ/CBNZ Wt, <offset> */
function clause execute CompareAndBranch32(t, offset, branch_on_nonzero) = {
  /* Compare only lower 32 bits */
  let operand : bits(32) = X(t)[31..0];
  let is_zero = (operand == 0x00000000);
  let should_branch = if branch_on_nonzero then not_bool(is_zero) else is_zero;

  if should_branch then {
    let base = _PC;
    let addr = base + offset;
    _PC = addr;
  }
  else _PC = _PC + 4;
}

/* ========================================================================
 * Load/Store Instructions: 32-bit (word) variants
 * ========================================================================
 *
 * Load/Store use size field (bits [31:30]) instead of sf:
 *   00 = byte (8-bit)
 *   01 = halfword (16-bit)
 *   10 = word (32-bit)      <-- This file implements these
 *   11 = doubleword (64-bit)
 *
 * For word (32-bit) loads:
 *   - LDR Wt, [Xn, ...] loads 32 bits and zero-extends to 64
 *   - STR Wt, [Xn, ...] stores lower 32 bits
 *
 * Encoding (unsigned immediate):
 *   size 111 0 01 opc imm12 Rn Rt
 *   size=10 for 32-bit word operations
 *
 * Encoding (register offset):
 *   size 111 0 00 opc 1 Rm option S 10 Rn Rt
 *   size=10 for 32-bit word operations
 */

union clause ast = LoadRegister32 : (reg_index, reg_index, reg_index)
union clause ast = StoreRegister32 : (reg_index, reg_index, reg_index)
union clause ast = LoadImmediate32 : (reg_index, reg_index, bits(12))
union clause ast = StoreImmediate32 : (reg_index, reg_index, bits(12))

val decodeLoadStoreRegister32 : (bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> option(ast)

/* Load/Store Register (register offset) - 32-bit word */
/* 10 111 0 00 opc 1 Rm option S 10 Rn Rt */
function clause decode (0b10@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister32(opc, Rm, option_v, S, Rn, Rt)
}

function decodeLoadStoreRegister32 (opc, Rm, option_v, S, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  /* option_v == 0b011 and S == 0 means offset used as-is (no shift/extend) */
  /* For 32-bit with S==1, offset would be shifted by 2 (scale for 4-byte access) */
  if option_v != 0b011 then None ()
  else if opc == 0b01
  then Some(LoadRegister32((t,n,m)))
  else if opc == 0b00
  then Some(StoreRegister32((t,n,m)))
  else None ();
}

/* LDR Wt, [Xn, Xm] - 32-bit word load */
function clause execute LoadRegister32(t, n, m) = {
  let base_addr = X(n);
  let offset = X(m);
  let addr = base_addr + offset;
  let accdesc = create_readAccessDescriptor(false, false, false);
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };
  _PC = _PC + 4;
  /* Read 4 bytes (32 bits) from memory */
  let data : bits(32) = rMem32(addr, accdesc);
  /* Zero-extend to 64 bits when writing to register */
  X(t) = sail_zero_extend(data, 64);
}

/* STR Wt, [Xn, Xm] - 32-bit word store */
function clause execute StoreRegister32(t, n, m) = {
  let base_addr = X(n);
  let offset = X(m);
  let addr = base_addr + offset;
  let accdesc = create_writeAccessDescriptor(false, false);
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };
  wMem_Addr(addr);
  _PC = _PC + 4;
  /* Store lower 32 bits of register */
  let data : bits(32) = X(t)[31..0];
  wMem32(addr, data, accdesc);
}

val decodeLoadStoreImmediate32 : (bits(2), bits(12), bits(5), bits(5)) -> option(ast)

/* Load/Store Register (Unsigned Immediate) - 32-bit word */
/* 10 111 0 01 opc imm12 Rn Rt */
function clause decode (0b10@0b111@0b0@0b01@(opc:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreImmediate32(opc, imm12, Rn, Rt)
}

function decodeLoadStoreImmediate32 (opc, imm12, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  if opc == 0b01
  then Some(LoadImmediate32((t,n,imm12)))
  else if opc == 0b00
  then Some(StoreImmediate32((t,n,imm12)))
  else None()
}

/* LDR Wt, [Xn, #pimm] - 32-bit word load with immediate offset */
function clause execute LoadImmediate32(t, n, imm12) = {
  let base_addr = X(n);
  /* The immediate is scaled by 4 (word size) */
  let offset : bits(64) = sail_zero_extend(imm12 @ 0b00, 64);
  let addr = base_addr + offset;
  let accdesc = create_readAccessDescriptor(false, false, false);
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };
  _PC = _PC + 4;
  let data : bits(32) = rMem32(addr, accdesc);
  X(t) = sail_zero_extend(data, 64);
}

/* STR Wt, [Xn, #pimm] - 32-bit word store with immediate offset */
function clause execute StoreImmediate32(t, n, imm12) = {
  let base_addr = X(n);
  /* The immediate is scaled by 4 (word size) */
  let offset : bits(64) = sail_zero_extend(imm12 @ 0b00, 64);
  let addr = base_addr + offset;
  let accdesc = create_writeAccessDescriptor(false, false);
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };
  wMem_Addr(addr);
  _PC = _PC + 4;
  let data : bits(32) = X(t)[31..0];
  wMem32(addr, data, accdesc);
}

/* ========================================================================
 * Required Helper Functions (to be added to memory interface)
 * ========================================================================
 *
 * The following functions are needed for 32-bit memory operations:
 *
 * val rMem32 : (bits(addr_size), AccessDescriptor) -> bits(32)
 * val wMem32 : (bits(addr_size), bits(32), AccessDescriptor) -> unit
 *
 * These should read/write 4 bytes from/to memory at the given address.
 */

/* ========================================================================
 * Future Extensions
 * ========================================================================
 *
 * Additional instructions that could support 32-bit variants:
 *
 * Logical operations:
 *   - AND, ORR, BIC, EON, ORN (shifted register)
 *   - AND, ORR, EOR (immediate) - uses different bitmask encoding
 *
 * Arithmetic with flags:
 *   - ADDS, SUBS (set flags based on 32-bit result)
 *   - CMP, CMN (compare using 32-bit operands)
 *
 * Shift/rotate:
 *   - LSL, LSR, ASR, ROR (shift amount mod 32 for W registers)
 *
 * Bit manipulation:
 *   - CLZ, CLS, RBIT, REV (operate on 32 bits)
 *
 * Multiply:
 *   - MUL, MADD, MSUB (32-bit multiply)
 *   - SMULL, UMULL (32x32->64 widening multiply)
 *
 * Division:
 *   - SDIV, UDIV (32-bit division)
 *
 * Load/Store additional sizes:
 *   - LDRB/STRB (8-bit byte)
 *   - LDRH/STRH (16-bit halfword)
 *   - LDRSB/LDRSH/LDRSW (sign-extending loads)
 */

/* ========================================================================
 * Exclusive and Acquire/Release Load/Store Instructions (32-bit)
 * ========================================================================
 *
 * 32-bit variants of exclusive and acquire/release memory access.
 * See instrs-atomic.sail for 64-bit variants and detailed documentation.
 */

/* ========================================================================
 * Load Exclusive Register (LDXR) - 32-bit
 * ========================================================================
 */

union clause ast = LoadExclusive32 : (reg_index, reg_index)

/* LDXR Wt, [Xn]
 * Encoding: 10 001000 0 1 0 11111 0 11111 Rn Rt */
function clause decode (0b10@0b001000@0b0@0b1@0b0@0b11111@0b0@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(LoadExclusive32(unsigned(Rt), unsigned(Rn)))
}

/* LDXR Wt, [Xn] - 32-bit */
function clause execute LoadExclusive32(t, n) = {
  let addr = X(n);
  let accdesc = create_readAccessDescriptor(true, false, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  _PC = _PC + 4;
  let data : bits(32) = rMem32(addr, accdesc);
  X(t) = sail_zero_extend(data, 64);
}

/* ========================================================================
 * Store Exclusive Register (STXR) - 32-bit
 * ========================================================================
 */

union clause ast = StoreExclusive32 : (reg_index, reg_index, reg_index)

/* STXR Ws, Wt, [Xn]
 * Encoding: 10 001000 0 0 0 Rs 0 11111 Rn Rt */
function clause decode (0b10@0b001000@0b0@0b0@0b0@(Rs:bits(5))@0b0@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(StoreExclusive32(unsigned(Rs), unsigned(Rt), unsigned(Rn)))
}

/* STXR Ws, Wt, [Xn] - 32-bit */
function clause execute StoreExclusive32(s, t, n) = {
  let addr = X(n);
  let accdesc = create_writeAccessDescriptor(true, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  wMem_Addr(addr);
  _PC = _PC + 4;
  let data : bits(32) = X(t)[31..0];

  let status = wMemExclusive32(addr, data, accdesc);
  X(s) = sail_zero_extend(status, 64);
}

/* ========================================================================
 * Load-Acquire Exclusive Register (LDAXR) - 32-bit
 * ========================================================================
 */

union clause ast = LoadAcquireExclusive32 : (reg_index, reg_index)

/* LDAXR Wt, [Xn]
 * Encoding: 10 001000 0 1 0 11111 1 11111 Rn Rt */
function clause decode (0b10@0b001000@0b0@0b1@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(LoadAcquireExclusive32(unsigned(Rt), unsigned(Rn)))
}

/* LDAXR Wt, [Xn] - 32-bit */
function clause execute LoadAcquireExclusive32(t, n) = {
  let addr = X(n);
  let accdesc = create_readAccessDescriptor(true, true, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  _PC = _PC + 4;
  let data : bits(32) = rMem32(addr, accdesc);
  X(t) = sail_zero_extend(data, 64);
}

/* ========================================================================
 * Store-Release Exclusive Register (STLXR) - 32-bit
 * ========================================================================
 */

union clause ast = StoreReleaseExclusive32 : (reg_index, reg_index, reg_index)

/* STLXR Ws, Wt, [Xn]
 * Encoding: 10 001000 0 0 0 Rs 1 11111 Rn Rt */
function clause decode (0b10@0b001000@0b0@0b0@0b0@(Rs:bits(5))@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(StoreReleaseExclusive32(unsigned(Rs), unsigned(Rt), unsigned(Rn)))
}

/* STLXR Ws, Wt, [Xn] - 32-bit */
function clause execute StoreReleaseExclusive32(s, t, n) = {
  let addr = X(n);
  let accdesc = create_writeAccessDescriptor(true, true);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  wMem_Addr(addr);
  _PC = _PC + 4;
  let data : bits(32) = X(t)[31..0];

  let status = wMemExclusive32(addr, data, accdesc);
  X(s) = sail_zero_extend(status, 64);
}

/* ========================================================================
 * Load-Acquire Register (LDAR) - 32-bit
 * ========================================================================
 */

union clause ast = LoadAcquire32 : (reg_index, reg_index)

/* LDAR Wt, [Xn]
 * Encoding: 10 001000 1 1 0 11111 1 11111 Rn Rt */
function clause decode (0b10@0b001000@0b1@0b1@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(LoadAcquire32(unsigned(Rt), unsigned(Rn)))
}

/* LDAR Wt, [Xn] - 32-bit */
function clause execute LoadAcquire32(t, n) = {
  let addr = X(n);
  let accdesc = create_readAccessDescriptor(false, true, false);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  _PC = _PC + 4;
  let data : bits(32) = rMem32(addr, accdesc);
  X(t) = sail_zero_extend(data, 64);
}

/* ========================================================================
 * Store-Release Register (STLR) - 32-bit
 * ========================================================================
 */

union clause ast = StoreRelease32 : (reg_index, reg_index)

/* STLR Wt, [Xn]
 * Encoding: 10 001000 1 0 0 11111 1 11111 Rn Rt */
function clause decode (0b10@0b001000@0b1@0b0@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  Some(StoreRelease32(unsigned(Rt), unsigned(Rn)))
}

/* STLR Wt, [Xn] - 32-bit */
function clause execute StoreRelease32(t, n) = {
  let addr = X(n);
  let accdesc = create_writeAccessDescriptor(false, true);

  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return ()
    };

  wMem_Addr(addr);
  _PC = _PC + 4;
  let data : bits(32) = X(t)[31..0];
  wMem32(addr, data, accdesc);
}
