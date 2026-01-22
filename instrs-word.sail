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
  else if opc == 0b01 then Some(LoadRegister32((t,n,m)))
  else if opc == 0b00 then Some(StoreRegister32((t,n,m)))
  else None ();
}

/* LDR Wt, [Xn, Xm] - 32-bit word load */
function clause execute LoadRegister32(t, n, m) = {
  let base_addr = X(n);
  let offset = X(m);
  let addr = base_addr + offset;
  let accdesc = create_readAccessDescriptor();
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
  let accdesc = create_writeAccessDescriptor();
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
  let accdesc = create_readAccessDescriptor();
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
  let accdesc = create_writeAccessDescriptor();
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
