/* Helper functions for Load/Store operations */
function execute_load(t : reg_index, vaddr : bits(64)) -> unit = {
  let accdesc = create_readAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(vaddr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  /* Read value from memory and write to register Xt */
  let data = rMem(addr, accdesc);
  X(t) = data;
}

function execute_store(t : reg_index, vaddr : bits(64)) -> unit = {
  let accdesc = create_writeAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(vaddr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* Announce that a store will be performed to this address */
  wMem_Addr(addr);
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  /* Read value from register Xt and write to memory */
  let data = X(t);
  wMem(addr, data, accdesc);
}

/* LoadStore: LDR and STR (register and immediate forms) */
union clause ast = Load : (reg_index, reg_index, operand)
union clause ast = Store : (reg_index, reg_index, operand)

val decodeLoadStoreRegister : (bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> option(ast)

function clause decode (0b11@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister(opc, Rm, option_v, S, Rn, Rt)
}

function decodeLoadStoreRegister (opc, Rm, option_v, S, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  if option_v != 0b011 | S == bitone then None ()
  else if opc == 0b01 then Some(Load((t, n, OperandReg(m))))
  else if opc == 0b00 then Some(Store((t, n, OperandReg(m))))
  else None ();
}

val decodeLoadStoreImmediate : (bits(2), bits(12), bits(5), bits(5)) -> option(ast)

/* 11 111 0 01 opc imm12 Rn Rt */
function clause decode (0b11@0b111@0b0@0b01@(opc:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreImmediate(opc, imm12, Rn, Rt)
}

function decodeLoadStoreImmediate (opc, imm12, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  if opc == 0b01 then Some(Load((t, n, OperandImm(imm12))))
  else if opc == 0b00 then Some(Store((t, n, OperandImm(imm12))))
  else None()
}

/* LDR Xt, [Xn, Xm] or LDR Xt, [Xn, #pimm] */
function clause execute Load(t, n, op) = {
  let addr : bits(64) = match op {
    OperandReg(m) => X(n) + X(m),
    OperandImm(imm12) => X(n) + sail_zero_extend(imm12 @ 0b000, 64)
  };
  execute_load(t, addr);
}

/* STR Xt, [Xn, Xm] or STR Xt, [Xn, #pimm] */
function clause execute Store(t, n, op) = {
  let addr : bits(64) = match op {
    OperandReg(m) => X(n) + X(m),
    OperandImm(imm12) => X(n) + sail_zero_extend(imm12 @ 0b000, 64)
  };
  execute_store(t, addr);
}

/* Exclusive OR: EOR */
union clause ast = ExclusiveOr : (reg_index, reg_index, reg_index)

val decodeExclusiveOr : (bit, bits(2), bit, bits(5), bits(6), bits(5), bits(5)) -> option(ast)

function clause decode ([sf]@0b10@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeExclusiveOr(sf, shift, N, Rm, imm6, Rn, Rd)
}

function decodeExclusiveOr (sf, shift, N, Rm, imm6, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  if sf == bitzero & imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None ()
  else Some(ExclusiveOr((d,n,m)));
}

/* EOR Xd, Xn, Xm */
function clause execute ExclusiveOr(d, n, m) = {
  /* Increment the program counter, at the start, since no branching out possible */
  _PC = _PC + 4;
  /* Ask for the value of register Xn and record it in the local
   * variable operand1 */
  let operand1 = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable operand2 */
  let operand2 = X(m);
  /* Compute the bitwise exclusive OR, and ask for the value of
   * the result to be written to register Xd */
  X(d) = operand1 ^ operand2;
}

/* Move (register and immediate forms) */
union clause ast = Move : (reg_index, move_operand)

/* MOV (register) - Alias of ORR (shifted register) */
/* ORR (shifted register): sf 0 101010 shift 0 Rm imm6 Rn Rd */
/* MOV Xd, Xm is ORR Xd, XZR, Xm */
function clause decode (0b1@0b0@0b101010@0b00@0b0@(Rm:bits(5))@0b000000@0b11111@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let m : reg_index = unsigned(Rm);
  Some(Move((d, MoveReg(m))))
}

/* MOVZ: 1 10 100101 hw imm16 Rd */
function clause decode (0b1@0b10@0b100101@(hw:bits(2))@(imm16:bits(16))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  Some(Move((d, MoveImm(struct { imm = imm16, hw = hw }))))
}

/* MOV Xd, Xm or MOVZ Xd, #imm, LSL #shift */
function clause execute Move(d, op) = {
  _PC = _PC + 4;
  let res : bits(64) = match op {
    MoveReg(m) => X(m),
    MoveImm(data) => match data.hw {
      0b00 => sail_zero_extend(data.imm, 64),                /* imm at bits [15:0] */
      0b01 => sail_zero_extend(data.imm, 48) @ 0x0000,       /* imm at bits [31:16] */
      0b10 => sail_zero_extend(data.imm, 32) @ 0x00000000,   /* imm at bits [47:32] */
      0b11 => data.imm @ 0x000000000000                      /* imm at bits [63:48] */
    }
  };
  X(d) = res;
}

/* Arithmetic: ADD/SUB (register and immediate forms) */
union clause ast = Add : (reg_index, reg_index, operand)
union clause ast = Sub : (reg_index, reg_index, operand)

val decodeAddSub : (bit, bit, bit, bits(2), bits(12), bits(6), bits(5), bits(5), bits(5)) -> option(ast)

/* ADD (shifted register) */
function clause decode (0b1@0b00@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(bitone, bitzero, bitzero, shift, 0x000, imm6, Rm, Rn, Rd)
}

/* SUB (shifted register) */
function clause decode (0b1@0b10@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(bitone, bitone, bitzero, shift, 0x000, imm6, Rm, Rn, Rd)
}

/* ADD (immediate) */
function clause decode (0b1@0b00@0b10001@(shift:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(bitone, bitzero, bitone, shift, imm12, 0b000000, 0b00000, Rn, Rd)
}

/* SUB (immediate) */
function clause decode (0b1@0b10@0b10001@(shift:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(bitone, bitone, bitone, shift, imm12, 0b000000, 0b00000, Rn, Rd)
}

function decodeAddSub (sf, op, is_imm, shift, imm12, imm6, Rm, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  if is_imm == bitzero then {
    /* Register form */
    if imm6 != 0b000000 then None () /* We only support unshifted for now */
    else if op == bitzero then Some(Add((d, n, OperandReg(m))))
    else Some(Sub((d, n, OperandReg(m))))
  } else {
    /* Immediate form - only support shift == 0b00 (no shift) for now */
    if shift == 0b00 then {
      if op == bitzero then Some(Add((d, n, OperandImm(imm12))))
      else Some(Sub((d, n, OperandImm(imm12))))
    } else None()
  }
}

/* ADD Xd, Xn, Xm or ADD Xd, Xn, #imm */
function clause execute Add(d, n, op) = {
  _PC = _PC + 4;
  let op1 = X(n);
  let op2 : bits(64) = match op {
    OperandReg(m) => X(m),
    OperandImm(imm12) => sail_zero_extend(imm12, 64)
  };
  X(d) = op1 + op2;
}

/* SUB Xd, Xn, Xm or SUB Xd, Xn, #imm */
function clause execute Sub(d, n, op) = {
  _PC = _PC + 4;
  let op1 = X(n);
  let op2 : bits(64) = match op {
    OperandReg(m) => X(m),
    OperandImm(imm12) => sail_zero_extend(imm12, 64)
  };
  X(d) = op1 + (not_vec(op2) + 1);
}

/* Data Barrier */
union clause ast = DataMemoryBarrier : (MBReqDomain, MBReqTypes)
union clause ast = DataSynchronizationBarrier : (MBReqDomain, MBReqTypes)
union clause ast = InstructionSynchronizationBarrier : unit

val decodeDataBarrier : (bits(4), bool) -> option(ast)

function decodeDataBarrier(CRm, is_sync) = {
  let domain : MBReqDomain =
    match CRm[3..2] {
      0b11 => MBReqDomain_FullSystem,
      0b10 => MBReqDomain_InnerShareable,
      0b01 => MBReqDomain_Nonshareable,
      0b00 => MBReqDomain_OuterShareable,
      _ => return None()
    };

  let types : MBReqTypes =
    match CRm[1..0] {
      0b01 => MBReqTypes_Reads,
      0b10 => MBReqTypes_Writes,
      0b11 => MBReqTypes_All,
      _ => return None()
    };

  if is_sync then
    Some(DataSynchronizationBarrier(domain, types))
  else
    Some(DataMemoryBarrier(domain, types))
}

/* DMB */
function clause decode (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b1@0b01@0b11111) = {
  decodeDataBarrier(CRm, false)
}

function clause execute DataMemoryBarrier(domain, types) = {
  // Update the PC
  _PC = _PC + 4;
  // Then perform the barrier
  dataMemoryBarrier(domain, types);
}

/* DSB */
function clause decode (0b11010101000000110011@(CRm:bits(4))@0b100@0b11111) = {
  decodeDataBarrier(CRm, true)
}

function clause execute DataSynchronizationBarrier(domain, types) = {
  // Update the PC
  _PC = _PC + 4;
  // Then perform the barrier
  dataSynchronizationBarrer(domain, types)
}

/* ISB */
function clause decode (0b11010101000000110011@(CRm:bits(4))@0b110@0b11111) = {
  Some(InstructionSynchronizationBarrier())
}

function clause execute InstructionSynchronizationBarrier() = {
  // Update the PC
  _PC = _PC + 4;
  // Then perform the barrier
  instructionSynchronizationBarrier()
}

/* CompareAndBranch: CBZ */
union clause ast = CompareAndBranch : (reg_index, bits(64))

val decodeCompareAndBranch : (bits(19), bits(5)) -> option(ast)

function clause decode (0b1@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(imm19, Rt)
}

function decodeCompareAndBranch(imm19, Rt) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00,64);

  Some(CompareAndBranch(t,offset));
}

/* CBZ Xt, <offset> */
function clause execute CompareAndBranch(t, offset) = {
  /* Ask for the value of register Xt and record it in the local
   * variable operand */
  let operand = X(t);
  /* Check if operand is 0 */
  if operand == 0x0000000000000000 then {
    /* Ask for the value of the program counter register and record it
     * in the local variable base */
    let base = PC();
    /* Compute the address */
    let addr = base + offset;
    /* Ask for the value of result to be written to the program counter
     * register */
    PC() = addr;
  }
  else _PC = _PC + 4;
}
