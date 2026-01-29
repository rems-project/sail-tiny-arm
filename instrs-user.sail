/* Helper functions for Load/Store operations
 * size: 00 = 8-bit (B), 01 = 16-bit (H), 10 = 32-bit (W), 11 = 64-bit (X) */
function execute_load(size : bits(2), t : reg_index, vaddr : bits(64)) -> unit = {
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
  /* Read value from memory and write to register */
  match size {
    0b11 => { let data : bits(64) = rMem(8, addr, accdesc); X(t) = data },
    0b10 => { let data : bits(32) = rMem(4, addr, accdesc); W(t) = data },
    0b01 => { let data : bits(16) = rMem(2, addr, accdesc); W(t) = sail_zero_extend(data, 32) },
    0b00 => { let data : bits(8)  = rMem(1, addr, accdesc); W(t) = sail_zero_extend(data, 32) }
  }
}

function execute_store(size : bits(2), t : reg_index, vaddr : bits(64)) -> unit = {
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
  /* Read value from register and write to memory */
  match size {
    0b11 => { let data = X(t); wMem(8, addr, data, accdesc) },
    0b10 => { let data = W(t); wMem(4, addr, data, accdesc) },
    0b01 => { let data = W(t); wMem(2, addr, data[15..0], accdesc) },
    0b00 => { let data = W(t); wMem(1, addr, data[7..0], accdesc) }
  }
}

/* LoadStore: LDR/STR, LDRH/STRH, LDRB/STRB (register and immediate forms)
 * size: 00 = 8-bit (B), 01 = 16-bit (H), 10 = 32-bit (W), 11 = 64-bit (X) */
union clause ast = Load : (bits(2), reg_index, reg_index, operand)
union clause ast = Store : (bits(2), reg_index, reg_index, operand)

val decodeLoadStoreRegister : (bits(2), bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> option(ast)

/* LDR/STR register: size 111 0 00 opc 1 Rm option S 10 Rn Rt */
function clause decode ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister(size, opc, Rm, option_v, S, Rn, Rt)
}

function decodeLoadStoreRegister (size, opc, Rm, option_v, S, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  if option_v != 0b011 | S == bitone then None ()
  else if opc == 0b01 then Some(Load((size, t, n, OperandReg(m))))
  else if opc == 0b00 then Some(Store((size, t, n, OperandReg(m))))
  else None ();
}

val decodeLoadStoreImmediate : (bits(2), bits(2), bits(12), bits(5), bits(5)) -> option(ast)

/* LDR/STR immediate: size 111 0 01 opc imm12 Rn Rt */
function clause decode ((size:bits(2))@0b111@0b0@0b01@(opc:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreImmediate(size, opc, imm12, Rn, Rt)
}

function decodeLoadStoreImmediate (size, opc, imm12, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  if opc == 0b01 then Some(Load((size, t, n, OperandImm(imm12))))
  else if opc == 0b00 then Some(Store((size, t, n, OperandImm(imm12))))
  else None()
}

/* LDR/LDRH/LDRB Xt/Wt, [Xn, Xm] or [Xn, #pimm] */
function clause execute Load(size, t, n, op) = {
  let addr : bits(64) = match op {
    OperandReg(m) => X(n) + X(m),
    /* Immediate scaled by access size: 8/4/2/1 bytes */
    OperandImm(imm12) => match size {
      0b11 => X(n) + sail_zero_extend(imm12 @ 0b000, 64),
      0b10 => X(n) + sail_zero_extend(imm12 @ 0b00, 64),
      0b01 => X(n) + sail_zero_extend(imm12 @ 0b0, 64),
      0b00 => X(n) + sail_zero_extend(imm12, 64)
    }
  };
  execute_load(size, t, addr);
}

/* STR/STRH/STRB Xt/Wt, [Xn, Xm] or [Xn, #pimm] */
function clause execute Store(size, t, n, op) = {
  let addr : bits(64) = match op {
    OperandReg(m) => X(n) + X(m),
    /* Immediate scaled by access size: 8/4/2/1 bytes */
    OperandImm(imm12) => match size {
      0b11 => X(n) + sail_zero_extend(imm12 @ 0b000, 64),
      0b10 => X(n) + sail_zero_extend(imm12 @ 0b00, 64),
      0b01 => X(n) + sail_zero_extend(imm12 @ 0b0, 64),
      0b00 => X(n) + sail_zero_extend(imm12, 64)
    }
  };
  execute_store(size, t, addr);
}

/* Exclusive OR: EOR
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = ExclusiveOr : (datasize, reg_index, reg_index, reg_index)

val decodeExclusiveOr : (bit, bits(2), bit, bits(5), bits(6), bits(5), bits(5)) -> option(ast)

/* EOR (shifted register): sf 10 01010 shift N Rm imm6 Rn Rd */
function clause decode ([sf]@0b10@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeExclusiveOr(sf, shift, N, Rm, imm6, Rn, Rd)
}

function decodeExclusiveOr (sf, shift, N, Rm, imm6, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  /* For 32-bit (sf=0), imm6[5] must be 0 */
  if sf == bitzero & imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None () /* We only support unshifted for now */
  else Some(ExclusiveOr((sf, d, n, m)));
}

/* EOR Xd/Wd, Xn/Wn, Xm/Wm */
function clause execute ExclusiveOr(sf, d, n, m) = {
  _PC = _PC + 4;
  if sf == bitone then {
    /* 64-bit */
    let operand1 = X(n);
    let operand2 = X(m);
    X(d) = operand1 ^ operand2;
  } else {
    /* 32-bit */
    let operand1 = W(n);
    let operand2 = W(m);
    W(d) = operand1 ^ operand2;
  }
}

/* Move (register and immediate forms)
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = Move : (datasize, reg_index, move_operand)

/* MOV (register) - Alias of ORR (shifted register) */
/* ORR (shifted register): sf 0 101010 shift 0 Rm imm6 Rn Rd */
/* MOV Xd/Wd, Xm/Wm is ORR Xd/Wd, XZR/WZR, Xm/Wm */
function clause decode ([sf]@0b0@0b101010@0b00@0b0@(Rm:bits(5))@0b000000@0b11111@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let m : reg_index = unsigned(Rm);
  Some(Move((sf, d, MoveReg(m))))
}

/* MOVZ: sf 10 100101 hw imm16 Rd */
function clause decode ([sf]@0b10@0b100101@(hw:bits(2))@(imm16:bits(16))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  /* For 32-bit (sf=0), hw must be 00 or 01 (hw[1]=0) */
  if sf == bitzero & hw[1] == bitone then None()
  else Some(Move((sf, d, MoveImm(struct { imm = imm16, hw = hw }))))
}

/* MOV Xd/Wd, Xm/Wm or MOVZ Xd/Wd, #imm, LSL #shift */
function clause execute Move(sf, d, op) = {
  _PC = _PC + 4;
  if sf == bitone then {
    /* 64-bit */
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
  } else {
    /* 32-bit - zero-extended on write */
    let res : bits(32) = match op {
      MoveReg(m) => W(m),
      MoveImm(data) => match data.hw {
        0b00 => sail_zero_extend(data.imm, 32),          /* imm at bits [15:0] */
        0b01 => data.imm @ 0x0000,                       /* imm at bits [31:16] */
        _ => sail_zeros(32)                              /* unreachable: validated in decode */
      }
    };
    W(d) = res;
  }
}

/* Arithmetic: ADD/SUB (register and immediate forms)
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = Add : (datasize, reg_index, reg_index, operand)
union clause ast = Sub : (datasize, reg_index, reg_index, operand)

val decodeAddSub : (bit, bit, bit, bits(2), bits(12), bits(6), bits(5), bits(5), bits(5)) -> option(ast)

/* ADD (shifted register): sf 00 01011 shift 0 Rm imm6 Rn Rd */
function clause decode ([sf]@0b00@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(sf, bitzero, bitzero, shift, 0x000, imm6, Rm, Rn, Rd)
}

/* SUB (shifted register): sf 10 01011 shift 0 Rm imm6 Rn Rd */
function clause decode ([sf]@0b10@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(sf, bitone, bitzero, shift, 0x000, imm6, Rm, Rn, Rd)
}

/* ADD (immediate): sf 00 10001 shift imm12 Rn Rd */
function clause decode ([sf]@0b00@0b10001@(shift:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(sf, bitzero, bitone, shift, imm12, 0b000000, 0b00000, Rn, Rd)
}

/* SUB (immediate): sf 10 10001 shift imm12 Rn Rd */
function clause decode ([sf]@0b10@0b10001@(shift:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSub(sf, bitone, bitone, shift, imm12, 0b000000, 0b00000, Rn, Rd)
}

function decodeAddSub (sf, op, is_imm, shift, imm12, imm6, Rm, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  /* For 32-bit (sf=0), imm6[5] must be 0 in register form */
  if sf == bitzero & is_imm == bitzero & imm6[5] == bitone then None ()
  else if is_imm == bitzero then {
    /* Register form */
    if imm6 != 0b000000 then None () /* We only support unshifted for now */
    else if op == bitzero then Some(Add((sf, d, n, OperandReg(m))))
    else Some(Sub((sf, d, n, OperandReg(m))))
  } else {
    /* Immediate form - only support shift == 0b00 (no shift) for now */
    if shift == 0b00 then {
      if op == bitzero then Some(Add((sf, d, n, OperandImm(imm12))))
      else Some(Sub((sf, d, n, OperandImm(imm12))))
    } else None()
  }
}

/* ADD Xd/Wd, Xn/Wn, Xm/Wm or ADD Xd/Wd, Xn/Wn, #imm */
function clause execute Add(sf, d, n, op) = {
  _PC = _PC + 4;
  if sf == bitone then {
    /* 64-bit */
    let op1 = X(n);
    let op2 : bits(64) = match op {
      OperandReg(m) => X(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 64)
    };
    X(d) = op1 + op2;
  } else {
    /* 32-bit */
    let op1 = W(n);
    let op2 : bits(32) = match op {
      OperandReg(m) => W(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 32)
    };
    W(d) = op1 + op2;
  }
}

/* SUB Xd/Wd, Xn/Wn, Xm/Wm or SUB Xd/Wd, Xn/Wn, #imm */
function clause execute Sub(sf, d, n, op) = {
  _PC = _PC + 4;
  if sf == bitone then {
    /* 64-bit */
    let op1 = X(n);
    let op2 : bits(64) = match op {
      OperandReg(m) => X(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 64)
    };
    X(d) = op1 + (not_vec(op2) + 1);
  } else {
    /* 32-bit */
    let op1 = W(n);
    let op2 : bits(32) = match op {
      OperandReg(m) => W(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 32)
    };
    W(d) = op1 + (not_vec(op2) + 1);
  }
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

/* NOP: No Operation */
union clause ast = Nop : unit

/* NOP: 1101 0101 0000 0011 0010 0000 0001 1111 = 0xD503201F */
function clause decode (0b11010101000000110010000000011111) = {
  Some(Nop())
}

function clause execute Nop() = {
  /* Just advance the PC */
  _PC = _PC + 4;
}

/* CompareAndBranch: CBZ / CBNZ
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = CompareAndBranch : (datasize, reg_index, bits(64), bool)

val decodeCompareAndBranch : (bit, bit, bits(19), bits(5)) -> option(ast)

/* CBZ: sf 011010 0 imm19 Rt */
function clause decode ([sf]@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(sf, bitzero, imm19, Rt)
}

/* CBNZ: sf 011010 1 imm19 Rt */
function clause decode ([sf]@0b011010@0b1@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(sf, bitone, imm19, Rt)
}

function decodeCompareAndBranch(sf, op, imm19, Rt) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00,64);
  /* iszero: true for CBZ (op=0), false for CBNZ (op=1) */
  let iszero : bool = (op == bitzero);

  Some(CompareAndBranch(sf, t, offset, iszero));
}

/* CBZ/CBNZ Xt/Wt, <offset> */
function clause execute CompareAndBranch(sf, t, offset, iszero) = {
  /* Get operand value - 64-bit or 32-bit (zero-extended for comparison) */
  let operand : bits(64) = if sf == bitone then X(t) else sail_zero_extend(W(t), 64);
  /* Check condition: CBZ branches if zero, CBNZ branches if not zero */
  let condition_met = if iszero
    then operand == 0x0000000000000000
    else operand != 0x0000000000000000;
  if condition_met then {
    let base = PC();
    let addr = base + offset;
    PC() = addr;
  }
  else _PC = _PC + 4;
}

/* Unconditional Branch: B */
union clause ast = Branch : bits(64)

/* B <label> - Encoding: 0 00101 imm26 */
function clause decode (0b0@0b00101@(imm26:bits(26))) = {
  /* Sign-extend imm26 shifted left by 2 to get byte offset */
  let offset : bits(64) = sail_sign_extend(imm26 @ 0b00, 64);
  Some(Branch(offset))
}

/* B <offset> */
function clause execute Branch(offset) = {
  /* Get the current program counter */
  let base = PC();
  /* Compute the target address (PC-relative) */
  let target = base + offset;
  /* Branch to the target address */
  PC() = target;
}
