/* LoadStore: LDR/STR, LDRH/STRH, LDRB/STRB (register and immediate forms)
 * size is the log of the byte size, writing 2^{size} bytes */
union clause ast = Load : (/* size:*/ range(0,3), reg_index, reg_index, operand)
union clause ast = Store : (/* size:*/ range(0,3), reg_index, reg_index, operand)

val decodeLoadStoreRegister : (bits(2), bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> option(ast)

/* LDR/STR register: size 111 0 00 opc 1 Rm option S 10 Rn Rt */
function clause decode ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister(size, opc, Rm, option_v, S, Rn, Rt)
}

function decodeLoadStoreRegister (size, opc, Rm, option_v, S, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  /* option_v == 0b011 and S == 1 means that the offset in Rm is used as is and not shifted or extended */
  if option_v != 0b011 | S == bitone then None ()
  else if opc == 0b01 then Some(Load((unsigned(size), t, n, OperandReg(m))))
  else if opc == 0b00 then Some(Store((unsigned(size), t, n, OperandReg(m))))
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
  if opc == 0b01 then Some(Load((unsigned(size), t, n, OperandImm(imm12))))
  else if opc == 0b00 then Some(Store((unsigned(size), t, n, OperandImm(imm12))))
  else None()
}

/* LDR/LDRH/LDRB Xt/Wt, [Xn, Xm] or [Xn, #pimm] */
function clause execute Load(size, t, n, op) = {
  /* Create an access descriptor (pure operation) */
  let accdesc = create_readAccessDescriptor();

  /* Compute the (virtual) address of the access */
  let vaddr : bits(64) = match op {
    OperandReg(m) => X(n) + X(m),
    /* Immediate scaled by access size: 8/4/2/1 bytes */
    OperandImm(imm12) =>
      X(n) + sail_shiftleft(sail_zero_extend(imm12, 64), size)
  };

  /* Translate the virtual address into the physical address.
   * In user mode, `translate_address` returns the input address. */
  let addr : bits(addr_size) =
    match translate_address(vaddr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };

  /* The instruction can't fault now, so update the PC */
  _PC = _PC + 4;

  /* Read value from memory and write to register Xt */
  X(t) = sail_zero_extend(rMem(2^size, addr, accdesc), 64);
}

/* STR/STRH/STRB Xt/Wt, [Xn, Xm] or [Xn, #pimm] */
function clause execute Store(size, t, n, op) = {
  /* Create an access descriptor (pure operation) */
  let accdesc = create_writeAccessDescriptor();

  /* Compute the (virtual) address of the access */
  let vaddr : bits(64) = match op {
    OperandReg(m) => X(n) + X(m),
    /* Immediate scaled by access size: 8/4/2/1 bytes */
    OperandImm(imm12) =>
      X(n) + sail_shiftleft(sail_zero_extend(imm12, 64), size)
  };
  /* Translate the virtual address into the physical address.
   * In user mode, `translate_address` returns the input address. */
  let addr : bits(addr_size) =
    match translate_address(vaddr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };

  /* Announce that a store will be performed to this address */
  wMem_Addr(addr);

  /* The instruction can't fault now, so update the PC */
  _PC = _PC + 4;

  /* Read value from register Xt and write to memory */
  wMem(2^size, addr, X(t)[(8*2^size-1)..0], accdesc)
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

  if imm6 != 0b000000 then None () /* We only support unshifted for now */
  else Some(ExclusiveOr((sf, d, n, m)));
}

/* EOR Xd/Wd, Xn/Wn, Xm/Wm */
function clause execute ExclusiveOr(sf, d, n, m) = {
  _PC = _PC + 4;
  let size = if sf == bitone then 64 else 32;
  let operand1 = XS(n, size);
  let operand2 = XS(m, size);
  XS(d, size) = operand1 ^ operand2;
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
  let size = if sf == bitone then 64 else 32;
  match op {
    MoveReg(m) => XS(d, size) = XS(m, size),
    MoveImm(data) => {
      /* Compute 64-bit result, then truncate for 32-bit */
      let res : bits(64) = sail_shiftleft(sail_zero_extend(data.imm, 64), 16 * unsigned(data.hw));
      XS(d, size) = res[size-1..0]
    }
  }
}

/* Arithmetic: ADD/SUB (register and immediate forms)
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = Add : (datasize, reg_index, reg_index, operand)
union clause ast = Sub : (datasize, reg_index, reg_index, operand)

/* ADD/SUB (shifted register) */
val decodeAddSubShift : (bit, bit, bits(2), bits(6), bits(5), bits(5), bits(5)) -> option(ast)
function clause decode ([sf]@[op]@0b0@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSubShift(sf, op, shift, imm6, Rm, Rn, Rd)
}

function decodeAddSubShift (sf, op, shift, imm6, Rm, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  if imm6 != 0b000000 then return None (); /* We only support unshifted for now */

  if op == bitzero then Some(Add((sf, d, n, OperandReg(m))))
  else Some(Sub((sf, d, n, OperandReg(m))))
}


val decodeAddSubImm : (bit, bit, bits(1), bits(12), bits(5), bits(5)) -> option(ast)
/* ADD/SUB (immediate) */
function clause decode ([sf]@[op]@0b0@0b100010@(sh:bits(1))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSubImm(sf, op, sh, imm12, Rn, Rd)
}

function decodeAddSubImm (sf, op, sh, imm12, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);

  if sh != 0b0 then return None(); /* Only support unshifted immediate */

  if op == bitzero then Some(Add((sf, d, n, OperandImm(imm12))))
  else Some(Sub((sf, d, n, OperandImm(imm12))))
}


/* ADD Xd/Wd, Xn/Wn, Xm/Wm or ADD Xd/Wd, Xn/Wn, #imm */
function clause execute Add(sf, d, n, op) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let op1 = XS(n, 'size);
  let op2 : bits('size) = match op {
    OperandReg(m) => XS(m, 'size),
    OperandImm(imm12) => sail_zero_extend(imm12, 'size)
  };
  XS(d, 'size) = op1 + op2;
}

/* SUB Xd/Wd, Xn/Wn, Xm/Wm or SUB Xd/Wd, Xn/Wn, #imm */
function clause execute Sub(sf, d, n, op) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let op1 = XS(n, 'size);
  let op2 : bits('size) = match op {
    OperandReg(m) => XS(m, 'size),
    OperandImm(imm12) => sail_zero_extend(imm12, 'size)
  };
  XS(d, 'size) = op1 + (not_vec(op2) + 1);
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

/* CompareAndBranch: CBZ
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = CompareAndBranch : (datasize, reg_index, bits(64))

val decodeCompareAndBranch : (bit, bits(19), bits(5)) -> option(ast)

/* CBZ: sf 011010 0 imm19 Rt */
function clause decode ([sf]@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(sf, imm19, Rt)
}

function decodeCompareAndBranch(sf, imm19, Rt) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00,64);

  Some(CompareAndBranch(sf, t, offset));
}

/* CBZ Xt/Wt, <offset> */
function clause execute CompareAndBranch(sf, t, offset) = {
  /* Get operand value - 64-bit or 32-bit (zero-extended for comparison) */
  let operand : bits(64) = if sf == bitone then X(t) else sail_zero_extend(W(t), 64);
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
