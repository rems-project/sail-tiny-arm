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
  let imm = sail_zero_extend(imm12, 64);
  if opc == 0b01 then Some(Load((unsigned(size), t, n, OperandImm(imm))))
  else if opc == 0b00 then Some(Store((unsigned(size), t, n, OperandImm(imm))))
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
    OperandImm(imm) => X(n) + sail_shiftleft(imm, size)
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


/* EOR/ORR/AND
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = BitwiseLogic : (datasize, bitwise_op, reg_index, reg_index, operand)

function decode_bitwise_op(opc : bits(2)) -> bitwise_op =
  match opc {
    0b00 => And,
    0b10 => Eor,
    0b01 => Or,
    0b11 => fail("ANDS unsupported")
  }

/* EOR/ORR/AND (shifted register): sf opc 01010 shift 0 Rm 000000 Rn Rd */
function clause decode ([sf]@(opc : bits(2))@0b01010@(shift:bits(2))@0b0@(Rm:bits(5))@0b000000@(Rn:bits(5))@(Rd:bits(5))) = {
  if opc == 0b11 then return None(); // ANDS unsupported
  let op = decode_bitwise_op(opc);
  Some(BitwiseLogic(sf, op, unsigned(Rd), unsigned(Rn), OperandReg(unsigned(Rm))))
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

/* EOR/ORR/AND (immediate): sf opc 100100 N immr imms Rn Rd */
function clause decode ([sf]@(opc : bits(2))@0b100100@[N]@(immr:bits(6))@(imms:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  if opc == 0b11 then return None(); // ANDS unsupported
  let op = decode_bitwise_op(opc);
  if N == bitone & sf == bitzero then return None();
  let mask = decode_bitmask(N, imms, immr); //

  Some(BitwiseLogic(sf, op, unsigned(Rd), unsigned(Rn), OperandImm(mask)))
}

/* EOR/ORR/AND Xd/Wd, Xn/Wn, Xm/Wm and EOR/ORR/AND Xd/Wd, Xn/Wn, #imm */
function clause execute BitwiseLogic(sf, op, d, n, op2) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let operand1 = XS(n, size);
  let operand2 : bits('size) = match op2 {
      OperandReg(m) => XS(m, size),
      OperandImm(mask) => mask[size-1..0]
    };
  match op {
    Eor => XS(d, size) = operand1 ^ operand2,
    Or => XS(d, size) = operand1 | operand2,
    And => XS(d, size) = operand1 & operand2,
  }
}


/* MOVZ
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = Movz : (datasize, reg_index, bits(16), range(0,3))

/* MOVZ: sf 10 100101 hw imm16 Rd */
function clause decode ([sf]@0b10@0b100101@(hw:bits(2))@(imm16:bits(16))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  /* For 32-bit (sf=0), hw must be 00 or 01 (hw[1]=0) */
  if sf == bitzero & hw[1] == bitone then None()
  else Some(Movz((sf, d, imm16, unsigned(hw))))
}

/* MOVZ Xd/Wd, #imm, LSL #shift */
function clause execute Movz(sf, d, imm, hw) = {
  _PC = _PC + 4;

  let size = if sf == bitone then 64 else 32;
  /* Compute 64-bit result, then truncate for 32-bit */
  let res : bits(64) = sail_shiftleft(sail_zero_extend(imm, 64), 16 * hw);
  XS(d, size) = res[size-1..0]
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

  let imm =
    if sh == 0b0 then 0x0000000000000@imm12 else 0x0000000000@imm12@0x000;

  if op == bitzero then Some(Add((sf, d, n, OperandImm(imm))))
  else Some(Sub((sf, d, n, OperandImm(imm))))
}


/* ADD Xd/Wd, Xn/Wn, Xm/Wm or ADD Xd/Wd, Xn/Wn, #imm */
function clause execute Add(sf, d, n, op) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let op1 = XS(n, size);
  let op2 : bits('size) = match op {
    OperandReg(m) => XS(m, size),
    OperandImm(imm) => imm[size-1..0]
  };
  XS(d, size) = op1 + op2;
}

/* SUB Xd/Wd, Xn/Wn, Xm/Wm or SUB Xd/Wd, Xn/Wn, #imm */
function clause execute Sub(sf, d, n, op) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let op1 = XS(n, size);
  let op2 : bits('size) = match op {
    OperandReg(m) => XS(m, size),
    OperandImm(imm) => imm[size-1..0]
  };
  XS(d, size) = op1 - op2;
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
union clause ast = CompareAndBranch : (datasize, reg_index, bits(64), /* is Z */ bool)

val decodeCompareAndBranch : (bit, bit, bits(19), bits(5)) -> option(ast)

/* CBZ/CBNZ: sf 011010 op imm19 Rt */
function clause decode ([sf]@0b011010@[op]@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(sf, op, imm19, Rt)
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
