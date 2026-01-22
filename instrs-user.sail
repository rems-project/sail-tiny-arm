/* LoadStoreRegister: LDR and STR */
union clause ast = LoadRegister : (reg_index, reg_index, reg_index)
union clause ast = StoreRegister : (reg_index, reg_index, reg_index)

val decodeLoadStoreRegister : (bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> option(ast)

function clause decode (0b11@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister(opc, Rm, option_v, S, Rn, Rt)
}

function decodeLoadStoreRegister (opc, Rm, option_v, S, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  /* option_v == 0b011 and S == 1 means that the offset in Rm is used as is and not shifted or extended */
  if option_v != 0b011 | S == bitone then None ()
  else if opc == 0b01
  then Some(LoadRegister((t,n,m)))
  else if opc == 0b00
  then Some(StoreRegister((t,n,m)))
  else None ();
}

/* LDR Xt, [Xn, Xm] */
function clause execute LoadRegister(t, n, m) = {
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  let accdesc = create_readAccessDescriptor(false, false, false);
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  /* Ask for the eight-byte value in memory starting from location
  addr and record it in the local variable data */
  let data = rMem(addr, accdesc);
  /* Ask for the value of data to be written to register Xt */
  X(t) = data;
}

/* STR Xt, [Xn, Xm] */
function clause execute StoreRegister(t, n, m) = {
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  let accdesc = create_writeAccessDescriptor(false, false);
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* Announce that a store into the eight bytes of memory starting
   * from location addr will be performed later */
  wMem_Addr(addr);
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  /* Ask for the value of register Xt and record it in the local
  * variable data */
  let data = X(t);
  /* Ask for the value of data to be stored into the eight bytes of
  * memory starting from location addr */
  wMem(addr, data, accdesc);
}

/* LoadStoreImmediate: LDR and STR (unsigned immediate) */
union clause ast = LoadImmediate : (reg_index, reg_index, bits(12))
union clause ast = StoreImmediate : (reg_index, reg_index, bits(12))

val decodeLoadStoreImmediate : (bits(2), bits(12), bits(5), bits(5)) -> option(ast)

/* Load/Store Register (Unsigned Immediate) */
function clause decode (0b11@0b111@0b0@0b01@(opc:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreImmediate(opc, imm12, Rn, Rt)
}

function decodeLoadStoreImmediate (opc, imm12, Rn, Rt) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  if opc == 0b01
  then Some(LoadImmediate((t,n,imm12)))
  else if opc == 0b00
  then Some(StoreImmediate((t,n,imm12)))
  else None()
}

/* LDR Xt, [Xn, #pimm] */
function clause execute LoadImmediate(t, n, imm12) = {
  let base_addr = X(n);
  /* The immediate is scaled by the instruction size 8 */
  let offset : bits(64) = sail_zero_extend(imm12 @ 0b000, 64);
  let addr = base_addr + offset;
  let accdesc = create_readAccessDescriptor(false, false, false);
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  let data = rMem(addr, accdesc);
  X(t) = data;
}

/* STR Xt, [Xn, #pimm] */
function clause execute StoreImmediate(t, n, imm12) = {
  let base_addr = X(n);
  let offset : bits(64) = sail_zero_extend(imm12 @ 0b000, 64);
  let addr = base_addr + offset;
  let accdesc = create_writeAccessDescriptor(false, false);
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(addr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  wMem_Addr(addr);
  /* The instruction can't fault now (in a real model), so update the PC */
  _PC = _PC + 4;
  let data = X(t);
  wMem(addr, data, accdesc);
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

/* Move */
union clause ast = Move : (reg_index, reg_index)

/* MOV (register) - Alias of ORR (shifted register) */
/* ORR (shifted register): sf 0 101010 shift 0 Rm imm6 Rn Rd */
/* MOV Xd, Xm is ORR Xd, XZR, Xm */
function clause decode (0b1@0b0@0b101010@0b00@0b0@(Rm:bits(5))@0b000000@0b11111@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let m : reg_index = unsigned(Rm);
  Some(Move((d,m)))
}

/* MOV Xd, Xm */
function clause execute Move(d, m) = {
  _PC = _PC + 4;
  X(d) = X(m);
}

/* Move Wide (Immediate) */
union clause ast = MoveWide : (reg_index, bits(16), bits(2))

/* MOVZ: 1 10 100101 hw imm16 Rd */
function clause decode (0b1@0b10@0b100101@(hw:bits(2))@(imm16:bits(16))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  Some(MoveWide(d, imm16, hw))
}

/* MOVZ Xd, #imm, LSL #shift */
function clause execute MoveWide(d, imm, hw) = {
  _PC = _PC + 4;
  let res : bits(64) = match hw {
    0b00 => sail_zero_extend(imm, 64),
    0b01 => sail_zero_extend(imm, 48) @ 0x0000,
    0b10 => sail_zero_extend(imm, 32) @ 0x00000000,
    0b11 => imm @ 0x000000000000
  };
  X(d) = res;
}

/* Arithmetic: ADD/SUB */
union clause ast = Add : (reg_index, reg_index, reg_index)
union clause ast = Sub : (reg_index, reg_index, reg_index)
union clause ast = AddImmediate : (reg_index, reg_index, bits(12))
union clause ast = SubImmediate : (reg_index, reg_index, bits(12))

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
  /* Rm and imm6 are irrelevant for immediate, passing 0s */
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
    else if op == bitzero then Some(Add((d,n,m)))
    else Some(Sub((d,n,m)))
  } else {
    /* Immediate form */
    let imm : bits(12) = imm12;
    /* Ideally we would store shift too, but sticking to existing pattern of simplicity */
    /* If shift is 00 (LSL 0) or 01 (LSL 12). */
    if shift == 0b00 then {
       if op == bitzero then Some(AddImmediate((d,n,imm)))
       else Some(SubImmediate((d,n,imm)))
    } else None()
  }
}

/* ADD Xd, Xn, Xm */
function clause execute Add(d, n, m) = {
  _PC = _PC + 4;
  let op1 = X(n);
  let op2 = X(m);
  X(d) = op1 + op2;
}

/* SUB Xd, Xn, Xm */
function clause execute Sub(d, n, m) = {
  _PC = _PC + 4;
  let op1 = X(n);
  let op2 = X(m);
  X(d) = op1 + (not_vec(op2) + 1);
}

/* ADD Xd, Xn, #imm */
function clause execute AddImmediate(d, n, imm12) = {
  _PC = _PC + 4;
  let op1 = X(n);
  let op2 : bits(64) = sail_zero_extend(imm12, 64);
  X(d) = op1 + op2;
}

/* SUB Xd, Xn, #imm */
function clause execute SubImmediate(d, n, imm12) = {
  _PC = _PC + 4;
  let op1 = X(n);
  let op2 : bits(64) = sail_zero_extend(imm12, 64);
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

/* Branch: B (unconditional) */
union clause ast = Branch : bits(64)

/* B: 0 00101 imm26 */
function clause decode (0b0@0b00101@(imm26:bits(26))) = {
  /* Sign-extend the 26-bit immediate shifted left by 2 to get byte offset */
  let offset : bits(64) = sail_sign_extend(imm26 @ 0b00, 64);
  Some(Branch(offset))
}

/* B <offset> */
function clause execute Branch(offset) = {
  /* Compute target address: PC + offset */
  let target = _PC + offset;
  /* Update PC to target address */
  _PC = target;
}

/* NOP: No Operation */
union clause ast = Nop : unit

/* NOP: 1101 0101 0000 0011 0010 0000 0001 1111 = 0xD503201F */
/* This is HINT #0 (NOP) */
function clause decode (0b11010101000000110010000000011111) = {
  Some(Nop())
}

function clause execute Nop() = {
  /* Just advance the PC */
  _PC = _PC + 4;
}

/* CompareAndBranch: CBZ and CBNZ */
/* The boolean flag indicates whether to branch on non-zero (true = CBNZ, false = CBZ) */
union clause ast = CompareAndBranch : (reg_index, bits(64), bool)

val decodeCompareAndBranch : (bit, bits(19), bits(5)) -> option(ast)

/* CBZ: sf 011010 0 imm19 Rt */
function clause decode (0b1@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(bitzero, imm19, Rt)
}

/* CBNZ: sf 011010 1 imm19 Rt */
function clause decode (0b1@0b011010@0b1@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(bitone, imm19, Rt)
}

function decodeCompareAndBranch(op, imm19, Rt) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00,64);
  let branch_on_nonzero : bool = (op == bitone);

  Some(CompareAndBranch(t, offset, branch_on_nonzero));
}

/* CBZ/CBNZ Xt, <offset> */
function clause execute CompareAndBranch(t, offset, branch_on_nonzero) = {
  /* Ask for the value of register Xt and record it in the local
   * variable operand */
  let operand = X(t);
  /* Determine if we should branch:
   * - CBZ: branch if operand == 0
   * - CBNZ: branch if operand != 0 */
  let is_zero = (operand == 0x0000000000000000);
  let should_branch = if branch_on_nonzero then not_bool(is_zero) else is_zero;

  if should_branch then {
    /* Ask for the value of the program counter register and record it
     * in the local variable base */
    let base = _PC;
    /* Compute the address */
    let addr = base + offset;
    /* Ask for the value of result to be written to the program counter
     * register */
    _PC = addr;
  }
  else _PC = _PC + 4;
}
