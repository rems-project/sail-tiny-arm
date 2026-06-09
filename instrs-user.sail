/* LoadStore: LD(AP?)?X?R(H/B)?/STL?X?R(H/B)?, (register and immediate forms)
 * size is the log of the byte size, writing 2^{size} bytes */
union clause ast = Load : (
  /* size:*/ range(0,3), reg_index, reg_index, operand,
  /* acquire */ bool, /* RCpc */ bool, /* exclusive */ bool
)
union clause ast = Store : (
  /* size:*/ range(0,3), reg_index, reg_index, operand,
  /* release */ bool, /* if exclusive, the target Rs */ option(reg_index)
)


val decodeLoadStoreRegister : (bits(2), bits(2), bits(5), bits(3), bit, bits(5), bits(5)) -> ast

/* LDR/STR register: size 111 0 00 opc 1 Rm option S 10 Rn Rt */
function clause decode ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreRegister(size, opc, Rm, option_v, S, Rn, Rt)
}


function decodeLoadStoreRegister (size, opc, Rm, option_v, S, Rn, Rt) = {
  let size = unsigned(size);
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  let shift : range(0,4) = if S == bitone then size else 0;
  if option_v[1] == bitzero then fail("Sub-word extend in Load/Store");
  let offset = OperandRegExt(m, ext_bits(option_v), shift);
  match opc {
    0b01 => Load(size, t, n, offset, /*acq*/false, /*rcpc*/false, /*excl*/false),
    0b00 => Store(size, t, n, offset, /*rel*/false, /*excl*/None()),
    _ => fail("Sign-extend loads are not supported")
  }
}

val decodeLoadStoreImmediate : (bits(2), bits(2), bits(12), bits(5), bits(5)) -> ast

/* LDR/STR immediate: size 111 0 01 opc imm12 Rn Rt */
function clause decode ((size:bits(2))@0b111@0b0@0b01@(opc:bits(2))@(imm12:bits(12))@(Rn:bits(5))@(Rt:bits(5))) = {
  decodeLoadStoreImmediate(size, opc, imm12, Rn, Rt)
}

function decodeLoadStoreImmediate (size, opc, imm12, Rn, Rt) = {
  let size = unsigned(size);
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let imm = sail_shiftleft(sail_zero_extend(imm12, 64), size);
  let offset = OperandImm(imm);
  match opc {
    0b01 => Load(size, t, n, offset, /*acq*/false, /*rcpc*/false, /*excl*/false),
    0b00 => Store(size, t, n, offset, /*rel*/false, /*excl*/None()),
    _ => fail("Sign-extend loads are not supported")
  }
}

/* Acquire/release accesses : LDAR[B|H]? and STLR[B|H]? */
function clause decode ((size:bits(2))@0b001000@0b1@[L]@0b0@0b11111@0b1@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  let size = unsigned(size);
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  if L == bitone
  then Load(size, t, n, zero_operand, /*acq*/true, /*rcpc*/false, /*excl*/false)
  else Store(size, t, n, zero_operand, /*rel*/true, /*excl*/None())
}

/* RCpc acquire loads: LDAPR[B|H]? */
function clause decode ((size:bits(2))@0b111000@0b10@0b1@0b11111@0b1100@0b00@(Rn:bits(5))@(Rt:bits(5))) = {
  let size = unsigned(size);
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  Load(size, t, n, zero_operand, /*acq*/true, /*rcpc*/true, /*excl*/false)
}

/* Exclusive loads: LD(A?)XR[B|H]? */
function clause decode ((size:bits(2))@0b001000@0b0@0b1@0b0@0b11111@[o0]@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  let size = unsigned(size);
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let acquire = o0 == bitone;
  Load(size, t, n, zero_operand, acquire, /*rcpc*/false, /*excl*/true)
}

/* Exclusive stores: ST(L?)XR[B|H]? */
function clause decode ((size:bits(2))@0b001000@0b0@0b0@0b0@(Rs:bits(5))@[o0]@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  let size = unsigned(size);
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let s : reg_index = unsigned(Rs);
  let release = o0 == bitone; 
  assert(s != t, "Store exclusive can't store value and success to same register");
  assert(s == 31 | s != n, "Store exclusive success can't be stored to address register");
  Store(size, t, n, zero_operand, release, Some(s))
}

/* LD(AP?)?X?R(H/B)? */
function clause execute Load(size, t, n, offset, acquire, rcpc, exclusive) = {
  /* Create an access descriptor */
  let accdesc = create_readAccessDescriptor(acquire, rcpc, exclusive);

  /* Compute the (virtual) address of the access */
  let base = if n == 31 then SP() else X(n);
  let vaddr : bits(64) = base + eval_operand(64, offset);

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
/* STL?X?R(H/B)? */
function clause execute Store(size, t, n, offset, release, s) = {
  /* Create an access descriptor */
  let exclusive : bool = match s { Some(_) => true, None() => false };
  let accdesc = create_writeAccessDescriptor(release, exclusive);

  /* Compute the (virtual) address of the access */
  let base = if n == 31 then SP() else X(n);
  let vaddr : bits(64) = base + eval_operand(64, offset);

  /* Translate the virtual address into the physical address.
   * In user mode, `translate_address` returns the input address. */
  let addr : bits(addr_size) =
    match translate_address(vaddr, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };

  /* Ordinary stores always write; exclusive stores may fail and report status in Rs. */
  match s {
    None() => {
      /* Announce that a store will be performed to this address */
      wMem_Addr(addr);

      /* The instruction can't fault now, so update the PC */
      _PC = _PC + 4;

      /* Read value from register Xt and write to memory */
      wMem(2^size, addr, X(t)[(8*2^size-1)..0], accdesc)
    },
    Some(s) => {
      /* Choose the STXR outcome nondeterministically; sail_mem_write prunes
       * successful branches that the exclusive memory model rejects. */
      let success : bool = undefined;
      if success then {
        wMem_Addr(addr);
        _PC = _PC + 4;
        X(s) = sail_zero_extend(0b0, 64);
        wMem(2^size, addr, X(t)[(8*2^size-1)..0], accdesc);
      } else {
        _PC = _PC + 4;
        X(s) = sail_zero_extend(0b1, 64);
      }
    }
  }
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

/* EOR/ORR/AND (shifted register): sf opc 01010 shift 0 Rm imm6 Rn Rd */
function clause decode ([sf]@(opc : bits(2))@0b01010@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  let op = decode_bitwise_op(opc);
  if sf == bitzero & imm6[5] == bitone then
    fail("bitwise_op: shift by more than 31 bits on 32 bit operation");
  let operand = OperandRegShift(unsigned(Rm), shift_bits(shift), unsigned(imm6));
  BitwiseLogic(sf, op, unsigned(Rd), unsigned(Rn), operand)
}

/* EOR/ORR/AND (immediate): sf opc 100100 N immr imms Rn Rd */
function clause decode ([sf]@(opc : bits(2))@0b100100@[N]@(immr:bits(6))@(imms:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  let op = decode_bitwise_op(opc);
  if N == bitone & sf == bitzero then
    fail("64 bit mask in 32 bit bitwise operation");
  let mask = decode_bitmask(N, imms, immr); //
  BitwiseLogic(sf, op, unsigned(Rd), unsigned(Rn), OperandImm(mask))
}

/* EOR/ORR/AND Xd/Wd, Xn/Wn, Xm/Wm and EOR/ORR/AND Xd/Wd, Xn/Wn, #imm */
function clause execute BitwiseLogic(sf, op, d, n, op2) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let operand1 = X(n, size);
  let operand2  = eval_operand('size, op2);
  let result : bits('size) = match op {
    Eor => operand1 ^ operand2,
    Or => operand1 | operand2,
    And => operand1 & operand2,
  };
  // If the operand was an immediate, d == 31 means SP otherwise it means 0
  let use_sp : bool = match op2 {
    OperandRegShift (_) => false,
    OperandRegExt (_) => fail("bitwise operation shouldn't have OperandRegExt"),
    OperandImm(_) => true };
  if use_sp & d == 31 then SP(size) = result else X(d, size) = result;
}


/* MOVZ
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = Movz : (datasize, reg_index, bits(16), range(0,3))

/* MOVZ: sf 10 100101 hw imm16 Rd */
function clause decode ([sf]@0b10@0b100101@(hw:bits(2))@(imm16:bits(16))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  if sf == bitzero & hw[1] == bitone then
    /* For 32-bit (sf=0), hw must be 00 or 01 (hw[1]=0) */
    fail("MOVZ: writing the top 32 bits in a 32 bit operation");
  Movz(sf, d, imm16, unsigned(hw))
}

/* MOVZ Xd/Wd, #imm, LSL #shift */
function clause execute Movz(sf, d, imm, hw) = {
  _PC = _PC + 4;

  let size = if sf == bitone then 64 else 32;
  /* Compute 64-bit result, then truncate for 32-bit */
  let res : bits(64) = sail_shiftleft(sail_zero_extend(imm, 64), 16 * hw);
  X(d, size) = res[size-1..0]
}

/* Arithmetic: ADD(S)/SUB(S) (register and immediate forms)
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers)
 * op: 0 is ADD, 1 is SUB
 * S (suffix): 0 doesn't write NZCV, and 1 does write NZCV */
union clause ast = AddSub : (datasize, /*op*/bit, /*S*/bit, reg_index,
                             reg_index, operand)

/* ADD(S)/SUB(S) (extended register) */
val decodeAddSubExt : (bit, bit, bit, bits(3), bits(3), bits(5), bits(5), bits(5)) -> ast
function clause decode ([sf]@[op]@[S]@0b01011@0b00@0b1@(Rm:bits(5))@(option_v:bits(3))@(imm3:bits(3))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSubExt(sf, op, S, option_v, imm3, Rm, Rn, Rd)
}

function decodeAddSubExt (sf, op, S, option_v, imm3, Rm, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);

  let shift = unsigned(imm3);
  let shift : range(0,4) =
    if shift > 4
    then fail("AddSub (extended register) shift is greater than 4")
    else shift;
  let operand = OperandRegExt(unsigned(Rm), ext_bits(option_v), shift);

  AddSub(sf, op, S, d, n, operand)
}

/* ADD(S)/SUB(S) (shifted register) */
val decodeAddSubShift : (bit, bit, bit, bits(2), bits(6), bits(5), bits(5), bits(5)) -> ast
function clause decode ([sf]@[op]@[S]@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSubShift(sf, op, S, shift, imm6, Rm, Rn, Rd)
}

function decodeAddSubShift (sf, op, S, shift, imm6, Rm, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);

  if shift == 0b11 then fail("ADD/SUB doesn't support ROR");
  if sf == bitzero & imm6[5] == bitone then
    fail("ADD/SUB: shift by more than 31 bits on 32 bit operation");
  let operand = OperandRegShift(unsigned(Rm), shift_bits(shift), unsigned(imm6));

  AddSub(sf, op, S, d, n, operand)
}

/* ADD(S)/SUB(S) (immediate) */
val decodeAddSubImm : (bit, bit, bit, bits(1), bits(12), bits(5), bits(5)) -> ast
function clause decode ([sf]@[op]@[S]@0b100010@(sh:bits(1))@(imm12:bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  decodeAddSubImm(sf, op, S, sh, imm12, Rn, Rd)
}

function decodeAddSubImm (sf, op, S, sh, imm12, Rn, Rd) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);

  let imm =
    if sh == 0b0 then 0x0000000000000@imm12 else 0x0000000000@imm12@0x000;

  AddSub(sf, op, S, d, n, OperandImm(imm))
}


/* ADD(S)/SUB(S) */
function clause execute AddSub(sf, op, S, d, n, m) = {
  _PC = _PC + 4;
  let 'size = if sf == bitone then 64 else 32;
  let addition = op == bitzero;
  // Don't use SP in the shift case but do use it in the others
  let use_sp : bool = match m {OperandRegShift(_) => false, _ => true};
  let op1 = if use_sp & n == 31 then SP(size) else X(n, size);
  let op2 = eval_operand('size, m);
  let result = if addition then op1 + op2 else op1 - op2;
  // We're only writing SP if not writing flags
  if use_sp & S == bitzero & d == 31 then SP(size) = result else X(d, size) = result;

  if S == bitone then {
    let n = result[size-1];
    let z = if result == sail_zeros(size) then bitone else bitzero;

    let c =
      if addition
      // u(result) < u(op1) <==> u(op1) + u(op2) == 2^size + u(result)
      then if unsigned(result) < unsigned(op1) then bitone else bitzero
      // Unsigned substraction underflow is represented by c=0
      else if unsigned(op1) >= unsigned(op2) then bitone else bitzero;

    // Signed overflow happens when the two operands have the same sign and the
    // result has the opposite sign. If substraction, the second sign is
    // reversed
    let s1 = op1[size-1];
    let s2 = if addition then op2[size-1] else not_bit(op2[size-1]);
    let v = if s1 == s2 then if s1 != n then bitone else bitzero else bitzero;

    NZCV = [n]@[z]@[c]@[v]
  }
}


/* CAS/CASB/CASH variants: size 0010001 L 1 Rs o0 11111 Rn Rt */
function clause decode ((size:bits(2))@0b0010001@[L]@0b1@(Rs:bits(5))@[o0]@0b11111@(Rn:bits(5))@(Rt:bits(5))) = {
  fail("Instruction not supported by design: CAS/CASB/CASH variants")
}

/* CSEL: sf 00 11010100 Rm cond 00 Rn Rd */
function clause decode ([sf]@0b00@0b11010100@(Rm:bits(5))@(cond:bits(4))@0b00@(Rn:bits(5))@(Rd:bits(5))) = {
  fail("Instruction not supported by design: CSEL")
}

/* SWP/SWPA/SWPL/SWPAL: size 11 1000 A R 1 Rs 1 00000 Rn Rt */
function clause decode ((size:bits(2))@0b11@0b1000@[A]@[R]@0b1@(Rs:bits(5))@0b1@0b00000@(Rn:bits(5))@(Rt:bits(5))) = {
  fail("Instruction not supported by design: SWP/SWPA/SWPL/SWPAL")
}

/* Data Barrier */
union clause ast = DataMemoryBarrier : (MBReqDomain, MBReqTypes)
union clause ast = DataSynchronizationBarrier : (MBReqDomain, MBReqTypes)

val decodeDataBarrier : (bits(4), bool) -> ast

// TODO Arm updated their barriers definitions, follow that update
function decodeDataBarrier(CRm, is_sync) = {
  let domain : MBReqDomain =
    match CRm[3..2] {
      0b11 => MBReqDomain_FullSystem,
      0b10 => MBReqDomain_InnerShareable,
      0b01 => MBReqDomain_Nonshareable,
      0b00 => MBReqDomain_OuterShareable,
    };

  let types : MBReqTypes =
    match CRm[1..0] {
      0b01 => MBReqTypes_Reads,
      0b10 => MBReqTypes_Writes,
      0b11 => MBReqTypes_All,
      _ => fail("DxB: Invalid encoding of kind of barrier")
    };

  if is_sync then
    DataSynchronizationBarrier(domain, types)
  else
    DataMemoryBarrier(domain, types)
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
union clause ast = InstructionSynchronizationBarrier : unit

function clause decode (0b11010101000000110011@(CRm:bits(4))@0b110@0b11111) = {
  InstructionSynchronizationBarrier()
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
  Nop()
}

function clause execute Nop() = {
  /* Just advance the PC */
  _PC = _PC + 4;
}


/* CompareAndBranch: CBZ / CBNZ
 * sf (size flag): 0 = 32-bit (W registers), 1 = 64-bit (X registers) */
union clause ast = CompareAndBranch : (datasize, reg_index, bits(64), /* is Z */ bool)

val decodeCompareAndBranch : (bit, bit, bits(19), bits(5)) -> ast

/* CBZ/CBNZ: sf 011010 op imm19 Rt */
function clause decode ([sf]@0b011010@[op]@(imm19:bits(19))@(Rt:bits(5))) = {
  decodeCompareAndBranch(sf, op, imm19, Rt)
}

function decodeCompareAndBranch(sf, op, imm19, Rt) = {
  let t : reg_index = unsigned(Rt);
  let offset : bits(64) = sail_sign_extend(imm19@0b00,64);
  /* iszero: true for CBZ (op=0), false for CBNZ (op=1) */
  let iszero : bool = (op == bitzero);

  CompareAndBranch(sf, t, offset, iszero);
}

/* CBZ/CBNZ Xt/Wt, <offset> */
function clause execute CompareAndBranch(sf, t, offset, iszero) = {
  let size = if sf == bitone then 64 else 32;
  /* Get operand value - 64-bit or 32-bit (zero-extended for comparison) */
  let operand : bits(64) = sail_zero_extend(X(t, size), 64);
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
  Branch(offset)
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


/* Conditional Branch: B.cond */
union clause ast = ConditionalBranch : (bits(64), cond)

/* The different conditions */
mapping cond_bits : cond <-> bits(4) = {
  EQ <-> 0b0000,
  NE <-> 0b0001,
  CS <-> 0b0010,
  CC <-> 0b0011,
  MI <-> 0b0100,
  PL <-> 0b0101,
  VS <-> 0b0110,
  VC <-> 0b0111,
  HI <-> 0b1000,
  LS <-> 0b1001,
  GE <-> 0b1010,
  LT <-> 0b1011,
  GT <-> 0b1100,
  LE <-> 0b1101,
  AL <-> 0b1110,
  NV <-> 0b1111,
}

/* B.cond <label> - Encoding: 010 101 00 imm19 0 cond */
function clause decode (0b010@0b101@0b00@(imm19:bits(19))@0b0@(cond:bits(4))) = {
  let offset : bits(64) = sail_sign_extend(imm19 @ 0b00, 64);
  ConditionalBranch(offset, cond_bits(cond))
}

/* Compute a condition using the flags */
val condition_holds : cond -> bool
function condition_holds(cond) = match cond {
  EQ => Z() == bitone,
  NE => Z() == bitzero,
  CS => C() == bitone,
  CC => C() == bitzero,
  MI => N() == bitone,
  PL => N() == bitzero,
  VS => V() == bitone,
  VC => V() == bitzero,
  HI => C() == bitone & Z() == bitzero,
  LS => C() == bitzero | Z() == bitone,
  GE => N() == V(),
  LT => N() != V(),
  GT => N() == V() & Z() == bitzero,
  LE => N() != V() | Z() == bitone,
  AL => true,
  NV => true // Arm is weird, but actuall NV and AL are the same
}

/* B.cond <offset> */
function clause execute ConditionalBranch(offset, cond) = {
  /* Get the current program counter */
  let base = PC();

  if condition_holds(cond) then {
    /* Compute the target address (PC-relative) */
    let target = base + offset;
    /* Branch to the target address */
    PC() = target;
  } else PC() = base + 4
}


/* ADR: form PC-relative address */
union clause ast = Adr : (reg_index, bits(64))

/* ADR: 0 immlo 10000 immhi Rd */
function clause decode (0b0@(immlo:bits(2))@0b10000@(immhi:bits(19))@(Rd:bits(5))) = {
  let offset : bits(64) = sail_sign_extend(immhi @ immlo, 64);
  Adr(unsigned(Rd), offset)
}

/* ADR Xd, <label> */
function clause execute Adr(d, offset) = {
  let base = PC();
  _PC = _PC + 4;
  X(d) = base + offset;
}


/* BR: Branch to register */
union clause ast = BranchRegister : reg_index

/* BR: 1101011 0000 11111 000000 Rn 00000 */
function clause decode (0b1101011@0b0000@0b11111@0b000000@(Rn:bits(5))@0b00000) = {
  BranchRegister(unsigned(Rn))
}

/* BR Xn */
function clause execute BranchRegister(n) = {
  PC() = X(n);
}
