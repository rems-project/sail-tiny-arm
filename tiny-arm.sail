$ifdef SYSTEM_TINY_ARM
union ast =  {
  LoadRegister : (reg_index, reg_index, reg_index),
  StoreRegister : (reg_index, reg_index, reg_index),
  ExclusiveOr : (reg_index, reg_index, reg_index),
  DataMemoryBarrier : MBReqTypes,
  CompareAndBranch : (reg_index, bits(64)),
  TLBIInstr : (TLBIOp, TLBILevel, TLBIMemAttr, Shareability, bool, bool, reg_index)
}
$else
union ast =  {
  LoadRegister : (reg_index, reg_index, reg_index),
  StoreRegister : (reg_index, reg_index, reg_index),
  ExclusiveOr : (reg_index, reg_index, reg_index),
  DataMemoryBarrier : MBReqTypes,
  CompareAndBranch : (reg_index, bits(64)),
}
$endif

val decode : bits(32) -> option(ast)

scattered function decode

val execute : ast -> unit

scattered function execute


/* LoadStoreRegister: LDR and STR */
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
  let accdesc = create_readAccessDescriptor();
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
  let accdesc = create_writeAccessDescriptor();
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

/* Exclusive OR: EOR */
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




/* DMB */
val decodeDataMemoryBarrier : bits(4) -> option(ast)

function clause decode (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b1@0b01@0b11111) = {
  decodeDataMemoryBarrier(CRm)
}

function clause decodeDataMemoryBarrier(0b1111) =
  Some(DataMemoryBarrier(MBReqTypes_All))

function clause decodeDataMemoryBarrier(0b1110) =
  Some(DataMemoryBarrier(MBReqTypes_Writes))

function clause decodeDataMemoryBarrier(0b1101) =
  Some(DataMemoryBarrier(MBReqTypes_Reads))

function clause decodeDataMemoryBarrier(_) = None()

function clause execute DataMemoryBarrier(types) = {
  // Update the PC
  _PC = _PC + 4;
  // Then perform the barrier
  dataMemoryBarrier(types);
}

/* CompareAndBranch: CBZ */
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

$ifdef SYSTEM_TINY_ARM

/* TLB Invalidation: TLBI */
val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)

function clause decode (0b1101010100@0b0@0b01@(op1:bits(3))@(CRn:bits(4))
                                       @(CRm:bits(4))@(op2:bits(3))
                                       @(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  let t : reg_index = unsigned(Rt);

  match (op1, CRn, CRm, op2) {
    /* TLBI VMALLE1IS: Invalidate by VMID, All, EL1, Inner-Shareable */
    (0b000, 0b1000, 0b0011, 0b000) => {
      Some(TLBIInstr(
        TLBIOp_VMALL,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        false,
        t
      ))
    },

    /* TLBI VMALLE1OS: Invalidate by VMID, All, EL1, Outer-Shareable */
    (0b000, 0b1000, 0b0001, 0b000) => {
      Some(TLBIInstr(
        TLBIOp_VMALL,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        false,
        t
      ))
    },

    /* TLBI VAE1: Invalidate by VA, EL1 */
    (0b000, 0b1000, 0b0111, 0b001) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_NSH,
        false,
        true,   /* Xt supplies VA */
        t
      ))
    },

    /* TLBI VAE1IS: Invalidate by VA, EL1, Inner-Shareable */
    (0b000, 0b1000, 0b0011, 0b001) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAE1OS: Invalidate by VA, EL1, Outer-Shareable */
    (0b000, 0b1000, 0b0001, 0b001) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        true,
        t
      ))
    },

    /* TLBI ASIDE1: Invalidate by ASID, EL1 (Xt supplies ASID) */
    (0b000, 0b1000, 0b0111, 0b010) => {
      Some(TLBIInstr(
        TLBIOp_VA,   /* generic “by parameter” op */
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_NSH,
        false,
        true,       /* Xt supplies ASID */
        t
      ))
    },

    /* TLBI ASIDE1IS: Inner-Shareable */
    (0b000, 0b1000, 0b0011, 0b010) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        true,
        t
      ))
    },

    /* TLBI ASIDE1OS: Outer-Shareable */
    (0b000, 0b1000, 0b0001, 0b010) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAAE1: Invalidate by VA, All ASID, EL1 */
    (0b000, 0b1000, 0b0111, 0b011) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_NSH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAAE1IS: Inner-Shareable */
    (0b000, 0b1000, 0b0011, 0b011) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAAE1OS: Outer-Shareable */
    (0b000, 0b1000, 0b0001, 0b011) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        true,
        t
      ))
    },

    /* TLBI ALLE1: Invalidate All, EL1 */
    (0b100, 0b1000, 0b0111, 0b100) => {
      Some(TLBIInstr(
        TLBIOp_VMALL,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_NSH,
        false,
        false,
        t
      ))
    },

    /* TLBI ALLE1IS: Inner-Shareable */
    (0b100, 0b1000, 0b0011, 0b100) => {
      Some(TLBIInstr(
        TLBIOp_VMALL,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        false,
        t
      ))
    },

    /* TLBI ALLE1OS: Outer-Shareable */
    (0b100, 0b1000, 0b0001, 0b100) => {
      Some(TLBIInstr(
        TLBIOp_VMALL,
        TLBILevel_Any,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        false,
        t
      ))
    },

    /* TLBI VALE1: Invalidate by VA, Last-level, EL1 */
    (0b000, 0b1000, 0b0111, 0b101) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Last,
        TLBI_AllAttr,
        Shareability_NSH,
        false,
        true,
        t
      ))
    },

    /* TLBI VALE1IS: Inner-Shareable */
    (0b000, 0b1000, 0b0011, 0b101) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Last,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        true,
        t
      ))
    },

    /* TLBI VALE1OS: Outer-Shareable */
    (0b000, 0b1000, 0b0001, 0b101) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Last,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAALE1: Invalidate by VA, All ASID, Last-level, EL1 */
    (0b000, 0b1000, 0b0111, 0b111) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Last,
        TLBI_AllAttr,
        Shareability_NSH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAALE1IS: Inner-Shareable */
    (0b000, 0b1000, 0b0011, 0b111) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Last,
        TLBI_AllAttr,
        Shareability_ISH,
        false,
        true,
        t
      ))
    },

    /* TLBI VAALE1OS: Outer-Shareable */
    (0b000, 0b1000, 0b0001, 0b111) => {
      Some(TLBIInstr(
        TLBIOp_VA,
        TLBILevel_Last,
        TLBI_AllAttr,
        Shareability_OSH,
        false,
        true,
        t
      ))
    },

    /* TODO: TLBI by ranges? */
    _ => None()
  }
}

/* TLBI */
function clause execute TLBIInstr(op, level, attr, shareability,
                                  is_range, uses_addr, t) = {
  _PC = _PC + 4;

  let addr = if uses_addr then X(t) else 0x0000000000000000;

  let r : TLBIRecord = struct {
    op = op,
    from_aarch64 = true,
    security = SS_NonSecure,
    regime = Regime_EL10,
    vmid = 0x0000,
    asid = ASID_read(),
    level = level,
    attr = attr,
    ipaspace = PAS_NonSecure,
    address = addr,
    end_address_name = addr,
    d64 = true,
    d128 = false,
    ttl = 0b0000,
    tg = 0b00,
  };

  invalidateTLB(r, shareability);
}

$endif

// This needs to be the last clause
function clause decode(_) = { None() }

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit

function fetch_and_execute () = {
  let accdesc = create_iFetchAccessDescriptor();
  /* Translate the virtual address into the physical address.
   * In the user mode, `translate_address` returns input address. */
  let addr : bits(addr_size) =
    match translate_address(_PC, accdesc) {
      Some(addr) => addr,
      None() => return () // A translation fault is handled in `translate_address`.
    };
  let machineCode = iFetch(addr, accdesc);
  let instr = decode(machineCode);
  match instr {
    Some (instr) => execute(instr),
    None () => assert (false, "Unsupported Encoding")
  }
}

