$ifdef SYSTEM_TINY_ARM
/* TLBI */
union clause ast = TLBInvalidation : (TLBIOp, Shareability, reg_index)

val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> ast
function clause decode (0b1101010100001@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  let t : reg_index = unsigned(Rt);
  let (tlbi_op, shareability) : (TLBIOp, Shareability) =
    match (op1, CRn, CRm, op2) {
      /* TLBI ALL (TLBI ALLE1) */
      (0b100, 0b1000, 0b0111, 0b100) => (TLBIOp_ALL, Shareability_NSH),
      /* TLBI by VMID, all ASIDs (TLBI VMALLE1IS) */
      (0b000, 0b1000, 0b0011, 0b000) => (TLBIOp_VMALL, Shareability_ISH),
      /* TLBI by VA (TLBI VAE1IS) */
      (0b000, 0b1000, 0b0011, 0b001) => (TLBIOp_VA, Shareability_ISH),
      /* TLBI by ASID (TLBI ASIDE1IS) */
      (0b000, 0b1000, 0b0011, 0b010) => (TLBIOp_ASID, Shareability_ISH),
      /* TLBI by VA, all ASIDs (TLBI VAAE1IS) */
      (0b000, 0b1000, 0b0011, 0b011) => (TLBIOp_VAA, Shareability_ISH),
      /* TLBI by VA, all ASIDs (TLBI VAAE1) */
      (0b000, 0b1000, 0b0111, 0b011) => (TLBIOp_VAA, Shareability_NSH),
      _ => fail("Unsupported TLBI operation encoding")
    };
  TLBInvalidation(tlbi_op, shareability, t)
}

function decodeASID(v: bits(64)) -> bits(16) = v[63..48]

function decodeVA(v: bits(64)) -> bits(64) =
  sail_zero_extend(v[43..0] @ 0x000, 64)

function clause execute TLBInvalidation(op, shareability, t) = {
  _PC = _PC + 4;

  let (va, asid) : (option(bits(64)), option(bits(16))) =
    match op {
      TLBIOp_ALL => (None(), None()),
      TLBIOp_VMALL => (None(), None()),
      TLBIOp_VA => {
        let v = X(t);
        (Some(decodeVA(v)), Some(decodeASID(v)))
      },
      TLBIOp_ASID => (None(), Some(decodeASID(X(t)))),
      TLBIOp_VAA => (Some(decodeVA(X(t))), None()),
      _ => return ()
    };
  reportTLBI(op, shareability, va, asid);
}


/* Supervisor Call (SVC) */
union clause ast = SupervisorCall : bits(16)

/* SVC #imm16: 1101 0100 000 imm16 000 01 */
function clause decode (0b11010100000@(imm16:bits(16))@0b00001) = {
  SupervisorCall(imm16)
}

function clause execute SupervisorCall(imm16) = {
  let target_el = 0b01; /* SVC always targets EL1 */

  /* Save return address (next instruction after SVC) - must be done before _PC is modified */
  ELR_EL1 = _PC + 4;

  /* Build ESR_EL1: EC=0b010101 (SVC from AArch64), IL=1, ISS=imm16 */
  let ec : bits(6) = 0b010101;
  let il : bits(1) = 0b1;
  let iss : bits(25) = sail_zero_extend(imm16, 25);
  ESR_EL1 = sail_zero_extend((ec @ il) @ iss, 64);

  take_exception(target_el, None())
}


/* Exception Return (ERET) - EL1 only */
union clause ast = ExceptionReturn : unit

/* ERET: 1101 0110 1001 1111 0000 0011 1110 0000 */
function clause decode (0b11010110100111110000001111100000) = {
  ExceptionReturn()
}

function clause execute ExceptionReturn() = {
  assert (CurrentEL != 0b00, "Trying to ERET from EL0, fault not implemented");
  /* Set PC to the exception link register (no +4 increment) */
  _PC = ELR_EL1;

  /* Read saved program status register */
  let spsr = SPSR_EL1;
  assert (spsr[4..4] == 0b0, "AArch32 not supported");
  assert (spsr[3..2] == 0b00 | spsr[3..2] == 0b01,
          "EL2 and EL3 not supported");
  assert (spsr[3..0] != 0b0001, "Can't have SPSel set to 1 in EL0");

  NZCV = spsr[31..28];
  DAIF = spsr[9..6];
  CurrentEL = spsr[3..2];
  SPSel = spsr[0..0];
}
$endif
