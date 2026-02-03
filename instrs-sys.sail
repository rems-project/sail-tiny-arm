$ifdef SYSTEM_TINY_ARM
/* TLBI */
union clause ast = TLBInvalidation : (TLBIOp, reg_index)

val decodeTLBI : (bits(3), bits(4), bits(4), bits(3), bits(5)) -> option(ast)
function clause decode (0b1101010100001@(op1:bits(3))@(CRn:bits(4))@(CRm:bits(4))@(op2:bits(3))@(Rt:bits(5))) = {
  decodeTLBI(op1, CRn, CRm, op2, Rt)
}

function decodeTLBI(op1, CRn, CRm, op2, Rt) = {
  let t : reg_index = unsigned(Rt);
  /* We are only considering invalidations applied to EL1 in the ISH domain */
  let tlbi_op : TLBIOp =
    match (op1, CRn, CRm, op2) {
      /* TLBI ALL (TLBI ALLE1IS) */
      (0b100, 0b1000, 0b0111, 0b100) => TLBIOp_ALL,
      /* TLBI by VA (TLBI VAE1IS) */
      (0b000, 0b1000, 0b0011, 0b001) => TLBIOp_VA,
      /* TLBI by ASID (TLBI ASIDE1IS) */
      (0b000, 0b1000, 0b0011, 0b010) => TLBIOp_ASID,
      /* TLBI by VA, all ASIDs (TLBI VAAE1IS) */
      (0b000, 0b1000, 0b0011, 0b011) => TLBIOp_VAA,
      _ => return None()
    };
  Some(TLBInvalidation(tlbi_op, t))
}

function decodeASID(v: bits(64)) -> bits(16) = v[63..48]

function decodeVA(v: bits(64)) -> bits(64) =
  sail_zero_extend(v[43..0] @ 0x000, 64)

function clause execute TLBInvalidation(op, t) = {
  _PC = _PC + 4;

  let (va, asid) : (option(bits(64)), option(bits(16))) =
    match op {
      TLBIOp_ALL => (None(), None()),
      TLBIOp_VA => {
        let v = X(t);
        (Some(decodeVA(v)), Some(decodeASID(v)))
      },
      TLBIOp_ASID => (None(), Some(decodeASID(X(t)))),
      TLBIOp_VAA => (Some(decodeVA(X(t))), None()),
      _ => return ()
    };
  reportTLBI(op, va, asid);
}

/* Supervisor Call (SVC) */
union clause ast = SupervisorCall : bits(16)

/* SVC #imm16: 1101 0100 000 imm16 000 01 */
function clause decode (0b11010100000@(imm16:bits(16))@0b00001) = {
  Some(SupervisorCall(imm16))
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
  Some(ExceptionReturn())
}

function clause execute ExceptionReturn() = {
  /* Set PC to the exception link register (no +4 increment) */
  _PC = ELR_EL1;

  /* Read saved program status register */
  let spsr = SPSR_EL1;

  /* Restore PSTATE fields from SPSR */
  let new_pstate = {PSTATE with
    N = spsr[31..31],
    Z = spsr[30..30],
    C = spsr[29..29],
    V = spsr[28..28],
    D = spsr[9..9],
    A = spsr[8..8],
    I = spsr[7..7],
    F = spsr[6..6],
    EL = spsr[3..2],
    SP = spsr[0..0]
  };
  PSTATE = new_pstate;
}
 
/* CMP Xn/Wn, Xm/Wm or CMP Xn/Wn, #imm - sets NZCV flags (system mode) */
function clause execute Compare(sf, n, op) = {
  _PC = _PC + 4;
  if sf == bitone then {
    /* 64-bit */
    let op1 : bits(64) = X(n);
    let op2 : bits(64) = match op {
      OperandReg(m) => X(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 64)
    };
    let result : bits(65) = sail_zero_extend(op1, 65) + sail_zero_extend(not_vec(op2), 65) + 1;
    let result64 : bits(64) = result[63..0];
    /* Set condition flags */
    let sign1 = op1[63..63];
    let sign2 = op2[63..63];
    let signr = result64[63..63];
    let overflow : bool = (sign1 != sign2) & (sign1 != signr);
    PSTATE = {PSTATE with
      N = signr,
      Z = if result64 == 0x0000000000000000 then 0b1 else 0b0,
      C = result[64..64],
      V = if overflow then 0b1 else 0b0
    };
  } else {
    /* 32-bit */
    let op1 : bits(32) = W(n);
    let op2 : bits(32) = match op {
      OperandReg(m) => W(m),
      OperandImm(imm12) => sail_zero_extend(imm12, 32)
    };
    let result : bits(33) = sail_zero_extend(op1, 33) + sail_zero_extend(not_vec(op2), 33) + 1;
    let result32 : bits(32) = result[31..0];
    /* Set condition flags */
    let sign1 = op1[31..31];
    let sign2 = op2[31..31];
    let signr = result32[31..31];
    let overflow : bool = (sign1 != sign2) & (sign1 != signr);
    PSTATE = {PSTATE with
      N = signr,
      Z = if result32 == 0x00000000 then 0b1 else 0b0,
      C = result[32..32],
      V = if overflow then 0b1 else 0b0
    };
  }
}

$endif
