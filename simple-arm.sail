union ast =  {
  LoadRegister : (reg_index, reg_index, reg_index),
  StoreRegister : (reg_index, reg_index, reg_index),
  ExclusiveOr : (reg_index, reg_index, reg_index),
  DataMemoryBarrier : unit,
  CompareAndBranch : (reg_index, bits(64)),
}

val decodeLoadStoreRegister : bits(32) -> option(ast)
function decodeLoadStoreRegister (0b11@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  let t : reg_index = unsigned(Rt);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);
  if option_v != 0b011 | S == bitone then None ()
  else if opc == 0b00
  then Some(LoadRegister((t,n,m)))
  else if opc == 0b01
  then Some(StoreRegister((t,n,m)))
  else None ();
}

val execute : ast -> unit

scattered function execute

/* LDR Xt, [Xn, Xm] */
function clause execute LoadRegister(t, n, m) = {
  _PC = _PC + 4;
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  /* Ask for the eight-byte value in memory starting from location
  addr and record it in the local variable data */
  let data = rMem(addr);
  /* Ask for the value of data to be written to register Xt */
  X(t) = data;
}

/* STR Xt, [Xn, Xm] */
function clause execute StoreRegister(t, n, m) = {
  _PC = _PC + 4;
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  let base_addr = X(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  let offset = X(m);
  /* Compute the address */
  let addr = base_addr + offset;
  /* Announce that a store into the eight bytes of memory starting
   * from location addr will be performed later */
  wMem_Addr(addr);
  /* Ask for the value of register Xt and record it in the local
   * variable data */
  let data = X(t);
  /* Ask for the value of data to be stored into the eight bytes of
   * memory starting from location addr */
  wMem(addr, data);
}

val decodeExclusiveOr : bits(32) -> option(ast)
function decodeExclusiveOr ([sf]@0b10@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6:bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : reg_index = unsigned(Rd);
  let n : reg_index = unsigned(Rn);
  let m : reg_index = unsigned(Rm);

  if sf == bitzero & imm6[5] == bitone then None ()
  else if imm6 != 0b000000 then None ()
  else Some(ExclusiveOr((d,n,m)));
}

/* EOR Xd, Xn, Xm */
function clause execute ExclusiveOr(d, n, m) = {
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

val decodeDataMemoryBarrier : bits(32) -> option(ast)
function decodeDataMemoryBarrier (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b1@0b01@0b11111) = {
  if CRm != 0b1111 then None ()
  else Some(DataMemoryBarrier());
}

/* DMB */
function clause execute DataMemoryBarrier() = {
  dataMemoryBarrier();
}

val decodeCompareAndBranch : bits(32) -> option(ast)
function decodeCompareAndBranch (0b1@0b011010@0b0@(imm19:bits(19))@(Rt:bits(5))) = {
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

val decode : bits(32) -> option(ast)
function decode (machineCode) = {
  match machineCode {
    (0b11@0b111@0b0@0b00@(_:bits(2))@0b1@(_:bits(9))@0b10@(_:bits(10))) => decodeLoadStoreRegister(machineCode),
    ([_]@0b10@0b01010@(_:bits(24)))                                     => decodeExclusiveOr(machineCode),
    (0b1101010100@0b0@0b00@0b011@0b0011@(_ : bits(4))@0b1@0b01@0b11111) => decodeDataMemoryBarrier(machineCode),
    (0b1@0b011010@0b0@(_:bits(24)))                                     => decodeCompareAndBranch(machineCode),
    _                                                                   => None()
  }
}

// Simple top level fetch and execute loop.
val fetch_and_execute : unit -> unit

function fetch_and_execute () = {
  let machineCode = iFetch(_PC);
  let instr = decode(machineCode);
  match instr {
    Some (instr) => execute(instr),
    None () => assert (false, "Unsupported Encoding")
  }
}
