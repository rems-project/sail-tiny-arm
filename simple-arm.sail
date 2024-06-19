union ast =  {
  LoadRegister : (reg_index, reg_index, reg_index),
  StoreRegister : (reg_index, reg_index, reg_index),
  ExclusiveOr : (reg_index, reg_index, reg_index),
  DataMemoryBarrier : unit,
  CompareAndBranch : (reg_index, bits(64)),
}

val execute : ast -> unit
scattered function execute

/* LDR Xt, [Xn, Xm] */
function clause execute ( LoadRegister((t, n, m)) ) = {
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  base_addr : bits(64) = rX(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  offset    : bits(64) = rX(m);
  /* Compute the address */
  addr : bits(64) = base_addr + offset;
  /* Ask for the eight-byte value in memory starting from location
  addr and record it in the local variable data */
  data : bits(64) = rMem(addr);
  /* Ask for the value of data to be written to register Xt */
  wX(t) = data;
}

/* STR Xt, [Xn, Xm] */
function clause execute ( StoreRegister((t, n, m)) ) = {
  /* Ask for the value of register Xn and record it in the local
   * variable base_addr */
  base_addr : bits(64) = rX(n);
  /* Ask for the value of register Xm and record it in the local
   * variable offset */
  offset : bits(64) = rX(m);
  /* Compute the address */
  addr : bits(64) = base_addr + offset;
  /* Announce that a store into the eight bytes of memory starting
   * from location addr will be performed later */
  wMem_Addr(addr);
  /* Ask for the value of register Xt and record it in the local
   * variable data */
  data : bits(64) = rX(t);
  /* Ask for the value of data to be stored into the eight bytes of
   * memory starting from location addr */
  wMem(addr, data);
}

/* EOR Xd, Xn, Xm */
function clause execute ( ExclusiveOr((d, n, m)) ) = {
  /* Ask for the value of register Xn and record it in the local
   * variable operand1 */
  operand1 : bits(64) = rX(n);
  /* Ask for the value of register Xm and record it in the local
   * variable operand2 */
  operand2 : bits(64) = rX(m);
  /* Compute the bitwise exclusive OR */
  result : bits(64) = (operand1 ^ operand2);
  /* Ask for the value of result to be written to register Xd */
  wX(d) = result;
}

/* DMB */
function clause execute ( DataMemoryBarrier() ) = {
  dataMemoryBarrier();
}

/* CBZ Xt, <offset> */
function clause execute ( CompareAndBranch((t, offset)) ) = {
  /* Ask for the value of register Xt and record it in the local
   * variable operand */
  operand : bits(64) = rX(t);
  /* Check if operand is 0 */
  if operand == 0x0000000000000000 then {
    /* Ask for the value of the program counter register and record it
     * in the local variable base */
    base : bits(64) = rPC();
    /* Compute the address */
    addr : bits(64) = base + offset;
    /* Ask for the value of result to be written to the program counter
     * register */
    wPC() = addr;
  };
}
