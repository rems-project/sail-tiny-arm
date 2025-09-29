/* BSD 3-clause Clear License

Copyright (c) 2022
  Arm Limited (or its affiliates),
  Thomas Bauereiss,
  Brian Campbell,
  Alasdair Armstrong,
  Alastair Reid,
  Peter Sewell

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted (subject to the limitations in the
disclaimer below) provided that the following conditions are met:

  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
  * Neither the name of ARM Limited nor the names of its contributors
    may be used to endorse or promote products derived from this
    software without specific prior written permission.

NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE GRANTED
BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,
BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

// Generated from the official sail-arm repo:
// - version 9.4
// - sail commit 38371c9f
// - sail-arm commit 17e64fb
// - command (in armv9.4 folder): make interface_types.sail

enum SecurityState = {SS_NonSecure, SS_Root, SS_Realm, SS_Secure}

type PARTIDtype = bits(16)

type PMGtype = bits(8)

enum PARTIDspaceType = {
  PIdSpace_Secure,
  PIdSpace_Root,
  PIdSpace_Realm,
  PIdSpace_NonSecure
}

struct MPAMinfo = {
  mpam_sp : PARTIDspaceType,
  partid : PARTIDtype,
  pmg : PMGtype
}

enum AccessType = {
  AccessType_IFETCH,
  AccessType_GPR,
  AccessType_ASIMD,
  AccessType_SVE,
  AccessType_SME,
  AccessType_IC,
  AccessType_DC,
  AccessType_DCZero,
  AccessType_AT,
  AccessType_NV2,
  AccessType_SPE,
  AccessType_GCS,
  AccessType_GPTW,
  AccessType_TTW
}

enum VARange = {VARange_LOWER, VARange_UPPER}

enum MemAtomicOp = {
  MemAtomicOp_GCSSS1,
  MemAtomicOp_ADD,
  MemAtomicOp_BIC,
  MemAtomicOp_EOR,
  MemAtomicOp_ORR,
  MemAtomicOp_SMAX,
  MemAtomicOp_SMIN,
  MemAtomicOp_UMAX,
  MemAtomicOp_UMIN,
  MemAtomicOp_SWP,
  MemAtomicOp_CAS
}

enum CacheOp = {CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate}

enum CacheOpScope = {
  CacheOpScope_SetWay,
  CacheOpScope_PoU,
  CacheOpScope_PoC,
  CacheOpScope_PoE,
  CacheOpScope_PoP,
  CacheOpScope_PoDP,
  CacheOpScope_PoPA,
  CacheOpScope_ALLU,
  CacheOpScope_ALLUIS
}

enum CacheType = {
  CacheType_Data,
  CacheType_Tag,
  CacheType_Data_Tag,
  CacheType_Instruction
}

enum CachePASpace = {
  CPAS_NonSecure,
  CPAS_Any,
  CPAS_RealmNonSecure,
  CPAS_Realm,
  CPAS_Root,
  CPAS_SecureNonSecure,
  CPAS_Secure
}

struct AccessDescriptor = {
  acctype : AccessType,
  el : bits(2),
  ss : SecurityState,
  acqsc : bool,
  acqpc : bool,
  relsc : bool,
  limitedordered : bool,
  exclusive : bool,
  atomicop : bool,
  modop : MemAtomicOp,
  nontemporal : bool,
  read : bool,
  write : bool,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  pan : bool,
  transactional : bool,
  nonfault : bool,
  firstfault : bool,
  first : bool,
  contiguous : bool,
  streamingsve : bool,
  ls64 : bool,
  mops : bool,
  rcw : bool,
  rcws : bool,
  toplevel : bool,
  varange : VARange,
  a32lsmd : bool,
  tagchecked : bool,
  tagaccess : bool,
  mpam : MPAMinfo
}

enum MemType = {MemType_Normal, MemType_Device}

enum DeviceType = {
  DeviceType_GRE,
  DeviceType_nGRE,
  DeviceType_nGnRE,
  DeviceType_nGnRnE
}

struct MemAttrHints = {attrs : bits(2), hints : bits(2), transient : bool}

enum Shareability = {Shareability_NSH, Shareability_ISH, Shareability_OSH}

enum MemTagType = {
  MemTag_Untagged,
  MemTag_AllocationTagged,
  MemTag_CanonicallyTagged
}

struct MemoryAttributes = {
  memtype : MemType,
  device : DeviceType,
  inner : MemAttrHints,
  outer : MemAttrHints,
  shareability : Shareability,
  tags : MemTagType,
  notagaccess : bool,
  xs : bits(1)
}

enum PASpace = {PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm}

struct FullAddress = {paspace : PASpace, address : bits(56)}

enum GPCF = {GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail}

struct GPCFRecord = {gpf : GPCF, level : int}

enum Fault = {
  Fault_None,
  Fault_AccessFlag,
  Fault_Alignment,
  Fault_Background,
  Fault_Domain,
  Fault_Permission,
  Fault_Translation,
  Fault_AddressSize,
  Fault_SyncExternal,
  Fault_SyncExternalOnWalk,
  Fault_SyncParity,
  Fault_SyncParityOnWalk,
  Fault_GPCFOnWalk,
  Fault_GPCFOnOutput,
  Fault_AsyncParity,
  Fault_AsyncExternal,
  Fault_TagCheck,
  Fault_Debug,
  Fault_TLBConflict,
  Fault_BranchTarget,
  Fault_HWUpdateAccessFlag,
  Fault_Lockdown,
  Fault_Exclusive,
  Fault_ICacheMaint
}

enum ErrorState = {
  ErrorState_UC,
  ErrorState_UEU,
  ErrorState_UEO,
  ErrorState_UER,
  ErrorState_CE,
  ErrorState_Uncategorized,
  ErrorState_IMPDEF
}

struct FaultRecord = {
  statuscode : Fault,
  access : AccessDescriptor,
  ipaddress : FullAddress,
  gpcf : GPCFRecord,
  paddress : FullAddress,
  gpcfs2walk : bool,
  s2fs1walk : bool,
  write : bool,
  s1tagnotdata : bool,
  tagaccess : bool,
  level : int,
  extflag : bits(1),
  secondstage : bool,
  assuredonly : bool,
  toplevel : bool,
  overlay : bool,
  dirtybit : bool,
  domain : bits(4),
  merrorstate : ErrorState,
  debugmoe : bits(4)
}

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

struct CacheRecord = {
  acctype : AccessType,
  cacheop : CacheOp,
  opscope : CacheOpScope,
  cachetype : CacheType,
  regval : bits(64),
  paddress : FullAddress,
  vaddress : bits(64),
  setnum : int,
  waynum : int,
  level : int,
  shareability : Shareability,
  translated : bool,
  is_vmid_valid : bool,
  vmid : bits(16),
  is_asid_valid : bool,
  asid : bits(16),
  security : SecurityState,
  cpas : CachePASpace
}

enum Regime = {Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10}

enum TGx = {TGx_4KB, TGx_16KB, TGx_64KB}

struct TLBContext = {
  ss : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  nG : bits(1),
  ipaspace : PASpace,
  includes_s1_name : bool,
  includes_s2_name : bool,
  includes_gpt_name : bool,
  ia : bits(64),
  tg : TGx,
  cnp : bits(1),
  level : int,
  isd128 : bool,
  xs : bits(1)
}

struct AddressDescriptor = {
  fault : FaultRecord,
  memattrs : MemoryAttributes,
  paddress : FullAddress,
  tlbcontext : TLBContext,
  s1assured : bool,
  s2fs1mro : bool,
  mecid : bits(16),
  vaddress : bits(64)
}

struct TranslationStartInfo = {
  ss : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  va : bits(64),
  cnp : bits(1),
  accdesc : AccessDescriptor,
  size : int
}

enum TLBILevel = {TLBILevel_Any, TLBILevel_Last}

enum TLBIOp = {
  TLBIOp_DALL,
  TLBIOp_DASID,
  TLBIOp_DVA,
  TLBIOp_IALL,
  TLBIOp_IASID,
  TLBIOp_IVA,
  TLBIOp_ALL,
  TLBIOp_ASID,
  TLBIOp_IPAS2,
  TLBIPOp_IPAS2,
  TLBIOp_VAA,
  TLBIOp_VA,
  TLBIPOp_VAA,
  TLBIPOp_VA,
  TLBIOp_VMALL,
  TLBIOp_VMALLS12,
  TLBIOp_RIPAS2,
  TLBIPOp_RIPAS2,
  TLBIOp_RVAA,
  TLBIOp_RVA,
  TLBIPOp_RVAA,
  TLBIPOp_RVA,
  TLBIOp_RPA,
  TLBIOp_PAALL
}

enum TLBIMemAttr = {TLBI_AllAttr, TLBI_ExcludeXS}

struct TLBIRecord = {
  op : TLBIOp,
  from_aarch64 : bool,
  security : SecurityState,
  regime : Regime,
  vmid : bits(16),
  asid : bits(16),
  level : TLBILevel,
  attr : TLBIMemAttr,
  ipaspace : PASpace,
  address : bits(64),
  end_address_name : bits(64),
  d64 : bool,
  d128 : bool,
  ttl : bits(4),
  tg : bits(2)
}

struct TLBIInfo = {rec : TLBIRecord, shareability : Shareability}

struct DxB = {domain : MBReqDomain, types : MBReqTypes, nXS : bool}

union Barrier = {
  Barrier_DSB : DxB,
  Barrier_DMB : DxB,
  Barrier_ISB : unit,
  Barrier_SSBB : unit,
  Barrier_PSSBB : unit,
  Barrier_SB : unit
}

$ifdef SYSTEM_TINY_ARM
enum DescriptorType = {
  DescriptorType_Table,
  DescriptorType_Leaf,
  DescriptorType_Invalid
}

enum SDFType = {
  SDFType_Table,
  SDFType_Invalid,
  SDFType_Supersection,
  SDFType_Section,
  SDFType_LargePage,
  SDFType_SmallPage
}

struct Permissions = {
  ap_table : bits(2),
  xn_table : bits(1),
  pxn_table : bits(1),
  uxn_table : bits(1),
  ap : bits(3),
  xn : bits(1),
  uxn : bits(1),
  pxn : bits(1),
  ppi : bits(4),
  upi : bits(4),
  ndirty : bits(1),
  s2pi : bits(4),
  s2dirty : bits(1),
  po_index : bits(4),
  s2po_index : bits(4),
  s2ap : bits(2),
  s2tag_na : bits(1),
  s2xnx : bits(1),
  s2xn : bits(1)
}

struct TTWState = {
  istable : bool,
  level : int,
  baseaddress : FullAddress,
  contiguous : bits(1),
  s1assured : bool,
  s2assuredonly : bits(1),
  disch : bits(1),
  nG : bits(1),
  guardedpage : bits(1),
  sdftype : SDFType,
  domain : bits(4),
  memattrs : MemoryAttributes,
  permissions : Permissions
}

enum Exception = {
  Exception_Uncategorized,
  Exception_WFxTrap,
  Exception_CP15RTTrap,
  Exception_CP15RRTTrap,
  Exception_CP14RTTrap,
  Exception_CP14DTTrap,
  Exception_CP14RRTTrap,
  Exception_AdvSIMDFPAccessTrap,
  Exception_FPIDTrap,
  Exception_LDST64BTrap,
  Exception_PACTrap,
  Exception_IllegalState,
  Exception_SupervisorCall,
  Exception_HypervisorCall,
  Exception_MonitorCall,
  Exception_SystemRegisterTrap,
  Exception_ERetTrap,
  Exception_InstructionAbort,
  Exception_PCAlignment,
  Exception_DataAbort,
  Exception_NV2DataAbort,
  Exception_PACFail,
  Exception_SPAlignment,
  Exception_FPTrappedException,
  Exception_SError,
  Exception_Breakpoint,
  Exception_SoftwareStep,
  Exception_Watchpoint,
  Exception_NV2Watchpoint,
  Exception_SoftwareBreakpoint,
  Exception_VectorCatch,
  Exception_IRQ,
  Exception_SVEAccessTrap,
  Exception_SMEAccessTrap,
  Exception_TSTARTAccessTrap,
  Exception_GPC,
  Exception_BranchTarget,
  Exception_MemCpyMemSet,
  Exception_GCSFail,
  Exception_SystemRegister128Trap,
  Exception_FIQ
}

struct ExceptionRecord = {
  exceptype : Exception,
  syndrome : bits(25),
  syndrome2 : bits(24),
  paddress : FullAddress,
  vaddress : bits(64),
  ipavalid : bool,
  pavalid : bool,
  NS : bits(1),
  ipaddress : bits(56),
  trappedsyscallinst : bool
}
$endif
