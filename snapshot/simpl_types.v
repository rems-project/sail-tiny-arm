(*Generated by Sail from simpl.*)
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import SailStdpp.ConcurrencyInterface.
Require Import SailStdpp.ConcurrencyInterfaceBuiltins.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

Definition bits (n : Z) : Type := mword n.

Definition boolean : Type := bitU.

Definition integer : Type := Z.

Definition uinteger : Type := Z.

Definition reg_index : Type := Z.

Inductive ast :=
| LoadRegister : (reg_index * reg_index * reg_index) -> ast
| StoreRegister : (reg_index * reg_index * reg_index) -> ast
| ExclusiveOr : (reg_index * reg_index * reg_index) -> ast
| DataMemoryBarrier : unit -> ast
| CompareAndBranch : (reg_index * bits 64) -> ast.
Arguments ast : clear implicits.

#[export]
Instance dummy_ast : Inhabited (ast) := { inhabitant := LoadRegister inhabitant }.

Inductive register_value :=
| Regval_vector : list register_value -> register_value
| Regval_list : list register_value -> register_value
| Regval_option : option register_value -> register_value
| Regval_bool : bool -> register_value
| Regval_int : Z -> register_value
| Regval_real : R -> register_value
| Regval_string : string -> register_value
| Regval_bit : bitU -> register_value
| Regval_bitvector_64 : mword 64 -> register_value.
Arguments register_value : clear implicits.

#[export]
Instance dummy_register_value : Inhabited (register_value) := {
  inhabitant := Regval_vector inhabitant
}.

Record regstate := {
  R0 : mword 64;
  R1 : mword 64;
  R2 : mword 64;
  R3 : mword 64;
  R4 : mword 64;
  R5 : mword 64;
  R6 : mword 64;
  R7 : mword 64;
  R8 : mword 64;
  R9 : mword 64;
  R10 : mword 64;
  R11 : mword 64;
  R12 : mword 64;
  R13 : mword 64;
  R14 : mword 64;
  R15 : mword 64;
  R16 : mword 64;
  R17 : mword 64;
  R18 : mword 64;
  R19 : mword 64;
  R20 : mword 64;
  R21 : mword 64;
  R22 : mword 64;
  R23 : mword 64;
  R24 : mword 64;
  R25 : mword 64;
  R26 : mword 64;
  R27 : mword 64;
  R28 : mword 64;
  R29 : mword 64;
  R30 : mword 64;
  _PC : mword 64;
}.
Arguments regstate : clear implicits.
Notation "{[ r 'with' 'R0' := e ]}" :=
  match r with Build_regstate _ f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate e f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R1' := e ]}" :=
  match r with Build_regstate f0 _ f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 e f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R2' := e ]}" :=
  match r with Build_regstate f0 f1 _ f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 e f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R3' := e ]}" :=
  match r with Build_regstate f0 f1 f2 _ f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 e f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R4' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 _ f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 e f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R5' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 _ f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 e f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R6' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 _ f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 e f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R7' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 _ f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 e f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R8' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 _ f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 e f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R9' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 _ f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 e f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R10' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 _ f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R11' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 _ f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R12' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 e f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R13' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 _ f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 e f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R14' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 _ f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 e f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R15' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 _ f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 e f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R16' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _ f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 e f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R17' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 _ f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 e f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R18' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 _ f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 e f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R19' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 _ f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 e f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R20' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 _ f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 e f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R21' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 _ f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 e f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R22' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 _ f23 f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 e f23 f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R23' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 _ f24 f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 e f24 f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R24' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 _ f25 f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 e f25 f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R25' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 _ f26 f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 e f26 f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R26' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 _ f27 f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 e f27 f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R27' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 _ f28 f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 e f28 f29 f30 f31
      end.
Notation "{[ r 'with' 'R28' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 _ f29 f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 e f29 f30 f31
      end.
Notation "{[ r 'with' 'R29' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 _ f30 f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 e f30 f31
      end.
Notation "{[ r 'with' 'R30' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 _ f31 =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 e f31
      end.
Notation "{[ r 'with' '_PC' := e ]}" :=
  match r with Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 _ =>
    Build_regstate f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 e
      end.
#[export]
Instance dummy_regstate : Inhabited (regstate ) := {
  inhabitant := {|
    R0 := inhabitant;
    R1 := inhabitant;
    R2 := inhabitant;
    R3 := inhabitant;
    R4 := inhabitant;
    R5 := inhabitant;
    R6 := inhabitant;
    R7 := inhabitant;
    R8 := inhabitant;
    R9 := inhabitant;
    R10 := inhabitant;
    R11 := inhabitant;
    R12 := inhabitant;
    R13 := inhabitant;
    R14 := inhabitant;
    R15 := inhabitant;
    R16 := inhabitant;
    R17 := inhabitant;
    R18 := inhabitant;
    R19 := inhabitant;
    R20 := inhabitant;
    R21 := inhabitant;
    R22 := inhabitant;
    R23 := inhabitant;
    R24 := inhabitant;
    R25 := inhabitant;
    R26 := inhabitant;
    R27 := inhabitant;
    R28 := inhabitant;
    R29 := inhabitant;
    R30 := inhabitant;
    _PC := inhabitant
|} }.




Definition bit_of_regval (merge_var : register_value) : option bitU :=
   match merge_var with | Regval_bit v => Some v | _ => None end.

Definition regval_of_bit (v : bitU) : register_value := Regval_bit v.

Definition bitvector_64_of_regval (merge_var : register_value) : option (mword 64) :=
   match merge_var with | Regval_bitvector_64 v => Some v | _ => None end.

Definition regval_of_bitvector_64 (v : mword 64) : register_value := Regval_bitvector_64 v.



Definition bool_of_regval (merge_var : register_value) : option bool :=
  match merge_var with | Regval_bool v => Some v | _ => None end.

Definition regval_of_bool (v : bool) : register_value := Regval_bool v.

Definition int_of_regval (merge_var : register_value) : option Z :=
  match merge_var with | Regval_int v => Some v | _ => None end.

Definition regval_of_int (v : Z) : register_value := Regval_int v.

Definition real_of_regval (merge_var : register_value) : option R :=
  match merge_var with | Regval_real v => Some v | _ => None end.

Definition regval_of_real (v : R) : register_value := Regval_real v.

Definition string_of_regval (merge_var : register_value) : option string :=
  match merge_var with | Regval_string v => Some v | _ => None end.

Definition regval_of_string (v : string) : register_value := Regval_string v.

Definition vector_of_regval {a} n (of_regval : register_value -> option a) (rv : register_value) : option (vec a n) := match rv with
  | Regval_vector v => if n =? length_list v then map_bind (vec_of_list n) (just_list (List.map of_regval v)) else None
  | _ => None
end.

Definition regval_of_vector {a size} (regval_of : a -> register_value) (xs : vec a size) : register_value := Regval_vector (List.map regval_of (list_of_vec xs)).

Definition list_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (list a) := match rv with
  | Regval_list v => just_list (List.map of_regval v)
  | _ => None
end.

Definition regval_of_list {a} (regval_of : a -> register_value) (xs : list a) : register_value := Regval_list (List.map regval_of xs).

Definition option_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (option a) := match rv with
  | Regval_option v => option_map of_regval v
  | _ => None
end.

Definition regval_of_option {a} (regval_of : a -> register_value) (v : option a) := Regval_option (option_map regval_of v).


Definition R0_ref := {|
  name := "R0";
  read_from := (fun s => s.(R0));
  write_to := (fun v s => ({[ s with R0 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R1_ref := {|
  name := "R1";
  read_from := (fun s => s.(R1));
  write_to := (fun v s => ({[ s with R1 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R2_ref := {|
  name := "R2";
  read_from := (fun s => s.(R2));
  write_to := (fun v s => ({[ s with R2 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R3_ref := {|
  name := "R3";
  read_from := (fun s => s.(R3));
  write_to := (fun v s => ({[ s with R3 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R4_ref := {|
  name := "R4";
  read_from := (fun s => s.(R4));
  write_to := (fun v s => ({[ s with R4 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R5_ref := {|
  name := "R5";
  read_from := (fun s => s.(R5));
  write_to := (fun v s => ({[ s with R5 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R6_ref := {|
  name := "R6";
  read_from := (fun s => s.(R6));
  write_to := (fun v s => ({[ s with R6 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R7_ref := {|
  name := "R7";
  read_from := (fun s => s.(R7));
  write_to := (fun v s => ({[ s with R7 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R8_ref := {|
  name := "R8";
  read_from := (fun s => s.(R8));
  write_to := (fun v s => ({[ s with R8 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R9_ref := {|
  name := "R9";
  read_from := (fun s => s.(R9));
  write_to := (fun v s => ({[ s with R9 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R10_ref := {|
  name := "R10";
  read_from := (fun s => s.(R10));
  write_to := (fun v s => ({[ s with R10 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R11_ref := {|
  name := "R11";
  read_from := (fun s => s.(R11));
  write_to := (fun v s => ({[ s with R11 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R12_ref := {|
  name := "R12";
  read_from := (fun s => s.(R12));
  write_to := (fun v s => ({[ s with R12 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R13_ref := {|
  name := "R13";
  read_from := (fun s => s.(R13));
  write_to := (fun v s => ({[ s with R13 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R14_ref := {|
  name := "R14";
  read_from := (fun s => s.(R14));
  write_to := (fun v s => ({[ s with R14 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R15_ref := {|
  name := "R15";
  read_from := (fun s => s.(R15));
  write_to := (fun v s => ({[ s with R15 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R16_ref := {|
  name := "R16";
  read_from := (fun s => s.(R16));
  write_to := (fun v s => ({[ s with R16 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R17_ref := {|
  name := "R17";
  read_from := (fun s => s.(R17));
  write_to := (fun v s => ({[ s with R17 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R18_ref := {|
  name := "R18";
  read_from := (fun s => s.(R18));
  write_to := (fun v s => ({[ s with R18 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R19_ref := {|
  name := "R19";
  read_from := (fun s => s.(R19));
  write_to := (fun v s => ({[ s with R19 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R20_ref := {|
  name := "R20";
  read_from := (fun s => s.(R20));
  write_to := (fun v s => ({[ s with R20 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R21_ref := {|
  name := "R21";
  read_from := (fun s => s.(R21));
  write_to := (fun v s => ({[ s with R21 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R22_ref := {|
  name := "R22";
  read_from := (fun s => s.(R22));
  write_to := (fun v s => ({[ s with R22 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R23_ref := {|
  name := "R23";
  read_from := (fun s => s.(R23));
  write_to := (fun v s => ({[ s with R23 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R24_ref := {|
  name := "R24";
  read_from := (fun s => s.(R24));
  write_to := (fun v s => ({[ s with R24 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R25_ref := {|
  name := "R25";
  read_from := (fun s => s.(R25));
  write_to := (fun v s => ({[ s with R25 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R26_ref := {|
  name := "R26";
  read_from := (fun s => s.(R26));
  write_to := (fun v s => ({[ s with R26 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R27_ref := {|
  name := "R27";
  read_from := (fun s => s.(R27));
  write_to := (fun v s => ({[ s with R27 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R28_ref := {|
  name := "R28";
  read_from := (fun s => s.(R28));
  write_to := (fun v s => ({[ s with R28 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R29_ref := {|
  name := "R29";
  read_from := (fun s => s.(R29));
  write_to := (fun v s => ({[ s with R29 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition R30_ref := {|
  name := "R30";
  read_from := (fun s => s.(R30));
  write_to := (fun v s => ({[ s with R30 := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Definition _PC_ref := {|
  name := "_PC";
  read_from := (fun s => s.(_PC));
  write_to := (fun v s => ({[ s with _PC := v ]}));
  of_regval := (fun v => bitvector_64_of_regval v);
  regval_of := (fun v => regval_of_bitvector_64 v) |}.

Local Open Scope string.
Definition get_regval (reg_name : string) (s : regstate) : option register_value :=
  if string_dec reg_name "R0" then Some (R0_ref.(regval_of) (R0_ref.(read_from) s)) else
  if string_dec reg_name "R1" then Some (R1_ref.(regval_of) (R1_ref.(read_from) s)) else
  if string_dec reg_name "R2" then Some (R2_ref.(regval_of) (R2_ref.(read_from) s)) else
  if string_dec reg_name "R3" then Some (R3_ref.(regval_of) (R3_ref.(read_from) s)) else
  if string_dec reg_name "R4" then Some (R4_ref.(regval_of) (R4_ref.(read_from) s)) else
  if string_dec reg_name "R5" then Some (R5_ref.(regval_of) (R5_ref.(read_from) s)) else
  if string_dec reg_name "R6" then Some (R6_ref.(regval_of) (R6_ref.(read_from) s)) else
  if string_dec reg_name "R7" then Some (R7_ref.(regval_of) (R7_ref.(read_from) s)) else
  if string_dec reg_name "R8" then Some (R8_ref.(regval_of) (R8_ref.(read_from) s)) else
  if string_dec reg_name "R9" then Some (R9_ref.(regval_of) (R9_ref.(read_from) s)) else
  if string_dec reg_name "R10" then Some (R10_ref.(regval_of) (R10_ref.(read_from) s)) else
  if string_dec reg_name "R11" then Some (R11_ref.(regval_of) (R11_ref.(read_from) s)) else
  if string_dec reg_name "R12" then Some (R12_ref.(regval_of) (R12_ref.(read_from) s)) else
  if string_dec reg_name "R13" then Some (R13_ref.(regval_of) (R13_ref.(read_from) s)) else
  if string_dec reg_name "R14" then Some (R14_ref.(regval_of) (R14_ref.(read_from) s)) else
  if string_dec reg_name "R15" then Some (R15_ref.(regval_of) (R15_ref.(read_from) s)) else
  if string_dec reg_name "R16" then Some (R16_ref.(regval_of) (R16_ref.(read_from) s)) else
  if string_dec reg_name "R17" then Some (R17_ref.(regval_of) (R17_ref.(read_from) s)) else
  if string_dec reg_name "R18" then Some (R18_ref.(regval_of) (R18_ref.(read_from) s)) else
  if string_dec reg_name "R19" then Some (R19_ref.(regval_of) (R19_ref.(read_from) s)) else
  if string_dec reg_name "R20" then Some (R20_ref.(regval_of) (R20_ref.(read_from) s)) else
  if string_dec reg_name "R21" then Some (R21_ref.(regval_of) (R21_ref.(read_from) s)) else
  if string_dec reg_name "R22" then Some (R22_ref.(regval_of) (R22_ref.(read_from) s)) else
  if string_dec reg_name "R23" then Some (R23_ref.(regval_of) (R23_ref.(read_from) s)) else
  if string_dec reg_name "R24" then Some (R24_ref.(regval_of) (R24_ref.(read_from) s)) else
  if string_dec reg_name "R25" then Some (R25_ref.(regval_of) (R25_ref.(read_from) s)) else
  if string_dec reg_name "R26" then Some (R26_ref.(regval_of) (R26_ref.(read_from) s)) else
  if string_dec reg_name "R27" then Some (R27_ref.(regval_of) (R27_ref.(read_from) s)) else
  if string_dec reg_name "R28" then Some (R28_ref.(regval_of) (R28_ref.(read_from) s)) else
  if string_dec reg_name "R29" then Some (R29_ref.(regval_of) (R29_ref.(read_from) s)) else
  if string_dec reg_name "R30" then Some (R30_ref.(regval_of) (R30_ref.(read_from) s)) else
  if string_dec reg_name "_PC" then Some (_PC_ref.(regval_of) (_PC_ref.(read_from) s)) else
  None.

Definition set_regval (reg_name : string) (v : register_value) (s : regstate) : option regstate :=
  if string_dec reg_name "R0" then option_map (fun v => R0_ref.(write_to) v s) (R0_ref.(of_regval) v) else
  if string_dec reg_name "R1" then option_map (fun v => R1_ref.(write_to) v s) (R1_ref.(of_regval) v) else
  if string_dec reg_name "R2" then option_map (fun v => R2_ref.(write_to) v s) (R2_ref.(of_regval) v) else
  if string_dec reg_name "R3" then option_map (fun v => R3_ref.(write_to) v s) (R3_ref.(of_regval) v) else
  if string_dec reg_name "R4" then option_map (fun v => R4_ref.(write_to) v s) (R4_ref.(of_regval) v) else
  if string_dec reg_name "R5" then option_map (fun v => R5_ref.(write_to) v s) (R5_ref.(of_regval) v) else
  if string_dec reg_name "R6" then option_map (fun v => R6_ref.(write_to) v s) (R6_ref.(of_regval) v) else
  if string_dec reg_name "R7" then option_map (fun v => R7_ref.(write_to) v s) (R7_ref.(of_regval) v) else
  if string_dec reg_name "R8" then option_map (fun v => R8_ref.(write_to) v s) (R8_ref.(of_regval) v) else
  if string_dec reg_name "R9" then option_map (fun v => R9_ref.(write_to) v s) (R9_ref.(of_regval) v) else
  if string_dec reg_name "R10" then option_map (fun v => R10_ref.(write_to) v s) (R10_ref.(of_regval) v) else
  if string_dec reg_name "R11" then option_map (fun v => R11_ref.(write_to) v s) (R11_ref.(of_regval) v) else
  if string_dec reg_name "R12" then option_map (fun v => R12_ref.(write_to) v s) (R12_ref.(of_regval) v) else
  if string_dec reg_name "R13" then option_map (fun v => R13_ref.(write_to) v s) (R13_ref.(of_regval) v) else
  if string_dec reg_name "R14" then option_map (fun v => R14_ref.(write_to) v s) (R14_ref.(of_regval) v) else
  if string_dec reg_name "R15" then option_map (fun v => R15_ref.(write_to) v s) (R15_ref.(of_regval) v) else
  if string_dec reg_name "R16" then option_map (fun v => R16_ref.(write_to) v s) (R16_ref.(of_regval) v) else
  if string_dec reg_name "R17" then option_map (fun v => R17_ref.(write_to) v s) (R17_ref.(of_regval) v) else
  if string_dec reg_name "R18" then option_map (fun v => R18_ref.(write_to) v s) (R18_ref.(of_regval) v) else
  if string_dec reg_name "R19" then option_map (fun v => R19_ref.(write_to) v s) (R19_ref.(of_regval) v) else
  if string_dec reg_name "R20" then option_map (fun v => R20_ref.(write_to) v s) (R20_ref.(of_regval) v) else
  if string_dec reg_name "R21" then option_map (fun v => R21_ref.(write_to) v s) (R21_ref.(of_regval) v) else
  if string_dec reg_name "R22" then option_map (fun v => R22_ref.(write_to) v s) (R22_ref.(of_regval) v) else
  if string_dec reg_name "R23" then option_map (fun v => R23_ref.(write_to) v s) (R23_ref.(of_regval) v) else
  if string_dec reg_name "R24" then option_map (fun v => R24_ref.(write_to) v s) (R24_ref.(of_regval) v) else
  if string_dec reg_name "R25" then option_map (fun v => R25_ref.(write_to) v s) (R25_ref.(of_regval) v) else
  if string_dec reg_name "R26" then option_map (fun v => R26_ref.(write_to) v s) (R26_ref.(of_regval) v) else
  if string_dec reg_name "R27" then option_map (fun v => R27_ref.(write_to) v s) (R27_ref.(of_regval) v) else
  if string_dec reg_name "R28" then option_map (fun v => R28_ref.(write_to) v s) (R28_ref.(of_regval) v) else
  if string_dec reg_name "R29" then option_map (fun v => R29_ref.(write_to) v s) (R29_ref.(of_regval) v) else
  if string_dec reg_name "R30" then option_map (fun v => R30_ref.(write_to) v s) (R30_ref.(of_regval) v) else
  if string_dec reg_name "_PC" then option_map (fun v => _PC_ref.(write_to) v s) (_PC_ref.(of_regval) v) else
  None.

Definition register_accessors := (get_regval, set_regval).


Module Arch <: Arch.
  Definition reg := string.
  Definition reg_type := register_value.
  Definition va_size := 64%N.
  Definition pa := mword 64.
  Definition arch_ak := unit.
  Definition translation := unit.
  Definition abort := unit.
  Definition barrier := unit.
  Definition cache_op := unit.
  Definition tlb_op := unit.
  Definition fault (deps : Type) := unit.
  Definition footprint_system_registers : list reg := [].
End Arch.

Module Interface := Interface Arch.
Module Defs := Defs Arch Interface.

Definition M a := Defs.monad a unit.
Definition MR a r := Defs.monad a (r + unit)%type.
Definition returnM {A:Type} : A -> M A := Defs.returnm (E := unit).
Definition returnR {A:Type} (R:Type) : A -> MR A R := Defs.returnm (E := R + unit)%type.