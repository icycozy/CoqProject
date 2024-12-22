Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope sets_scope.

(*********************************************************)
(**                                                      *)
(** Binary Tree                                          *)
(**                                                      *)
(*********************************************************)

Module BinaryTree.

Record BinaryTree (Vertex Edge: Type) := {
  vvalid : Vertex -> Prop;
  evalid : Edge -> Prop;
  src : Edge -> Vertex;
  dst : Edge -> Vertex;
  go_left: Edge -> Prop;
}.

Definition go_right (V E: Type) (bt: BinaryTree V E) (e: E): Prop :=
  ~ go_left _ _ bt e.

Notation "bt '.(vvalid)'" := (vvalid _ _ bt) (at level 1).
Notation "bt '.(evalid)'" := (evalid _ _ bt) (at level 1).
Notation "bt '.(src)'" := (src _ _ bt) (at level 1).
Notation "bt '.(dst)'" := (dst _ _ bt) (at level 1).
Notation "bt '.(go_left)'" := (go_left _ _ bt) (at level 1).
Notation "bt '.(go_right)'" := (go_right _ _ bt) (at level 1). 

Record step_aux {V E: Type} (bt: BinaryTree V E) (e: E) (x y: V): Prop :=
{
  step_evalid: bt.(evalid) e;
  step_src_valid: bt.(vvalid) x;
  step_dst_valid: bt.(vvalid) y;
  step_src: bt.(src) e = x;
  step_dst: bt.(dst) e = y;
}.

Definition step_l {V E: Type} (bt: BinaryTree V E) (x y: V): Prop :=
  exists e, step_aux bt e x y /\ bt.(go_left) e.

Definition step_r {V E: Type} (bt: BinaryTree V E) (x y: V): Prop :=
  exists e, step_aux bt e x y /\ bt.(go_right) e.

Definition step_u {V E: Type} (bt: BinaryTree V E) (x y: V): Prop :=
  exists e, step_aux bt e y x.

Record legal {V E: Type} (bt: BinaryTree V E): Prop :=
{
  step_l_unique: forall x y1 y2, step_l bt x y1 -> step_l bt x y2 -> y1 = y2;
  step_r_unique: forall x y1 y2, step_r bt x y1 -> step_r bt x y2 -> y1 = y2;
  step_u_unique: forall x y1 y2, step_u bt x y1 -> step_u bt x y2 -> y1 = y2;
}.

End BinaryTree.

Notation "bt '.(vvalid)'" := (BinaryTree.vvalid _ _ bt) (at level 1).
Notation "bt '.(evalid)'" := (BinaryTree.evalid _ _ bt) (at level 1).
Notation "bt '.(src)'" := (BinaryTree.src _ _ bt) (at level 1).
Notation "bt '.(dst)'" := (BinaryTree.dst _ _ bt) (at level 1).
Notation "bt '.(go_left)'" := (BinaryTree.go_left _ _ bt) (at level 1).
Notation "bt '.(go_right)'" := (BinaryTree.go_right _ _ bt) (at level 1).
Notation "'BinTree'" := (BinaryTree.BinaryTree) (at level 0).

Record Heap (h: BinTree Z Z): Prop :=
{
  heap_l: forall x y: Z, BinaryTree.step_l h x y -> (x <= y)%Z;
  heap_r: forall x y: Z, BinaryTree.step_r h x y -> (x <= y)%Z;
}.

Definition Abs (h: BinTree Z Z) (X: Z -> Prop): Prop :=
  X == h.(vvalid).
