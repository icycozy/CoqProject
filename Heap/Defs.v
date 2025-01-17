Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Import SetsNotation
       StateRelMonad
       StateRelMonadOp
       StateRelMonadHoare
       MonadNotation
       Monad.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{|
  bind := StateRelMonad.bind Σ;
  ret := StateRelMonad.ret Σ;
|}.

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

(* 二叉树合法性：唯一父亲，唯一左右儿子，**唯一的树根** *)

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

(* 完全二叉树 *)

Fixpoint is_complete_bintree_v_n (h: BinTree Z Z) (v: Z) (n: nat): Prop :=
  match n with
  | O => h.(vvalid) v /\ 
         ~ exists lc, BinaryTree.step_l h v lc /\
         ~ exists rc, BinaryTree.step_r h v rc
  | S n' => h.(vvalid) v /\
          (exists lc, BinaryTree.step_l h v lc /\ is_complete_bintree_v_n h lc n') /\
          (exists rc, BinaryTree.step_r h v rc /\ is_complete_bintree_v_n h rc n')
  end.

Definition is_complete_bintree_v (h: BinTree Z Z) (v: Z): Prop :=
  exists n, is_complete_bintree_v_n h v n.

(* 满二叉树。为了插入和删除操作的方便，这里的满二叉树不能是完全的 *)

Fixpoint is_full_bintree_v_n (h: BinTree Z Z) (v: Z) (n: nat): Prop :=
  match n with
  | O => False
  | S n' => match n' with
            | O => h.(vvalid) v /\ 
                    (exists lc, BinaryTree.step_l h v lc /\ is_complete_bintree_v_n h lc O) /\
                    ~ exists rc, BinaryTree.step_r h v rc
                   
            | S n'' => h.(vvalid) v /\
                       (
                        ((exists lc, BinaryTree.step_l h v lc /\ is_complete_bintree_v_n h lc n') /\ 
                        (exists rc, BinaryTree.step_r h v rc /\ is_full_bintree_v_n h rc n'))
                        \/
                        ((exists lc, BinaryTree.step_l h v lc /\ is_complete_bintree_v_n h lc n') /\ 
                        (exists rc, BinaryTree.step_r h v rc /\ is_complete_bintree_v_n h rc n''))
                        \/
                        ((exists lc, BinaryTree.step_l h v lc /\ is_full_bintree_v_n h lc n') /\ 
                        (exists rc, BinaryTree.step_r h v rc /\ is_complete_bintree_v_n h rc n''))
                       )
            end
  end.

Definition is_full_bintree_v (h: BinTree Z Z) (v: Z): Prop :=
  exists n, is_full_bintree_v_n h v n.

(* 这是要保持的性质，满二叉树或完全二叉树 *)

Definition is_complete_or_full_bintree (h: BinTree Z Z): Prop :=
  forall v, h.(vvalid) v -> (is_complete_bintree_v h v \/ is_full_bintree_v h v).

(* 小根堆 *)

Record Heap (h: BinTree Z Z): Prop :=
{
  heap_l: forall x y: Z, BinaryTree.step_l h x y -> x < y;
  heap_r: forall x y: Z, BinaryTree.step_r h x y -> x < y;
}.

(* 第一种局部破坏：
1. 当前节点v与父节点fa的大小关系不满足
2. fa与v的左右儿子lc, rc（若存在）的大小关系满足
可能出现在插入过程中。 *)

Record Heap_broken_up (h: BinTree Z Z) (v: Z): Prop :=
{
  up_fa_v_lc_rc: exists fa: Z, BinaryTree.step_u h v fa /\ v < fa /\ 
                               forall lc: Z, BinaryTree.step_l h v lc -> fa < lc /\
                               forall rc: Z, BinaryTree.step_r h v rc -> fa < rc;
  up_others_l: forall x y: Z, BinaryTree.step_l h x y -> ~ (y = v) -> x < y;
  up_others_r: forall x y: Z, BinaryTree.step_r h x y -> ~ (y = v) -> x < y;
}.  

(* 第二种局部破坏：
1. 当前节点v与左右子节点lc, rc的大小关系不满足
2. v的父亲fa（若存在）与lc, rc的大小关系满足
可能出现在删除过程中。 *)

Record Heap_broken_down (h: BinTree Z Z) (v: Z): Prop :=
{
  down_v_lc_rc: (exists lc: Z, BinaryTree.step_l h v lc /\ v > lc) \/
                (exists rc: Z, BinaryTree.step_r h v rc /\ v > rc);
  down_fa_lc_rc: forall fa: Z, BinaryTree.step_u h v fa -> v < fa ->
                    (forall lc: Z, BinaryTree.step_l h v lc -> fa < lc) /\
                    (forall rc: Z, BinaryTree.step_r h v rc -> fa < rc);
  down_others_l: forall x y: Z, BinaryTree.step_l h x y -> ~ (x = v) -> x < y;
  down_others_r: forall x y: Z, BinaryTree.step_r h x y -> ~ (x = v) -> x < y;
}.

Definition Abs (h: BinTree Z Z) (X: Z -> Prop): Prop :=
  X == h.(vvalid).

Record state: Type :=
{
  heap: BinTree Z Z;
}.

Notation "s '.(heap)'" := (heap s) (at level 1).

Definition test_lc_empty (v: Z): StateRelMonad.M state unit :=
  test (fun s => s.(heap).(vvalid) v /\
                 ~ exists lc, BinaryTree.step_l s.(heap) v lc).

Definition test_lc_not_empty (v: Z): StateRelMonad.M state unit :=
  test (fun s => exists lc, BinaryTree.step_l s.(heap) v lc).

Definition test_rc_empty (v: Z): StateRelMonad.M state unit :=
  test (fun s => s.(heap).(vvalid) v /\
                 ~ exists rc, BinaryTree.step_r s.(heap) v rc).

Definition test_rc_not_empty (v: Z): StateRelMonad.M state unit :=
  test (fun s => exists rc, BinaryTree.step_r s.(heap) v rc).

Definition test_is_leaf (v: Z): StateRelMonad.M state unit :=
  test (fun s => s.(heap).(vvalid) v /\
                 (~ exists lc, BinaryTree.step_l s.(heap) v lc) /\
                 (~ exists rc, BinaryTree.step_r s.(heap) v rc)).

Definition test_is_not_leaf (v: Z): StateRelMonad.M state unit :=
  test (fun s => exists lc, BinaryTree.step_l s.(heap) v lc \/
                 exists rc, BinaryTree.step_r s.(heap) v rc).

Definition test_is_root (v: Z): StateRelMonad.M state unit :=
  test (fun s => s.(heap).(vvalid) v /\ 
                   ~ exists fa, BinaryTree.step_u s.(heap) v fa).

Definition test_is_not_root (v: Z): StateRelMonad.M state unit :=
  test (fun s => exists fa, BinaryTree.step_u s.(heap) v fa).

Definition test_empty: StateRelMonad.M state unit :=
  test (fun s => ~ exists x, s.(heap).(vvalid) x).

Definition test_not_empty: StateRelMonad.M state unit :=
  test (fun s => exists x, s.(heap).(vvalid) x).

Definition any_valid_v: StateRelMonad.M state Z :=
  fun s1 v s2 =>
    s1.(heap).(vvalid) v /\ s2 = s1. 

Definition get_fa (v: Z): StateRelMonad.M state Z :=
  fun s1 fa s2 =>
    BinaryTree.step_u s1.(heap) v fa /\ s2 = s1.

Definition get_lc (v: Z): StateRelMonad.M state Z :=
  fun s1 lc s2 =>
    BinaryTree.step_l s1.(heap) v lc /\ s2 = s1.

Definition get_rc (v: Z) : StateRelMonad.M state Z :=
  fun s1 rc s2 =>
    BinaryTree.step_r s1.(heap) v rc /\ s2 = s1.

Definition get_minimum: StateRelMonad.M state Z :=
  fun s1 rt s2 =>
    s1.(heap).(vvalid) rt /\
    forall v, s1.(heap).(vvalid) v -> v >= rt /\
    s2 = s1.



(*********************************************************)
(**                                                      *)
(** swap_v_u                                             *)
(**                                                      *)
(*********************************************************)

Inductive ExistOrEmpty: Type :=
| by_exist (a: Z)
| by_empty.

Definition get_lc' (v: Z): StateRelMonad.M state ExistOrEmpty :=
  choice
    (test_lc_empty v;;
      ret by_empty)
    (lc <- get_lc v;;
    ret (by_exist lc)).

Definition get_rc' (v: Z): StateRelMonad.M state ExistOrEmpty :=
  choice
    (test_rc_empty v;;
      ret by_empty)
    (rc <- get_rc v;;
    ret (by_exist rc)).

Definition get_fa' (v: Z): StateRelMonad.M state ExistOrEmpty :=
  choice
    (test_is_root v;;
      ret by_empty)
    (fa <- get_fa v;;
    ret (by_exist fa)).

Definition remove_go_left_edge (v lc: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) /\
      (exists e0: Z, 
        ~ s2.(heap).(evalid) e0 /\
        s2.(heap).(evalid) ∪ Sets.singleton e0 == s1.(heap).(evalid) /\
        s2.(heap).(src) e0 = v /\
        s2.(heap).(dst) e0 = lc /\
        s2.(heap).(go_left) e0 /\ 
        (forall e: Z, ~ e = e0 ->
          s2.(heap).(src) e = s1.(heap).(src) e /\ 
          s2.(heap).(dst) e = s1.(heap).(dst) e /\ 
          s2.(heap).(go_left) e = s1.(heap).(go_left) e))
    ).

Definition remove_go_right_edge (v rc: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) /\
      (exists e0: Z, 
        ~ s2.(heap).(evalid) e0 /\
        s2.(heap).(evalid) ∪ Sets.singleton e0 == s1.(heap).(evalid) /\
        s2.(heap).(src) e0 = v /\
        s2.(heap).(dst) e0 = rc /\
        ~ s2.(heap).(go_left) e0 /\ 
        (forall e: Z, ~ e = e0 ->
          s2.(heap).(src) e = s1.(heap).(src) e /\ 
          s2.(heap).(dst) e = s1.(heap).(dst) e /\ 
          s2.(heap).(go_left) e = s1.(heap).(go_left) e))
    ).

Definition add_go_left_edge (v lc: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) /\
      (exists e0: Z, 
        ~ s1.(heap).(evalid) e0 /\
        s2.(heap).(evalid) == s1.(heap).(evalid) ∪ Sets.singleton e0 /\
        s2.(heap).(src) e0 = v /\
        s2.(heap).(dst) e0 = lc /\
        s2.(heap).(go_left) e0 /\ 
        (forall e: Z, ~ e = e0 ->
          s2.(heap).(src) e = s1.(heap).(src) e /\ 
          s2.(heap).(dst) e = s1.(heap).(dst) e /\ 
          s2.(heap).(go_left) e = s1.(heap).(go_left) e))
    ).

Definition add_go_right_edge (v rc: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) /\
      (exists e0: Z, 
        ~ s1.(heap).(evalid) e0 /\
        (s2.(heap).(evalid) == s1.(heap).(evalid) ∪ Sets.singleton e0 /\
        s2.(heap).(src) e0 = v /\
        s2.(heap).(dst) e0 = rc /\
        ~ s2.(heap).(go_left) e0) /\ 
        (forall e: Z, ~ e = e0 ->
          s2.(heap).(src) e = s1.(heap).(src) e /\ 
          s2.(heap).(dst) e = s1.(heap).(dst) e /\ 
          s2.(heap).(go_left) e = s1.(heap).(go_left) e))
    ).

Definition remove_go_left_edge' (v: Z) (a: ExistOrEmpty)
  : StateRelMonad.M state unit :=
    match a with
    | by_exist lc => remove_go_left_edge v lc
    | by_empty => ret tt
    end.

Definition remove_go_right_edge' (v: Z) (a: ExistOrEmpty)
  : StateRelMonad.M state unit :=
    match a with
    | by_exist rc => remove_go_right_edge v rc
    | by_empty => ret tt
    end.

Definition add_go_left_edge' (v: Z) (a: ExistOrEmpty)
  : StateRelMonad.M state unit :=
    match a with
    | by_exist lc => add_go_left_edge v lc
    | by_empty => ret tt
    end.

Definition add_go_right_edge' (v: Z) (a: ExistOrEmpty)
  : StateRelMonad.M state unit :=
    match a with
    | by_exist rc => add_go_right_edge v rc
    | by_empty => ret tt
    end.  

Definition get_dir (fa v: Z): StateRelMonad.M state Z :=
  fun s1 dir s2 =>
    (
      (dir = 0 /\ BinaryTree.step_l s2.(heap) fa v /\ s2 = s1) \/
      (dir = 1 /\ BinaryTree.step_r s2.(heap) fa v /\ s2 = s1)
    ).

Definition swap_v_u (v fa: Z): StateRelMonad.M state unit :=
  lc_v <- get_lc' v;;
  rc_v <- get_rc' v;;
  lc_fa <- get_lc' fa;;
  rc_fa <- get_rc' fa;;
  dir_fa_v <- get_dir fa v;;
  remove_go_left_edge' v lc_v;;
  remove_go_right_edge' v rc_v;;
  remove_go_left_edge' fa lc_fa;;
  remove_go_right_edge' fa rc_fa;;
  (choice
    (test_is_root fa)
    (gf <- get_fa fa;;
      choice
        (test (fun s => BinaryTree.step_l s.(heap) gf fa);;
          remove_go_left_edge gf fa;;
          add_go_left_edge gf v)
        (test (fun s => BinaryTree.step_r s.(heap) gf fa);;
          remove_go_right_edge gf fa;;
          add_go_right_edge gf v)));;
  (choice
    (test (fun s => dir_fa_v = 0);;
      add_go_left_edge v fa;;
      add_go_right_edge' v rc_fa)
    (test (fun s => dir_fa_v = 1);;
      add_go_left_edge' v lc_fa;;
      add_go_right_edge v fa));;
  add_go_left_edge' fa lc_v;;
  add_go_right_edge' fa rc_v.


(*********************************************************)
(**                                                      *)
(** insert                                               *)
(**                                                      *)
(*********************************************************)


(* 从v开始向上调整 *)

Definition body_move_up (v: Z):
  StateRelMonad.M state (ContinueOrBreak Z unit) :=
    choice
      (test_is_root v;;
        break tt)
      (fa <- get_fa v;;
      choice
        (test (fun s => v > fa);;
          break tt)
        (test (fun s => v < fa);;
          swap_v_u v fa;;
          continue v)).

Definition move_up (v: Z): StateRelMonad.M state unit :=
  repeat_break body_move_up v.

Definition ext_insert_node (val: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) ∪ Sets.singleton val /\
      BinaryTree.legal s2.(heap) /\
      (Heap s2.(heap) \/ Heap_broken_up s2.(heap) val) /\
      is_complete_or_full_bintree s2.(heap)
    ).

Definition insert (val: Z): StateRelMonad.M state unit :=
  (ext_insert_node val;;
  move_up val).


(*********************************************************)
(**                                                      *)
(** delete                                               *)
(**                                                      *)
(*********************************************************)


Definition body_move_down (v: Z):
  StateRelMonad.M state (ContinueOrBreak Z unit) :=
    choice4
      (test_is_leaf v;;
          break tt)
      (test_lc_empty v;;
        rc <- get_rc v;;
        choice
          (test (fun s => v < rc);;
            break tt)
          (test (fun s => v > rc);;
            swap_v_u v rc;;
            continue v))
      (test_rc_empty v;;
        lc <- get_lc v;;
        choice
          (test (fun s => v < lc);;
            break tt)
          (test (fun s => v > lc);;
            swap_v_u v lc;;
            continue v))
      (lc <- get_lc v;;
      rc <- get_rc v;;
      choice
        (test (fun s => lc < rc);;
          choice
            (test (fun s => v < lc);;
              break tt)
            (test (fun s => v > lc);;
              swap_v_u v lc;;
              continue v))
        (test (fun s => lc > rc);;
          choice
            (test (fun s => v < rc);;
              break tt)
            (test (fun s => v > rc);;
              swap_v_u v rc;;
              continue v))).

Definition move_down (v: Z): StateRelMonad.M state unit :=
  repeat_break body_move_down v.

Definition ext_delete_node (rt: Z): StateRelMonad.M state Z :=
  fun s1 v s2 =>
    (
      ~ s2.(heap).(vvalid) rt /\
      s2.(heap).(vvalid) v /\
      s2.(heap).(vvalid) ∪ Sets.singleton rt == s1.(heap).(vvalid) /\
      BinaryTree.legal s2.(heap) /\
      (Heap s2.(heap) \/ Heap_broken_down s2.(heap) v) /\
      is_complete_or_full_bintree s2.(heap)
    ).

Definition ext_delete_iso_node (rt: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      ~ s2.(heap).(vvalid) rt /\
      s2.(heap).(vvalid) ∪ Sets.singleton rt == s1.(heap).(vvalid) /\
      BinaryTree.legal s2.(heap) /\
      Heap s2.(heap) /\
      is_complete_or_full_bintree s2.(heap)
    ).

Definition delete: StateRelMonad.M state Z :=
    rt <- get_minimum;;
    choice
      (test_is_leaf rt;;
        ext_delete_iso_node rt;;
        ret rt)
      (test_is_not_leaf rt;;
        v <- ext_delete_node rt;;
        move_down v;;
        ret rt).

Definition is_minimum (val: Z) (V: Z -> Prop): Prop :=
    forall x, V x -> x >= val.