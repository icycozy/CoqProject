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

Definition is_root {V E: Type} (bt: BinaryTree V E) (x: V): Prop :=
  bt.(vvalid) x /\ ~ exists y, step_u bt x y.

(* 二叉树合法性：唯一父亲，唯一左右儿子，**唯一的树根** *)

Record legal {V E: Type} (bt: BinaryTree V E): Prop :=
{
  step_l_unique: forall x y1 y2, step_l bt x y1 -> step_l bt x y2 -> y1 = y2;
  step_r_unique: forall x y1 y2, step_r bt x y1 -> step_r bt x y2 -> y1 = y2;
  step_u_unique: forall x y1 y2, step_u bt x y1 -> step_u bt x y2 -> y1 = y2;
  empty_or_unique_root: (~ exists x, bt.(vvalid) x) \/
                        (exists x, is_root bt x /\ forall x1 x2, is_root bt x1 -> is_root bt x2 -> x1 = x2);
}.

End BinaryTree.

Notation "bt '.(vvalid)'" := (BinaryTree.vvalid _ _ bt) (at level 1).
Notation "bt '.(evalid)'" := (BinaryTree.evalid _ _ bt) (at level 1).
Notation "bt '.(src)'" := (BinaryTree.src _ _ bt) (at level 1).
Notation "bt '.(dst)'" := (BinaryTree.dst _ _ bt) (at level 1).
Notation "bt '.(go_left)'" := (BinaryTree.go_left _ _ bt) (at level 1).
Notation "bt '.(go_right)'" := (BinaryTree.go_right _ _ bt) (at level 1).
Notation "'BinTree'" := (BinaryTree.BinaryTree) (at level 0).

(* 小根堆 *)

Record Heap (h: BinTree Z Z): Prop :=
{
  heap_l: forall x y: Z, BinaryTree.step_l h x y -> x < y;
  heap_r: forall x y: Z, BinaryTree.step_r h x y -> x < y;
}.

(* 第一种局部破坏：当前节点v与父节点fa的大小关系不满足。可能出现在插入过程中。 *)

Record Heap_broken_up (h: BinTree Z Z) (v: Z): Prop :=
{
  up_fa2v: exists fa: Z, BinaryTree.step_u h v fa /\ v < fa;
  up_others_l: forall x y: Z, BinaryTree.step_l h x y -> ~ (y = v) -> x < y;
  up_others_r: forall x y: Z, BinaryTree.step_r h x y -> ~ (y = v) -> x < y;
}.  

(* 第二种局部破坏：当前节点v与左右子节点lc, rc的大小关系不满足。可能出现在删除过程中。 *)

Record Heap_broken_down (h: BinTree Z Z) (v: Z): Prop :=
{
  down_v2lc_or_v2rc: (exists lc: Z, BinaryTree.step_l h v lc /\ v > lc) \/
                     (exists rc: Z, BinaryTree.step_r h v rc /\ v > rc);
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

Definition test_is_root (v: Z): StateRelMonad.M state unit :=
  test (fun s => BinaryTree.is_root s.(heap) v).

Definition test_is_not_root (v: Z): StateRelMonad.M state unit :=
  test (fun s => ~ BinaryTree.is_root s.(heap) v).

Definition test_lc_empty (v: Z): StateRelMonad.M state unit :=
  test (fun s => ~ exists lc, BinaryTree.step_l s.(heap) v lc).

Definition test_rc_empty (v: Z): StateRelMonad.M state unit :=
  test (fun s => ~ exists rc, BinaryTree.step_r s.(heap) v rc).

Definition test_empty: StateRelMonad.M state unit :=
  test (fun s => ~ exists x, s.(heap).(vvalid) x).

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

Definition get_root: StateRelMonad.M state Z :=
  fun s1 rt s2 =>
    BinaryTree.is_root s1.(heap) rt /\ s2 = s1.

(* 在v的左儿子插入val *)

Definition insert_lc (v val: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) ∪ Sets.singleton val /\
      exists e: Z, 
        (s2.(heap).(evalid) == s1.(heap).(evalid) ∪ Sets.singleton e /\
        s2.(heap).(src) e = v /\
        s2.(heap).(dst) e = val /\
        s2.(heap).(go_left) e)
    ).

(* 在v的右儿子插入val *)

Definition insert_rc (v val: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) ∪ Sets.singleton val /\
      exists e: Z, 
        (s2.(heap).(evalid) == s1.(heap).(evalid) ∪ Sets.singleton e /\
        s2.(heap).(src) e = v /\
        s2.(heap).(dst) e = val /\
        s2.(heap).(go_right) e)
    ).

(* 删除叶子v *)

Definition delete_leaf (v: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) ∪ Sets.singleton v == s1.(heap).(vvalid) /\
      exists e: Z,
        (s2.(heap).(evalid) ∪ Sets.singleton e == s1.(heap).(evalid) /\
        s1.(heap).(dst) e = v)
    ).

(* 交换节点v与u，分五种边讨论 *)
    
Definition swap_v_u (v u: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == s1.(heap).(vvalid) /\
      s2.(heap).(evalid) == s1.(heap).(evalid) /\
      forall e: Z, s2.(heap).(go_left) e = s1.(heap).(go_left) e /\ 

      forall e: Z, (s1.(heap).(evalid) e ->
                    (~ s1.(heap).(src) e = v /\ ~ s1.(heap).(src) e = u) ->
                    (~ s1.(heap).(dst) e = v /\ ~ s1.(heap).(dst) e = u) ->
                    s2.(heap).(src) e = s1.(heap).(src) e /\
                    s2.(heap).(dst) e = s1.(heap).(dst) e) /\ 

      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(src) e = v ->
                      (s2.(heap).(src) e = u /\
                      s2.(heap).(dst) e = s1.(heap).(dst) e)) /\
      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(src) e = u ->
                      (s2.(heap).(src) e = v /\
                      s2.(heap).(dst) e = s1.(heap).(dst) e)) /\
      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(dst) e = v ->
                      (s2.(heap).(dst) e = u /\
                      s2.(heap).(src) e = s1.(heap).(src) e)) /\
      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(dst) e = u ->
                      (s2.(heap).(dst) e = v /\
                      s2.(heap).(src) e = s1.(heap).(src) e))
    ).

(* 建立只含一个元素的堆 *)

Definition heap_single (v: Z): StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == Sets.singleton v /\
      s2.(heap).(evalid) == Sets.empty
    ).

(* 建立空堆 *)

Definition heap_empty: StateRelMonad.M state unit :=
  fun s1 _ s2 =>
    (
      s2.(heap).(vvalid) == Sets.empty /\
      s2.(heap).(evalid) == Sets.empty
    ).

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
  
(* 上移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，最终恢复堆性质 *)

Theorem move_up_correctness: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap_broken_up s.(heap) v \/ Heap s.(heap)))
        (move_up v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Admitted.

Definition insert (val: Z): StateRelMonad.M state unit :=
  choice
    (v <- any_valid_v;;
     choice
      (test_lc_empty v;;
        insert_lc v val;;
        move_up val)
      (test_rc_empty v;;
        insert_rc v val;;  
        move_up val))
    (test_empty;;
      heap_single val).

(* 插入操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 保持堆性质 *)

Theorem insert_correctness: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        (insert val)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton val) /\ 
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Admitted.


Definition body_move_down (v: Z):
  StateRelMonad.M state (ContinueOrBreak Z unit) :=
    choice
      (test_lc_empty v;;
        choice
          (test_rc_empty v;;
            break tt)
          (rc <- get_rc v;;
            choice
              (test (fun s => v < rc);;
                break tt)
              (test (fun s => v > rc);;
                swap_v_u v rc;;
                continue v)))
      (lc <- get_lc v;;
      choice
        (test_rc_empty v;;
          choice
            (test (fun s => v < lc);;
              break tt)
            (test (fun s => v > lc);;
              swap_v_u v lc;;
              continue v))
        (rc <- get_rc v;;
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
                continue v)))).

Definition move_down (v: Z): StateRelMonad.M state unit :=
  repeat_break body_move_down v.

(* 下移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，最终恢复堆性质 *)

Theorem move_down_correctness: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap_broken_down s.(heap) v \/ Heap s.(heap)))
        (move_down v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Admitted.

Definition delete: StateRelMonad.M state Z :=
  rt <- get_root;;
  v <- any_valid_v;;
  test_lc_empty v;;
  test_rc_empty v;;
  choice
    (test (fun s => v = rt);;
      heap_empty;;
      ret rt)
    (test (fun s => ~ v = rt);;
      swap_v_u v rt;;
      delete_leaf rt;;
      move_down v;;
      ret rt).

Definition is_minimum (val: Z) (V: Z -> Prop): Prop :=
  forall x, V x -> x >= val.

(* 删除操作正确性（保证非空的前提下）：
1. 删除的元素是最小值
2. 保持二叉树合法性
3. 保持堆性质 *)

Theorem delete_correctness: forall (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ V == ∅ /\
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        delete
        (fun val s => (s.(heap).(vvalid) ∪ Sets.singleton val) == V /\
                      is_minimum val V /\
                      BinaryTree.legal s.(heap) /\
                      Heap s.(heap)).
Admitted.