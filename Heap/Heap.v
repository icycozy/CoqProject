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
                 ~ exists lc, BinaryTree.step_l s.(heap) v lc /\
                 ~ exists rc, BinaryTree.step_r s.(heap) v rc).

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

(* Definition get_root: StateRelMonad.M state Z :=
  fun s1 rt s2 =>
    BinaryTree.is_root s1.(heap) rt /\ s2 = s1. *)

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

(* 交换节点v与u，
将边按照src, dst是否是v, u分类讨论 *)
    
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
                    s1.(heap).(dst) e = u ->
                      (s2.(heap).(src) e = u /\
                      s2.(heap).(dst) e = v)) /\

      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(src) e = u ->
                    s1.(heap).(dst) e = v ->
                      (s2.(heap).(src) e = v /\
                      s2.(heap).(dst) e = u)) /\

      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(src) e = v ->
                    ~ s1.(heap).(dst) e = u ->
                      (s2.(heap).(src) e = u /\
                      s2.(heap).(dst) e = s1.(heap).(dst) e)) /\

      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(src) e = u ->
                    ~ s1.(heap).(dst) e = v ->
                      (s2.(heap).(src) e = v /\
                      s2.(heap).(dst) e = s1.(heap).(dst) e)) /\

      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(dst) e = v ->
                    ~ s1.(heap).(src) e = u ->
                      (s2.(heap).(dst) e = u /\
                      s2.(heap).(src) e = s1.(heap).(src) e)) /\

      forall e: Z, (s1.(heap).(evalid) e ->
                    s1.(heap).(dst) e = u ->
                    ~ s1.(heap).(src) e = v ->
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
  
(* 上移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，变为堆
4. 保持满二叉树 *)

Theorem move_up_correctness1: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap_broken_up s.(heap) v \/ Heap s.(heap)))
        (move_up v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Proof.
   intros.
   unfold Hoare. split.
   + unfold Abs. destruct H as [h1 h2].
     destruct h2 as [h3 h4].
     unfold Abs in h3.
     rewrite h3. unfold move_up in H0.
     apply (StateRelMonadHoare.Hoare_repeat_break _ 
     (fun '(s1,a,s2) => (s1.(heap)).(vvalid) ==
     (s2.(heap)).(vvalid))) in H0.
Admitted.

Locate Hoare_repeat_break.

Theorem move_up_correctness2: forall (v: Z),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (move_up v)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros v.
  unfold Hoare.
  intros s1 ? s2 [Hvalid [Hlegal Hcomplete]].
  generalize dependent s2.
  (* apply (StateRelMonadHoare.Hoare_repeat_break _ (fun s => s.(heap).(vvalid) v /\
                                                      BinaryTree.legal s.(heap) /\
                                                      is_complete_or_full_bintree s.(heap))). *)
Admitted.

Definition body_insert_node (val: Z) (v: Z):
  StateRelMonad.M state (ContinueOrBreak Z unit) :=
    choice3
      (test_lc_empty v;;
        insert_lc v val;;
        break tt)
      (test_lc_not_empty v;;
        test_rc_empty v;;
          insert_rc v val;;
          break tt)
      (lc <- get_lc v;;
      rc <- get_rc v;;
      choice4
        (test (fun s => is_full_bintree_v s.(heap) lc);;
          continue lc)
        (test (fun s => is_complete_bintree_v s.(heap) lc /\ 
                        is_complete_bintree_v s.(heap) rc /\ 
                        ~ is_complete_bintree_v s.(heap) v);;
          continue rc)
        (test (fun s => is_complete_bintree_v s.(heap) lc /\ 
                        is_full_bintree_v s.(heap) rc);;
          continue rc)
        (test (fun s => is_complete_bintree_v s.(heap) v);;
          continue lc)).
    
Definition insert_node (val: Z): StateRelMonad.M state unit :=
  rt <- get_minimum;;
  repeat_break (body_insert_node val) rt.

(* 插入节点操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

Theorem insert_node_correctness: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (insert_node val)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton val) /\
                    BinaryTree.legal s.(heap) /\
                    (Heap_broken_up s.(heap) val \/ Heap s.(heap)) /\
                    is_complete_or_full_bintree s.(heap)).
Admitted.

Definition insert (val: Z): StateRelMonad.M state unit :=
  choice
    (test_not_empty;;
      insert_node val;;
      move_up val)
    (test_empty;;
      heap_single val).

(* Definition insert (val: Z): StateRelMonad.M state unit :=
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
      heap_single val). *)

(* 插入操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 保持堆性质
4. 保持满二叉树 *)

Theorem insert_correctness: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (insert val)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton val) /\ 
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap) /\ 
                    is_complete_or_full_bintree s.(heap)).
Admitted.


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

(* 下移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，最终恢复堆性质
4. 保持满二叉树 *)

Theorem move_down_correctness1: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap_broken_down s.(heap) v \/ Heap s.(heap)))
        (move_down v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Admitted.

Theorem move_down_correctness2: forall (v: Z),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (move_down v)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Admitted.

Definition body_delete_node (v: Z):
  StateRelMonad.M state (ContinueOrBreak Z Z) :=
    choice3
      (test_lc_empty v;;
        rt <- get_minimum;;
        swap_v_u v rt;;
        delete_leaf rt;;
        break v)
      (test_lc_not_empty v;;
        test_rc_empty v;;
          rt <- get_minimum;;
          lc <- get_lc v;;
          swap_v_u lc rt;;
          delete_leaf rt;;
          break lc)
      (lc <- get_lc v;;
      rc <- get_rc v;;
      choice4
        (test (fun s => is_full_bintree_v s.(heap) lc);;
          continue lc)
        (test (fun s => is_complete_bintree_v s.(heap) lc /\ 
                        is_complete_bintree_v s.(heap) rc /\ 
                        ~ is_complete_bintree_v s.(heap) v);;
          continue lc)
        (test (fun s => is_complete_bintree_v s.(heap) lc /\ 
                        is_full_bintree_v s.(heap) rc);;
          continue rc)
        (test (fun s => is_complete_bintree_v s.(heap) v);;
          continue rc)).
    
Definition delete_node: StateRelMonad.M state Z :=
  rt <- get_minimum;;
  repeat_break body_delete_node rt.

(* 删除节点操作正确性（保证根不是叶子）：
1. 最小值被删除
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

(* to be added *)
(* Theorem delete_node_correctness *)


Definition delete: StateRelMonad.M state Z :=
  rt <- get_minimum;;
  choice
    (test_is_leaf rt;;
      heap_empty;;
      ret rt)
    (test_is_not_leaf rt;;
      v <- delete_node;;
      move_down v;;
      ret rt).

(* Definition delete: StateRelMonad.M state Z :=
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
      ret rt). *)

Definition is_minimum (val: Z) (V: Z -> Prop): Prop :=
  forall x, V x -> x >= val.

(* 删除操作正确性（保证非空的前提下（似乎没用））：
1. 删除的元素是最小值
2. 保持二叉树合法性
3. 保持堆性质 *)

Theorem delete_correctness: forall (V: Z -> Prop), ~ V == ∅ ->
  Hoare (fun s => Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        delete
        (fun val s => (s.(heap).(vvalid) ∪ Sets.singleton val) == V /\
                      is_minimum val V /\
                      BinaryTree.legal s.(heap) /\
                      Heap s.(heap)).
Admitted.