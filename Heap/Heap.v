Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Import SetsNotation
       StateRelMonad
       StateRelMonadOp
       StateRelMonadHoare
       MonadNotation
       Monad.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.
  
(* 上移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，变为堆
4. 保持满二叉树 *)

Fact get_fa_fact: forall (v: Z) P, 
  Hoare P (get_fa v) (fun fa s => P s /\ BinaryTree.step_u s.(heap) v fa).
Proof.
  intros.
  unfold Hoare, get_fa; sets_unfold.
  intros. destruct H0.
  split.
  - rewrite H1. tauto.
  - rewrite H1. tauto.
Qed.

(* 有些条件多余 *)

Fact swap_v_fa_fact1: forall (v fa: Z) (V: Z -> Prop), 
  Hoare
    (fun s => v < fa /\
              ((s.(heap)).(vvalid) v /\
                Abs s.(heap) V /\
                BinaryTree.legal s.(heap) /\
                (Heap s.(heap) \/ Heap_broken_up s.(heap) v)) /\
              BinaryTree.step_u s.(heap) v fa)
    (swap_v_u v fa)
    (fun _ s => (s.(heap)).(vvalid) v /\
                Abs s.(heap) V /\
                BinaryTree.legal s.(heap) /\
                (Heap s.(heap) \/ Heap_broken_up s.(heap) v)).
Admitted.


Lemma L1: forall (x y: Z),
  x < y -> x > y -> False.
Admitted.

Theorem move_up_correctness1: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap s.(heap) \/ Heap_broken_up s.(heap) v))
        (move_up v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Proof.
  intros. revert v.
  unfold move_up.
  apply Hoare_repeat_break.
  intros v.
  unfold body_move_up.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    apply Hoare_ret'.
    intros.
    destruct H as [[? ?] [? [? [? ?]]]].
    split; [apply H2|].
    split; [apply H3|].
    destruct H4; [apply H4|].
    destruct H4.
    destruct up_fa_v_lc_rc as [fa ?].
    assert (exists fa : Z, BinaryTree.step_u s.(heap) v fa).
    { exists fa; apply H4. }
    tauto. 
  - eapply Hoare_bind; [apply get_fa_fact| cbv beta].
    intros fa.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? [? [? ?]]] ?]].
      split; [apply H1|].
      split; [apply H2|].
      destruct H3; [apply H3|].
      destruct H3.
      destruct up_fa_v_lc_rc as [fa' [? [? _]]].
      assert (fa = fa').
      { pose proof (BinaryTree.step_u_unique s.(heap) H2 v fa fa' H4 H3). tauto. }
      subst fa'.
      pose proof (L1 v fa H5 H). tauto.
    + apply Hoare_test_bind.
      eapply Hoare_bind; [apply (swap_v_fa_fact1 v fa V)| cbv beta; intros _].
      apply Hoare_ret'.
      intros.
      destruct H as [? [? [? ?]]].
      split; [apply H|].
      split; [apply H0|].
      split; [apply H1|].
      apply H2.
Qed.

(* 有些条件多余 *)

Fact swap_v_fa_fact2: forall (v fa: Z), 
  Hoare
    (fun s => v < fa /\
              ((s.(heap)).(vvalid) v /\
                BinaryTree.legal s.(heap) /\
                is_complete_or_full_bintree s.(heap)) /\
              BinaryTree.step_u s.(heap) v fa)
    (swap_v_u v fa)
    (fun _ s => (s.(heap)).(vvalid) v /\
                BinaryTree.legal s.(heap) /\
                is_complete_or_full_bintree s.(heap)).
Admitted.

Theorem move_up_correctness2: forall (v: Z),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (move_up v)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros. revert v.
  unfold move_up.
  apply Hoare_repeat_break.
  intros v.
  unfold body_move_up.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    apply Hoare_ret'.
    intros.
    tauto.
  - eapply Hoare_bind; [apply get_fa_fact| cbv beta].
    intros fa.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      tauto.
    + apply Hoare_test_bind.
      eapply Hoare_bind; [apply (swap_v_fa_fact2 v fa)| cbv beta; intros _].
      apply Hoare_ret'.
      intros.
      apply H.
Qed.


(* 插入节点操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

Fact get_minimum_correctness: forall P, 
  Hoare P get_minimum (fun rt s => P s /\ s.(heap).(vvalid) rt).
Proof.
  intros.
  unfold Hoare, get_minimum; sets_unfold.
  intros. destruct H0.
  split.
  - apply H1 in H0.
    destruct H0.
    rewrite H2. tauto.
  - assert (HH: s2 = s1).
    { apply H1 in H0. tauto. }
    subst s2. tauto.
Qed.

Fact insert_lc_fact: forall (v val: Z) (V: Z -> Prop), 
  Hoare
  (fun s : state =>
                    ((s.(heap)).(vvalid) v /\
                    ~ (exists lc : Z, BinaryTree.step_l s.(heap) v lc)) /\
                    ((exists x : Z, (s.(heap)).(vvalid) x) /\
                    Abs s.(heap) V /\
                    ~ (s.(heap)).(vvalid) val /\
                    BinaryTree.legal s.(heap) /\ Heap s.(heap)) /\
                    (s.(heap)).(vvalid) v)
    (insert_lc v val)
    (fun _ s => (s.(heap)).(vvalid) == V ∪ Sets.singleton val /\
                BinaryTree.legal s.(heap) /\
                (Heap_broken_up s.(heap) val \/ Heap s.(heap))).
Admitted.


Fact insert_rc_fact: forall (v val: Z) (V: Z -> Prop), 
  Hoare
  (fun s : state =>
                    ((s.(heap)).(vvalid) v /\
                    ~ (exists rc : Z, BinaryTree.step_r s.(heap) v rc)) /\
                    (exists lc : Z, BinaryTree.step_l s.(heap) v lc) /\
                    ((exists x : Z, (s.(heap)).(vvalid) x) /\
                    Abs s.(heap) V /\
                    ~ (s.(heap)).(vvalid) val /\
                    BinaryTree.legal s.(heap) /\ Heap s.(heap)) /\
                    (s.(heap)).(vvalid) v)
    (insert_rc v val)
    (fun _ s => (s.(heap)).(vvalid) == V ∪ Sets.singleton val /\
                BinaryTree.legal s.(heap) /\
                (Heap_broken_up s.(heap) val \/ Heap s.(heap))).
Admitted.

Fact get_lc_fact: forall (rt: Z) P, 
  Hoare P (get_lc rt) (fun lc s => P s /\ BinaryTree.step_l s.(heap) rt lc).
Admitted.

Fact get_rc_fact: forall (rt: Z) P, 
  Hoare P (get_rc rt) (fun rc s => P s /\ BinaryTree.step_r s.(heap) rt rc).
Admitted.

Theorem insert_node_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => (exists x : Z, (s.(heap)).(vvalid) x) /\
                  Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        (insert_node val)
        (fun _ s =>
                    Abs s.(heap) (V ∪ Sets.singleton val) /\
                    BinaryTree.legal s.(heap) /\
                    (Heap_broken_up s.(heap) val \/ Heap s.(heap))).
Proof.
  intros.
  unfold insert_node.
  eapply Hoare_bind; [apply get_minimum_correctness| cbv beta].
  apply Hoare_repeat_break.
  intros v.
  unfold body_insert_node.
  apply Hoare_choice3.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply insert_lc_fact| cbv beta].
    intros.
    apply Hoare_ret'.
    intros.
    destruct H as [? [? ?]].
    split.
    + unfold Abs.
      rewrite <- H.
      reflexivity.
    + split; [apply H0|].
      apply H1.
  - apply Hoare_test_bind.
    apply Hoare_test_bind.
    eapply Hoare_bind; [apply insert_rc_fact| cbv beta].
    intros.
    apply Hoare_ret'.
    intros.
    destruct H as [? [? ?]].
    unfold Abs.
    rewrite <- H.
    split; [reflexivity|].
    split; [apply H0|].
    apply H1.
  - eapply Hoare_bind; [apply get_lc_fact| cbv beta].
    intros lc.
    eapply Hoare_bind; [apply get_rc_fact| cbv beta].
    intros rc.
    apply Hoare_choice4.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? ?] ?]].
      destruct H0 as [[? [? [? [? ?]]]] ?].
      unfold BinaryTree.step_l in H1.
      destruct H1 as [e [[? ?] ?]].
      tauto.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? ?] ?]].
      destruct H0 as [[? [? [? [? ?]]]] ?].
      unfold BinaryTree.step_r in H2.
      destruct H2 as [e [[? ?] ?]].
      tauto.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? ?] ?]].
      destruct H0 as [[? [? [? [? ?]]]] ?].
      unfold BinaryTree.step_l in H2.
      destruct H2 as [e [[? ?] ?]].
      tauto.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? ?] ?]].
      destruct H0 as [[? [? [? [? ?]]]] ?].
      unfold BinaryTree.step_r in H1.
      destruct H1 as [e [[? ?] ?]].
      tauto.
Qed.


(* 插入操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 保持堆性质
4. 保持满二叉树 *)

Lemma Sets2_proof_sample1: forall A (X Y Z: A -> Prop),
  X ∪ Y ⊆ Z ->
  Y ⊆ Z.
Proof.
  intros.
  Sets_unfold in H.
  Sets_unfold.
  intros a b.
  apply H.
  tauto.
Qed.

Lemma val_in_vvalid: forall (val: Z) (V: Z -> Prop) (s: state),
  (V ∪ Sets.singleton val) == (s.(heap)).(vvalid) ->
  (s.(heap)).(vvalid) val.
Proof.
  intros val V s H.
  apply Sets_equiv_Sets_included in H.
  destruct H.
  apply Sets2_proof_sample1 in H.
  apply H.
  unfold Sets.singleton.
  tauto.
Qed.

Lemma  heap_single_correctness1: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s : state =>
                          ~ (exists x : Z, (s.(heap)).(vvalid) x) /\
                          Abs s.(heap) V /\
                          ~ (s.(heap)).(vvalid) v /\
                          BinaryTree.legal s.(heap) /\
                          Heap s.(heap)) 
        (heap_single v)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton v) /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Admitted.

Lemma helper: forall (val: Z) (V: Z -> Prop),
  Hoare
    (fun s : state =>
    Abs s.(heap) (V ∪ [val]) /\
    BinaryTree.legal s.(heap) /\
    (Heap_broken_up s.(heap) val \/ Heap s.(heap)))
    (move_up val)
    (fun (_ : unit) (s : state) =>
    Abs s.(heap) (V ∪ [val]) /\
    BinaryTree.legal s.(heap) /\ Heap s.(heap)).
Proof.
  intros.
  unfold Hoare.
  intros.
  destruct H as [? [? ?]].
  assert ((s1.(heap)).(vvalid) val).
Admitted.


Theorem insert_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        (insert val)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton val) /\ 
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Proof.
  intros val V.
  unfold insert.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply insert_node_correctness1| cbv beta].
    intros.
    apply move_up_correctness1.
  - apply Hoare_test_bind.
    apply heap_single_correctness.
Qed.  


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


(* 删除节点操作正确性（保证根不是叶子）：
1. 最小值被删除
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

(* to be added *)
(* Theorem delete_node_correctness *)



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
Proof.
  intros.
  unfold delete.
  eapply Hoare_bind; [apply get_minimum_correctness| cbv beta].
  intros rt.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    
Admitted.