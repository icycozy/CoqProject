Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.Swapvu.
Require Import Classical.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Psatz.
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
      { pose proof BinaryTree.legal2legal' _ _ s.(heap) H2.
         pose proof (BinaryTree.step_u_unique s.(heap) H6 v fa fa' H4 H3). tauto. }
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