Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.MoveUp.
Require Import HEAP.Helpers.
Import SetsNotation
       StateRelMonad
       StateRelMonadOp
       StateRelMonadHoare
       MonadNotation
       Monad.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

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
Proof.
  intros. revert v.
  unfold move_down.
  apply Hoare_repeat_break.
  intros v.
  unfold body_move_down.
  apply Hoare_choice4.
  - apply Hoare_test_bind.
    apply Hoare_ret'.
    intros.
    destruct H as [[? [? ?]] [? [? [? ?]]]].
    split; [apply H3|].
    split; [apply H4|].
    destruct H5; [| tauto].
    destruct H5.
    destruct down_v_lc_rc.
    + destruct H5 as [lc ?].
      assert (exists lc : Z, BinaryTree.step_l s.(heap) v lc).
      { exists lc; apply H5. }
      tauto.
    + destruct H5 as [rc ?].
      assert (exists rc : Z, BinaryTree.step_r s.(heap) v rc).
      { exists rc; apply H5. }
      tauto.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply get_rc_fact| cbv beta].
    intros rc.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[[? ?] [? [? [? ?]]]] ?]].
      split; [apply H3|].
      split; [apply H4|].
      destruct H5; [| tauto].
      destruct H5.
      destruct down_v_lc_rc.
      * destruct H5 as [lc [? ?]].
        assert (exists lc : Z, BinaryTree.step_l s.(heap) v lc).
        { exists lc; apply H5. }
        tauto.
      * destruct H5 as [rc' [? ?]].
        assert (rc = rc').
        { pose proof BinaryTree.step_r_unique s.(heap) H4 v rc rc' H6 H5. tauto. }
        subst rc'.
        pose proof (L1 v rc H H7). tauto.
    + apply Hoare_test_bind.
    

Admitted.

Theorem move_down_correctness2: forall (v: Z),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (move_down v)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  unfold move_down.
  apply Hoare_repeat_break.
  intros v.
  unfold body_move_down.
  apply Hoare_choice4.
  - apply Hoare_test_bind.
    apply Hoare_ret'.
    intros.
    destruct H as [? [? [? ?]]].
    tauto.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply get_rc_fact| cbv beta].
    intros rc.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? [? [? ?]]] ?]].
      tauto.
    + apply Hoare_test_bind.

Admitted.
