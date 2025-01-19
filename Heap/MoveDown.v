Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.Swapvu.
Import SetsNotation
       StateRelMonad
       StateRelMonadOp
       StateRelMonadHoare
       MonadNotation
       Monad.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Fact get_lc_fact: forall (v: Z) P, 
  Hoare P (get_lc v) (fun lc s => P s /\ BinaryTree.step_l s.(heap) v lc).
Proof.
  intros.
  unfold Hoare, get_lc; sets_unfold.
  intros. destruct H0.
  split.
  - rewrite H1. tauto.
  - rewrite H1. tauto.
Qed.

Fact get_rc_fact: forall (v: Z) P, 
  Hoare P (get_rc v) (fun rc s => P s /\ BinaryTree.step_r s.(heap) v rc).
Proof.
  intros.
  unfold Hoare, get_rc; sets_unfold.
  intros. destruct H0.
  split.
  - rewrite H1. tauto.
  - rewrite H1. tauto.
Qed.

Lemma L1: forall (x y: Z),
  x < y -> x > y -> False.
Proof.
  intros.
  lia.
Qed.

Lemma L2: forall (x y z: Z),
  x < y -> y < z -> x < z.
Proof.
  intros.
  lia.
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
        { pose proof BinaryTree.legal2legal' _ _ s.(heap) H4.
          pose proof BinaryTree.step_r_unique s.(heap) H8 v rc rc' H6 H5. tauto. }
        subst rc'.
        pose proof (L1 v rc H H7). tauto.
    + apply Hoare_test_bind.
      eapply Hoare_bind; [apply swap_v_u_helper1| cbv beta].
      intros.
      apply Hoare_ret'.
      intros.
      tauto.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply get_lc_fact| cbv beta].
    intros lc.
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
      * destruct H5 as [lc' [? ?]].
        assert (lc = lc').
        { pose proof BinaryTree.legal2legal' _ _ s.(heap) H4.
          pose proof BinaryTree.step_l_unique s.(heap) H8 v lc lc' H6 H5. tauto. }
        subst lc'.
        pose proof (L1 v lc H H7). tauto.
      * destruct H5 as [rc [? ?]].
        assert (exists rc : Z, BinaryTree.step_r s.(heap) v rc).
        { exists rc; apply H5. }
        tauto.
    + apply Hoare_test_bind.
      eapply Hoare_bind; [apply swap_v_u_helper2| cbv beta].
      intros.
      apply Hoare_ret'.
      intros.
      tauto.
  - eapply Hoare_bind; [apply get_lc_fact| cbv beta].
    intros lc.
    eapply Hoare_bind; [apply get_rc_fact| cbv beta].
    intros rc.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_choice.
      * apply Hoare_test_bind.
        apply Hoare_ret'.
        intros.
        destruct H as [? [? [[[? [? [? ?]]] ?] ?]]].
        split; [apply H2|].
        split; [apply H3|].
        destruct H4; [| tauto].
        destruct H4.
        destruct down_v_lc_rc.
        -- destruct H4 as [lc' [? ?]].
           assert (lc = lc').
           { pose proof BinaryTree.legal2legal' _ _ s.(heap) H3. 
             pose proof BinaryTree.step_l_unique s.(heap) H8 v lc lc' H5 H4. tauto. }
           subst lc'.
           pose proof (L1 v lc H H7). tauto.
        -- destruct H4 as [rc' [? ?]].
           assert (rc = rc').
           { pose proof BinaryTree.legal2legal' _ _ s.(heap) H3.
             pose proof BinaryTree.step_r_unique s.(heap) H8 v rc rc' H6 H4. tauto. }
           subst rc'.
           assert (v < rc).
           {pose proof (L2 v lc rc H H0). tauto. }
           pose proof (L1 v rc H8 H7). tauto.
      * apply Hoare_test_bind.
        eapply Hoare_bind; [apply swap_v_u_helper3| cbv beta].
        intros.
        apply Hoare_ret'.
        intros.
        tauto.
    + apply Hoare_test_bind.
      apply Hoare_choice.
      * apply Hoare_test_bind.
        apply Hoare_ret'.
        intros.
        destruct H as [? [? [[[? [? [? ?]]] ?] ?]]].
        split; [apply H2|].
        split; [apply H3|].
        destruct H4; [| tauto].
        destruct H4.
        destruct down_v_lc_rc.
        -- destruct H4 as [lc' [? ?]].
           assert (lc = lc').
           { pose proof BinaryTree.legal2legal' _ _ s.(heap) H3.
             pose proof BinaryTree.step_l_unique s.(heap) H8 v lc lc' H5 H4. tauto. }
           subst lc'.
           assert (rc < lc).
           {lia. }
           assert (v < lc).
           {pose proof (L2 v rc lc H H8). tauto. }
           pose proof (L1 v lc H9 H7). tauto.
        -- destruct H4 as [rc' [? ?]].
           assert (rc = rc').
           { pose proof BinaryTree.legal2legal' _ _ s.(heap) H3.
            pose proof BinaryTree.step_r_unique s.(heap) H8 v rc rc' H6 H4. tauto. }
           subst rc'.
           pose proof (L1 v rc H H7). tauto.
      * apply Hoare_test_bind.
        eapply Hoare_bind; [apply swap_v_u_helper4| cbv beta].
        intros.
        apply Hoare_ret'.
        intros.
        tauto.
Qed.


(* 条件改动时Delete中相应改动 *)
Theorem move_down_correctness2: forall (v: Z),
  Hoare (fun s => is_complete_or_full_bintree s.(heap))
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
    destruct H as [? ?].
    tauto.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply get_rc_fact| cbv beta].
    intros rc.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? ?]]].
      tauto.
    + apply Hoare_test_bind.

Admitted.
