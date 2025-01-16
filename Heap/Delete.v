Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Psatz.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.MoveDown.
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

(* 删除节点操作正确性（保证根不是叶子）：
1. 最小值被删除
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

Theorem ext_delete_node_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => (exists lc : Z, BinaryTree.step_l s.(heap) val lc \/
                    (exists rc : Z, BinaryTree.step_r s.(heap) val rc)) /\
                  Abs s.(heap) V /\ 
                  BinaryTree.legal s.(heap) /\ 
                  Heap s.(heap) /\
                  is_minimum val V)
        (ext_delete_node val)
        (fun v s => s.(heap).(vvalid) v /\
                    (s.(heap).(vvalid) ∪ Sets.singleton val) == V /\
                    is_minimum val V /\
                    BinaryTree.legal s.(heap) /\
                    (Heap_broken_down s.(heap) v \/ Heap s.(heap))).
Proof.
  intros.
  unfold ext_delete_node.
  unfold Hoare, Abs; sets_unfold.
  intros.
  destruct H as [? [? [? [? ?]]]].
  destruct H0 as [? [? [? [? [? ?]]]]].
  - split; [tauto| split; [| split; [| split]]].
    + intros.
      rewrite H1.
      apply H6.
    + tauto.
    + tauto.
    + tauto.
Qed.

Theorem ext_delete_node_correctness2: forall (val: Z),
  Hoare (fun s => (exists lc : Z, BinaryTree.step_l s.(heap) val lc \/
                    (exists rc : Z, BinaryTree.step_r s.(heap) val rc)) /\
                  is_complete_or_full_bintree s.(heap))
        (ext_delete_node val)
        (fun v s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros.
  unfold ext_delete_node.
  unfold Hoare, Abs; sets_unfold.
  intros.
  destruct H as [? ?].
  destruct H0 as [? [? [? ?]]].
  tauto.
Qed.


Theorem delete_iso_node_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s: state =>
                        ((s.(heap)).(vvalid) val /\
                        ~ (exists lc : Z, BinaryTree.step_l s.(heap) val lc) /\
                        ~ (exists rc : Z, BinaryTree.step_r s.(heap) val rc)) /\
                        Abs s.(heap) V /\ 
                        BinaryTree.legal s.(heap) /\ 
                        Heap s.(heap) /\
                        is_minimum val V)
        (ext_delete_iso_node val)
        (fun _ s => (s.(heap).(vvalid) ∪ Sets.singleton val) == V /\
                    is_minimum val V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Proof.
  intros.
  unfold ext_delete_iso_node.
  unfold Hoare, Abs; sets_unfold.
  intros.
  destruct H as [[? [? ?]] [? [? [? ?]]]].
  destruct H0 as [? [? [? ?]]].
  split; [| split; [| split]].
  - intros.
    rewrite H3.
    apply H7.
  - tauto.
  - tauto.
  - tauto.
Qed.

Theorem delete_iso_node_correctness2: forall (val: Z),
  Hoare (fun s: state =>
                        ((s.(heap)).(vvalid) val /\
                        ~ (exists lc : Z, BinaryTree.step_l s.(heap) val lc) /\
                        ~ (exists rc : Z, BinaryTree.step_r s.(heap) val rc)) /\
                        is_complete_or_full_bintree s.(heap))
        (ext_delete_iso_node val)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros.
  unfold ext_delete_iso_node.
  unfold Hoare, Abs; sets_unfold.
  intros.
  destruct H as [? ?].
  destruct H0 as [? [? [? ?]]].
  tauto.
Qed.

(* 删除操作正确性（保证非空的前提下（似乎没用））：
1. 删除的元素是最小值
2. 保持二叉树合法性
3. 保持堆性质 *)

Theorem delete_correctness1: forall (V: Z -> Prop), ~ V == ∅ ->
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
  eapply Hoare_bind; [apply get_min_correctness1| cbv beta].
  intros val.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply delete_iso_node_correctness1| cbv beta].
    intros.
    apply Hoare_ret'.
    intros.
    destruct H0 as [? [? [? ?]]].
    split; [| split; [tauto | tauto]].
    tauto.
  - apply Hoare_test_bind.
    revert val.
    intros.
    eapply Hoare_bind; [apply ext_delete_node_correctness1| cbv beta].
    intros v.
    eapply Hoare_bind; [apply move_down_helper1| cbv beta].
    intros.
    apply Hoare_ret'.
    intros.
    destruct H0 as [? [? [? ?]]].
    split; [| split; [tauto | tauto]].
    tauto.
Qed.

Theorem delete_correctness2: forall (V: Z -> Prop),
  Hoare (fun s => is_complete_or_full_bintree s.(heap))
        delete
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros.
  unfold delete.
  eapply Hoare_bind; [apply get_min_correctness2| cbv beta].
  intros val.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply delete_iso_node_correctness2| cbv beta].
    intros.
    apply Hoare_ret'.
    intros.
    tauto.
  - apply Hoare_test_bind.
    eapply Hoare_bind; [apply ext_delete_node_correctness2| cbv beta].
    intros v.
    eapply Hoare_bind; [apply move_down_correctness2| cbv beta].
    intros.
    apply Hoare_ret'.
    intros.
    tauto.
Qed.
  