Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.MoveUp.
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
Admitted.

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

Lemma move_up_helper1: forall (val: Z) (V: Z -> Prop),
  Hoare
    (fun s : state => Abs s.(heap) (V ∪ [val]) /\
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
  { unfold Abs in H.
    apply val_in_vvalid in H.
    tauto. }
  assert (H_all : s1.(heap).(vvalid) val /\
                  Abs s1.(heap) (V ∪ Sets.singleton val) /\
                  BinaryTree.legal s1.(heap) /\
                  (Heap s1.(heap) \/ Heap_broken_up s1.(heap) val)).
  { tauto. }
  clear H H1 H2 H3.
  revert val V s1 a s2 H_all H0.
  change (forall v V, Hoare (fun s => s.(heap).(vvalid) v /\
                                      Abs s.(heap) (V ∪ Sets.singleton v) /\
                                      BinaryTree.legal s.(heap) /\
                                      (Heap s.(heap) \/ Heap_broken_up s.(heap) v))
                            (move_up v)
                            (fun _ s => Abs s.(heap) (V ∪ Sets.singleton v) /\
                                        BinaryTree.legal s.(heap) /\
                                        Heap s.(heap))).
  intros.
  apply move_up_correctness1 with (V := V ∪ Sets.singleton v).
Qed.

Lemma move_up_helper2: forall (val: Z) (V: Z -> Prop),
  Hoare
    (fun s : state => Abs s.(heap) (V ∪ [val]) /\
                      BinaryTree.legal s.(heap) /\
                      is_complete_or_full_bintree s.(heap))
    (move_up val)
    (fun (_ : unit) (s : state) => is_complete_or_full_bintree s.(heap)).
Proof.
  intros.
  unfold Hoare.
  intros.
  destruct H as [? [? ?]].
  assert ((s1.(heap)).(vvalid) val).
  { unfold Abs in H.
    apply val_in_vvalid in H.
    tauto. }
  assert (H_all : s1.(heap).(vvalid) val /\
                  BinaryTree.legal s1.(heap) /\
                  (is_complete_or_full_bintree s1.(heap))).
  { tauto. }
  clear H H1 H2 H3.
  revert val V s1 a s2 H_all H0.
  change (forall (v: Z) (V: Z -> Prop), Hoare (fun s => s.(heap).(vvalid) v /\
                                      BinaryTree.legal s.(heap) /\
                                      is_complete_or_full_bintree s.(heap))
                            (move_up v)
                            (fun _ s => is_complete_or_full_bintree s.(heap))).
  intros.
  apply move_up_correctness2.
Qed.


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
