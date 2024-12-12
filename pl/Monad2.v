Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Import SetsNotation
       KleeneFix Sets_CPO
       Monad
       MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Module SetMonadExamples4.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       ListNotations.

(** * 程序验证案例一：归并排序中的归并步骤 *)

Definition body_merge:
  list Z * list Z * list Z ->
  SetMonad.M (ContinueOrBreak (list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3) =>
    match l1, l2 with 
    | nil, _ => break (l3 ++ l2)
    | _, nil => break (l3 ++ l1)
    | x :: l1', y :: l2' =>
        choice
          (test (x <= y);; continue (l1', l2, l3 ++ x :: nil))
          (test (y <= x);; continue (l1, l2', l3 ++ y :: nil))
  end.

Definition merge l l0 :=
  repeat_break body_merge (l, l0, nil).

Fixpoint incr_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ incr_aux l0 y
  end.

Definition incr (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => incr_aux l0 x
  end.

Theorem merge_perm:
  forall l1 l2,
    Hoare (merge l1 l2) (Permutation (l1 ++ l2)).
Proof.
  intros.
  unfold merge.
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') =>
              Permutation (l1 ++ l2) (l1' ++ l2' ++ l3'))).
  2: {
    rewrite app_nil_r.
    reflexivity.
  }
  intros [[l1' l2'] l3'] ?.
  unfold body_merge.
  destruct l1' as [ | x l1']; [| destruct l2' as [| y l2']].
  + apply Hoare_ret.
    rewrite H; simpl.
    apply Permutation_app_comm.
  + apply Hoare_ret.
    rewrite H.
    rewrite Permutation_app_comm.
    reflexivity.
  + apply Hoare_choice; apply Hoare_test_bind; intros.
    - apply Hoare_ret.
      rewrite H.
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [x]).
      reflexivity.
    - apply Hoare_ret.
      rewrite H.
      apply Permutation_app; [reflexivity |].
      rewrite ! app_assoc.
      rewrite (Permutation_app_comm _ [y]).
      reflexivity.
Qed.

Lemma incr_app_cons: forall l1 x l2,
  incr (l1 ++ [x]) ->
  incr (x :: l2) ->
  incr (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv1: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma incr_app_cons_inv2: forall l1 x l2,
  incr (l1 ++ x :: l2) ->
  incr (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Theorem merge_incr:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (merge l1 l2) incr.
Proof.
  intros.
  unfold merge.
  apply (Hoare_repeat_break _
           (fun '(l1', l2', l3') => 
              incr (l3' ++ l1') /\
              incr (l3' ++ l2'))).
  2: {
    tauto.
  }
  clear l1 l2 H H0.
  intros [[l1 l2] l3] [? ?].
  destruct l1 as [ | x l1]; [| destruct l2 as [| y l2]].
  + apply Hoare_ret; tauto.
  + apply Hoare_ret; tauto.
  + apply Hoare_choice; apply Hoare_test_bind; intros.
    - apply Hoare_ret.
      split.
      * rewrite <- app_assoc.
        exact H.
      * rewrite <- app_assoc.
        simpl.
        apply incr_app_cons_inv1 in H.
        apply incr_app_cons_inv2 in H0.
        apply incr_app_cons; simpl in *; tauto.
    - apply Hoare_ret.
      split.
      * rewrite <- app_assoc.
        simpl.
        apply incr_app_cons_inv1 in H0.
        apply incr_app_cons_inv2 in H.
        apply incr_app_cons; simpl in *; tauto.
      * rewrite <- app_assoc.
        exact H0.
Qed.

Theorem functional_correctness_merge:
  forall l1 l2,
    incr l1 ->
    incr l2 ->
    Hoare (merge l1 l2)
          (fun l3 => Permutation (l1 ++ l2) l3 /\ incr l3).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply merge_perm.
  + apply merge_incr; tauto.
Qed.

(** * 程序验证案例二：归并排序 *)

Definition ext_sort (l: list Z): SetMonad.M (list Z) :=
  fun l' => Permutation l l' /\ incr l'.

Definition ext_split (l: list Z): SetMonad.M (list Z * list Z) :=
  fun '(l0, l1) => Permutation l (l0 ++ l1).

Definition gmergesort_f (W: list Z -> SetMonad.M (list Z)):
  list Z -> SetMonad.M (list Z) :=
  fun x => 
    choice
      (ext_sort x)
      (test (length x >= 2)%nat;;
       '(p1, q1) <- ext_split x ;; 
       p2 <- W (p1) ;; 
       q2 <- W (q1) ;; 
       merge p2 q2).

Definition gmergesort := Kleene_LFix gmergesort_f.
Lemma ext_sort_fact:
  forall l,
    Hoare (ext_sort l) (fun l0 => Permutation l l0 /\ incr l0).
Proof.
  unfold Hoare, ext_sort; sets_unfold.
  intros.
  tauto.
Qed.

Lemma ext_split_fact:
  forall l,
    Hoare (ext_split l) (fun '(l1, l2) => Permutation l (l1 ++ l2)).
Proof.
  unfold Hoare, ext_split; sets_unfold.
  intros.
  tauto.
Qed.

Theorem functional_correctness_mergesort:
  forall l,
    Hoare (gmergesort l) (fun l0 => Permutation l l0 /\ incr l0).
Proof.
  intros.
  unfold Hoare, gmergesort, Kleene_LFix; unfold_CPO_defs.
  intros.
  destruct H as [n ?].
  revert l a H.
  change (forall l,
          Hoare (Nat.iter n gmergesort_f ∅ l)
                (fun l0 => Permutation l l0 /\ incr l0)).
  induction n; simpl; intros.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold gmergesort_f at 1.
    apply Hoare_choice; [apply ext_sort_fact |].
    apply Hoare_test_bind.
    intros.
    eapply Hoare_bind; [apply ext_split_fact |].
    intros [l1 l2] ?.
    eapply Hoare_bind; [apply IHn |].
    intros l1' [? ?].
    eapply Hoare_bind; [apply IHn |].
    intros l2' [? ?].
    eapply Hoare_conseq; [| apply functional_correctness_merge; tauto].
    intros l3 [? ?].
    rewrite <- H5 at 1.
    rewrite <- H1, <- H3.
    tauto.
Qed.

End SetMonadExamples4.

Module SetMonadOperator2.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       SetMonadProperties0
       SetMonadHoare.

Arguments bind: simpl never.
Arguments ret: simpl never.

Fixpoint list_iter
           {A B: Type}
           (f: A -> B -> SetMonad.M B)
           (l: list A)
           (b: B):
  SetMonad.M B :=
  match l with
  | nil => ret b
  | a :: l0 => b0 <- f a b;; list_iter f l0 b0
  end.

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0)).
Proof.
  (** 此处的证明需要对list使用反向归纳法。*)
  intros.
  pattern l.
  refine (rev_ind _ _ _ l); simpl.
  + apply Hoare_ret.
    apply H0.
  + intros.
    (** 此时需要将_[list_iter f (l0 ++ [x]) b]_变换为
        _[b0 <- list_iter f l0 b;; f x b]_。
        我们先来证明这一条引理。*)
Abort.

(************)
(** 习题：  *)
(************)

Lemma list_iter_app:
  forall {A B: Type}
         (f: A -> B -> SetMonad.M B)
         (l1 l2: list A)
         (b: B),
    b0 <- list_iter f l1 b;; list_iter f l2 b0 ==
    list_iter f (l1 ++ l2) b.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

#[export] Instance Hoare_congr {A: Type}:
  Proper (Sets.equiv ==> eq ==> iff) (@Hoare A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem Hoare_list_iter {A B: Type}:
  forall (f: A -> B -> SetMonad.M B)
         (P: list A -> B -> Prop),
    (forall b l a,
       P l b ->
       Hoare (f a b) (fun b0 => P (l ++ a :: nil) b0)) ->
    (forall b l, P nil b -> Hoare (list_iter f l b) (fun b0 => P l b0)).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Import SetMonadExamples4.


Definition insertion (x: Z) (l: list Z): SetMonad.M (list Z) :=
  fun l' => exists l1 l2,
    l = l1 ++ l2 /\ l' = l1 ++ x :: l2 /\ incr l'.

Definition ins_sort (l: list Z) :=
  list_iter insertion l nil.

(************)
(** 习题：  *)
(************)

Theorem ins_sort_perm:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem ins_sort_incr:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => incr l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem functional_correctness_ins_sort:
  forall L,
    Hoare
      (ins_sort L)
      (fun l => Permutation L l /\ incr l).
Proof.
  intros.
  apply Hoare_conjunct.
  + apply ins_sort_perm.
  + apply ins_sort_incr.
Qed.

End SetMonadOperator2.
