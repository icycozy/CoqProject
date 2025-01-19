Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import Classical.
Require Import Coq.Setoids.Setoid.
Require Import Coq.micromega.Psatz.
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


Fact remove_go_left_edge_fact1: forall (v lc: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V)
        (remove_go_left_edge v lc)
        (fun _ s => Abs s.(heap) V).
Proof.
  intros.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros. 
  destruct H0 as [? ?].
  assert ((s2.(heap)).(vvalid) == (s1.(heap)).(vvalid)).
  { 
    sets_unfold.
    tauto.
  }
  unfold Abs in H.
  unfold Abs.
  rewrite H.
  rewrite <- H2.
  reflexivity.
Qed.

Fact remove_go_right_edge_fact1: forall (v rc: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V)
        (remove_go_right_edge v rc)
        (fun _ s => Abs s.(heap) V).
Proof.
  intros.
  unfold Hoare, remove_go_right_edge; sets_unfold.
  intros. 
  destruct H0 as [? ?].
  assert ((s2.(heap)).(vvalid) == (s1.(heap)).(vvalid)).
  { 
    sets_unfold.
    tauto.
  }
  unfold Abs in H.
  unfold Abs.
  rewrite H.
  rewrite <- H2.
  reflexivity.
Qed.

Fact remove_go_left_edge'_fact1:
  forall (v: Z) (a: ExistOrEmpty) (V: Z -> Prop),
    Hoare (fun s => Abs s.(heap) V)
          (remove_go_left_edge' v a)
          (fun _ s => Abs s.(heap) V).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - unfold remove_go_left_edge, Hoare; sets_unfold.
    intros.
    destruct H0 as [? ?].
    assert ((s2.(heap)).(vvalid) == (s1.(heap)).(vvalid)).
    { 
      sets_unfold.
      tauto.
    }
    unfold Abs in H.
    unfold Abs.
    rewrite H.
    rewrite <- H2.
    reflexivity.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact1:
  forall (v: Z) (a: ExistOrEmpty) (V: Z -> Prop),
    Hoare (fun s => Abs s.(heap) V)
          (remove_go_right_edge' v a)
          (fun _ s => Abs s.(heap) V).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - unfold remove_go_right_edge, Hoare; sets_unfold.
    intros.
    destruct H0 as [? ?].
    assert ((s2.(heap)).(vvalid) == (s1.(heap)).(vvalid)).
    { 
      sets_unfold.
      tauto.
    }
    unfold Abs in H.
    unfold Abs.
    rewrite H.
    rewrite <- H2.
    reflexivity.
  - unfold Hoare; sets_unfold.
  intros.
  subst s2.
    tauto.
Qed.


(*********************************************************)
(*********************************************************)

Fact remove_go_left_edge_fact2: forall (v lc: Z),
  Hoare (fun s => BinaryTree.legal s.(heap))
        (remove_go_left_edge v lc)
        (fun _ s => BinaryTree.legal s.(heap) /\ 
                    ~ (exists x, BinaryTree.step_l s.(heap) v x) /\ 
                    ~ (exists x, BinaryTree.step_u s.(heap) lc x)).
Proof.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_l.
  unfold not.
  split.
  - intros.
    split.
    + intros.
      pose proof (classic (e1 = x)).
      destruct H8.
      * rewrite H8.
        pose proof (classic (e2 = x)).
        destruct H9.
        ** rewrite H9.
            tauto.
        ** rewrite H8 in H6.
        destruct H6.
        destruct H6.
        tauto.
      * pose proof (classic (e2 = x)).
        destruct H9.
        ** rewrite H9 in H7.
           destruct H7.
           destruct H7.
           tauto.
        ** pose proof H5 e1 H8 x0 y1.
           pose proof H5 e2 H9 x0 y2.
           destruct H10.
           destruct H10.
           destruct H6.
           apply H10 in H6.
           rewrite H12 in H14.
            (*H14 H6  *)
           destruct H11.
           destruct H11.
           destruct H7.
           rewrite H15 in H17.
           apply H11 in H7.
           (* H17 H7 *)
           destruct H.
           pose proof edge_l_unique x0 y1 y2 e1.
           (* 现在利用H14 H6 H17 H7应当满足H中条件，推出目标 *)
           admit.
    + intros.
      pose proof (classic (e1 = x)).
      destruct H8.
      * rewrite H8.
        pose proof (classic (e2 = x)).
        destruct H9.
        ** rewrite H9.
            tauto.
        ** rewrite H8 in H6.
        destruct H6.
        destruct H6.
        tauto.
      * pose proof (classic (e2 = x)).
        destruct H9.
        ** rewrite H9 in H7.
          destruct H7.
          destruct H7.
          tauto.
        ** pose proof H5 e1 H8 x0 y1.
          pose proof H5 e2 H9 x0 y2.
          destruct H10.
          destruct H10.
          destruct H6.
          apply H10 in H6.
          unfold BinaryTree.go_right in H14.
          rewrite H12 in H14.
          (*H14 H6  *)
          destruct H11.
          destruct H11.
          destruct H7.
          unfold BinaryTree.go_right in H17.
          rewrite H15 in H17.
          apply H11 in H7.
          (* H17 H7 *)
          destruct H.
          pose proof edge_r_unique x0 y1 y2 e1.
          admit.
    + intros.
      pose proof (classic (e1 = x)).
      destruct H8.
      * rewrite H8.
        pose proof (classic (e2 = x)).
        destruct H9.
        ** rewrite H9.
            tauto.
        ** rewrite H8 in H6.
        destruct H6.
        tauto.
      * pose proof (classic (e2 = x)).
        destruct H9.
        ** rewrite H9 in H7.
          destruct H7.
          tauto.
        ** pose proof H5 e1 H8 y1 x0.
          pose proof H5 e2 H9 y2 x0.
          destruct H10.
          destruct H10.
          apply H10 in H6.
          (* H6  *)
          destruct H11.
          destruct H11.
          apply H11 in H7.
          (* H7 *)
          destruct H.
          pose proof edge_u_unique x0 y1 y2 e1.
        admit.
  - split.
    + intros.
      destruct H6.
      destruct H6.
      pose proof (classic(x1 = x)).
      destruct H7.
      * rewrite H7 in H6.
        destruct H6.
        destruct H6.
        tauto.
      * pose proof H5 x1 H7. 
        destruct H6.
        pose proof H8 v x0.
        destruct H10.
        rewrite H11 in H9.
        apply H10 in H6.
        destruct H.
        pose proof edge_l_unique v lc x0 x.
        assert( BinaryTree.step_aux s1.(heap) x v lc /\ (s1.(heap)).(go_left) x) as H13.
          tauto.
        assert( BinaryTree.step_aux s1.(heap) x1 v x0 /\ (s1.(heap)).(go_left) x1) as H12.
          tauto.
        (* 此时取H中e2为x1，可推出x1=x,与条件中的x1<>x得到矛盾 *)
        admit.
    + intros.
      destruct H6.
      destruct H6.
      pose proof (classic(x1 = x)).
      destruct H7. 
      * rewrite H7 in H6.
        destruct H6.
        tauto.
      * pose proof H5 x1 H7.
        pose proof H8 x0 lc.
        destruct H9.
        destruct H9.
        apply H9 in H6.
        destruct H.
        pose proof edge_u_unique lc v x0 x.
        (* 此时取H中e2为x1，可推出x1=x,与条件中的x1<>x得到矛盾 *)
        admit.
Admitted.


Fact remove_go_right_edge_fact2: forall (v rc: Z),
  Hoare (fun s => BinaryTree.legal s.(heap))
        (remove_go_right_edge v rc)
        (fun _ s => BinaryTree.legal s.(heap) /\ 
                    ~ (exists x, BinaryTree.step_r s.(heap) v x) /\ 
                    ~ (exists x, BinaryTree.step_u s.(heap) rc x)).
Admitted.

(*********************************************************)
(*********************************************************)

Fact remove_go_left_edge'_fact2:
  forall (v: Z) (a: ExistOrEmpty),
    Hoare (fun s => BinaryTree.legal s.(heap))
          (remove_go_left_edge' v a)
          (fun _ s => BinaryTree.legal s.(heap) /\ 
                      ~ (exists x, BinaryTree.step_l s.(heap) v x) /\
                      match a with
                      | by_exist lc => ~ (exists x, BinaryTree.step_u s.(heap) lc x)
                      | by_empty => True
                      end).
Admitted.

Fact remove_go_right_edge'_fact2:
  forall (v: Z) (a: ExistOrEmpty),
    Hoare (fun s => BinaryTree.legal s.(heap))
          (remove_go_right_edge' v a)
          (fun _ s => BinaryTree.legal s.(heap) /\ 
                      ~ (exists x, BinaryTree.step_r s.(heap) v x) /\
                      match a with
                      | by_exist rc => ~ (exists x, BinaryTree.step_u s.(heap) rc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  destruct a.
  - apply remove_go_right_edge_fact2.
Admitted.

(*********************************************************)
(*********************************************************)

Fact remove_go_left_edge_fact3_l:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_l s.(heap) u x)
          (remove_go_left_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Proof.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_l.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6. destruct H6.
     tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_l in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e u x /\ (s1.(heap)).(go_left) e).
  * exists x0, e0.
    pose proof H8 u x0.
    destruct H6.
    destruct H9.
    rewrite <- H11.
    tauto.
  *tauto.
Qed.

Fact remove_go_left_edge_fact3_r:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_r s.(heap) u x)
          (remove_go_left_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Proof.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_r.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6. destruct H6.
     tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_r in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e u x /\ (s1.(heap)).(go_right) e).
  * exists x0, e0.
    pose proof H8 u x0.
    destruct H6.
    destruct H9.
    unfold BinaryTree.go_right.
    unfold BinaryTree.go_right in H10.
    rewrite <- H11.
    tauto.
  *tauto.
Qed.

Fact remove_go_left_edge_fact3_u:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_u s.(heap) u x)
          (remove_go_left_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Proof.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_u.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6.
     tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_u in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e x u).
  * exists x0, e0.
    pose proof H8 x0 u.
    tauto.
  *tauto.
Qed.

Fact remove_go_right_edge_fact3_l:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_l s.(heap) u x)
          (remove_go_right_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Proof.
  unfold Hoare, remove_go_right_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_l.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6. destruct H6.
    tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_l in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e u x /\ (s1.(heap)).(go_left) e).
  * exists x0, e0.
    pose proof H8 u x0.
    destruct H6.
    destruct H9.    
    unfold BinaryTree.go_right in H11.
Admitted.


Fact remove_go_right_edge_fact3_r: 
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_r s.(heap) u x)
          (remove_go_right_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Proof.
unfold Hoare, remove_go_left_edge; sets_unfold.
intros.
destruct H0 as [? [? [? [? [? [? ?]]]]]].
unfold BinaryTree.step_l.
unfold not.
intros.
destruct H6.
destruct H6 as [e0 ?].
pose proof (classic (e0 = x)).
destruct H7.
+ subst e0.
  destruct H6. destruct H6.
   tauto.
+ pose proof H5 e0 H7.
  unfold BinaryTree.step_l in H.
assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e u x /\ (s1.(heap)).(go_right) e).
* exists x0, e0.
  pose proof H8 u x0.
  destruct H6.
  destruct H9.
  rewrite <- H11.
  tauto.
*tauto.
Qed.
  

Fact remove_go_right_edge_fact3_u:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_u s.(heap) u x)
          (remove_go_right_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Proof.
  unfold Hoare, remove_go_right_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_u.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6.
     tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_u in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e x u).
  * exists x0, e0.
    pose proof H8 x0 u.
    tauto.
  *tauto.
Qed.

(*********************************************************)
(*********************************************************)

Fact remove_go_left_edge'_fact3_l:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_l s.(heap) u x)
          (remove_go_left_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Proof.
  intros.
  destruct a.
  - simpl.
    apply remove_go_left_edge_fact3_l.
  - simpl.
    unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.


Fact remove_go_left_edge'_fact3_r:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_r s.(heap) u x)
          (remove_go_left_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Proof.
  intros.
  destruct a.
  - simpl.
    apply remove_go_left_edge_fact3_r.
  - simpl.
    unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_left_edge'_fact3_u:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_u s.(heap) u x)
          (remove_go_left_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Proof.
  intros.
  destruct a.
  - simpl.
    apply remove_go_left_edge_fact3_u.
  - simpl.
    unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact3_l:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_l s.(heap) u x)
          (remove_go_right_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Proof.
  intros.
  destruct a.
  - simpl.
    apply remove_go_right_edge_fact3_l.
  - simpl.
    unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact3_r:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_r s.(heap) u x)
          (remove_go_right_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Proof.
  intros.
  destruct a.
  - simpl.
    apply remove_go_right_edge_fact3_r.
  - simpl.
    unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact3_u:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_u s.(heap) u x)
          (remove_go_right_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Proof.
  intros.
  destruct a.
  - simpl.
    apply remove_go_right_edge_fact3_u.
  - simpl.
    unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

(*********************************************************)
(*********************************************************)

Fact remove_go_left_edge_fact4_l:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_left_edge v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  destruct u.
  2 : { tauto. }
  unfold BinaryTree.step_l.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6. destruct H6.
    tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_l in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e a1 x /\ (s1.(heap)).(go_left) e).
  * exists x0, e0.
    pose proof H8 a1 x0.
    destruct H6.
    destruct H9.
    rewrite <- H11.
    tauto.
  *tauto.
Qed.

Fact remove_go_left_edge_fact4_r:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_left_edge v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  destruct u.
  2 : { tauto. }
  unfold BinaryTree.step_r.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6. destruct H6.
    tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_r in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e a1 x /\ (s1.(heap)).(go_right) e).
  * exists x0, e0.
    pose proof H8 a1 x0.
    destruct H6.
    destruct H9.
    unfold BinaryTree.go_right in H11.
    unfold BinaryTree.go_right.
    rewrite <- H11.
    tauto.
  *tauto.
Qed.

Fact remove_go_left_edge_fact4_u:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_left_edge v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  destruct u.
  2 : { tauto. }
  unfold BinaryTree.step_u.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6.
    tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_u in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e x a1).
  * exists x0, e0.
    pose proof H8 x0 a1.
    tauto.
  *tauto.
Qed.

Fact remove_go_right_edge_fact4_l:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_l s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_l s.(heap) u x)
                      | by_empty => True
                      end).
Admitted.

Fact remove_go_right_edge_fact4_r:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_r s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_r s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold Hoare, remove_go_right_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  destruct u.
  2 : { tauto. }
  unfold BinaryTree.step_r.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6. destruct H6.
    tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_r in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e a1 x /\ (s1.(heap)).(go_right) e).
  * exists x0, e0.
    pose proof H8 a1 x0.
    destruct H6.
    destruct H9.
    unfold BinaryTree.go_right in H11.
    unfold BinaryTree.go_right.
    rewrite <- H11.
    tauto.
  *tauto.
Qed.


Fact remove_go_right_edge_fact4_u:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold Hoare, remove_go_right_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  destruct u.
  2 : { tauto. }
  unfold BinaryTree.step_u.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + subst e0.
    destruct H6.
    tauto.
  + pose proof H5 e0 H7.
    unfold BinaryTree.step_u in H.
  assert (exists x e : Z, BinaryTree.step_aux s1.(heap) e x a1).
  * exists x0, e0.
    pose proof H8 x0 a1.
    tauto.
  *tauto.
Qed.

(*********************************************************)
(*********************************************************)

Fact remove_go_left_edge'_fact4_l:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_l s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_l s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - apply remove_go_left_edge_fact4_l.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_left_edge'_fact4_r:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_r s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_r s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - apply remove_go_left_edge_fact4_r.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_left_edge'_fact4_u:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - apply remove_go_left_edge_fact4_u.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact4_l:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_l s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_l s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - apply remove_go_right_edge_fact4_l.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact4_r:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_r s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_r s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - apply remove_go_right_edge_fact4_r.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

Fact remove_go_right_edge'_fact4_u:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty => True
                    end)
          (remove_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - apply remove_go_right_edge_fact4_u.
  - unfold Hoare; sets_unfold.
    intros.
    subst s2.
    tauto.
Qed.

(*********************************************************)
(*********************************************************)

