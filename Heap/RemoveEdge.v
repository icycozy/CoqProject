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
    destruct H0.
    rewrite H1.
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
  destruct H0.
  rewrite H1.
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
(* Proof. *)
  (* intros.
  unfold remove_go_left_edge, Hoare; sets_unfold.
  intros.
  destruct H as [? Hx].
  destruct H0 as [? [? [? [? [? [? [? ?]]]]]]].
  assert (forall a: Z, (s2.(heap)).(evalid) a -> (s1.(heap)).(evalid) a).
  {
    intros.
    pose proof (H2 a0).
    destruct H8.
    apply H8.
    left; tauto. 
  }
  split; [split| split].
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    destruct HH1.
    destruct HH2.
    assert (e1 <> x).
    {
      intros h.
      subst.
      tauto.
    }
    assert (e2 <> x).
    {
      intros h.
      subst.
      tauto.
    }
    apply H7 in step_evalid.
    apply H7 in step_evalid0.
    assert (Hy1: BinaryTree.step_l s1.(heap) x0 y1).
    {
      apply H6 in H8.
      destruct H8 as [? [? ?]].
      unfold BinaryTree.step_l.
      exists e1.
      split; [split|].
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H8; tauto.
      - rewrite <- H10; tauto.
      - rewrite <- H11; tauto.
    }
    assert (Hy2: BinaryTree.step_l s1.(heap) x0 y2).
    {
      apply H6 in H9.
      destruct H9 as [? [? ?]].
      unfold BinaryTree.step_l.
      exists e2.
      split; [split|].
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H9; tauto.
      - rewrite <- H10; tauto.
      - rewrite <- H11; tauto.
    }
    destruct H.
    pose proof (step_l_unique x0 y1 y2 Hy1 Hy2).
    tauto.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    destruct HH1.
    destruct HH2.
    assert (e1 <> x).
    {
      intros h.
      subst.
      tauto.
    }
    assert (e2 <> x).
    {
      intros h.
      subst.
      tauto.
    }
    apply H7 in step_evalid.
    apply H7 in step_evalid0.
    assert (Hy1: BinaryTree.step_r s1.(heap) x0 y1).
    {
      apply H6 in H8.
      destruct H8 as [? [? ?]].
      unfold BinaryTree.step_r.
      exists e1.
      split; [split|].
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H8; tauto.
      - rewrite <- H10; tauto.
      - unfold BinaryTree.go_right.
        rewrite <- H11; tauto.
    }
    assert (Hy2: BinaryTree.step_r s1.(heap) x0 y2).
    {
      apply H6 in H9.
      destruct H9 as [? [? ?]].
      unfold BinaryTree.step_r.
      exists e2.
      split; [split|].
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H9; tauto.
      - rewrite <- H10; tauto.
      - unfold BinaryTree.go_right.
        rewrite <- H11; tauto.
    }
    destruct H.
    pose proof (step_r_unique x0 y1 y2 Hy1 Hy2).
    tauto.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 HH1].
    destruct HH2 as [e2 HH2].
    destruct HH1.
    destruct HH2.
    assert (e1 <> x).
    {
      intros h.
      subst.
      tauto.
    }
    assert (e2 <> x).
    {
      intros h.
      subst.
      tauto.
    }
    apply H7 in step_evalid.
    apply H7 in step_evalid0.
    assert (Hy1: BinaryTree.step_u s1.(heap) x0 y1).
    {
      apply H6 in H8.
      destruct H8 as [? [? ?]].
      unfold BinaryTree.step_u.
      exists e1.
      split.
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H8; tauto.
      - rewrite <- H10; tauto.
    }
    assert (Hy2: BinaryTree.step_u s1.(heap) x0 y2).
    {
      apply H6 in H9.
      destruct H9 as [? [? ?]].
      unfold BinaryTree.step_u.
      exists e2.
      split.
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H9; tauto.
      - rewrite <- H10; tauto.
    }
    destruct H.
    pose proof (step_u_unique x0 y1 y2 Hy1 Hy2).
    tauto.
  - intros h.
    destruct h.
    destruct H8 as [e1 ?].
    destruct H8.
    destruct H8.
    assert (HH: BinaryTree.step_l s1.(heap) v x0).
    {
      unfold BinaryTree.step_l.
      exists e1.
      assert (e1 <> x).
      {
        intros h.
        subst.
        tauto.
      }
      apply H7 in step_evalid.
      apply H6 in H8.
      destruct H8 as [? [? ?]].
      split; [split|].
      - tauto.
      - apply H0; tauto.
      - apply H0; tauto.
      - rewrite <- H8; tauto.
      - rewrite <- H10; tauto.
      - rewrite <- H11; tauto. 
    }
    destruct H. *)
Proof.
  unfold Hoare, remove_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_l.
  unfold not.
  split.
  - intros.
    split.
    
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
    destruct H0.
    rewrite H1.
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
    destruct H0.
    rewrite H1.
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
    destruct H0.
    rewrite H1.
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
    destruct H0.
    rewrite H1.
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
    destruct H0.
    rewrite H1.
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
    destruct H0.
    rewrite H1.
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
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_left_edge v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
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
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                      | by_empty => True
                      end).
Admitted.

Fact remove_go_right_edge_fact4_r:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
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
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
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
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - apply remove_go_left_edge_fact4_l.
  - unfold Hoare; sets_unfold.
    intros.
    destruct H0.
    rewrite H1.
    tauto.
Qed.

Fact remove_go_left_edge'_fact4_r:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - apply remove_go_left_edge_fact4_r.
  - unfold Hoare; sets_unfold.
    intros.
    destruct H0.
    rewrite H1.
    tauto.
Qed.

Fact remove_go_left_edge'_fact4_u:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_left_edge'.
  induction a.
  - apply remove_go_left_edge_fact4_u.
  - unfold Hoare; sets_unfold.
    intros.
    destruct H0.
    rewrite H1.
    tauto.
Qed.

Fact remove_go_right_edge'_fact4_l:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_l s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - apply remove_go_right_edge_fact4_l.
  - unfold Hoare; sets_unfold.
    intros.
    destruct H0.
    rewrite H1.
    tauto.
Qed.

Fact remove_go_right_edge'_fact4_r:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_r s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - apply remove_go_right_edge_fact4_r.
  - unfold Hoare; sets_unfold.
    intros.
    destruct H0.
    rewrite H1.
    tauto.
Qed.

Fact remove_go_right_edge'_fact4_u:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
                    | by_empty => True
                    end)
          (remove_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist lc => ~ (exists x : Z, BinaryTree.step_u s.(heap) lc x)
                      | by_empty => True
                      end).
Proof.
  intros.
  unfold remove_go_right_edge'.
  induction a.
  - apply remove_go_right_edge_fact4_u.
  - unfold Hoare; sets_unfold.
    intros.
    destruct H0.
    rewrite H1.
    tauto.
Qed.


(*********************************************************)
(*********************************************************)


