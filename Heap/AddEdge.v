Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import Classical.
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

Fact add_go_left_edge_fact1: forall (v lc: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V)
        (add_go_left_edge v lc)
        (fun _ s => Abs s.(heap) V).
Proof.
  intros.
  unfold Hoare, add_go_left_edge; sets_unfold.
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

Fact add_go_right_edge_fact1: forall (v rc: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V)
        (add_go_right_edge v rc)
        (fun _ s => Abs s.(heap) V).
Proof.
  intros.
  unfold Hoare, add_go_right_edge; sets_unfold.
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




Fact add_go_left_edge_fact2: forall (v lc: Z),
  Hoare (fun s => BinaryTree.legal s.(heap) /\ 
                  ~ (exists x, BinaryTree.step_l s.(heap) v x) /\ 
                  ~ (exists x, BinaryTree.step_u s.(heap) lc x))
        (add_go_left_edge v lc)
        (fun _ s => BinaryTree.legal s.(heap)).
Admitted.

Fact add_go_left_edge'_fact2:
  forall (v: Z) (a: ExistOrEmpty),
  Hoare (fun s => BinaryTree.legal s.(heap) /\ 
                  ~ (exists x, BinaryTree.step_l s.(heap) v x) /\ 
                  match a with
                  | by_exist lc => ~ (exists x, BinaryTree.step_u s.(heap) lc x)
                  | by_empty => True
                  end)
        (add_go_left_edge' v a)
        (fun _ s => BinaryTree.legal s.(heap)).
Admitted.

      
(* Proof.
  intros.
  unfold Hoare, add_go_left_edge; sets_unfold.
  intros. destruct H0.
  destruct H as [? [? ?]].
  destruct H.
  destruct H1 as [? [? [? [? [? [? ?]]]]]].
  split.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    destruct HH1.
    destruct HH2.
    apply H1 in step_evalid.
    apply H1 in step_evalid0.
    destruct step_evalid.
    + destruct step_evalid0.
      * assert (Hy1: BinaryTree.step_l s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_l.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - rewrite <- H13; tauto.
        }
        assert (Hy2: BinaryTree.step_l s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_l.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - rewrite <- H13; tauto.
        }
        pose proof (step_l_unique x0 y1 y2 Hy1 Hy2).
        tauto.
      * assert (Hy1: BinaryTree.step_l s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_l.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - rewrite <- H13; tauto.
        }
        rewrite H9 in H4.
        rewrite H4 in step_src0.
        rewrite <- step_src0 in Hy1.
        assert (exists x: Z, BinaryTree.step_l s1.(heap) v x).
        { 
          exists y1.
          tauto.
        }
        tauto.
    + destruct step_evalid0.
      * assert (Hy2: BinaryTree.step_l s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_l.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - rewrite <- H13; tauto.
        }
        rewrite H8 in H4.
        rewrite H4 in step_src.
        rewrite <- step_src in Hy2.
        assert (exists x: Z, BinaryTree.step_l s1.(heap) v x).
        { 
          exists y2.
          tauto.
        }
        tauto.
      * rewrite <- H8 in step_dst.
        rewrite <- H9 in step_dst0.
        rewrite step_dst in step_dst0.
        tauto.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    assert (Hy1: BinaryTree.step_r s1.(heap) x0 y1).
    { 
      unfold BinaryTree.step_r.
      exists e1.
      unfold BinaryTree.go_right in HHH1.
      assert (e1 <> x).
      { intro. subst. tauto. }
      assert (x <> e1).
      { intro. subst. tauto. }
      apply H7 in H8.
      destruct H8 as [? [? ?]].
      destruct HH1.
      split.
      - split.
        + apply H1 in step_evalid.
          destruct step_evalid; [tauto|].
          contradiction.
        + apply H0; tauto.
        + apply H0; tauto.
        + rewrite <- H8; tauto.
        + rewrite <- H10; tauto. 
      - unfold BinaryTree.go_right.
        rewrite <- H11; tauto.
    }
    assert (Hy2: BinaryTree.step_r s1.(heap) x0 y2).
    { 
      unfold BinaryTree.step_r.
      exists e2.
      unfold BinaryTree.go_right in HHH2.
      assert (e2 <> x).
      { intro. subst. tauto. }
      assert (x <> e2).
      { intro. subst. tauto. }
      apply H7 in H8.
      destruct H8 as [? [? ?]].
      destruct HH2.
      split.
      - split.
        + apply H1 in step_evalid.
          destruct step_evalid; [tauto|].
          contradiction.
        + apply H0; tauto.
        + apply H0; tauto.
        + rewrite <- H8; tauto.
        + rewrite <- H10; tauto. 
      - unfold BinaryTree.go_right.
        rewrite <- H11; tauto.
    }
    pose proof (step_r_unique x0 y1 y2 Hy1 Hy2).
    tauto.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    apply H1 in HH1.
    apply H1 in HH2.
    destruct HH1.
    + destruct HH2.
      * assert (Hy1: BinaryTree.step_u s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_u.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        assert (Hy2: BinaryTree.step_u s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_u.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        pose proof (step_u_unique x0 y1 y2 Hy1 Hy2).
        tauto.
      * assert (Hy1: BinaryTree.step_u s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_u.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        rewrite H9 in H5.
        rewrite H5 in step_dst0.
        rewrite <- step_dst0 in Hy1.
        assert (exists x: Z, BinaryTree.step_u s1.(heap) lc x).
        { 
          exists y1.
          tauto.
        }
        tauto.
    + destruct HH2.
      * assert (Hy2: BinaryTree.step_u s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_u.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        rewrite H8 in H5.
        rewrite H5 in step_dst.
        rewrite <- step_dst in Hy2.
        assert (exists x: Z, BinaryTree.step_u s1.(heap) lc x).
        { 
          exists y2.
          tauto.
        }
        tauto.
      * rewrite <- H8 in step_src.
        rewrite <- H9 in step_src0.
        rewrite step_src in step_src0.
        tauto.
Qed. *)

Fact add_go_right_edge_fact2: forall (v rc: Z),
  Hoare (fun s => BinaryTree.legal s.(heap) /\ 
                  ~ (exists x, BinaryTree.step_r s.(heap) v x) /\ 
                  ~ (exists x, BinaryTree.step_u s.(heap) rc x))
        (add_go_right_edge v rc)
        (fun _ s => BinaryTree.legal s.(heap)).
Admitted.

Fact add_go_right_edge'_fact2:
  forall (v: Z) (a: ExistOrEmpty),
  Hoare (fun s => BinaryTree.legal s.(heap) /\ 
                  ~ (exists x, BinaryTree.step_r s.(heap) v x) /\ 
                  match a with
                  | by_exist rc => ~ (exists x, BinaryTree.step_u s.(heap) rc x)
                  | by_empty => True
                  end)
        (add_go_right_edge' v a)
        (fun _ s => BinaryTree.legal s.(heap)).
Admitted.

    
(* Proof.
  intros.
  unfold Hoare, add_go_right_edge; sets_unfold.
  intros. destruct H0.
  destruct H as [? [? ?]].
  destruct H.
  destruct H1 as [? [? [[? [? [? ?]]]]]].
  split.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    assert (Hy1: BinaryTree.step_l s1.(heap) x0 y1).
    { 
      unfold BinaryTree.step_l.
      exists e1.
      unfold BinaryTree.go_left in HHH1.
      assert (e1 <> x).
      { intro. subst. tauto. }
      assert (x <> e1).
      { intro. subst. tauto. }
      apply H7 in H8.
      destruct H8 as [? [? ?]].
      destruct HH1.
      split.
      - split.
        + apply H1 in step_evalid.
          destruct step_evalid; [tauto|].
          contradiction.
        + apply H0; tauto.
        + apply H0; tauto.
        + rewrite <- H8; tauto.
        + rewrite <- H10; tauto. 
      - rewrite <- H11; tauto.
    }
    assert (Hy2: BinaryTree.step_l s1.(heap) x0 y2).
    { 
      unfold BinaryTree.step_l.
      exists e2.
      unfold BinaryTree.go_left in HHH2.
      assert (e2 <> x).
      { intro. subst. tauto. }
      assert (x <> e2).
      { intro. subst. tauto. }
      apply H7 in H8.
      destruct H8 as [? [? ?]].
      destruct HH2.
      split.
      - split.
        + apply H1 in step_evalid.
          destruct step_evalid; [tauto|].
          contradiction.
        + apply H0; tauto.
        + apply H0; tauto.
        + rewrite <- H8; tauto.
        + rewrite <- H10; tauto. 
      - rewrite <- H11; tauto.
    }
    pose proof (step_l_unique x0 y1 y2 Hy1 Hy2).
    tauto.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    destruct HH1.
    destruct HH2.
    apply H1 in step_evalid.
    apply H1 in step_evalid0.
    destruct step_evalid.
    + destruct step_evalid0.
      * assert (Hy1: BinaryTree.step_r s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_r.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - unfold BinaryTree.go_right.
            rewrite <- H13; tauto.
        }
        assert (Hy2: BinaryTree.step_r s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_r.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - unfold BinaryTree.go_right.
            rewrite <- H13; tauto.
        }
        pose proof (step_r_unique x0 y1 y2 Hy1 Hy2).
        tauto.
      * assert (Hy1: BinaryTree.step_r s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_r.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - unfold BinaryTree.go_right.
            rewrite <- H13; tauto.
        }
        rewrite H9 in H4.
        rewrite H4 in step_src0.
        rewrite <- step_src0 in Hy1.
        assert (exists x: Z, BinaryTree.step_r s1.(heap) v x).
        { 
          exists y1.
          tauto.
        }
        tauto.
    + destruct step_evalid0.
      * assert (Hy2: BinaryTree.step_r s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_r.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          - split.
            + tauto.
            + apply H0; tauto.
            + apply H0; tauto.
            + rewrite <- H10; tauto.
            + rewrite <- H12; tauto. 
          - unfold BinaryTree.go_right.
            rewrite <- H13; tauto.
        }
        rewrite H8 in H4.
        rewrite H4 in step_src.
        rewrite <- step_src in Hy2.
        assert (exists x: Z, BinaryTree.step_r s1.(heap) v x).
        { 
          exists y2.
          tauto.
        }
        tauto.
      * rewrite <- H8 in step_dst.
        rewrite <- H9 in step_dst0.
        rewrite step_dst in step_dst0.
        tauto.
  - intros x0 y1 y2 HH1 HH2.
    destruct HH1 as [e1 ?].
    destruct H8 as [HH1 HHH1].
    destruct HH2 as [e2 ?].
    destruct H8 as [HH2 HHH2].
    apply H1 in HH1.
    apply H1 in HH2.
    destruct HH1.
    + destruct HH2.
      * assert (Hy1: BinaryTree.step_u s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_u.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        assert (Hy2: BinaryTree.step_u s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_u.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        pose proof (step_u_unique x0 y1 y2 Hy1 Hy2).
        tauto.
      * assert (Hy1: BinaryTree.step_u s1.(heap) x0 y1).
        { 
          unfold BinaryTree.step_u.
          exists e1.
          assert (e1 <> x).
          { intro. subst. tauto. }
          assert (x <> e1).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        rewrite H9 in H5.
        rewrite H5 in step_dst0.
        rewrite <- step_dst0 in Hy1.
        assert (exists x: Z, BinaryTree.step_u s1.(heap) rc x).
        { 
          exists y1.
          tauto.
        }
        tauto.
    + destruct HH2.
      * assert (Hy2: BinaryTree.step_u s1.(heap) x0 y2).
        { 
          unfold BinaryTree.step_u.
          exists e2.
          assert (e2 <> x).
          { intro. subst. tauto. }
          assert (x <> e2).
          { intro. subst. tauto. }
          apply H7 in H10.
          destruct H10 as [? [? ?]].
          split.
          + tauto.
          + apply H0; tauto.
          + apply H0; tauto.
          + rewrite <- H10; tauto.
          + rewrite <- H12; tauto. 
        }
        rewrite H8 in H5.
        rewrite H5 in step_dst.
        rewrite <- step_dst in Hy2.
        assert (exists x: Z, BinaryTree.step_u s1.(heap) rc x).
        { 
          exists y2.
          tauto.
        }
        tauto.
      * rewrite <- H8 in step_src.
        rewrite <- H9 in step_src0.
        rewrite step_src in step_src0.
        tauto.
Qed.  *)


(*********************************************************)
(*********************************************************)

Fact add_go_left_edge_fact3_l:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ u = v /\ ~ exists x, BinaryTree.step_l s.(heap) u x)
          (add_go_left_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Admitted.
(* 
Proof.
  unfold Hoare, add_go_left_edge; sets_unfold.
  intros.
  destruct H0 as [? [? [? [? [? [? ?]]]]]].
  unfold BinaryTree.step_l.
  unfold not.
  intros.
  destruct H6.
  destruct H6 as [e0 ?].
  pose proof (classic (e0 = x)).
  destruct H7.
  + destruct H3.
    subst e0.
    destruct H6.
    destruct H3.
    destruct H.
    rewrite <- step_src in H.
    rewrite <- step_src0 in H.
    tauto.
  + pose proof H5 e0 H7.
    destruct H.
    unfold not, BinaryTree.step_l in H9.
    destruct H9.
    destruct H6.
    destruct H8.
    destruct H10.
    rewrite H11 in H9.
    assert(BinaryTree.step_aux s1.(heap) e0 u x0).
      split.
      * pose proof H2 e0.
        destruct H12.
        destruct H6.
        apply H12 in step_evalid.
        destruct step_evalid.
        tauto.
        rewrite H6 in H7.
        tauto.
      * pose proof H0 u.
        destruct H12.
        destruct H6.
        apply H12 in step_src_valid.
        tauto.
      *  pose proof H0 x0.
        destruct H12.
        destruct H6.
        apply H12 in step_dst_valid.
        tauto.
      * destruct H6.
        rewrite H8 in step_src.
        tauto.
      * destruct H6.
        rewrite H10 in step_dst.
        tauto.
      * exists x0.
        exists e0.
        tauto.
Qed. *)

Fact add_go_left_edge_fact3_r:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_r s.(heap) u x)
          (add_go_left_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Admitted.

Fact add_go_left_edge_fact3_u:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ u = a /\ ~ exists x, BinaryTree.step_u s.(heap) u x)
          (add_go_left_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Admitted.

Fact add_go_right_edge_fact3_l:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_l s.(heap) u x)
          (add_go_right_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Admitted.

Fact add_go_right_edge_fact3_r:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ u = v /\ ~ exists x, BinaryTree.step_r s.(heap) u x)
          (add_go_right_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Admitted.

Fact add_go_right_edge_fact3_u:
  forall (v: Z) (a: Z) (u: Z),
    Hoare (fun s => ~ u = a /\ ~ exists x, BinaryTree.step_u s.(heap) u x)
          (add_go_right_edge v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Admitted.


(*********************************************************)
(*********************************************************)


Fact add_go_left_edge'_fact3_l:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ u = v
       /\ ~ exists x, BinaryTree.step_l s.(heap) u x)
          (add_go_left_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Admitted.

Fact add_go_left_edge'_fact3_r:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_r s.(heap) u x)
          (add_go_left_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Admitted.

Fact add_go_left_edge'_fact3_u:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x) /\ 
                    match a with
                    | by_exist a => ~ u = a
                    | by_empty => True
                    end)
          (add_go_left_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Admitted.

Fact add_go_right_edge'_fact3_l:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ exists x, BinaryTree.step_l s.(heap) u x)
          (add_go_right_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_l s.(heap) u x).
Admitted.

Fact add_go_right_edge'_fact3_r:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ u = v /\ ~ exists x, BinaryTree.step_r s.(heap) u x)
          (add_go_right_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_r s.(heap) u x).
Admitted.

Fact add_go_right_edge'_fact3_u:
  forall (v: Z) (a: ExistOrEmpty) (u: Z),
    Hoare (fun s => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x) /\ 
                    match a with
                    | by_exist a => ~ u = a
                    | by_empty => True
                    end)
          (add_go_right_edge' v a)
          (fun _ s => ~ exists x, BinaryTree.step_u s.(heap) u x).
Admitted.


(*********************************************************)
(*********************************************************)



Fact add_go_left_edge_fact4_u:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ u = a /\ ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty => True
                    end)
          (add_go_left_edge v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Admitted.

Fact add_go_right_edge_fact4_u:
  forall (v: Z) (a: Z) (u: ExistOrEmpty),
    Hoare (fun s => match u with
                    | by_exist u => ~ u = a /\ ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty => True
                    end)
          (add_go_right_edge v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Admitted.


(*********************************************************)
(*********************************************************)


Fact add_go_left_edge'_fact4_u:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match a, u with
                    | by_exist a, by_exist u =>
                      ~ a = u /\ ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty, _ => True
                    | _, by_empty => True
                    end)
          (add_go_left_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Admitted.

Fact add_go_right_edge'_fact4_u:
  forall (v: Z) (a: ExistOrEmpty) (u: ExistOrEmpty),
    Hoare (fun s => match a, u with
                    | by_exist a, by_exist u =>
                      ~ a = u /\ ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                    | by_empty, _ => True
                    | _, by_empty => True
                    end)
          (add_go_right_edge' v a)
          (fun _ s => match u with
                      | by_exist u => ~ (exists x : Z, BinaryTree.step_u s.(heap) u x)
                      | by_empty => True
                      end).
Admitted.

(*********************************************************)
(*********************************************************)