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
Require Import HEAP.AddEdge.
Require Import HEAP.RemoveEdge.
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

Fact get_fa'_fact: forall (fa: Z) P, 
  Hoare P (get_fa' fa) 
    (fun a s => P s /\ match a with
                      | by_exist gf => BinaryTree.step_u s.(heap) fa gf
                      | by_empty => ~ (exists x, BinaryTree.step_u s.(heap) fa x)
                      end). 
Admitted.

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

Fact get_lc'_fact: forall (v: Z) P, 
  Hoare P (get_lc' v)
    (fun a s => P s /\ match a with
                      | by_exist lc => BinaryTree.step_l s.(heap) v lc
                      | by_empty => ~ (exists x, BinaryTree.step_l s.(heap) v x)
                      end).
Proof.
  intros.
  unfold get_lc'.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    apply Hoare_ret'.
    tauto.
  + eapply Hoare_bind; [apply get_lc_fact| cbv beta].
    intros lc.
    apply Hoare_ret'.
    tauto.
Qed.

Fact get_rc_fact: forall (v: Z) P, 
  Hoare P (get_rc v) (fun rc s => P s /\ BinaryTree.step_r s.(heap) v rc).
Admitted.

Fact get_rc'_fact: forall (v: Z) P, 
  Hoare P (get_rc' v)
    (fun a s => P s /\ match a with
                      | by_exist rc => BinaryTree.step_r s.(heap) v rc
                      | by_empty => ~ (exists x, BinaryTree.step_r s.(heap) v x)
                      end).
Admitted.

Fact get_dir_fact: forall (fa v: Z) P, 
  Hoare P (get_dir fa v)
    (fun dir s => P s /\ (dir = 0 \/ dir = 1) /\
                  ((dir = 0 /\ BinaryTree.step_l s.(heap) fa v) \/
                   (dir = 1 /\ BinaryTree.step_r s.(heap) fa v))).
Admitted.

Fact get_dir'_fact:
  forall (fa: ExistOrEmpty) (v: Z) P,
    Hoare P (get_dir' fa v)
      (fun dir s => P s /\
        (
          match fa with
          | by_exist fa => (dir = 0 /\ BinaryTree.step_l s.(heap) fa v) \/
                           (dir = 1 /\ BinaryTree.step_r s.(heap) fa v)
          | by_empty => ~ (exists x, BinaryTree.step_u s.(heap) v x)
          end)).
Admitted.

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

Fact swap_v_fa_fact3: forall (v fa: Z) (V: Z -> Prop), 
  Hoare
    (fun s => Abs s.(heap) V)
    (swap_v_u v fa)
    (fun _ s => Abs s.(heap) V).
Admitted.


Lemma L1: forall (v fa: Z) (lc_v rc_v lc_fa rc_fa gf: ExistOrEmpty)
  (dir_fa_v: Z) (s: state), 
    ((((((BinaryTree.legal s.(heap) /\ BinaryTree.step_u s.(heap) v fa) /\
    match lc_v with
    | by_exist lc => BinaryTree.step_l s.(heap) v lc
    | by_empty => ~ (exists x : Z, BinaryTree.step_l s.(heap) v x)
    end) /\
    match rc_v with
    | by_exist rc => BinaryTree.step_r s.(heap) v rc
    | by_empty => ~ (exists x : Z, BinaryTree.step_r s.(heap) v x)
    end) /\
    match lc_fa with
    | by_exist lc => BinaryTree.step_l s.(heap) fa lc
    | by_empty => ~ (exists x : Z, BinaryTree.step_l s.(heap) fa x)
    end) /\
    match rc_fa with
    | by_exist rc => BinaryTree.step_r s.(heap) fa rc
    | by_empty => ~ (exists x : Z, BinaryTree.step_r s.(heap) fa x)
    end) /\
    match gf with
    | by_exist gf0 => BinaryTree.step_u s.(heap) fa gf0
    | by_empty => ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)
    end) /\
    (dir_fa_v = 0 \/ dir_fa_v = 1) /\
    (dir_fa_v = 0 /\ BinaryTree.step_l s.(heap) fa v \/
     dir_fa_v = 1 /\ BinaryTree.step_r s.(heap) fa v)
    -> 
      ((((((BinaryTree.legal s.(heap) /\ BinaryTree.step_u s.(heap) v fa) /\
      match lc_v with
      | by_exist lc => BinaryTree.step_l s.(heap) v lc
      | by_empty => ~ (exists x : Z, BinaryTree.step_l s.(heap) v x)
      end)
      /\
      match rc_v with
      | by_exist rc => BinaryTree.step_r s.(heap) v rc
      | by_empty => ~ (exists x : Z, BinaryTree.step_r s.(heap) v x)
      end)
      /\
      match lc_fa with
      | by_exist lc => BinaryTree.step_l s.(heap) fa lc
      | by_empty => ~ (exists x : Z, BinaryTree.step_l s.(heap) fa x)
      end)
      /\
      match rc_fa with
      | by_exist rc => BinaryTree.step_r s.(heap) fa rc
      | by_empty => ~ (exists x : Z, BinaryTree.step_r s.(heap) fa x)
      end)
      /\
      (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))
      /\ 
      (dir_fa_v = 0 \/ dir_fa_v = 1)
      /\
      (dir_fa_v = 0 -> lc_fa = by_exist v)
      /\ 
      (dir_fa_v = 1 -> rc_fa = by_exist v)
      /\ 
      ~ fa = v
      /\ 
      ~ v = fa
      /\ 
      ~ lc_v = rc_v 
      /\ 
      ~ lc_fa = rc_fa
      /\ 
      match gf with 
      | by_exist fa_fa => ~ v = fa_fa 
      | by_empty => True
      end
      /\ 
      match gf with 
      | by_exist fa_fa => ~ fa = fa_fa 
      | by_empty => True
      end
      /\ 
      match lc_v with
      | by_exist lc_v => lc_v <> v 
      | by_empty => True
      end
      /\ 
      match lc_v with
      | by_exist lc_v => lc_v <> fa 
      | by_empty => True
      end
      /\ 
      match lc_v with
      | by_exist lc_v => fa <> lc_v 
      | by_empty => True
      end
      /\ 
      match rc_v with
      | by_exist rc_v => rc_v <> fa
      | by_empty => True
      end
      /\ 
      match rc_v with
      | by_exist rc_v => fa <> rc_v
      | by_empty => True
      end
      /\ 
      match rc_v with
      | by_exist rc_v => rc_v <> v
      | by_empty => True
      end
      /\ 
      match lc_v, rc_v with
      | by_exist lc_v, by_exist rc_v => ~ lc_v = rc_v
      | by_empty, _ => True
      | _, by_empty => True
      end
      /\ 
      match rc_fa with
      | by_exist rc_fa => rc_fa <> fa
      | by_empty => True
      end.
Admitted.

Fact swap_v_fa_fact4: forall (v fa: Z), 
  Hoare
    (fun s => BinaryTree.legal s.(heap) /\
              BinaryTree.step_u s.(heap) v fa)
    (swap_v_u v fa)
    (fun _ s => BinaryTree.legal s.(heap)).
Proof.
  intros.
  unfold swap_v_u.
  eapply Hoare_bind; [apply get_lc'_fact| cbv beta; intros lc_v].
  eapply Hoare_bind; [apply get_rc'_fact| cbv beta; intros rc_v].
  eapply Hoare_bind; [apply get_lc'_fact| cbv beta; intros lc_fa].
  eapply Hoare_bind; [apply get_rc'_fact| cbv beta; intros rc_fa].
  eapply Hoare_bind; [apply get_fa'_fact| cbv beta; intros gf].
  eapply Hoare_bind; [apply get_dir_fact| cbv beta; intros dir_fa_v].
  eapply Hoare_conseq_pre; [apply L1| ].
  eapply Hoare_irr_right.
  intros.
  eapply Hoare_bind.
  { eapply Hoare_conj.
    + eapply Hoare_conseq_pre.
      2: { apply remove_go_left_edge'_fact2. }
      tauto.
    + assert (Hoare
                (fun s => BinaryTree.legal s.(heap) /\
                  (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))
                (remove_go_left_edge' v lc_v) 
                (fun _ s => (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))).
      {
        pose proof remove_go_left_edge'_fact3_u v lc_v fa.
        revert H0.
        unfold Hoare; sets_unfold; intros.
        destruct H1.
        pose proof H4 H3.
        pose proof H0 _ _ _ H5 H2.
        tauto.
      }
      eapply Hoare_conseq_pre.
      2: { apply H0. }
      tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { eapply Hoare_conj4.
    + eapply Hoare_conseq_pre.
      2: { apply remove_go_right_edge'_fact2. }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact3_l _ _ v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact4_u _ _ lc_v). }
      tauto.
    + assert (Hoare
                (fun s => BinaryTree.legal s.(heap) /\
                  (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))
                (remove_go_right_edge' v rc_v) 
                (fun _ s => (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))).
      {
        pose proof remove_go_right_edge'_fact3_u v rc_v fa.
        revert H0.
        unfold Hoare; sets_unfold; intros.
        destruct H1.
        pose proof H4 H3.
        pose proof H0 _ _ _ H5 H2.
        tauto.
      }
      eapply Hoare_conseq_pre.
      2: { apply H0. }
      tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { eapply Hoare_conj6.
    + eapply Hoare_conseq_pre.
      2: { apply remove_go_left_edge'_fact2. }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_left_edge'_fact3_l _ _ v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_left_edge'_fact3_r _ _ v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_left_edge'_fact4_u _ _ lc_v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_left_edge'_fact4_u _ _ rc_v). }
      tauto.
    + assert (Hoare
                (fun s => BinaryTree.legal s.(heap) /\
                  (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))
                (remove_go_left_edge' fa lc_fa) 
                (fun _ s => (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))).
      {
        pose proof remove_go_left_edge'_fact3_u fa lc_fa fa.
        revert H0.
        unfold Hoare; sets_unfold; intros.
        destruct H1.
        pose proof H4 H3.
        pose proof H0 _ _ _ H5 H2.
        tauto.
      }
      eapply Hoare_conseq_pre.
      2: { apply H0. }
      tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { eapply Hoare_conj8.
    + eapply Hoare_conseq_pre.
      2: { apply remove_go_right_edge'_fact2. }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact3_l _ _ v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact3_r _ _ v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact4_u _ _ lc_v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact4_u _ _ rc_v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact3_l _ _ fa). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact4_u _ _ lc_fa). }
      tauto.
    + assert (Hoare
                (fun s => BinaryTree.legal s.(heap) /\
                  (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))
                (remove_go_right_edge' fa rc_fa) 
                (fun _ s => (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))).
      {
        pose proof remove_go_right_edge'_fact3_u fa rc_fa fa.
        revert H0.
        unfold Hoare; sets_unfold; intros.
        destruct H1.
        pose proof H4 H3.
        pose proof H0 _ _ _ H5 H2.
        tauto.
      }
      eapply Hoare_conseq_pre.
      2: { apply H0. }
      tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { destruct gf.
    * eapply Hoare_choice.
      - apply Hoare_test_bind.
        eapply Hoare_bind.
        { 
          eapply Hoare_conj9.
          + eapply Hoare_conseq_pre.
            2: { apply remove_go_left_edge_fact2. }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact3_l _ _ v). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact3_r _ _ v). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact4_u _ _ lc_v). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact4_u _ _ rc_v). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact3_l _ _ fa). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact3_r _ _ fa). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact4_u _ _ lc_fa). }
            tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (remove_go_left_edge_fact4_u _ _ rc_fa). }
            tauto.  
        }
        cbv beta; intros _.
        eapply Hoare_conj10.
        + eapply Hoare_conseq_pre.
          2: { apply add_go_left_edge_fact2. }
          intros.
          destruct H0 as [H1 [_ [_ [_ [_ [H2 H3]]]]]].
          destruct H as [H4 [H5 [H6 _]]].
          pose proof (classic(dir_fa_v = 0)).
          destruct H.
          ++ pose proof H5 H.
             subst lc_fa.
             tauto.
          ++ destruct H4.
             -- tauto.
             -- pose proof H6 H0.
                subst rc_fa.
                tauto.
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact3_l _ _ v). }
          simpl; tauto.
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact3_r _ _ v). }
          simpl; tauto.
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact4_u _ _ lc_v). }
          simpl. destruct lc_v; tauto.
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact4_u _ _ rc_v). }
          simpl. destruct rc_v; tauto.
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact3_l _ _ fa). }
          simpl; tauto. 
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact3_r _ _ fa). }
          simpl; tauto.
        + eapply Hoare_conseq_pre.
          2: { apply (add_go_left_edge_fact3_u _ _ fa). }
          simpl; tauto.
        + assert (Hoare
                (fun s => BinaryTree.legal s.(heap) /\
                  (gf = by_empty -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))
                (add_go_left_edge' fa rc_fa) 
                (fun _ s => (dir_fa_v = 0 -> ~ (exists x : Z, BinaryTree.step_u s.(heap) fa x)))).
      {
        pose proof remove_go_right_edge'_fact3_u fa rc_fa fa.
        revert H0.
        unfold Hoare; sets_unfold; intros.
        destruct H1.
        pose proof H4 H3.
        pose proof H0 _ _ _ H5 H2.
        tauto.



      - cbv beta. 
        apply Hoare_test_bind.
          eapply Hoare_bind.
          { 
            eapply Hoare_conj9.
            + eapply Hoare_conseq_pre.
              2: { apply remove_go_right_edge_fact2. }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact3_l _ _ v). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact3_r _ _ v). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact4_u _ _ lc_v). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact4_u _ _ rc_v). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact3_l _ _ fa). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact3_r _ _ fa). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact4_u _ _ lc_fa). }
              tauto.
            + eapply Hoare_conseq_pre.
              2: { apply (remove_go_right_edge_fact4_u _ _ rc_fa). }
              tauto.  
          }
          cbv beta; intros _.
          eapply Hoare_conj8.
          + eapply Hoare_conseq_pre.
            2: { apply add_go_right_edge_fact2. }
            intros.
            destruct H0 as [H1 [_ [_ [_ [_ [H2 H3]]]]]].
            destruct H as [H4 [H5 [H6 _]]].
            pose proof (classic(dir_fa_v = 0)).
            destruct H.
            ++ pose proof H5 H.
              subst lc_fa.
              tauto.
            ++ destruct H4.
              -- tauto.
              -- pose proof H6 H0.
                  subst rc_fa.
                  tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact3_l _ _ v). }
            simpl; tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact3_r _ _ v). }
            simpl; tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact4_u _ _ lc_v). }
            simpl. destruct lc_v; tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact4_u _ _ rc_v). }
            simpl. destruct rc_v; tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact3_l _ _ fa). }
            simpl; tauto. 
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact3_r _ _ fa). }
            simpl; tauto.
          + eapply Hoare_conseq_pre.
            2: { apply (add_go_right_edge_fact3_u _ _ fa). }
            simpl; tauto.
    * cbv beta.
      unfold Hoare; sets_unfold; intros.
      subst s2.
      tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { eapply Hoare_conj6.
    + eapply Hoare_conseq_pre.
      2: { apply add_go_left_edge'_fact2. }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge'_fact3_l _ _ v). }
      simpl. tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge'_fact3_r _ _ v). }
      simpl; tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge'_fact4_u _ _ rc_v). }
      simpl; intros.
      destruct lc_v.
      ++ destruct rc_v; tauto.
      ++ tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge'_fact3_r _ _ fa). }
      simpl; tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge'_fact3_u _ _ fa). }
      simpl; tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { eapply Hoare_conj4.
    + eapply Hoare_conseq_pre.
      2: { apply add_go_right_edge'_fact2. }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_right_edge'_fact3_l _ _ v). }
      simpl. tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_right_edge'_fact3_r _ _ v). }
      simpl; tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_right_edge'_fact3_u _ _ fa). }
      simpl; tauto.
  }
  cbv beta; intros _.
  eapply Hoare_choice.
  - apply Hoare_test_bind.
    apply Hoare_irr_left; intros.
    eapply Hoare_bind.
    { eapply Hoare_conj.
    + eapply Hoare_conseq_pre.
      2: { apply add_go_left_edge_fact2. }
      simpl. tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge_fact4_u _ _ rc_fa). }
      simpl. intros. destruct rc_fa.
      ++ tauto. 
    + eapply Hoare_conseq_pre.
      2: { apply (add_go_left_edge_fact3_r _ _ v). }
      simpl; tauto.
  }

        
       
Fact swap_v_u_helper1: forall (v rc: Z) (V: Z -> Prop),
  Hoare
    (fun s : state =>
                      v > rc /\
                      (((s.(heap)).(vvalid) v /\
                        ~ (exists lc : Z, BinaryTree.step_l s.(heap) v lc)) /\
                        (s.(heap)).(vvalid) v /\
                        Abs s.(heap) V /\
                        BinaryTree.legal s.(heap) /\
                        (Heap_broken_down s.(heap) v \/ Heap s.(heap))) /\
                      BinaryTree.step_r s.(heap) v rc)
    (swap_v_u v rc)
    (fun (_ : unit) (s : state) =>
                      (s.(heap)).(vvalid) v /\
                      Abs s.(heap) V /\
                      BinaryTree.legal s.(heap) /\
                      (Heap_broken_down s.(heap) v \/ Heap s.(heap))).
Admitted.

Fact swap_v_u_helper2: forall (v lc: Z) (V: Z -> Prop),
  Hoare
    (fun s : state =>
                      v > lc /\
                      (((s.(heap)).(vvalid) v /\
                        ~ (exists rc : Z, BinaryTree.step_r s.(heap) v rc)) /\
                      (s.(heap)).(vvalid) v /\
                      Abs s.(heap) V /\
                      BinaryTree.legal s.(heap) /\
                      (Heap_broken_down s.(heap) v \/ Heap s.(heap))) /\
                      BinaryTree.step_l s.(heap) v lc)
    (swap_v_u v lc)
    (fun (_ : unit) (s : state) =>
                      (s.(heap)).(vvalid) v /\
                      Abs s.(heap) V /\
                      BinaryTree.legal s.(heap) /\
                      (Heap_broken_down s.(heap) v \/ Heap s.(heap))).
Admitted.

Fact swap_v_u_helper3: forall (v lc rc: Z) (V: Z -> Prop),
  Hoare
    (fun s : state =>
                      v > lc /\
                      lc < rc /\
                      (((s.(heap)).(vvalid) v /\
                        Abs s.(heap) V /\
                        BinaryTree.legal s.(heap) /\
                        (Heap_broken_down s.(heap) v \/ Heap s.(heap))) /\
                      BinaryTree.step_l s.(heap) v lc) /\
                      BinaryTree.step_r s.(heap) v rc)
    (swap_v_u v lc)
    (fun (_ : unit) (s : state) =>
                      (s.(heap)).(vvalid) v /\
                      Abs s.(heap) V /\
                      BinaryTree.legal s.(heap) /\
                      (Heap_broken_down s.(heap) v \/ Heap s.(heap))).
Admitted.

Fact swap_v_u_helper4: forall (v lc rc: Z) (V: Z -> Prop),
  Hoare
    (fun s : state =>
                      v > rc /\
                      lc > rc /\
                      (((s.(heap)).(vvalid) v /\
                        Abs s.(heap) V /\
                        BinaryTree.legal s.(heap) /\
                        (Heap_broken_down s.(heap) v \/ Heap s.(heap))) /\
                      BinaryTree.step_l s.(heap) v lc) /\
                      BinaryTree.step_r s.(heap) v rc) 
    (swap_v_u v rc)
    (fun (_ : unit) (s : state) =>  
                      (s.(heap)).(vvalid) v /\
                      Abs s.(heap) V /\
                      BinaryTree.legal s.(heap) /\
                      (Heap_broken_down s.(heap) v \/ Heap s.(heap))).
Admitted.

