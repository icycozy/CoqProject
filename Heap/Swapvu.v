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


Fact get_rc'_fact: forall (v: Z) P, 
  Hoare P (get_rc' v)
    (fun a s => P s /\ match a with
                      | by_exist rc => BinaryTree.step_r s.(heap) v rc
                      | by_empty => ~ (exists x, BinaryTree.step_r s.(heap) v x)
                      end).
Admitted.

Fact get_dir_fact: forall (fa v: Z) P, 
  Hoare P (get_dir fa v)
    (fun dir s => P s /\
      (
        (dir = 0 /\ BinaryTree.step_l s.(heap) fa v) \/
        (dir = 1 /\ BinaryTree.step_r s.(heap) fa v))
      ).
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
  eapply Hoare_bind; [apply get_dir_fact| cbv beta; intros dir_fa_v].
  eapply Hoare_bind.
  { eapply Hoare_conseq_pre.
    2: { apply remove_go_left_edge'_fact2. }
    + tauto. }
  cbv beta; intros _.
  eapply Hoare_bind.
  { eapply Hoare_conj3.
    + eapply Hoare_conseq_pre.
      2: { apply remove_go_right_edge'_fact2. }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact3_l _ _ v). }
      tauto.
    + eapply Hoare_conseq_pre.
      2: { apply (remove_go_right_edge'_fact4_u _ _ lc_v). }
      tauto.
  }
  cbv beta; intros _.
  eapply Hoare_bind.
  { apply Hoare_choice.
    + apply Hoare_test_bind.
      eapply Hoare_bind.
      { eapply Hoare_conj5.
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
      }
      cbv beta; intros _.
      eapply Hoare_conj7.
      * eapply Hoare_conseq_pre.
        2: { apply remove_go_right_edge'_fact2. }
        tauto.
      * eapply Hoare_conseq_pre.
        2: { apply (remove_go_right_edge'_fact3_l _ _ v). }
        tauto.
      * eapply Hoare_conseq_pre.
        2: { apply (remove_go_right_edge'_fact3_r _ _ v). }
        tauto.
      * eapply Hoare_conseq_pre.
        2: { apply (remove_go_right_edge'_fact3_u _ _ v). }
        tauto.
      * eapply Hoare_conseq_pre.
        2: { apply (remove_go_right_edge'_fact4_u _ _ lc_v). }
        tauto.
      * eapply Hoare_conseq_pre.
        2: { apply (remove_go_right_edge'_fact4_u _ _ rc_v). }
        tauto.
      * eapply Hoare_conseq_pre.
        2: {
          Check remove_go_right_edge'_fact3_l.
           Check (remove_go_right_edge'_fact3_l _ _ fa).
           }
        tauto.
      
    }
  }
  cbv beta; intros _.
  
  }
  

Admitted.
  (* 
  - apply (remove_go_left_edge'_fact2 v lc_v). *)

  
  


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

