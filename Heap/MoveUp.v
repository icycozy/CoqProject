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

(* 上移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，变为堆
4. 保持满二叉树 *)

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

(* 有些条件多余 *)

Lemma L2: forall (x y: Z),
  ~ x <> y -> x = y.
Proof.
  intros. tauto.
Qed.

Lemma L3: forall (bt: BinTree Z Z) (x y1 y2: Z), 
  BinaryTree.legal bt ->
    BinaryTree.step_l bt x y1 ->
      BinaryTree.step_l bt x y2 ->
        y1 = y2.
Proof.
  intros.
  destruct H.
  pose proof step_l_unique x y1 y2 H0 H1.
  tauto.
Qed.

Lemma L3': forall (bt: BinTree Z Z) (x y1 y2: Z), 
  BinaryTree.legal bt ->
    BinaryTree.step_r bt x y1 ->
      BinaryTree.step_r bt x y2 ->
        y1 = y2.
Proof.
  intros.
  destruct H.
  pose proof step_r_unique x y1 y2 H0 H1.
  tauto.
Qed.

Lemma L3'': forall (bt: BinTree Z Z) (x y1 y2: Z), 
  BinaryTree.legal bt ->
    BinaryTree.step_u bt x y1 ->
      BinaryTree.step_u bt x y2 ->
        y1 = y2.
Proof.
  intros.
  destruct H.
  pose proof step_u_unique x y1 y2 H0 H1.
  tauto.
Qed.

Lemma L4: forall (x y: Z),
  x < y -> x = y -> False.
Proof. lia. Qed.

Lemma L5: forall (bt: BinTree Z Z) (v fa: Z), 
  BinaryTree.step_u bt v fa ->
    BinaryTree.step_l bt v fa ->
      False.
Admitted.

Lemma L5': forall (bt: BinTree Z Z) (v fa: Z), 
  BinaryTree.step_u bt v fa ->
    BinaryTree.step_r bt v fa ->
      False.
Admitted.

Lemma L5'': forall (bt: BinTree Z Z) (v fa: Z), 
  BinaryTree.step_u bt v fa ->
    BinaryTree.step_r bt v fa ->
      False.
Admitted.

Lemma L6: forall (bt: BinTree Z Z) (x y: Z), 
  BinaryTree.step_l bt x y ->
    ~ x = y.
Admitted.

Lemma L6': forall (bt: BinTree Z Z) (x y: Z), 
  BinaryTree.step_r bt x y ->
    ~ x = y.
Admitted.

Lemma L6'': forall (bt: BinTree Z Z) (x y: Z), 
  BinaryTree.step_u bt x y ->
    ~ x = y.
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
Proof.
  unfold Hoare; sets_unfold.
  unfold Abs.
  intros.
  destruct H as [? [[? [? [? ?]]] ?]].
  split.
  {
    unfold swap_v_u in H0.
    destruct H0 as [? _].
    apply H0. tauto.
  }
  split.
  {
    unfold swap_v_u in H0.
    destruct H0 as [? _].
    rewrite H0.
    tauto.
  }
  split.
  {
    split.
    {
      unfold swap_v_u in H0.
      intros.
      destruct H0 as [_ ?].
      pose proof (classic (~ x = v)).
      pose proof (classic (~ x = fa)).
      destruct H8, H9.
      {
        destruct H0 as [? _].
        specialize (H0 x H8 H9).
        pose proof (classic (~ y1 = v)).
        pose proof (classic (~ y1 = fa)).
        pose proof (classic (~ y2 = v)).
        pose proof (classic (~ y2 = fa)).
        destruct H10, H11, H12, H13.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10 H11.
          destruct H14 as [[? _] _].
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [[? _] _].
          apply H15 in H7.

          pose proof L3 s1.(heap) x y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [? [H0' _]].

          pose proof H0 y1 H10 H11.
          destruct H14 as [[? _] _].
          apply H14 in H6.

          destruct H0' as [[? _] _].
          pose proof L2 y2 fa H13.
          subst y2.
          apply H15 in H7.
          
          pose proof L3 s1.(heap) x y1 v H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [? [_ H0']].

          pose proof H0 y1 H10 H11.
          destruct H14 as [[? _] _].
          apply H14 in H6.

          destruct H0' as [[? _] _].
          pose proof L2 y2 v H12.
          subst y2.
          apply H15 in H7.

          pose proof L3 s1.(heap) x y1 fa H3 H6 H7.
          tauto.
        }
        {
          lia.
        }
        {
          destruct H0 as [? [H0' _]].

          destruct H0' as [[? _] _].
          pose proof L2 y1 fa H11.
          subst y1.
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [[? _] _].
          apply H15 in H7.
          
          pose proof L3 s1.(heap) x v y2 H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          destruct H0 as [_ [H0 H0']].

          destruct H0 as [[? _] _].
          pose proof L2 y1 fa H11.
          subst y1.
          apply H0 in H6.

          destruct H0' as [[? _] _].
          pose proof L2 y2 v H12.
          subst y2.
          apply H14 in H7.

          pose proof L3 s1.(heap) x v fa H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          destruct H0 as [H0 [_ H0']].

          destruct H0' as [[? _] _].
          pose proof L2 y1 v H10.
          subst y1.
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [[? _] _].
          apply H15 in H7.

          pose proof L3 s1.(heap) x fa y2 H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [_ [H0 H0']].

          destruct H0' as [[? _] _].
          pose proof L2 y1 v H10.
          subst y1.
          apply H14 in H6.

          destruct H0 as [[? _] _].
          pose proof L2 y2 fa H13.
          subst y2.
          apply H0 in H7.

          pose proof L3 s1.(heap) x fa v H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
      }
      {
        destruct H0 as [_ [? _]].
        pose proof L2 x fa H9.
        subst x.
        pose proof (classic (~ y1 = v)).
        pose proof (classic (~ y2 = v)).
        destruct H10, H11.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10.
          destruct H12 as [[? _] _].
          apply H12 in H6.

          pose proof H0 y2 H11.
          destruct H13 as [[? _] _].
          apply H13 in H7.

          pose proof L3 s1.(heap) v y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [_ ?].

          destruct H0 as [[? _] _].
          pose proof L2 y2 v H11.
          subst y2.
          apply H0 in H7.
          
          pose proof L5 s1.(heap) v fa H5 H7.
          tauto.
        }
        {
          destruct H0 as [_ ?].

          destruct H0 as [[? _] _].
          pose proof L2 y1 v H10.
          subst y1.
          apply H0 in H6.
          
          pose proof L5 s1.(heap) v fa H5 H6.
          tauto.
        }
        {
          lia.
        }
      }
      {
        destruct H0 as [_ [_ ?]].
        pose proof L2 x v H8.
        subst x.
        pose proof (classic (~ y1 = fa)).
        pose proof (classic (~ y2 = fa)).
        destruct H10, H11.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10.
          destruct H12 as [[? _] _].
          apply H12 in H6.

          pose proof H0 y2 H11.
          destruct H13 as [[? _] _].
          apply H13 in H7.

          pose proof L3 s1.(heap) fa y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [H0 H0'].

          pose proof L6 s2.(heap) v y1 H6.
          pose proof H0 y1 H10.
          destruct H13 as [[? _] _].
          apply H13 in H6.

          destruct H0' as [[? _] _].
          pose proof L2 y2 fa H11.
          subst y2.
          apply H14 in H7.
          
          pose proof L3 s1.(heap) fa y1 v H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [H0 H0'].

          destruct H0' as [[? _] _].
          pose proof L2 y1 fa H10.
          subst y1.
          apply H12 in H6.

          pose proof L6 s2.(heap) v y2 H7.
          pose proof H0 y2 H11.
          destruct H14 as [[? _] _].
          apply H14 in H7.   
          
          pose proof L3 s1.(heap) fa v y2 H3 H6 H7.
          lia.
        }
        {
          lia. 
        }
      }
      {
        lia.
      }
    }
    {
      unfold swap_v_u in H0.
      intros.
      destruct H0 as [_ ?].
      pose proof (classic (~ x = v)).
      pose proof (classic (~ x = fa)).
      destruct H8, H9.
      {
        destruct H0 as [? _].
        specialize (H0 x H8 H9).
        pose proof (classic (~ y1 = v)).
        pose proof (classic (~ y1 = fa)).
        pose proof (classic (~ y2 = v)).
        pose proof (classic (~ y2 = fa)).
        destruct H10, H11, H12, H13.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10 H11.
          destruct H14 as [_ [? _]].
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [_ [? _]].
          apply H15 in H7.

          pose proof L3' s1.(heap) x y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [? [H0' _]].

          pose proof H0 y1 H10 H11.
          destruct H14 as [_ [? _]].
          apply H14 in H6.

          destruct H0' as [_ [? _]].
          pose proof L2 y2 fa H13.
          subst y2.
          apply H15 in H7.
          
          pose proof L3' s1.(heap) x y1 v H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [? [_ H0']].

          pose proof H0 y1 H10 H11.
          destruct H14 as [_ [? _]].
          apply H14 in H6.

          destruct H0' as [_ [? _]].
          pose proof L2 y2 v H12.
          subst y2.
          apply H15 in H7.

          pose proof L3' s1.(heap) x y1 fa H3 H6 H7.
          tauto.
        }
        {
          lia.
        }
        {
          destruct H0 as [? [H0' _]].

          destruct H0' as [_ [? _]].
          pose proof L2 y1 fa H11.
          subst y1.
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [_ [? _]].
          apply H15 in H7.
          
          pose proof L3' s1.(heap) x v y2 H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          destruct H0 as [_ [H0 H0']].

          destruct H0 as [_ [? _]].
          pose proof L2 y1 fa H11.
          subst y1.
          apply H0 in H6.

          destruct H0' as [_ [? _]].
          pose proof L2 y2 v H12.
          subst y2.
          apply H14 in H7.

          pose proof L3' s1.(heap) x v fa H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          destruct H0 as [H0 [_ H0']].

          destruct H0' as [_ [? _]].
          pose proof L2 y1 v H10.
          subst y1.
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [_ [? _]].
          apply H15 in H7.

          pose proof L3' s1.(heap) x fa y2 H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [_ [H0 H0']].

          destruct H0' as [_ [? _]].
          pose proof L2 y1 v H10.
          subst y1.
          apply H14 in H6.

          destruct H0 as [_ [? _]].
          pose proof L2 y2 fa H13.
          subst y2.
          apply H0 in H7.

          pose proof L3' s1.(heap) x fa v H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
      }
      {
        destruct H0 as [_ [? _]].
        pose proof L2 x fa H9.
        subst x.
        pose proof (classic (~ y1 = v)).
        pose proof (classic (~ y2 = v)).
        destruct H10, H11.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10.
          destruct H12 as [_ [? _]].
          apply H12 in H6.

          pose proof H0 y2 H11.
          destruct H13 as [_ [? _]].
          apply H13 in H7.

          pose proof L3' s1.(heap) v y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [_ ?].

          destruct H0 as [_ [? _]].
          pose proof L2 y2 v H11.
          subst y2.
          apply H0 in H7.
          
          pose proof L5' s1.(heap) v fa H5 H7.
          tauto.
        }
        {
          destruct H0 as [_ ?].

          destruct H0 as [_ [? _]].
          pose proof L2 y1 v H10.
          subst y1.
          apply H0 in H6.
          
          pose proof L5' s1.(heap) v fa H5 H6.
          tauto.
        }
        {
          lia.
        }
      }
      {
        destruct H0 as [_ [_ ?]].
        pose proof L2 x v H8.
        subst x.
        pose proof (classic (~ y1 = fa)).
        pose proof (classic (~ y2 = fa)).
        destruct H10, H11.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10.
          destruct H12 as [_ [? _]].
          apply H12 in H6.

          pose proof H0 y2 H11.
          destruct H13 as [_ [? _]].
          apply H13 in H7.

          pose proof L3' s1.(heap) fa y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [H0 H0'].

          pose proof L6' s2.(heap) v y1 H6.
          pose proof H0 y1 H10.
          destruct H13 as [_ [? _]].
          apply H13 in H6.

          destruct H0' as [_ [? _]].
          pose proof L2 y2 fa H11.
          subst y2.
          apply H14 in H7.
          
          pose proof L3' s1.(heap) fa y1 v H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [H0 H0'].

          destruct H0' as [_ [? _]].
          pose proof L2 y1 fa H10.
          subst y1.
          apply H12 in H6.

          pose proof L6' s2.(heap) v y2 H7.
          pose proof H0 y2 H11.
          destruct H14 as [_ [? _]].
          apply H14 in H7.   
          
          pose proof L3' s1.(heap) fa v y2 H3 H6 H7.
          lia.
        }
        {
          lia. 
        }
      }
      {
        lia.
      }
    }
    {
      unfold swap_v_u in H0.
      intros.
      destruct H0 as [_ ?].
      pose proof (classic (~ x = v)).
      pose proof (classic (~ x = fa)).
      destruct H8, H9.
      {
        destruct H0 as [? _].
        specialize (H0 x H8 H9).
        pose proof (classic (~ y1 = v)).
        pose proof (classic (~ y1 = fa)).
        pose proof (classic (~ y2 = v)).
        pose proof (classic (~ y2 = fa)).
        destruct H10, H11, H12, H13.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10 H11.
          destruct H14 as [_ [_ ?]].
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [_ [_ ?]].
          apply H15 in H7.

          pose proof L3'' s1.(heap) x y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [? [H0' _]].

          pose proof H0 y1 H10 H11.
          destruct H14 as [_ [_ ?]].
          apply H14 in H6.

          destruct H0' as [_ [_ ?]].
          pose proof L2 y2 fa H13.
          subst y2.
          apply H15 in H7.
          
          pose proof L3'' s1.(heap) x y1 v H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [? [_ H0']].

          pose proof H0 y1 H10 H11.
          destruct H14 as [_ [_ ?]].
          apply H14 in H6.

          destruct H0' as [_ [_ ?]].
          pose proof L2 y2 v H12.
          subst y2.
          apply H15 in H7.

          pose proof L3'' s1.(heap) x y1 fa H3 H6 H7.
          tauto.
        }
        {
          lia.
        }
        {
          destruct H0 as [? [H0' _]].

          destruct H0' as [_ [_ ?]].
          pose proof L2 y1 fa H11.
          subst y1.
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [_ [_ ?]].
          apply H15 in H7.
          
          pose proof L3'' s1.(heap) x v y2 H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          destruct H0 as [_ [H0 H0']].

          destruct H0 as [_ [_ ?]].
          pose proof L2 y1 fa H11.
          subst y1.
          apply H0 in H6.

          destruct H0' as [_ [_ ?]].
          pose proof L2 y2 v H12.
          subst y2.
          apply H14 in H7.

          pose proof L3'' s1.(heap) x v fa H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          destruct H0 as [H0 [_ H0']].

          destruct H0' as [_ [_ ?]].
          pose proof L2 y1 v H10.
          subst y1.
          apply H14 in H6.

          pose proof H0 y2 H12 H13.
          destruct H15 as [_ [_ ?]].
          apply H15 in H7.

          pose proof L3'' s1.(heap) x fa y2 H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [_ [H0 H0']].

          destruct H0' as [_ [_ ?]].
          pose proof L2 y1 v H10.
          subst y1.
          apply H14 in H6.

          destruct H0 as [_ [_ ?]].
          pose proof L2 y2 fa H13.
          subst y2.
          apply H0 in H7.

          pose proof L3'' s1.(heap) x fa v H3 H6 H7.
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
        {
          lia.
        }
      }
      {
        destruct H0 as [_ [? _]].
        pose proof L2 x fa H9.
        subst x.
        pose proof (classic (~ y1 = v)).
        pose proof (classic (~ y2 = v)).
        destruct H10, H11.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10.
          destruct H12 as [_ [_ ?]].
          apply H12 in H6.

          pose proof H0 y2 H11.
          destruct H13 as [_ [_ ?]].
          apply H13 in H7.

          pose proof L3'' s1.(heap) v y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [H0 H0'].

          pose proof L6'' s2.(heap) fa y1 H6.
          pose proof H0 y1 H10.
          destruct H13 as [_ [_ ?]].
          apply H13 in H6.

          destruct H0' as [_ [_ ?]].
          pose proof L2 y2 v H11.
          subst y2.
          apply H14 in H7.
          
          pose proof L3'' s1.(heap) v y1 fa H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [H0 H0'].

          destruct H0' as [_ [_ ?]].
          pose proof L2 y1 v H10.
          subst y1.
          apply H12 in H6.

          pose proof L6'' s2.(heap) fa y2 H7.
          pose proof H0 y2 H11.
          destruct H14 as [_ [_ ?]].
          apply H14 in H7.

          pose proof L3'' s1.(heap) v fa y2 H3 H6 H7.
          lia.
        }
        {
          lia.
        }
      }
      {
        destruct H0 as [_ [_ ?]].
        pose proof L2 x v H8.
        subst x.
        pose proof (classic (~ y1 = fa)).
        pose proof (classic (~ y2 = fa)).
        destruct H10, H11.
        {
          destruct H0 as [? _].

          pose proof H0 y1 H10.
          destruct H12 as [_ [_ ?]].
          apply H12 in H6.

          pose proof H0 y2 H11.
          destruct H13 as [_ [_ ?]].
          apply H13 in H7.

          pose proof L3'' s1.(heap) fa y1 y2 H3 H6 H7.
          tauto.
        }
        {
          destruct H0 as [H0 H0'].

          pose proof L6'' s2.(heap) v y1 H6.
          pose proof H0 y1 H10.
          destruct H13 as [_ [_ ?]].
          apply H13 in H6.

          destruct H0' as [_ [_ ?]].
          pose proof L2 y2 fa H11.
          subst y2.
          apply H14 in H7.
          
          pose proof L3'' s1.(heap) fa y1 v H3 H6 H7.
          lia.
        }
        {
          destruct H0 as [H0 H0'].

          destruct H0' as [_ [_ ?]].
          pose proof L2 y1 fa H10.
          subst y1.
          apply H12 in H6.

          pose proof L6'' s2.(heap) v y2 H7.
          pose proof H0 y2 H11.
          destruct H14 as [_ [_ ?]].
          apply H14 in H7.   
          
          pose proof L3'' s1.(heap) fa v y2 H3 H6 H7.
          lia.
        }
        {
          lia. 
        }
      }
      {
        lia.
      }
    }
  }
Admitted.



Lemma L1: forall (x y: Z),
  x < y -> x > y -> False.
Admitted.

Theorem move_up_correctness1: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap s.(heap) \/ Heap_broken_up s.(heap) v))
        (move_up v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Proof.
  intros. revert v.
  unfold move_up.
  apply Hoare_repeat_break.
  intros v.
  unfold body_move_up.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    apply Hoare_ret'.
    intros.
    destruct H as [[? ?] [? [? [? ?]]]].
    split; [apply H2|].
    split; [apply H3|].
    destruct H4; [apply H4|].
    destruct H4.
    destruct up_fa_v_lc_rc as [fa ?].
    assert (exists fa : Z, BinaryTree.step_u s.(heap) v fa).
    { exists fa; apply H4. }
    tauto. 
  - eapply Hoare_bind; [apply get_fa_fact| cbv beta].
    intros fa.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      destruct H as [? [[? [? [? ?]]] ?]].
      split; [apply H1|].
      split; [apply H2|].
      destruct H3; [apply H3|].
      destruct H3.
      destruct up_fa_v_lc_rc as [fa' [? [? _]]].
      assert (fa = fa').
      { pose proof (BinaryTree.step_u_unique s.(heap) H2 v fa fa' H4 H3). tauto. }
      subst fa'.
      pose proof (L1 v fa H5 H). tauto.
    + apply Hoare_test_bind.
      eapply Hoare_bind; [apply (swap_v_fa_fact1 v fa V)| cbv beta; intros _].
      apply Hoare_ret'.
      intros.
      destruct H as [? [? [? ?]]].
      split; [apply H|].
      split; [apply H0|].
      split; [apply H1|].
      apply H2.
Qed.

(* 有些条件多余 *)

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

Theorem move_up_correctness2: forall (v: Z),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (move_up v)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros. revert v.
  unfold move_up.
  apply Hoare_repeat_break.
  intros v.
  unfold body_move_up.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    apply Hoare_ret'.
    intros.
    tauto.
  - eapply Hoare_bind; [apply get_fa_fact| cbv beta].
    intros fa.
    apply Hoare_choice.
    + apply Hoare_test_bind.
      apply Hoare_ret'.
      intros.
      tauto.
    + apply Hoare_test_bind.
      eapply Hoare_bind; [apply (swap_v_fa_fact2 v fa)| cbv beta; intros _].
      apply Hoare_ret'.
      intros.
      apply H.
Qed.