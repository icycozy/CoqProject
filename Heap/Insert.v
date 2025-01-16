Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.MoveUp.
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

(* 插入节点操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

Theorem ext_insert_node_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        (ext_insert_node val)
        (fun _ s =>
                    Abs s.(heap) (V ∪ Sets.singleton val) /\
                    BinaryTree.legal s.(heap) /\
                    (Heap_broken_up s.(heap) val \/ Heap s.(heap))).
Proof.
  intros val V.
  unfold ext_insert_node.
  unfold Hoare, Abs; sets_unfold.
  intros.
  destruct H as [? [? [? ?]]].
  destruct H0 as [? [? [? ?]]].
  split; [| split; [tauto | tauto]].
  intros.
  rewrite H.
  rewrite <- H0.
  reflexivity.
Qed. 

Theorem ext_insert_node_correctness2: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (ext_insert_node val)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton val) /\
                    BinaryTree.legal s.(heap) /\
                    is_complete_or_full_bintree s.(heap)).
Proof.
  intros val V.
  unfold ext_insert_node.
  unfold Hoare, Abs; sets_unfold.
  intros.
  destruct H as [? [? [? ?]]].
  destruct H0 as [? [? [? ?]]].
  split; [| split; [tauto | tauto]].
  intros.
  rewrite H.
  rewrite <- H0.
  reflexivity.
Qed. 


(* 插入操作正确性：
1. val不在堆中，插入后在堆中
2. 保持二叉树合法性
3. 保持堆性质
4. 保持满二叉树 *)


Theorem insert_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap))
        (insert val)
        (fun _ s => Abs s.(heap) (V ∪ Sets.singleton val) /\ 
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Proof.
  intros val V.
  unfold insert.
  eapply Hoare_bind; [apply ext_insert_node_correctness1| cbv beta].
  intros.
  apply move_up_helper1.
Qed.  

Theorem insert_correctness2: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V /\
                  ~ s.(heap).(vvalid) val /\ 
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (insert val)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Proof.
  intros val V.
  unfold insert.
  eapply Hoare_bind; [apply ext_insert_node_correctness2| cbv beta].
  intros.
  apply move_up_helper2.
Qed.
