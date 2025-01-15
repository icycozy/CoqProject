Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.MoveDown.
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

(* to be added *)
(* Theorem delete_node_correctness *)



(* 删除操作正确性（保证非空的前提下（似乎没用））：
1. 删除的元素是最小值
2. 保持二叉树合法性
3. 保持堆性质 *)

Theorem delete_correctness: forall (V: Z -> Prop), ~ V == ∅ ->
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
  eapply Hoare_bind; [apply get_minimum_correctness| cbv beta].
  intros rt.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    
Admitted.