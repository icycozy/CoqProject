Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
Require Import HEAP.Defs.
Require Import HEAP.MoveDown.
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

(* 删除节点操作正确性（保证根不是叶子）：
1. 最小值被删除
2. 保持二叉树合法性
3. 从堆开始，变为局部破坏的堆或堆
4. 保持满二叉树 *)

Theorem ext_delete_node_correctness1: forall (val: Z) (V: Z -> Prop),
  Hoare (fun s => ((exists lc: Z, BinaryTree.step_l s.(heap) val lc) \/
                        (exists rc: Z, BinaryTree.step_r s.(heap) val rc)) /\
                  Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  Heap s.(heap) /\ 
                  s.(heap).(vvalid) val)
        (ext_delete_node val)
        (fun _ s => (s.(heap).(vvalid) ∪ Sets.singleton val) == V /\
                    is_minimum val V /\
                    BinaryTree.legal s.(heap) /\
                    (Heap_broken_down s.(heap) val \/ Heap s.(heap))).
Admitted.

(* Theorem delete_iso_node_correctness1 *)


(* 删除操作正确性（保证非空的前提下（似乎没用））：
1. 删除的元素是最小值
2. 保持二叉树合法性
3. 保持堆性质 *)

Theorem delete_correctness1: forall (V: Z -> Prop), ~ V == ∅ ->
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
  intros v.
  apply Hoare_choice.
  - apply Hoare_test_bind.
    (* eapply Hoare_bind; [apply delete_iso_node_correctness1| cbv beta]. *)
    admit.
  - apply Hoare_test_bind.
    revert v.
    (* eapply Hoare_bind; [apply ext_delete_node_correctness1| cbv beta].
     *)
    
Admitted.