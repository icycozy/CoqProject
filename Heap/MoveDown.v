Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import PL.Monad.
Require Import PL.Monad2.
Require Import SetsClass.
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

(* 下移节点操作正确性：
1. 集合不变
2. 保持二叉树合法性
3. 从堆或局部破坏的堆开始，最终恢复堆性质
4. 保持满二叉树 *)

Theorem move_down_correctness1: forall (v: Z) (V: Z -> Prop),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  Abs s.(heap) V /\
                  BinaryTree.legal s.(heap) /\
                  (Heap_broken_down s.(heap) v \/ Heap s.(heap)))
        (move_down v)
        (fun _ s => Abs s.(heap) V /\
                    BinaryTree.legal s.(heap) /\
                    Heap s.(heap)).
Admitted.

Theorem move_down_correctness2: forall (v: Z),
  Hoare (fun s => s.(heap).(vvalid) v /\
                  BinaryTree.legal s.(heap) /\
                  is_complete_or_full_bintree s.(heap))
        (move_down v)
        (fun _ s => is_complete_or_full_bintree s.(heap)).
Admitted.
