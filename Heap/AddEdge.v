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

Fact add_go_left_edge_fact1: forall (v lc: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V)
        (add_go_left_edge v lc)
        (fun _ s => Abs s.(heap) V).
Admitted.

Fact add_go_left_edge_fact2: forall (v lc: Z),
  Hoare (fun s => BinaryTree.legal s.(heap) /\ 
                  ~ (exists x, BinaryTree.step_l s.(heap) v x) /\ 
                  ~ (exists x, BinaryTree.step_u s.(heap) lc x))
        (add_go_left_edge v lc)
        (fun _ s => BinaryTree.legal s.(heap)).
Admitted.

Fact add_go_right_edge_fact1: forall (v rc: Z) (V: Z -> Prop),
  Hoare (fun s => Abs s.(heap) V)
        (add_go_right_edge v rc)
        (fun _ s => Abs s.(heap) V).
Admitted.

Fact add_go_right_edge_fact2: forall (v rc: Z),
  Hoare (fun s => BinaryTree.legal s.(heap) /\ 
                  ~ (exists x, BinaryTree.step_r s.(heap) v x) /\ 
                  ~ (exists x, BinaryTree.step_u s.(heap) rc x))
        (add_go_right_edge v rc)
        (fun _ s => BinaryTree.legal s.(heap)).
Admitted.

