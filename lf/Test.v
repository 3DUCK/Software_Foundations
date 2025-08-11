Require Import Arith. (* plus_n_O 정리 포함 *)

Theorem test_add_zero : forall n:nat, n + 0 = n.
Proof.
  intros.
  rewrite <- plus_n_O.
  reflexivity.
Qed.
