Require Import Coq.Arith.Arith.

Theorem mul_0_r : forall n:nat,

n * 0 = 0.

Proof.

intros n.

 induction n as [| n' IHn].

 - simpl. reflexivity.

 - simpl. rewrite -> IHn. reflexivity.

Qed.





Theorem plus_n_Sm : forall n m : nat,

 S (n + m) = n + (S m).

Proof.

 intros n m.

 induction n as [| n' IHn].

 - simpl. reflexivity.
 - simpl. rewrite -> IHn. reflexivity.

Qed.



Theorem add_0_r : forall n:nat, n + 0 = n.

Proof.

 intros n. induction n as [| n' IHn'].

 - (* n = 0 *) reflexivity.

 - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.





Theorem add_comm : forall n m : nat,

 n + m = m + n.

Proof.

 intros n m.

 induction n as [| n' IHn].

 - simpl. rewrite -> add_0_r. reflexivity.

 - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.

Qed.









Theorem add_assoc : forall n m p : nat,

 n + (m + p) = (n + m) + p.

Proof.

 intros n m p.

 induction n as [| n' IHn].

 - simpl. reflexivity.

 - simpl. rewrite -> IHn. reflexivity.

Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [| n' IHn].
  -
  simpl.
  reflexivity.
  -
  simpl.
  rewrite -> IHn.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.


Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn].
  -
  simpl.
  reflexivity.
  -
  simpl.
  rewrite -> IHn.
  reflexivity.
    

  

  

  
  

  