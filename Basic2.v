Require Import Nat.
Theorem plus_1_neq_0: forall n: nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
Qed.

Check negb.

Theorem negb_involutive: forall b: bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2: forall b c: bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
    - reflexivity.
    - rewrite <- H.
  destruct b.
    * reflexivity.
    * reflexivity.
Qed.

Theorem zero_nbeq_plus_1: forall n: nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n'].
  reflexivity.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice:
  forall (f: bool->bool),
  (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f H [].
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem neg_fn_applied_twice:
  forall (f: bool->bool),
  (forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f H [].
  rewrite -> H.
  rewrite -> H.
  reflexivity.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Lemma andb_true: forall (b: bool), andb b true = b.
Proof.
  intros [].
  reflexivity.
  reflexivity.
Qed.

Lemma andb_false: forall (b: bool), andb b false = false.
Proof.
  intros [].
  reflexivity.
  reflexivity.
Qed.

Lemma orb_true: forall (b:bool), orb b true = true.
Proof.
  intros [].
  reflexivity.
  reflexivity.
Qed.

Lemma orb_false: forall (b: bool), orb b false = b.
Proof.
  intros [].
  reflexivity.
  reflexivity.
Qed.

Theorem andb_eq_orb:
  forall (b c: bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct c.
  rewrite -> andb_true.
  rewrite -> orb_true.
  intros H.
  rewrite -> H.
  reflexivity.
  rewrite -> andb_false.
  rewrite -> orb_false.
  intros H1.
  rewrite -> H1.
  reflexivity.
Qed.


Inductive bin: Type :=
  | Z
  | A (n: bin)
  | B (n: bin).

Fixpoint incr (m:bin):bin :=
  match m with
  | Z => B Z
  | A n => B n
  | B n => A (incr n)
  end.

Fixpoint bin_to_nat (m: bin): nat :=
  match m with
  | Z => 0
  | A n => 2 * bin_to_nat n
  | B n => 1 + 2 * bin_to_nat n
  end.

Compute bin_to_nat (incr (A (A (A (A (B Z)))))).

Example test_bin_incr1 : (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (A (B Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
