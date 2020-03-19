Inductive bool: Type :=
  |true
  |false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Definition nandb (b1:bool) (b2:bool): bool := negb (andb b1 b2).
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1: bool) (b2: bool) (b3: bool): bool := andb (andb b1 b2) b3. 

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (1, 2, 3, 4, 5).




Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.


Check (S (S O)).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Compute (evenb 4).


Fixpoint factorial (n:nat):nat :=
  match n with
  | 0 => 1
  | S n => (S n) * factorial n
  end.

Compute factorial 8.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Definition ltb (n m : nat) : bool :=
  match minus n m with
  | 0 => match minus m n with
          | 0 => false
          | _ =>true
          end
  | _ => false
  end.


Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.


Theorem plus_id_example: forall m n:nat,
  n = m -> n + n = m + m.

Proof.
  intros m n.
  intros H.
  rewrite <- H.
  reflexivity. Qed.


Theorem plus_id_exercise: forall n m o: nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  intros H1.
  rewrite -> H1.
  reflexivity. Qed.

Require Import Arith.
Check mult_n_O.  (* forall n : nat, 0 = n * 0 *)
Check mult_n_Sm. (* forall n m : nat, n * m + n = n * S m *)

  
Theorem mult_n_1: forall n: nat,
  n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.










