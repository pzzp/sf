Theorem plus_n_0 : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [|n' IHn'].
    - reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.


Theorem mult_0_r: forall n: nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' iH].
  - reflexivity.
  - simpl. rewrite -> iH. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m: nat,
  S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n' iHn].
  - reflexivity.
  - simpl. rewrite -> iHn. reflexivity.
Qed.



Theorem plus_comm: forall a b: nat,
  a + b = b + a.
Proof.
  intros a b.
  induction a as [|a' iha'].
  - simpl.
    induction b as [| b' ihb'].
    * reflexivity.
    * simpl. rewrite <- ihb'. reflexivity.
  - simpl. rewrite -> iha'. rewrite <- plus_n_Sm. reflexivity.
Qed.


Theorem plus_assoc: forall a b c: nat,
  a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  induction a as [| a' iha'].
  - reflexivity.
  - simpl. rewrite <- iha'. reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall (n:nat), double n = n + n.
Proof.
  intros n.
  induction n as [|n' ihn'].
  - reflexivity.
  - rewrite <- plus_n_Sm. simpl. rewrite -> ihn'. reflexivity.
Qed.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.


Theorem negb2: forall b: bool,
  negb (negb b) = b.
Proof.
  intros [].
  reflexivity.
  reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
Proof.
  intros n.
  induction n as [|n' ihn'].
  - reflexivity.
  - rewrite -> ihn'. simpl. rewrite -> negb2. reflexivity.
Qed.

Theorem plus_swap: forall n m p: nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). rewrite <- plus_comm. reflexivity.
  rewrite -> H.
  reflexivity.
Qed.


Lemma mult_n_0: forall a, a * 0 = 0.
Proof.
  intros a.
  induction a as [|a' iHa'].
  - reflexivity.
  - simpl. rewrite -> iHa'. reflexivity.
Qed.

Lemma mult_n_1: forall a, a * 1 = a.
Proof.
  intros a.
  induction a as [|a' iHa'].
  - reflexivity.
  - simpl. rewrite -> iHa'. reflexivity.
Qed.

(*
Fixpoint mul n m :=
  match n with
  | 0 => 0
  | S p => m + p * m
  end
*)

Lemma mult_n_Sm: forall n m, n * S m = n + n * m.
Proof.
  intros m n.
  induction m as [| m' iHm'].
  - reflexivity.
  - simpl. rewrite -> iHm'. 
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    assert (H: n + m' = m' + n). rewrite -> plus_comm. reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

Theorem mult_comm: forall m n, m * n = n * m.
Proof.
  intros m n.
  induction m as [| m' iHm'].
  - rewrite -> mult_n_0. reflexivity.
  - simpl.
    rewrite -> iHm'.
    rewrite <- mult_n_Sm.
    reflexivity.
Qed.

Require Import Arith.
Check leb.

Theorem leb_refl: forall n:nat,
  true = (n <=? n).
Proof.
  intros n.
  induction n as [| n' iHn'].
  - reflexivity.
  - simpl. rewrite <- iHn'. reflexivity.
Qed.


Theorem zero_nbeq_S: forall n: nat,
  0 =? S n = false.
Proof.
  intros n.
  induction n as [| n' iHn'].
  - reflexivity.
  - reflexivity.
Qed.


Theorem and_false_r: forall b: bool,
  andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_1: forall n m p: nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  induction p as [|p iHp'].
  - rewrite -> plus_comm. 
    rewrite <- plus_n_0.
    rewrite -> plus_comm.
    rewrite <- plus_n_0.
    rewrite -> H.
    reflexivity.
  - simpl.
    rewrite -> iHp'.
    reflexivity.
Qed.

Theorem S_nbeq_0: forall n,
  S n =? 0 = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_1_1: forall n,
  1 * n = n.
Proof.
  simpl. 
  intros n.
  rewrite <- plus_n_0.
  reflexivity.
Qed.



Theorem all3_spec: forall b c: bool,
  orb
    (andb b c)
    (orb (negb b) (negb c))
  = true.

Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Theorem plus_eq_del: forall a b c:nat,
  b = c -> a + b = a + c.
Proof.
  intros a b c H.
  induction a as [|a' iHa'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> iHa'. reflexivity.
Qed.


Theorem mult_plus__distr_r: forall a b c,
  (a + b) * c = (a * c) + (b * c).
Proof.
  intros a b c.
  induction c as [| c' iHc'].
  - simpl.
    rewrite -> mult_n_0.
    rewrite -> mult_n_0.
    rewrite -> mult_n_0.
    reflexivity.
  - assert (H: forall x y, x * S y = S y * x). 
      intros x y. 
      rewrite -> mult_comm.
      reflexivity.
    rewrite -> H. rewrite -> H. rewrite -> H.
    simpl. rewrite <- plus_assoc. rewrite <- plus_assoc.
    assert (H1: b + c' * (a + b) = c' * a + (b + c' * b)).
      rewrite -> plus_swap.
      rewrite -> mult_comm.
      rewrite -> iHc'.
      rewrite -> mult_comm.
      assert (H2: b * c' = c' * b). rewrite -> mult_comm. reflexivity.
      rewrite -> H2.
      reflexivity.
    rewrite -> H1.
    reflexivity.
Qed.


Theorem mult_assoc: forall a b c,
  a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  induction a as [| a' iHa'].
  - reflexivity.
  - simpl.
    rewrite -> iHa'.
    rewrite -> mult_plus__distr_r.
    reflexivity.
Qed.

Theorem eqb_refl: forall n: nat,
  true = (n =? n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.


Theorem plus_swap' : forall n m p: nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite -> plus_comm.
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


Theorem bin_to_nat_pres_incr: forall x: bin,
  bin_to_nat (incr x) = S (bin_to_nat x).
Proof.
  intros x.
  induction x as [|xa iHxa|xb iHxb].
  - reflexivity.
  - simpl. replace (bin_to_nat xa + 0) with (bin_to_nat xa). reflexivity.
    rewrite <- plus_n_0.
    reflexivity.
  - simpl.
    replace (bin_to_nat xb + 0) with (bin_to_nat xb).
    replace ((bin_to_nat (incr xb)) + 0) with (bin_to_nat (incr xb)).
    rewrite -> iHxb.
    simpl.
    assert (H: forall a b, a + S b = S (a + b)).
      intros a b.
      induction a as [| a' iHa'].
      reflexivity.
      simpl. rewrite -> iHa'. reflexivity.
    rewrite -> H. reflexivity.
    rewrite <- plus_n_0. reflexivity.
    rewrite <- plus_n_0. reflexivity.
Qed.

Check true.

Compute (S 1) / 2.



    

