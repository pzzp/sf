Require Import Poly.
Require Import Arith.
Require Import Nat.

Theorem silly1: forall (n m o p: nat),
  n=m -> [n;o]=[n;p] -> [n;o]=[m;p].
Proof. 
  intros n m o p eq1 eq2. 
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2: forall (n m o p: nat),
  n = m -> (n = m -> [n; o] = [m; p]) -> [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.
  

Theorem  silly2a: forall (n m: nat),
  (n, n) = (m, m) -> 
  (forall (q r: nat), (q, q) = (r, r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.


Theorem silly_ex:
  (forall n, even n = true -> odd (S n) = true ) ->
  even 4 = true ->
  odd 3 = true.
Proof.
  intros p1 p2.
  apply p2.
Qed.

Theorem  silly3: forall (n: nat), true = (n =? 5) -> (S (S n)) =? 7 = true.
Proof.
  intros n eq1.
  symmetry.
  apply eq1.
Qed.



Theorem rev_exercise1: forall (a b: list nat),
  a = rev b -> b = rev a.
Proof.
  intros a b P.
  rewrite -> P.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example: forall (a b c d e f: nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq: forall (X:Type) (n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Example trans_eq_example': forall (a b c d e f: nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].

Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m :=[c;d]).
  apply eq1. apply eq2.
Qed.

Definition minustwo := fun x:nat => x - 2.

Example trans_eq_exercise: forall (n m o p: nat),
  m = (minustwo o ) ->
  n + p = m ->
  n + p = (minustwo o).
Proof.
  intros n m o p P1 P2.
  apply trans_eq with (m).
  apply P2. apply P1.
Qed.

Theorem  S_injective: forall (n m: nat),
  S n = S m -> n = m.
Proof.
  intros n m E.
  assert (H: n = pred (S n)). { reflexivity. }
  rewrite -> H. rewrite E. reflexivity.
Qed.

Theorem  S_injective': forall (n m: nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1: forall(n m o: nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Example injection_ex3: forall (X: Type) (x y z: X) (a b: list X),
  x::y::a = z::b ->
  b = z::a ->
  x = y.
Proof.
  intros X x y z a b H1.
  injection H1 as H1' H2'.
  rewrite -> H1'. rewrite <- H2'.
  intros H2.
  injection H2 as H2''. symmetry. apply H2''.
Qed.

Theorem eqb_0_1: forall n,
  0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as[| n'].
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.
  
Theorem discrimination_ex1: forall (n: nat),
  S n = 0 -> 2 + 2 = 5.
Proof.
  intros n contra. 
  discriminate contra.
Qed.


Example discriminate_ex3: 
  forall (X: Type) (x y z: X) (l j: list X),
    x::y::l = [] -> x = z.
Proof.
  intros X x y z l j H.
  discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal.
  apply H.
Qed.

Theorem S_inj: forall (n m: nat) (b: bool),
  S n =? S m = b -> 
  n =? m = b.
Proof.
  intros n m b H.
  simpl in H. apply H.
Qed.

Theorem silly3': forall (n: nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = (S (S n) =? 7).
Proof.
  intros n H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry.
  apply H2.
Qed.

Theorem eqb_true: forall n m, n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [|n' iHn'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [| m'].
    + discriminate H.
    + apply f_equal.
      apply iHn'.
      apply H.
Qed.


Check plus_n_Sm.
      
Theorem plus_n_n_injective: forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n' iHn'].
  - intros m H. simpl in H. destruct m as [| m'].
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [| m'].
    + discriminate H.
    + apply f_equal.
      apply iHn'.
      injection H as H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H.
      apply H.
Qed.


Theorem nth_error_after_last: forall (n: nat) (X: Type) (l: list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|h t H].
  - intros n. destruct n as [| n'].
    + intros H'. reflexivity.
    + intros H'. discriminate H'.
  - intros n.  destruct n as [|n'].
    + intros H'. discriminate H'.
    + intros H'. 
      apply H.
      injection H' as H'.
      apply H'.
Qed.

Definition square n := n * n.

Lemma square_mult: forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite -> mult_assoc. rewrite -> mult_assoc.
  assert (H: n * m * n = n * n * m).
    { rewrite mult_comm. rewrite mult_assoc. reflexivity. }
  rewrite H. reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2: forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m as [|m'].
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n: nat): bool :=
  if n =? 3 
  then false
  else if n =? 5
       then false
       else false.
Fact sillyfun_false: forall (n: nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n=?3).
  - reflexivity.
  - destruct (n=?5).
    + reflexivity.
    + reflexivity.
Qed.



    


Theorem bool_fn_applied_thrice:
  forall (f: bool->bool) (b: bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn: H.
  - destruct b eqn: H1.
    + rewrite H. apply H.
    + destruct (f true) eqn: H12.
      * apply H12.
      * apply H.
  - destruct b eqn: H2.
    + destruct (f false) eqn: H21.
      * apply H.
      * apply H21.
    + rewrite H. apply H.
Qed.

Theorem eqb_sym: forall (n m: nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [|n' iHn'].
  - intros m.
    destruct m as [|m'] eqn: E1.
    * reflexivity.
    * reflexivity.
  - destruct m as [|m'] eqn: E2.
    * reflexivity.
    * simpl. apply iHn'.
Qed.
 
Lemma eqb_eq: forall a b,
  a =? b = true -> a = b.
Proof.
  intros a.
  induction a as [|a' iHa'].
  - destruct b as [|b'] eqn: E1.
    * reflexivity.
    * simpl. intros H. discriminate H.
  - destruct b as [|b'] eqn: E2.
    * simpl. intros H. discriminate H.
    * simpl. intros H. apply iHa' in H.
      apply f_equal. apply H.
Qed.

Lemma eq_eqb: forall a b,
  a = b -> a =? b = true.
Proof.
  intros a.
  induction a as [|a' iHa'].
  - destruct b as [|b'] eqn: E1.
    * reflexivity.
    * simpl. intros H. discriminate H.
  - destruct b as [|b'] eqn: E2.
    * simpl. intros H. discriminate H.
    * simpl. intros H. injection H as H.
      apply iHa'. apply H.
Qed.
  
  
Theorem eqb_trans: forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p eqb1 eqb2.
  apply eqb_eq in eqb1.
  apply eqb_eq in eqb2.
  apply eq_eqb.
  apply trans_eq with (m).
  - apply eqb1.
  - apply eqb2.
Qed.


Theorem combine_split: forall X Y (a: list (X * Y)) a1 a2,
  split a = (a1, a2) ->
  combine a1 a2 = a.
Proof.
  intros X Y a.
  induction a as [|[x y] t iHa].
  - intros a1 a2 H. injection H as H1 H2. rewrite <- H1. rewrite <- H2. reflexivity.
  - simpl. destruct (split t) as [l1 l2].
    * intros a1 a2 H. injection H as H1 H2.
      rewrite <- H1. rewrite <- H2.
      simpl. apply f_equal.
      apply iHa.
      reflexivity. 
Qed.


Definition split_combine_statement: Prop :=
  forall (X: Type) (l1 l2: list X),
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).

Theorem split_combine: split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X l1.
  induction l1 as [|h1 t1 H1].
  - intros l2 H. destruct l2 as [|h2 t2] eqn: H2.
    * reflexivity.
    * discriminate H.
  - intros l2 H. destruct l2 as [|h2 t2] eqn: H2.
    * discriminate H.
    * simpl in H. injection H as H. apply H1 in H.
      simpl. rewrite -> H. reflexivity.
Qed.

Theorem filter_exercise: forall (X: Type) (test: X->bool) (x: X) (l lf: list X),
  filter test l = x::lf -> test x = true.
Proof.
  intros X test x l lf.
  induction l as [| h t iH].
  - intros H. discriminate H.
  - simpl. destruct (test h) eqn: E.
    * intros H1. injection H1 as H11 H12.
      rewrite <- H11. apply E.
    * intros H1. apply iH. apply H1.
Qed.

Fixpoint forallb {X: Type} (test: X->bool) (l: list X) : bool :=
  match l with
  | nil => true
  | h::t => if test h then forallb test t else false
  end.
Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X: Type} (test: X->bool) (l: list X) : bool :=
  match l with
  | nil => false
  | h::t => if test h then true else existsb test t
  end.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X:Type} (test: X->bool) (l: list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).
Theorem existsb_existsb: forall (X: Type) (test: X->bool) (l: list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [|h t H].
  - reflexivity.
  - simpl. destruct (test h) eqn: E.
    * unfold existsb'. simpl. rewrite E. simpl. reflexivity.
    * unfold existsb'. simpl. rewrite E. simpl. 
      apply H.
Qed.










