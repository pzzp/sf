From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Definition eqb_string (x y: string): bool :=
  if string_dec x y then true else false.
Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s.
  unfold eqb_string.
  destruct (string_dec s s) as [H|H].
  - reflexivity.
  - destruct H. reflexivity.
Qed.

Theorem eqb_string_true_iff: forall x y: string,
  eqb_string x y = true <-> x = y.
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y) as [H|H].
  - rewrite H. split. reflexivity. reflexivity.
  - split.
    + intros contra. discriminate contra.
    + intros H'. rewrite H' in H. destruct H. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. 
Qed.

Theorem false_eqb_string: forall x y: string,
  x <> y -> eqb_string x y = false.
Proof.
  intros x y.
  rewrite eqb_string_false_iff.
  intros H. apply H.
Qed.

Definition total_map (A: Type) := string->A.
Definition t_empty {A: Type} (v: A) :total_map A :=
  (fun _ => v).
Definition t_update {A: Type} (m: total_map A) (x: string) (v: A) :=
  fun x' => if eqb_string x x' then v else m x'.
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).
Notation "x '!->' v ';' m" := (t_update m x v) (at level 100, v at next level, right associativity).
Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

Lemma t_apply_empty: forall (A: Type) (x: string) (v: A),
  (_!->v) x = v.
Proof.
  intros A x v.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq:
  forall (A: Type) (m: total_map A) x v,
    (x !->v; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  destruct (eqb_string x x) eqn: E.
  - reflexivity.
  - rewrite <- eqb_string_refl in E.
    discriminate E.
Qed.

Lemma t_update_neq:
  forall (A: Type) (m: total_map A) x y v,
    x <> y -> (x !-> v; m) y = m y.
Proof.
  intros.
  unfold t_update.
  apply eqb_string_false_iff in H.
  rewrite H.
  reflexivity.
Qed.

Lemma eqb_stringP: forall x y: string,
  reflect (x = y) (eqb_string x y).
Proof.
  intros x y.
  unfold eqb_string.
  destruct (string_dec x y).
  - rewrite e.
    apply ReflectT. reflexivity.
  - apply ReflectF. apply n.
Qed.

Theorem  t_update_same:
  forall (A: Type) (m: total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update.
  apply functional_extensionality.
  intros x0.
  destruct (eqb_stringP x x0).
  - rewrite e. reflexivity.
  - reflexivity. 
Qed.


Theorem t_update_permute:
  forall (A: Type) (m: total_map A) v1 v2 x1 x2,
    x2 <> x1 ->
      (x1 !-> v1 ; x2 !-> v2 ; m) = 
        (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. 
  unfold t_update.
  apply functional_extensionality.
  intros.
  destruct (eqb_stringP x1 x).
  - destruct (eqb_stringP x2 x).
    + exfalso. apply H. rewrite e0. symmetry. apply e.
    + reflexivity.
  - reflexivity. 
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* FILL IN HERE *) Admitted.


Definition partial_map (A: Type) :=
  total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty x v)
  (at level 100).
Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).
