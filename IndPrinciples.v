Check nat_ind.

Theorem mult_0_r':
  forall n: nat, n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n H. apply H.
Qed.

Theorem plus_one_r': forall n: nat, n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n H. 
    simpl. f_equal. apply H. 
Qed.


Inductive time : Type :=
  | day
  | night.
Check time_ind.


Inductive ExSet: Type :=
| con1: bool -> ExSet
| con2: nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.

Check list_ind.

(*
forall (X: Type) (P: tree X -> Prop),
  (forall x: X, P (leaf x)) ->
  (forall t1: tree X, P t1) ->
  forall t2: tree X, P t2 ->
  P (node t1 t2)) -> 
  (forall (t: tree X), P t)
*)
Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.


Inductive mytype (X: Type) : Type :=
| constr1: X -> mytype X
| constr2: nat -> mytype X
| constr3: mytype X -> nat -> mytype X.
Check mytype_ind.

Inductive foo (X Y: Type) : Type :=
| bar: X -> foo X Y
| baz: Y -> foo X Y
| quux: (nat->foo X Y) -> foo X Y.
Check foo_ind.


Inductive foo' (X: Type): Type :=
| c1 (l: list X) (f: foo' X)
| c2.

Definition P_m0r : nat->Prop :=
  fun n => n * 0 = 0.

Check foo'_ind.
Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* 请注意目前的证明状态！ *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. 
Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. 
Qed.





