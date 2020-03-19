Require Export IndProp.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.


Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)


Theorem ev_8: ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8': ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4': forall n, ev n -> ev (4 + n) :=
  fun (n: nat) => 
    fun (H: ev n) =>
      ev_SS (S (S n)) (ev_SS n H).

Definition add1: nat -> nat.
intros n.
Show Proof.
apply S.
Show Proof.
apply n.
Defined.



Module And.

Inductive and (P Q: Prop): Prop :=
  | conj: P -> Q -> and P Q.
End And.

Print prod.

Lemma and_comm:
  forall P Q: Prop, P/\Q <-> Q/\P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition  conj_fact: forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R: Prop) =>
    fun (x: and P Q) =>
      fun (y: and Q R) =>
        match x, y with
        | conj p _, conj _ r => conj p r
        end.
Check conj_fact.

Module Or.
Inductive or (P Q: Prop): Prop :=
| or_introl: P -> or P Q
| or_intror: Q -> or P Q.
End Or.

Definition or_comm: forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q: Prop) =>
    fun (x: or P Q) =>
      match x with
      | or_introl p => or_intror p
      | or_intror q => or_introl q
      end.


Module Ex.
Inductive ex {A: Type} (P: A->Prop): Prop :=
| ex_intro: forall x: A, P x -> ex P.
End Ex.

Check ex (fun n => ev n):Prop.
Definition some_nat_is_even: exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Check fun n => ev (S n).


Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).


Module MyEquality.
Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.
Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Lemma equality__leibniz_equality: forall (X: Type) (x y: X),
  x == y -> forall P: X -> Prop, P x -> P y.
Proof.
  intros X x y H1 P H2.
  destruct H1 as [x].
  apply H2.
Qed.


  











