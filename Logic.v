Set Warnings "-notation-overridden,-parsing".
Require Import Tactics.
Require Import Poly.
Require Import Nat.
Require Import Arith.
Require Import Induction.

From Coq Require Import Setoids.Setoid.

Lemma and_intro: forall A B: Prop, A->B->A/\B.
Proof.
  intros A B HA HB.
  split.
  apply HA.
  apply HB.
Qed.

Example and_exercise:
  forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  destruct n as [|n'] eqn: En.
  - simpl in H. split. 
    * reflexivity.
    * apply H.
  - discriminate H.
Qed.

Lemma and_example2:
  forall n m: nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm] eqn: HE.
  rewrite Hn. apply Hm.
Qed.

Lemma proj1: forall P Q: Prop, P /\ Q -> P.
Proof.
  intros P Q [PH _].
  apply PH.
Qed.

Lemma proj2: forall P Q: Prop, P /\ Q -> Q.
Proof.
  intros P Q [_ QH].
  apply QH.
Qed.

Theorem and_assoc: forall P Q R: Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.

Lemma or_intro_l: forall a b: Prop, a-> a \/ b.
Proof.
  intros a b H.
  left. apply H.
Qed.

Lemma zero_or_succ: forall n: nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Check not.

Theorem ex_falso_quodlibet: forall p: Prop, False -> p.
Proof.
  intros p contra.
  destruct contra.
Qed.

Fact not_implies_our_not: forall P: Prop, ~P -> (forall Q:Prop, P->Q).
Proof.
  intros P H1 Q H2.
  apply H1 in H2.
  destruct H2.
Qed.

Theorem not_False: ~False.
Proof. 
  unfold not.
  intros H. apply H.
Qed.

Theorem contradiction_implies_anything: forall P Q: Prop, (P/\~P) -> Q.
Proof.
  intros P Q [H1 H2].
  apply H2 in H1.
  destruct H1.
Qed.

Theorem double_neg: forall P: Prop, P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros H1.
  apply H1 in H.
  apply H.
Qed.

Theorem contraposite: forall (p q: Prop), (p->q)->(~q->~p).
Proof.
  intros p q H.
  unfold not. intros H1.
  intros H2.
  apply H in H2.
  apply H1 in H2.
  apply H2.
Qed.

Theorem not_both_true_and_false: forall p: Prop, ~(p /\ ~p).
Proof.
  intros p.
  unfold not.
  intros H.
  destruct H as [H1 H2].
  apply H2 in H1.
  apply H1.
Qed.

Theorem not_true_is_false: forall b: bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn: E.
  - exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true: True.
Proof. apply I. Qed.

Theorem iff_sym: forall p q: Prop, (p<->q) -> (q<->p).
Proof.
  intros P Q [H1 H2].
  split.
  - apply H2.
  - apply H1.
Qed.

Lemma not_true_iff_false: forall b, b<>true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H. unfold not. rewrite H. intros H1. discriminate H1.
Qed.

Theorem  or_distributes_over_and: forall p q r: Prop, p\/(q/\r) <-> (p\/q)/\(p\/r).
Proof.
  intros p q r.
  split.
  - intros [HP|[HQ HR]].
    + split.
      * left. apply HP.
      * left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP1|HQ] [HP2|HR]].
    * left. apply HP1.
    * left. apply HP1.
    * left. apply HP2.
    * right. split.
      { apply HQ. }
      { apply HR. }
Qed.

Check mult_comm.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0\/ m = 0.
Proof.
  split.
  - intros H. destruct n as [|n'] eqn: E.
    + left. reflexivity.
    + simpl in H. right. destruct m as [|m'] eqn:E1.
      * reflexivity.
      * simpl in H. discriminate H.
  - intros H. destruct H as [H|H].
    + rewrite H. reflexivity.
    + rewrite H. apply mult_comm.
Qed.


Lemma or_assoc:
  forall p q r: Prop, p \/ (q\/r) <-> (p\/q)\/r.
Proof.
  intros p q r. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3: forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example:
  forall n m: nat, n * m = 0 -> n=0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0.
  apply H.
Qed.


Theorem dist_not_exists: forall (X: Type) (P: X->Prop),
  (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros X P H.
  unfold not.
  intros H1.
  destruct H1 as [x E].
  apply E. apply H.
Qed.

Theorem dist_exists_or: forall (X: Type) (p q: X->Prop),
  (exists x, p x \/ q x) <-> (exists x, p x) \/ (exists x, q x).
Proof.
  intros X p q.
  split.
  - intros [x' H]. destruct H as [H|H].
    * left. exists x'. apply H.
    * right. exists x'. apply H.
  - intros [[x' H]|[x' H]].
    * exists x'. left. apply H.
    * exists x'. right. apply H.
Qed.


Fixpoint In {X: Type} (x: X) (l: list X): Prop :=
  match l with
  | nil => False
  | h::t => x = h \/ In x t
  end.


Lemma In_map: forall (A B: Type) (f: A->B) (l: list A) (x: A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|h t H].
  - intros H1. simpl. unfold In in H1. apply H1.
  - simpl.
    intros H1.
    destruct H1 as [H1|H1].
    * left. rewrite H1. reflexivity.
    * apply H in H1.
      right. apply H1.
Qed.

Lemma In_map_iff:
  forall (A B: Type) (f: A->B) (l: list A) (y: B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|h t H].
    * simpl. intros H'. destruct H'.
    * simpl. intros H'. destruct H' as [H'|H'].
      + exists h. split.
        { rewrite H'. reflexivity. }
        { left. reflexivity. }
      + apply H in H'.
        destruct H' as [x' H'].
        exists x'.
        destruct H' as [H'1 H'2].
        split.
        { apply H'1. }
        { right. apply H'2. }
  - intros [x' H].
    induction l as [|h t iH].
    * destruct H as [H1 H2].
      simpl in H2.
      destruct H2.
    * simpl. destruct H as [H1 H2].
      simpl in H2.
      destruct H2 as [H2 | H2].
      + rewrite H2 in H1.
        left. symmetry. apply H1.
      + right. apply iH. split.
        { apply H1. }
        { apply H2. }
Qed.


Lemma In_app_iff: forall A l1 l2 (a: A),
  In a (l1 ++ l2) <-> In a l1 \/ In a l2.
Proof.
  split. 
  - intros H. induction l1 as [|h t iH].
    + right. simpl in H. apply H.
    + simpl in H. destruct H as [H | H].
      * left. rewrite H. simpl. left. reflexivity.
      * simpl. apply or_assoc. right.
        apply iH. apply H.
  - intros H. destruct H as [H | H].
    + induction l1 as [|h t iH].
      * destruct H.
      * simpl. simpl in H. destruct H as [H|H].
        { left. apply H. }
        { right. apply iH. apply H. }
    + induction l1 as [|h t iH].
      * apply H.
      * simpl. right.  apply iH.
Qed.

Fixpoint All {T: Type} (P: T->Prop) (l: list T): Prop :=
  match l with
  | [] => True
  | h::t => P h /\ All P t
  end.

Lemma All_In: 
  forall T (P: T->Prop) (l: list T), 
    (forall x, In x l -> P x) <-> All P l.
Proof.
  split.
  - intros H.
    induction l as [|h t iH].
    + reflexivity.
    + simpl. simpl in H.
      split. 
      * apply H. left. reflexivity.
      * apply iH. intros x H'. apply H. right. apply H'.
  - intros H.
    induction l as [|h t iH].
    + intros x H'. destruct H'.
    + simpl. intros x H'. destruct H' as [H' | H'].
      * simpl in H. destruct H as [H0 H1]. rewrite <- H' in H0. apply H0.
      * simpl in H. destruct H as [H0 H1]. 
        specialize (iH H1). apply iH with (x) in H'.
        apply H'.
Qed.


Definition combine_odd_even (Podd Peven: nat -> Prop): nat-> Prop :=
  fun n: nat => if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop) (n: nat),
    (odd n = true -> Podd n) -> (odd n = false -> Peven n) -> combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (odd n) eqn: E.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven: nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n -> odd n = true -> Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1. 
  rewrite H2 in H1.
  apply H1.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven: nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n -> odd n = false -> Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1. 
  rewrite H2 in H1.
  apply H1.
Qed.


Lemma plus_comm3_take3: forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil: forall A (x: A) (l: list A), In x l -> l <> [].
Proof.
  intros A x l H.
  unfold not. intro H1. destruct l eqn: E.
  - simpl in H. destruct H.
  - discriminate H1.
Qed.


Example lemma_application_ex:
  forall {n: nat} {ns: list nat}, In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Fixpoint rev_append {X} (l1 l2: list X) : list X :=
  match l1 with
  | [] => l2
  | x :: xs => rev_append xs (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Axiom functional_extensionlity: 
  forall (X Y: Type) {f g: X -> Y}, (forall x: X, f x = g x) -> f = g.


Lemma rev_app: forall X (a b c: list X), rev_append a (b ++ c) = rev_append a b ++ c.
Proof.
  intros X a.
  induction a as [|h t iH].
  - reflexivity.
  - simpl. intros b c. 
    rewrite <- iH. apply f_equal.
    induction c as [|hc tc iHc].
    * reflexivity.
    * simpl. reflexivity.
Qed.

Lemma tr_rev_correct: forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionlity.
  intros x.
  induction x as [|h t iH].
  - reflexivity.
  - unfold tr_rev . simpl.
    unfold tr_rev in iH. 
    rewrite <- iH.
    replace ([h]) with ([] ++ [h]). rewrite rev_app. reflexivity.
    unfold app. reflexivity.
Qed.



Lemma evenb_double: forall k, evenb (double k) = true.
Proof.
  intros k.
  induction k as [|k' iHk].
  - reflexivity.
  - simpl. apply iHk.
Qed.

Lemma evenb_double_conv: 
  forall n, exists k, n = if evenb n then double k else S (double k).
Proof.
  intros n.
  induction n as [|n' iHn].
  - simpl. exists 0. reflexivity.
  - destruct (evenb n') eqn: E.
    + rewrite evenb_S. rewrite E. simpl. destruct iHn as [n'' iHn].
      exists n''. f_equal. apply iHn.
    + rewrite evenb_S.  rewrite E. simpl. destruct iHn as [n'' iHn].
      exists (S n'').  rewrite iHn.
      assert (H: forall x, double (S x) = S (S (double x))).
      * destruct x as [|x'].
        { reflexivity. }
        { simpl. reflexivity. }
      * rewrite H. reflexivity.
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

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Lemma andb_truee_iff: forall b1 b2: bool,
  andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  split.
  - intros H.
    destruct b1 eqn: E1.
    + destruct b2 eqn: E2.
      * split. 
        { reflexivity. }
        { reflexivity. }
      * discriminate H.
    + destruct b2 eqn: E2.
      * discriminate H.
      * discriminate H.
  - intros [H1 H2].
    rewrite H1. apply H2.
Qed.

Check eqb_refl.

Theorem eqb_neq: 
  forall (x y: nat), x =? y = false <-> x<>y.
Proof.
  split.
  - intros H.
    unfold not.
    intros H1.
    rewrite H1 in H.
    rewrite <- eqb_refl in H.
    discriminate H.
  - intros H1.
    unfold not in H1.
    destruct (x=?y) eqn: E.
    + apply eqb_eq in E. 
      apply H1 in E.
      destruct E.
    + reflexivity.
Qed.

Fixpoint eqb_list {A: Type} (eqb: A->A->bool) (l1 l2: list A): bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  | _, _ => false
  end.



Lemma eqb_list_true_iff:
  forall A (eqb: A->A->bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1=a2) ->
      (forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2).
Proof.
  intros A eqb H.
  induction l1 as [|h t iH1].
  + destruct l2.
    - split. 
      * intros _. reflexivity.
      * intros _. reflexivity.
    - split. 
      * simpl. intros H'. discriminate H'.
      * simpl. intros H'. discriminate H'. 
  + destruct l2.
    - split. 
      * simpl. intros H'. discriminate H'.
      * simpl. intros H'. discriminate H'.
    - split. 
      * simpl. intros H'. destruct (eqb h x) eqn: E.
        { apply iH1 in H'. rewrite H'. f_equal.
          apply H. apply E. }
        { discriminate H'. }
      * simpl. intros H'. injection H' as H1 H2.
        apply H in H1.  rewrite H1.  apply iH1. apply H2. 
Qed.

Fixpoint forallb {X: Type} (test: X->bool) (l: list X): bool :=
  match l with
  | [] => true
  | h::t => andb (test h) (forallb test t)
  end.
Theorem forallb_true_iff: forall X test (l: list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  split. 
  - intros H.
    induction l as [|h t iH].
    + reflexivity. 
    + simpl. simpl in H. destruct (test h) eqn: E.
      * simpl in H. split. 
        { reflexivity. } 
        { apply iH.  apply H. }
      * discriminate H. 
  - intros H. 
    induction l as [|h t iH].
    + reflexivity.
    + simpl. simpl in H. destruct H as [H1 H2].
      rewrite H1. simpl. apply iH.  apply H2. 
Qed.

Theorem excluded_middle_irrefutable: forall (P: Prop), ~~(P\/~P).
Proof.
  unfold not.
  intros P H.
  apply H. 
  right.
  intros H1.
  apply H. 
  left.
  apply H1. 
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~P.

Theorem not_exists_dist:
  excluded_middle -> 
  forall (X: Type) (P: X -> Prop), 
    ~(exists x, ~P x) -> (forall x, P x).
Proof.
  intros H1 X P H2 x.
  unfold excluded_middle in H1. 
  destruct (H1 (P x)) as [H1' | H1''].
  - apply H1'. 
  - exfalso. apply H2. exists x. apply H1''.
Qed.
    


Definition peirce := forall P Q: Prop, ((P->Q)->P)->P.
Definition double_negation_elimination := forall P: Prop, ~~P->P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q) -> (~P\/Q).

Theorem excluded_middle_to_double_negation_elimination: excluded_middle -> double_negation_elimination.
Proof.
  unfold double_negation_elimination.
  unfold excluded_middle.
  intros H P.
  unfold not.
  intros H1.
  destruct (H P) as [H'|H'].
  + apply H'.
  + exfalso. apply H1. apply H'.
Qed.


Theorem double_negation_elimination_to_de_morgan_not_and_not:
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  unfold de_morgan_not_and_not. 
  unfold double_negation_elimination.
  unfold not.
  intros H P Q H1.
 
  
  

