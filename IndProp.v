Set Warnings "-notation-overridden,-parsing".
Require Import Logic.
Require Coq.omega.Omega.
Require Import Induction.
Require Import List.
Require Import Bool.






Inductive ev: nat->Prop :=
  |ev_0: ev 0
  |ev_SS (n: nat) (H: ev n): ev (S (S n)).

Theorem ev_4: ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.
Theorem ev_4': ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_double: forall n, ev (double n).
Proof.
  intros n.
  induction n as [|n' Hn].
  - apply ev_0.
  - simpl. apply ev_SS. apply Hn.
Qed.

Theorem ev_inversion: forall (n: nat), ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [|n' E].
  - left. reflexivity.
  - right. exists n'. split.
    + reflexivity.
    + apply E.
Qed.

Compute pred 0.

Theorem ev_minus2: forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [|n E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Definition even x := exists n: nat, x = double n.

Theorem evSS_ev_remember:
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. remember (S (S n)) as k.
  destruct H as [|n' H'] eqn: E'.
  - discriminate Heqk.
  - injection Heqk as Heq.
    rewrite <- Heq.
    apply H'.
Qed.

Theorem evSS_ev: forall n, ev(S (S n)) -> ev n.
Proof.
  intros n H. 
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [n' [H1 H2]].
    injection H1 as H1.
    rewrite H1.
    apply H2.
Qed.

Theorem evSS_ev': forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E' EQ].
  apply E'.
Qed.

Theorem one_not_even: ~ ev 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem  SSSSev_even: forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' H' E].
  inversion H' as [| n'' H'' E'].
  apply H''.
Qed.
Check plus.
Theorem ev5_nonsense: ev 5 -> (plus 2 2 = 9).
Proof.
  intros H.
  unfold plus.
  inversion H.
  inversion H1.
  inversion H3.
Qed.


Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Theorem inversion_ex1: forall (n m o: nat), [ n; m ] = [o; o] -> [ n ] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Compute even 0.

Lemma ev_even: forall n, ev n -> even n.
Proof.
  intros n H. unfold even.
  induction H as [|n H']. 
  - exists 0. reflexivity.
  - destruct IHH' as [n' E].
    exists (S n').
    simpl. rewrite E.
    reflexivity.
Qed.

Theorem ev_even_iff:
  forall n, ev n <-> even n.
Proof.
  split. 
  unfold even.
  - apply ev_even.
  - intros [k Hk].
    rewrite Hk.
    apply ev_double.
Qed.
    
Theorem ev_sum:
  forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2.
  induction H1 as [|n' H1'].
  - apply H2.
  - simpl. 
    apply ev_SS.
    apply IHH1'.
Qed.

Inductive ev': nat->Prop :=
  | ev'_0: ev' 0
  | ev'_2: ev' 2
  | ev'_sum n m (Hn: ev' n) (Hm: ev' m): ev' (n + m).

Theorem ev'_ev: forall n, ev' n <-> ev n.
Proof.
  intros n.
  split. 
  - intros H.
    induction H as [| |n' m' H'].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply (ev_sum n' m' IHH' IHev'1).
  - intros H.
    induction H as [| n' H'].
    apply ev'_0.
    assert (H: forall n, S (S n) = plus 2 n).
    * intros n.
      induction n.
      { reflexivity. }
      { simpl. reflexivity. }
    * rewrite H. 
      apply (ev'_sum 2 n' ev'_2 IHH').
Qed.

Theorem ev_ev__ev: forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1 H2.
  induction H2 as [|n' H2'].
  - apply H1.
  - apply IHH2'.
    simpl in H1.
    inversion H1.
    apply H0.
Qed.

Notation "a + b" := (plus a b).

Theorem plus_plus_double:
  forall n: nat, n + n = double n.
Proof.
  intros n.
  induction n as [|n' iH].
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm.
    rewrite iH.
    reflexivity.
Qed. 



Theorem ev_plus_plus: 
  forall n m p, ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p H1 H2.
  assert (H3: ev ((n+m)+(n+p))).
  - apply (ev_sum (n+m) (n+p) H1 H2).
  - rewrite plus_assoc in H3.
    rewrite <- (plus_assoc n m n) in H3.
    rewrite (plus_comm m n) in H3.
    rewrite <- (plus_assoc n (n+m) p) in H3.
    rewrite <- (plus_assoc n m p) in H3.
    rewrite  (plus_assoc n n (m+p)) in H3.
    apply (ev_ev__ev (n+n) (m+p)) in H3.
    * apply H3.
    * rewrite plus_plus_double.
      apply ev_double.
Qed.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).
Notation "m <= n" := (le m n).

Definition lt (n m: nat) := le (S n) m.
Notation "m < n" := (lt m n).

Inductive square_of: nat -> nat -> Prop :=
  | sq n: square_of n (n * n).
Inductive next_nat: nat->nat->Prop :=
  | nn n: next_nat n (S n).
Inductive next_ev: nat->nat->Prop :=
  | ne_1 n (H: ev (S n)) : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))): next_ev n (S (S n)).

Inductive total_relation: nat->nat->Prop :=
  | tr n m: total_relation n m.

Inductive empty_relation: nat->nat->Prop :=
  .

Lemma le_trans: forall a b c, a <= b -> b <=c -> a<=c.
Proof.
  intros a b c H1 H2.
  induction H2 as [n' | n' m' H2' iH].
  - apply H1.
  - apply iH in H1.
    apply (le_S a m' H1).
Qed.

Theorem zero_le_n: forall n, 0 <= n.
Proof.
  intros n.
  induction n as [|n' iH].
  - apply le_n.
  - apply (le_S 0 n' iH).
Qed.

Theorem n_le_m_Sn_le_Sm:
  forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [n' | n' m' H iH].
  - apply le_n.
  - apply (le_S (S n') (S m') iH).
Qed.

Theorem Sn_le_Sm_n_le_m:
  forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - assert (H5: n <= S n).
    * apply (le_S n n (le_n n)).
    * apply (le_trans n (S n) m H5 H2).
Qed.


Theorem le_plus_l: forall a b, a <= a + b.
Proof.
  intros a b.
  induction b as [|b' iH].
  - rewrite plus_comm. simpl. apply (le_n a).
  - rewrite plus_comm. simpl.
    rewrite plus_comm.
    apply (le_S a (a + b') iH).
Qed.

Lemma Sn_le_m_n_le_m:
  forall n m, S n <= m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  - apply (le_S n n (le_n n)).
  - apply le_S.
    rewrite <- H2 in H.
    apply Sn_le_Sm_n_le_m in H.
    apply H.
Qed.


Lemma n_le_Sn:
  forall n, n <= S n.
Proof.
  intros n.
  apply (le_S n n (le_n n)).
Qed.
    

Theorem plus_le: 
  forall n1 n2 m,
    n1 + n2 <= m ->
      n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  induction m as [|m' iHm].
  * inversion H.
    split.
    + apply le_plus_l.
    + rewrite plus_comm. apply le_plus_l.
  * inversion H.
    + split.
      - apply le_plus_l.
      - rewrite plus_comm. apply le_plus_l.
    + split. 
      - apply iHm in H2.
        destruct H2 as [H2' _].
        apply (le_S n1 m' H2').
      - apply iHm in H2.
        destruct H2 as [_ H2'].
        apply (le_S n2 m' H2').
Qed.

Theorem le_gt_cases:
  forall a b,
    a <= b \/ b < a.
Proof.
  intros a b.
  induction a as [|a' iHa'].
  - left. apply zero_le_n.
  - destruct iHa' as [iHa'|iHa'].
    * inversion iHa'.
      + right. 
        unfold lt. apply le_n.
      + left. apply n_le_m_Sn_le_Sm.
        apply H.
    * right.
      unfold lt in iHa'.
      unfold lt.
      apply (le_S (S b) a' iHa').
Qed.

Lemma Sa_le_b_a_le_b:
  forall a b, (S a) <= b -> a <= b.
Proof.
  intros a b. generalize dependent a.
  induction b as [|b' iH].
  - intros a H. inversion H.
  - intros a H.
    inversion H.
    + apply (le_S b' b' (le_n b')).
    + apply iH in H2.
      apply (le_S a b' H2).
Qed.




Theorem add_le_cases:
  forall n m p q,
    n + m <= p + q ->
      n <= p \/ m <= q.
Proof.
  Admitted.


Theorem lt_S:
  forall n m,
    n < m -> n < S m.
Proof.
  intros n m.
  unfold lt.
  intros H.
  apply (le_S (S n) m H).
Qed.

Theorem plus_lt:
  forall n1 n2 m,
    n1 + n2 < m ->
      n1 < m /\ n2 < m.
Proof.
  Admitted.


Inductive R: nat->nat->nat->Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o) : R n m o.

Definition fR: nat->nat->nat := plus.

Theorem R_equiv_fR: forall m n o,
  R m n o <-> fR m n = o.
Proof.
  unfold fR.
  split.
  - intros H.
    induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. f_equal. apply IHR.
    + simpl in IHR.
      injection IHR as IHR.
      rewrite <- plus_n_Sm in IHR.
      injection IHR as IHR.
      apply IHR.
    + rewrite plus_comm.
      apply IHR.
  - generalize dependent n.
    generalize dependent o.
    induction m as [|m' iHm].
    + intros o.
      induction o as [|o' iHo].
      * intros n H.
        simpl in H.
        rewrite H.
        apply c1.
      * intros n H.
        simpl in H.
        rewrite H.
        apply c3.
        apply iHo.
        reflexivity.
    + intros o.
      destruct o as [|o'].
      * intros n H.
        simpl in H.
        discriminate H.
      * intros n H.
        simpl in H. 
        injection H as H.
        apply iHm in H.
        apply c2.
        apply H.
Qed.


Inductive subseq: list nat -> list nat -> Prop :=
  |e1 : subseq [] []
  |e2 a b (x: nat) (e: subseq a b) : subseq a (x::b)
  |e3 a b (x: nat) (e: subseq a b) : subseq (x::a) (x::b).

Theorem subseq_refl: forall a: list nat, subseq a a.
Proof.
  intros a.
  induction a as [|h t iHa].
  - apply e1.
  - apply (e3 t t h iHa).
Qed.

Theorem subseq_app: forall a b c, subseq a b -> subseq a (b ++ c).
Proof.
  intros a b c H.
  induction H as [|a b x H iH|a b x H iH].
  + induction c as [|hc tc iHc].
    * apply e1.
    * apply (e2 [] tc hc iHc).
  + simpl. 
    apply (e2 a (b++c) x iH).
  + apply (e3 a (b++c) x iH).
Qed.


Inductive reg_exp (T: Type) :Type :=
  | EmptySet
  | EmptyStr
  | Char (t: T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).
Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).
Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.


Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.
Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStarl:
  forall T s (re: reg_exp T),
    s =~ re ->
      s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (@app_nil_r T s).
  apply (MStarApp s [] re H (MStar0 re)).
Qed.

Lemma empty_is_empty: forall T (s: list T), ~(s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion': forall T (s: list T) (re1 re2: reg_exp T),
  s =~ re1 \/ s =~ re2 ->
    s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H as [H|H].
  - apply (MUnionL s re1 re2 H).
  - apply (MUnionR re1 s re2 H).
Qed.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (a: list X) (b: Y): Y :=
  match a with
  | nil => b
  | h::t => f h (fold f t b)
  end.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
    fold (@app T) ss [] =~ Star re.
Proof.
  intros T ss re H.
  induction ss as [|h t iH].
  - simpl. apply MStar0.
  - simpl. simpl in H. 
    apply (MStarApp h (fold (@app T) t []) re).
    + apply H. left. reflexivity.
    + apply iH. 
      intros s H1.
      apply H. 
      right.
      apply H1.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

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

Theorem in_re_match : 
  forall T (s : list T) (re : reg_exp T) (x : T),
    s =~ re ->
      In x s ->
        In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl in Hin. destruct Hin.
  - simpl. simpl in Hin. apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin|Hin].
    + left. apply IH1. apply Hin.
    + right. apply IH2. apply Hin.
  - simpl in *. rewrite In_app_iff in *.
    left. apply IH.  apply Hin.
  - simpl in *. rewrite In_app_iff in *.
    right. apply IH.  apply Hin.
  - destruct Hin.
  - simpl in *. rewrite In_app_iff in Hin. 
    destruct Hin as [Hin|Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.


Fixpoint re_not_empty {T} (re : reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
  end.
Lemma re_not_empty_correct: forall T (re: reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split. 
  - intros [s H].
    induction H.
    + reflexivity.
    + reflexivity. 
    + simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
    + simpl. rewrite IHexp_match. reflexivity.
    + simpl. rewrite IHexp_match. rewrite orb_comm. reflexivity.
    + reflexivity. 
    + reflexivity.
  - intros H. 
    induction re. 
    + discriminate H. 
    + exists []. apply MEmpty.
    + exists [t]. apply (MChar t).
    + simpl in H. apply andb_true_iff in H. 
      destruct H as [H1 H2].
      destruct (IHre1 H1) as [s1 H1'].
      destruct (IHre2 H2) as [s2 H2'].
      exists (s1++s2). apply (MApp s1 re1 s2 re2 H1' H2').
    + simpl in H. rewrite orb_true_iff in H.
      destruct H as [H|H].
      * destruct (IHre1 H) as [s H'].
        exists s. apply (MUnionL s re1 re2 H').
      * destruct (IHre2 H) as [s H'].
        exists s. apply (MUnionR re1 s re2 H').
    + exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2: list T) (re: reg_exp T),
  s1 =~ Star re ->
    s2 =~ Star re ->
      s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.
  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

Lemma MStar'': forall T (s: list T) (re: reg_exp T),
  s =~ Star re ->
    exists ss: list (list T),
      s = fold (@app T) ss [] /\
      forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as re'.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists [].
    split. 
    + reflexivity.
    + intros s' H'.
      inversion H'.
  - destruct (IHexp_match2 Heqre') as [ss' [H1 H2]].
    exists (s1::ss').
    split.
    + simpl. rewrite <- H1. reflexivity.
    + intros s' H3. injection Heqre' as Heqre'.
      destruct H3.
      * rewrite <- Heqre'.
        rewrite <- H3.
        apply H.
      * apply H2. apply H3.
Qed.

Inductive reflect (P: Prop): bool -> Prop :=
  | ReflectT (H: P): reflect P true
  | ReflectF (H: ~P): reflect P false.

Theorem iff_reflect: forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H.
  destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate H'.
Qed.

Theorem reflect_iff: forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H.
  destruct H.
  - split.
    + intros H'. reflexivity.
    + intros H'. apply H.
  - split.
    + intros H'.
      exfalso.  apply H.  apply H'.
    + intros H'. discriminate H'.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Theorem eqb_eq: forall n m, eqb n m = true <-> n = m.
Proof.
  Admitted.

Lemma eqbP: forall n m, reflect (n=m) (eqb n m).
Proof.
  intros n m.
  apply iff_reflect.
  rewrite eqb_eq.
  reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => eqb n x) l <> [] ->
    In n l.
Proof.
  intros n l.
  induction l as [|m l' IH1'].
  - simpl. 
    intros H'. apply H'. reflexivity.
  - simpl. 
    destruct (eqbP n m) as [H|H].
    + intros _. rewrite H. left. reflexivity.
    + intros H'. right. apply IH1'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if eqb n m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l H.
  induction l as [|h t iH].
  - simpl. intros H'. apply H'.
  - simpl. destruct (eqbP h n) as [H1|H1].
    + intros H2. simpl in H. 
      symmetry in H1.
      rewrite <- eqb_eq in H1. 
      rewrite H1 in H.
      inversion H. 
    + intros H2. apply H1.
      destruct H2 as [H3|H3].
      * apply H3.
      * simpl in H.
        destruct (eqb n h).
        { inversion H. }
        { apply iH in H. exfalso.  apply H.  apply H3. }
Qed.

Inductive nostutter {X: Type}: list X -> Prop :=
  | ns_nil: nostutter []
  | ns_unit x: nostutter [x]
  | ns_cons n x t (H: nostutter (x::t)):
      n <> x -> nostutter (n::x::t).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  apply ns_cons. 
  apply ns_cons.
  apply ns_cons.
  apply ns_cons. 
  apply ns_cons.
  apply ns_unit.
  - intros H. inversion H.
  - intros H. inversion H.
  - intros H. inversion H.
  - intros H. inversion H.
  - intros H. inversion H.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  apply ns_nil.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  apply ns_unit.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intros H. 
  inversion H. 
  inversion H2.
  apply H9.
  reflexivity.
Qed.

Fixpoint All {X: Type} (test: X->bool) (l: list X):bool :=
  match l with
  | nil => true
  | h::t => if test h then All test t else false
  end.



Inductive merge {X: Type}: list X -> list X -> list X -> Prop :=
  | m_nil: merge [] [] []
  | m_l a l l1 l2 (H: merge l l1 l2):
      merge (a::l) (a::l1) l2
  | m_r a l l1 l2 (H: merge l l1 l2):
      merge (a::l) l1 (a::l2).

Theorem filter_challenge:
  forall (X: Type) (l l1 l2: list X) (test: X->bool),
    merge l l1 l2 /\ (All test l1 = true) -> filter test l = l1.
Proof.
  Admitted.

























