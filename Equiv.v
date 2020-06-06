Set Warnings "-notation-overridden,-parsing".
Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

Theorem aequiv_example: aequiv (X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0) true.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Theorem skip_left : forall c,
  cequiv
    (SKIP;; c)
    c.
Proof.
  split.
  - intros.
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - intros.
    apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

Theorem skip_right : forall c,
  cequiv
    (c ;; SKIP)
    c.
Proof.
  split.
  - intros.
    inversion H. subst.
    inversion H5. subst. assumption.
  - intros.
    apply E_Seq with st'.
    + assumption.
    + apply E_Skip.
Qed.

Theorem TEST_true_simple : forall c1 c2,
  cequiv
    (TEST true THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - 
    inversion H; subst. assumption. inversion H5.
  - 
    apply E_IfTrue. reflexivity. assumption.  Qed.

Theorem TEST_true: forall b c1 c2,
  bequiv b BTrue  ->
  cequiv
    (TEST b THEN c1 ELSE c2 FI)
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - 
    inversion H; subst.
    + 
      assumption.
    + 
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - 
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.  Qed.

Theorem TEST_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv
    (TEST b THEN c1 ELSE c2 FI)
    c2.
Proof.
  split; intros.
  - inversion H0; subst.
    + unfold bequiv in H. simpl in H. rewrite H in H6. discriminate H6.
    + apply H7.
  - unfold bequiv in H.
    apply E_IfFalse.
    + simpl in H. apply H.
    + apply H0.
Qed.

  
Search negb.
Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (TEST b THEN e1 ELSE e2 FI)
    (TEST BNot b THEN e2 ELSE e1 FI).
Proof.
  split; intros.
  - destruct (beval st b) eqn: E.
    + apply E_IfFalse.
      * simpl. rewrite E. reflexivity.
      * inversion H. subst.
        { apply H6.  }
        { rewrite E in H5. discriminate H5. }
    + apply E_IfTrue.
      * simpl. rewrite E. reflexivity. 
      * inversion H. subst.
        { rewrite E in H5. discriminate H5. }
        { apply H6. }
  - destruct (beval st b) eqn: E.
    + apply E_IfTrue.
      * apply E.
      * inversion H; subst.
        { rewrite <- E in H5. simpl in H5. apply no_fixpoint_negb in H5. inversion H5. }
        { apply H6. }
    + apply E_IfFalse.
      * apply E.
      * inversion H; subst.
        { apply H6. }
        { rewrite <- E in H5. simpl in H5. apply no_fixpoint_negb in H5. inversion H5. }
Qed.
      

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - 
    inversion H; subst.
    + 
      apply E_Skip.
    + 
      rewrite Hb in H2. inversion H2.
  - 
    inversion H; subst.
    apply E_WhileFalse.
    rewrite Hb.
    reflexivity.  Qed.

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~( st =[ WHILE b DO c END ]=> st' ).
Proof.
  
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END)%imp as cw eqn:Heqcw.
  induction H;
  
  inversion Heqcw; subst; clear Heqcw.
  
  -  
    unfold bequiv in Hb.
    
    rewrite Hb in H. inversion H.
  -  
    apply IHceval2. reflexivity.  Qed.

Theorem WHILE_true : forall b c,
  bequiv b true  ->
  cequiv
    (WHILE b DO c END)
    (WHILE true DO SKIP END).
Proof.
  split; intros.
  - apply WHILE_true_nonterm in H0.
    + inversion H0.
    + apply H.
  - apply WHILE_true_nonterm in H0.
    + inversion H0.
    + unfold bequiv. intros. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    (WHILE b DO c END)
    (TEST b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  - 
    inversion Hce; subst.
    + 
      apply E_IfFalse. assumption. apply E_Skip.
    + 
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - 
    inversion Hce; subst.
    + 
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + 
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  split; intros.
  - inversion H. subst.
    inversion H2. subst.
    apply (E_Seq c1 (c2;;c3) st st'1 st' H3).
    + apply (E_Seq c2 c3 st'1 st'0 st' H7 H5).
  - inversion H. subst.
    inversion H5. subst.
    specialize (E_Seq c1 c2 st st'0 st'1 H2 H3) as H'.
    apply (E_Seq (c1;;c2) c3 st st'1 st' H' H7).
Qed.

Theorem identity_assignment : forall x,
  cequiv
    (x ::= x)
    SKIP.
Proof.
  intros.
  split; intro H; inversion H; subst.
  - 
    rewrite t_update_same.
    apply E_Skip.
  - 
    assert (Hx : st' =[ x ::= x ]=> (x !-> st' x ; st')).
    { apply E_Ass. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

Check E_Ass.

Theorem assign_aequiv : forall (x : string) e,
  aequiv x e ->
  cequiv SKIP (x ::= e).
Proof.
  unfold aequiv. unfold cequiv.
  split.
  - intros.
    inversion H0. subst.
    assert (H1: st' = t_update st' x (st' x)).
    + apply functional_extensionality.
      intros.
      rewrite t_update_same. reflexivity.
    + rewrite H1 in |- * at 2.
      apply E_Ass.
      rewrite <- H.
      reflexivity.
  - intros.
    inversion H0. subst.
    assert (H1: st = t_update st x (aeval st e)).
    + rewrite <- H in |- * at 1.
      apply functional_extensionality.
      intros.
      rewrite t_update_same. reflexivity.
    + rewrite <- H1. 
      apply E_Skip.
Qed.


Definition prog_a : com :=
  (WHILE ~(X <= 0) DO
    X ::= X + 1
  END)%imp.

Definition prog_b : com :=
  (TEST X = 0 THEN
    X ::= X + 1;;
    Y ::= 1
  ELSE
    Y ::= 0
  FI;;
  X ::= X - Y;;
  Y ::= 0)%imp.

Definition prog_c : com :=
  SKIP%imp.

Definition prog_d : com :=
  (WHILE ~(X = 0) DO
    X ::= (X * Y) + 1
  END)%imp.

Definition prog_e : com :=
  (Y ::= 0)%imp.

Definition prog_f : com :=
  (Y ::= X + 1;;
  WHILE ~(X = Y) DO
    Y ::= X + 1
  END)%imp.

Definition prog_g : com :=
  (WHILE true DO
    SKIP
  END)%imp.

Definition prog_h : com :=
  (WHILE ~(X = X) DO
    X ::= X + 1
  END)%imp.

Definition prog_i : com :=
  (WHILE ~(X = Y) DO
    X ::= Y + 1
  END)%imp.

Definition equiv_classes : list (list com)
  . Admitted.

Definition manual_grade_for_equiv_classes : option (nat*string) := None.

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (st =[ c1 ]=> st' <-> st =[ c2 ]=> st') as H'.
  {  apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (st =[ c2 ]=> st'). apply H12. apply H23.  Qed.

Theorem CAss_congruence : forall x a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss x a1) (CAss x a1').
Proof.
  intros x a1 a2 Heqv st st'.
  split; intros Hceval.
  - 
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - 
    inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.  Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - 
    remember (WHILE b1 DO c1 END)%imp as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + 
      apply E_WhileFalse. rewrite <- Hb1e. apply H.
    + 
      apply E_WhileTrue with (st' := st').
      *  rewrite <- Hb1e. apply H.
      * 
        apply (Hc1e st st').  apply Hce1.
      * 
        apply IHHce2. reflexivity.
  - 
    remember (WHILE b1' DO c1' END)%imp as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + 
      apply E_WhileFalse. rewrite -> Hb1e. apply H.
    + 
      apply E_WhileTrue with (st' := st').
      *  rewrite -> Hb1e. apply H.
      * 
        apply (Hc1e st st').  apply Hce1.
      * 
        apply IHHce2. reflexivity.  Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  split; intros;
  inversion H1; subst.
  - apply E_Seq with st'0.
    + apply H. apply H4.
    + apply H0. apply H7.
  - apply E_Seq with st'0.
    + apply H. apply H4.
    + apply H0. apply H7.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (TEST b THEN c1 ELSE c2 FI)
         (TEST b' THEN c1' ELSE c2' FI).
Proof.
  split; intros.
  - inversion H2; subst.
    + apply E_IfTrue.
      * rewrite (H st) in H8. apply H8.
      * rewrite (H0 st) in H9. apply H9. 
    + apply E_IfFalse.
      * rewrite (H st) in H8. apply H8.
      * rewrite (H1 st) in H9. apply H9.
  - inversion H2; subst.
    + apply E_IfTrue.
      * rewrite <- (H st) in H8. apply H8. 
      * rewrite <- (H0 st) in H9. apply H9. 
    + apply E_IfFalse.
      * rewrite <- (H st) in H8. apply H8.
      * rewrite <- (H1 st) in H9. apply H9.
Qed.

Example congruence_example:
  cequiv
    
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= 0
     ELSE
       Y ::= 42
     FI)
    
    (X ::= 0;;
     TEST X = 0
     THEN
       Y ::= X - X   
     ELSE
       Y ::= 42
     FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAss_congruence. unfold aequiv. simpl.
      * symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | APlus a1 a2  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp ((1 + 2) * X)
  = (3 * X)%imp.
Proof. reflexivity. Qed.

Compute fold_constants_aexp (1 + 2).

Example fold_aexp_ex2 :
  fold_constants_aexp (X - ((0 * 6) + Y))%imp = (X - (0 + Y))%imp.
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue        => BTrue
  | BFalse       => BFalse
  | BEq a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1  =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ~(false && true))%imp
  = true.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1))))%imp
  = ((X = Y) && true)%imp.
Proof. reflexivity. Qed.

Open Scope imp.
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP      =>
      SKIP
  | x ::= a   =>
      x ::= (fold_constants_aexp a)
  | c1 ;; c2  =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | TEST b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue  => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => TEST b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.
Close Scope imp.

Example fold_com_ex1 :
  fold_constants_com
    
    (X ::= 4 + 5;;
     Y ::= X - 3;;
     TEST (X - Y) = (2 + 4) THEN SKIP
     ELSE Y ::= 0 FI;;
     TEST 0 <= (4 - (2 + 1)) THEN Y ::= 0
     ELSE SKIP FI;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp
  = 
    (X ::= 9;;
     Y ::= X - 3;;
     TEST (X - Y) = 6 THEN SKIP
     ELSE Y ::= 0 FI;;
     Y ::= 0;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)%imp.
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    
    try reflexivity;
    
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    
    try reflexivity.
  - 
    simpl.

    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      simpl. destruct (n =? n0); reflexivity.
  - simpl.
    remember (fold_constants_aexp a1) as a1' eqn: Hlea1'.
    remember (fold_constants_aexp a2) as a2' eqn: Hlea2'.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    destruct a1'; destruct a2'; try reflexivity.
    * simpl. destruct (n <=? n0); reflexivity.
    * subst. rewrite <- fold_constants_aexp_sound. reflexivity. 
    * subst. rewrite <- fold_constants_aexp_sound. reflexivity. 
  - 
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - 
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  -  apply refl_cequiv.
  -  apply CAss_congruence.
              apply fold_constants_aexp_sound.
  -  apply CSeq_congruence; assumption.
  - 
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      
    + 
      apply trans_cequiv with c1; try assumption.
      apply TEST_true; assumption.
    + 
      apply trans_cequiv with c2; try assumption.
      apply TEST_false; assumption.
  - remember (fold_constants_bexp b).
    assert (bequiv b b0).
    + rewrite Heqb0. apply fold_constants_bexp_sound.
    + destruct b0; try (apply CWhile_congruence; assumption; assumption).
      * apply WHILE_true. assumption.
      * apply WHILE_false. assumption.
Qed.
     
   

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if eqb_string x x' then u else AId x'
  | APlus a1 a2  =>
      APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2  =>
      AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.

Example subst_aexp_ex :
  subst_aexp X (42 + 53) (Y + X)%imp
  = (Y + (42 + 53))%imp.
Proof. reflexivity.  Qed.

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv (x1 ::= a1;; x2 ::= a2)
         (x1 ::= a1;; x2 ::= subst_aexp x1 a1 a2).

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  
  remember (X ::= X + 1;;
            Y ::= X)%imp
      as c1.
  remember (X ::= X + 1;;
            Y ::= X + 1)%imp
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).

  
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Ass; reflexivity).
  apply H in H1.

  
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'.  Qed.

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (APlus a1 a2)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMinus a1 a2)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (AMult a1 a2).


Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros.
  induction H.
  - simpl. reflexivity.
  - simpl. apply t_update_neq. apply H.
  - simpl. 
    rewrite IHvar_not_used_in_aexp1.
    rewrite IHvar_not_used_in_aexp2.
    reflexivity.
  - simpl.
    rewrite IHvar_not_used_in_aexp1.
    rewrite IHvar_not_used_in_aexp2.
    reflexivity.
  - simpl.
    rewrite IHvar_not_used_in_aexp1.
    rewrite IHvar_not_used_in_aexp2.
    reflexivity.
Qed.


Theorem inequiv_exercise:
  ~ cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  Admitted.

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                

Notation "'SKIP'" :=
  CSkip : imp_scope.
Notation "X '::=' a" :=
  (CAss X a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity) : imp_scope.
Notation "'HAVOC' l" :=
  (CHavoc l) (at level 60) : imp_scope.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).

Open Scope imp_scope.
Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
  | E_Havoc: forall x st v,
      st =[ CHavoc x ]=> (x !-> v; st)
  where "st =[ c ]=> st'" := (ceval c st st').
Close Scope imp_scope.

Example havoc_example1 : empty_st =[ (HAVOC X)%imp ]=> (X !-> 0).
Proof.
  apply E_Havoc.
Qed.

Example havoc_example2 :
  empty_st =[ (SKIP;; HAVOC Z)%imp ]=> (Z !-> 42).
Proof.
  apply E_Seq with (empty_st).
  - apply E_Skip.
  - apply E_Havoc.
Qed.

Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

Definition pXY :=
  (HAVOC X;; HAVOC Y)%imp.

Definition pYX :=
  (HAVOC Y;; HAVOC X)%imp.

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.  
  left.
  unfold cequiv.
  intros.
  split.
  - intros.
    inversion H. subst.
    inversion H2. subst.
    inversion H5. subst.
    apply E_Seq with (Y !-> v0; st).
    + apply E_Havoc.
    + rewrite t_update_permute.
      * apply E_Havoc.
      * unfold not.
        intros.
        discriminate.
  - intros.
    inversion H. subst.
    inversion H2. subst.
    inversion H5. subst.
    apply E_Seq with (X !-> v0; st).
    + apply E_Havoc.
    + rewrite t_update_permute.
      * apply E_Havoc.
      * unfold not. intros. discriminate.
Qed.



Definition ptwice :=
  (HAVOC X;; HAVOC Y)%imp.

Definition pcopy :=
  (HAVOC X;; Y ::= X)%imp.

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.  Admitted.

Definition p1 : com :=
  (WHILE ~ (X = 0) DO
    HAVOC Y;;
    X ::= X + 1
  END)%imp.

Definition p2 : com :=
  (WHILE ~ (X = 0) DO
    SKIP
  END)%imp.




Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof.
   Admitted. 
Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
 Admitted.

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.  Admitted.

Definition p3 : com :=
  (Z ::= 1;;
  WHILE ~(X = 0) DO
    HAVOC X;;
    HAVOC Z
  END)%imp.

Definition p4 : com :=
  (X ::= 0;;
  Z ::= 1)%imp.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.  Admitted.

Definition p5 : com :=
  (WHILE ~(X = 1) DO
    HAVOC X
  END)%imp.

Definition p6 : com :=
  (X ::= 1)%imp.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof.  Admitted.

End Himp.

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    (l1 ::= a1;; l2 ::= a2)
    (l2 ::= a2;; l1 ::= a1).
Proof.
 Admitted.

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

Definition c3 : com
  . Admitted.
Definition c4 : com
  . Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof.  Admitted.

Definition cmin : com
  . Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof.  Admitted.

Definition zprop (c : com) : Prop
  . Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof.  Admitted.
