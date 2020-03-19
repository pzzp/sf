Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
Require Import Maps.



Module AExp.



Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).



Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.



Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.



Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.


Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  -  reflexivity.
  -  destruct a1 eqn:Ea1.
    +  destruct n eqn:En.
      *   simpl. apply IHa2.
      *  simpl. rewrite IHa2. reflexivity.
    + 
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + 
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + 
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - 
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - 
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.





Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity.  Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. 
  apply HP. 
Qed.





Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    
    -  simpl. reflexivity.
    -  simpl. reflexivity.
Qed.



Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  
  destruct n;
  
  simpl;
  
  reflexivity.
Qed.



Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    
  -  reflexivity.
  - 
    destruct a1 eqn:Ea1;
      
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    
    +  destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.





Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    
    try reflexivity.
  
  - 
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    +  destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.











Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.



Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.





Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  induction b; try (reflexivity); simpl;
  try (rewrite optimize_0plus_sound'; rewrite optimize_0plus_sound'; reflexivity);
  try (rewrite IHb; reflexivity);
  try (rewrite IHb1; rewrite IHb2; reflexivity).
Qed.











Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.








Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.













Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.



Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).



End TooHardToRead.



Notation "e '==>' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.



Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.
















Definition manual_grade_for_beval_rules : option (nat*string) := None.







Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
 split.
 - 
   intros H.
   induction H; simpl.
   + 
     reflexivity.
   + 
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + 
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + 
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - 
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + 
     apply E_ANum.
   + 
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + 
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + 
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.



Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  
  split.
  - 
    intros H; induction H; subst; reflexivity.
  - 
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.



Reserved Notation "e '-=>' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue: BTrue -=> true
  | E_BFalse: BFalse -=> false
  | E_BEq (a1 a2: aexp) (n1 n2: nat): 
      (a1 ==> n1) -> (a2 ==> n2) -> (BEq a1 a2) -=> (n1 =? n2)
  | E_BLe (a1 a2: aexp) (n1 n2: nat):
      (a1 ==> n1) -> (a2 ==> n2) -> (BLe a1 a2) -=> (n1 <=? n2)
  | E_BNot (b1: bexp) (b1': bool): (b1 -=> b1') -> (BNot b1) -=> (negb b1')
  | E_BAnd (b1 b2: bexp) (b1' b2': bool):
      (b1 -=> b1') -> (b2 -=> b2') -> (BAnd b1 b2) -=> (andb b1' b2')
  where "e '-=>' b" := (bevalR e b): type_scope.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split. 
  - intros H. 
    induction H; try reflexivity; simpl; 
    try apply aeval_iff_aevalR' in H;
    try apply aeval_iff_aevalR' in H0;
    try subst; 
    try reflexivity.
  - generalize dependent bv.
    induction b; simpl; 
    intros; subst; constructor; try (apply IHb); try (apply aeval_iff_aevalR');
    try reflexivity;
    try apply IHb1;
    try apply IHb2;
    reflexivity.
Qed.


End AExp.






Module aevalR_division.



Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         



Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.



End aevalR_division.

Module aevalR_extended.



Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).



Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n                        
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.



















Definition state := total_map nat.






Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x :  string)             
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).



Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".





Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).






Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.



Definition example_aexp : aexp := 3 + (X * 2).
Definition example_bexp : bexp := true && ~(X <= 4).



Set Printing Coercions.

Print example_bexp.


Unset Printing Coercions.






Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <=? (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.



Definition empty_st := (_ !-> 0).


Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X <= 4))
  = true.
Proof. reflexivity. Qed.













Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).



Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.



Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END).






Unset Printing Notations.
Print fact_in_coq.

Set Printing Notations.

Set Printing Coercions.
Print fact_in_coq.

Unset Printing Coercions.








Locate "&&".


Locate ";;".


Locate "WHILE".






Locate aexp.







Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.




Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END).

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.




Definition loop : com :=
  WHILE true DO
    SKIP
  END.












Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  
  end.
Close Scope imp_scope.



















Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

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

  where "st =[ c ]=> st'" := (ceval c st st').



Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  
  apply E_Seq with (X !-> 2).
  - 
    apply E_Ass. reflexivity.
  - 
    apply E_IfFalse.
    reflexivity.
    apply E_Ass. reflexivity.
Qed.


Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (Y !-> 1; X !-> 0).
    + apply E_Ass. reflexivity. 
    + apply E_Ass. reflexivity.
Qed.


Definition pup_to_n : com
  . Admitted.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
   Admitted.







Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  -  reflexivity.
  -  reflexivity.
  - 
    assert (st' = st'0) as EQ1.
    {  apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - 
      apply IHE1. assumption.
  - 
      rewrite H in H5. discriminate H5.
  - 
    rewrite H in H5. discriminate H5.
  - 
      apply IHE1. assumption.
  - 
    reflexivity.
  - 
    rewrite H in H2. discriminate H2.
  - 
    rewrite H in H4. discriminate H4.
  - 
      assert (st' = st'0) as EQ1.
      {  apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.






Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.






Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.



Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef
           eqn:Heqloopdef.
  induction contra; try discriminate; destruct b; try discriminate. 
  - apply IHcontra2. apply Heqloopdef.
Qed.



Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.
Close Scope imp_scope.



Inductive no_whilesR: com -> Prop :=
  | nw_skip: no_whilesR SKIP
  | nw_ass: forall (a: string) n, no_whilesR (a ::= n)
  | nw_seq: forall s1 s2 (H1: no_whilesR s1) (H2: no_whilesR s2), no_whilesR (s1;;s2)
  | nw_if: forall b c1 c2 (H1: no_whilesR c1) (H2: no_whilesR c2), 
      no_whilesR (TEST b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros H. induction c; inversion H; 
    try (apply andb_prop in H1; destruct H1 as [H2 H3]); constructor.
    + apply IHc1. apply H2.
    + apply IHc2. apply H3.
    + apply IHc1. apply H2.
    + apply IHc2. apply H3.
  - intros. induction c; simpl; try reflexivity; 
    try apply andb_true_iff; inversion H.
    + split. 
      * apply IHc1. apply H0.
      * apply IHc2. apply H3.
    + split. 
      * apply IHc1. apply H0.
      * apply IHc2. apply H4.
Qed.



Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.


Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Definition stack_op (st: list nat) (op:nat->nat->nat) : list nat :=
  match st with
  | a::b::s => (op b a)::s
  | _ => st
  end.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | p::ps => 
    match p with 
    | SPush n => s_execute st (n::stack) ps
    | SLoad s => s_execute st ((st s)::stack) ps
    | SPlus => s_execute st (stack_op stack (fun x y => x + y)) ps
    | SMinus => s_execute st (stack_op stack (fun x y => x - y)) ps
    | SMult => s_execute st (stack_op stack (fun x y => x * y)) ps
    end
  end.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.



Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus x y => s_compile x ++ s_compile y ++ [SPlus]
  | AMinus x y => s_compile x ++ s_compile y ++ [SMinus]
  | AMult x y => s_compile x ++ s_compile y ++ [SMult]
  end.



Example s_compile1 :
  s_compile (X - (2 * Y))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.




Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
   Admitted.






Module BreakImp.


Inductive com : Type :=
  | CSkip
  | CBreak                        
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).



Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, st' at next level).





Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').



Theorem break_ignore : forall c st st' s,
     st =[ BREAK;; c ]=> st' / s ->
     st = st'.
Proof.
   Admitted.

Theorem while_continue : forall b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s ->
  s = SContinue.
Proof.
   Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
   Admitted.



Theorem while_break_true : forall b c st st',
  st =[ WHILE b DO c END ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
 Admitted.



Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
   Admitted.


End BreakImp.






