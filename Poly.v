Require Import Nat.


Inductive list (X:Type): Type :=
  | nil
  | cons (x: X) (l: list X).

Check list.
Check nil.
Check cons.

Check cons nat 2.

Fixpoint repeat (X: Type) (x: X) (count: nat): list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.


(* Inductive mumble: Type :=
  | a
  | b (x: mumble) (y: nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m: mumble)
  | e (x: X).


Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Check c.
 *)
Fixpoint repeat' X x count: list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
Check repeat'.
Check repeat.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition repeat'' {X: Type} (x: X) (count: nat) :list X :=
  repeat' X x count.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r: forall (X:Type), forall (a: list X),
  a ++ [] = a.
Proof.
  intros X a.
  induction a as [|t h H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem app_assoc: forall A (a b c: list A),
  a ++ b ++ c = (a ++ b) ++ c.
Proof.
  intros A a b c.
  induction a as [|h t H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Lemma app_length: forall (X: Type) (a b: list X),
  length (a ++ b) = length a + length b.
Proof.
  intros X a b.
  induction a as [|h t H].
  - simpl. reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem rev_app_distr: forall (X:Type) (a b: list X), rev (a ++ b) = rev b ++ rev a.
Proof.
  intros X a b.
  induction a as [|ha ta H].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> H.  rewrite -> app_assoc.  reflexivity.
Qed.

Theorem rev_involutive: forall (X: Type) (a: list X), rev (rev a) = a.
Proof.
  intros X a.
  induction a as [|ha ta H].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr.  rewrite -> H. simpl.  reflexivity.
Qed.


Inductive prod (X Y: Type): Type :=
  | pair (x: X) (y: Y).

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.
Fixpoint split {X Y: Type} (l: list (X * Y)) : list X * list Y :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => 
    match split t with 
    | (l1, l2) => (x::l1, y::l2)
    end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X: Type): Type :=
  | Some (x: X)
  | None.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (a : list X) (n : nat) : option X :=
  match a, n with
  | [], _ => None
  | h::t, 0 => Some h
  | h::t, S x => nth_error t x
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X: Type} (a: list X): option X :=
  match a with
  | [] => None
  | h::t => Some h
  end.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Fixpoint filter {X: Type} (test: X -> bool) (a: list X) : list X :=
  match a with
  | nil => nil
  | h::t => if test h then h :: filter test t else filter test t
  end.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Check fun a => length a =? 1.
Check andb.
Check ltb.
Check negb.
Definition filter_even_gt7 :=
  filter (fun x => andb (even x) (7 <? x)).
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X: Type} (test: X->bool) (a: list X) : list X * list X :=
  (filter test a, filter (fun x => negb (test x)) a).
Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f: X -> Y) (a: list X) : list Y :=
  match a with
  | nil => nil
  | h::t => f h :: map f t
  end.
Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Theorem map_distr: forall (X Y: Type) (f: X->Y) (a b: list X),
  map f (a ++ b) = map f a ++ map f b.
Proof.
  intros X Y f a b.
  induction a as [| h t H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem map_rev: forall (X Y: Type) (f: X->Y) (a: list X),
  map f (rev a) = rev (map f a).
Proof.
  intros X Y f a.
  induction a as[|h t H].
  - reflexivity.
  - simpl. rewrite -> map_distr. simpl. rewrite -> H. reflexivity.
Qed.


Fixpoint flat_map {X Y: Type} (f: X -> list Y) (a: list X): list Y :=
  match a with
  | [] => []
  | h :: t => f h ++ flat_map f t
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (a: list X) (b: Y): Y :=
  match a with
  | nil => b
  | h::t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X: Type} (x: X): nat->X :=
  fun (k: nat) => x.

Check constfun.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition fold_map {X Y: Type} (f: X->Y) (a: list X) : list Y :=
  fold (fun x y => f x :: y) a [].

Theorem fold_map_correct: forall (X Y: Type) (f: X->Y) (a: list X),
  map f a = fold_map f a.
Proof.
  intros X Y f a.
  induction a as [|h t H].
  - reflexivity.
  - simpl. rewrite ->H. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z: Type}
  (f: X->Y->Z) (t: X * Y) : Z :=
  match t with
  |(x, y) => f x y
  end.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry: forall (X Y Z: Type) (f: X->Y->Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof. 
  intros X Y Z f [x y].
  reflexivity.
Qed.

Definition cnat := forall X: Type, (X->X)->X->X.

Definition zero: cnat :=
  fun (X: Type) (f: X->X) (x: X) => x.
Definition one: cnat :=
  fun (X: Type) (f: X->X) (x: X) => f x.
Definition two: cnat :=
  fun (X: Type) (f: X->X) (x: X) => f (f x).
Definition three: cnat :=
  fun (X: Type) (f: X->X) (x: X) => f (f (f x)).

Definition succ (n: cnat) : cnat :=
  fun (X: Type) (f: X->X) (x: X) => f (n X f x).
Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (a: cnat) (b: cnat) : cnat :=
  fun (X: Type) (f: X->X) (x: X) => a X f (b X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (a b: cnat): cnat := 
  fun (X: Type) (f: X->X) (x: X) => a X (b X f) x.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (a b: cnat): cnat :=
  fun (X:Type) => b (X->X) (a X).
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.  
