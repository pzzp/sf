Require Import Nat.
Require Import Plus.
Module NatList.


Inductive natprod: Type :=
  | pair (n1 n2: nat).

Definition fst (p:natprod): nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p:natprod): nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p: natprod): natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing: forall p: natprod,
  p = (fst p, snd p).
Proof.
  intros [n m]. simpl. reflexivity.
Qed.


Theorem snd_fst_is_swap: forall p: natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  intros [n m].
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd: forall p: natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros [a b].
  reflexivity.
Qed.


Inductive natlist: Type :=
  | nil
  | cons (n: nat) (l : natlist).


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check [].
Check [1;2;3].

Fixpoint repeat (n count: nat): natlist :=
  match count with
  | 0 => []
  | S c => n :: repeat n c
  end.

Fixpoint length (l: natlist) : nat :=
  match l with
  | nil => 0
  | h::t => S (length t)
  end.

Fixpoint append (a: natlist) (b: natlist) :natlist :=
  match a with
  | nil => b
  | h::t => h::append t b
  end.

Notation "a ++ b" := (append a b) (right associativity, at level 60).

Definition head (default: nat) (a: natlist) : nat :=
  match a with
  | nil => default
  | h::t => h
  end.

Definition tail (a: natlist) : natlist :=
  match a with
  | nil => nil
  | h::t => t
  end.

Fixpoint nonzeros (a: natlist) : natlist :=
  match a with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.




Fixpoint oddmembers (a:natlist) : natlist :=
  match a with
  | nil => nil
  | h :: t => if even h
              then oddmembers t
              else h :: oddmembers t
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint count_odd_members (a: natlist) : nat :=
  match a with
  | nil => 0
  | t :: h =>  (if even t then 0 else 1) + count_odd_members h
  end.

Example test_countoddmembers1:
  count_odd_members [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  count_odd_members [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  count_odd_members nil = 0.
Proof. reflexivity. Qed.

(* Fixpoint alternate (a b: natlist) : natlist :=
  match a with
  | nil => b
  | t :: h => t :: alternate b a
  end. *)

Fixpoint alternate (a b: natlist) : natlist :=
  match a, b with
  |nil, b' => b'
  |a', nil => a'
  |h1::t1, h2::t2 => h1 :: h2 :: alternate t1 t2
  end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.
Fixpoint count (v: nat) (s: bag) : nat :=
  match s with
  | nil => 0
  | x::t => (if v =? x then 1 else 0) + count v t
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum: bag->bag->bag := append.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add := cons.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v:nat) (s: bag) : bool :=
  match s with
  | nil => false
  | cons x t => if x =? v then true else member v t
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v: nat) (s: bag) : bag :=
  match s with
  | nil => nil
  | h::t => if h =? v then t else h :: remove_one v t
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v: nat) (s: bag) : bag :=
  match s with
  | nil => nil
  | cons x t => if x =? v then remove_all v t else x :: remove_all v t
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (a: bag) (b: bag) : bool :=
  match a with
  | nil => true
  | x::t => if member x b then subset t (remove_one x b) else false
  end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


Theorem count_add_elem: forall (x: nat) (s: bag),
  count x (add x s) = S (count x s).
Proof.
  intros x s.
  simpl. replace (if x =? x then 1 else 0) with (1). reflexivity.
  induction x as [|x' iHx].
  - reflexivity.
  - simpl. rewrite <- iHx. reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tail l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem append_assoc: forall a b c: natlist,
  (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  intros a b c.
  induction a as [|h t H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Fixpoint rev (a: natlist) :=
  match a with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length: forall a b: natlist,
  length (a ++ b) = length a + length b.
Proof.
  intros a b.
  induction a as [|t h H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.

Theorem rev_length: forall a: natlist, length a = length (rev a).
Proof.
  intros a.
  induction a as [| t h H].
  - reflexivity.
  - simpl. rewrite -> app_length. simpl. rewrite <- H.
    rewrite plus_comm.
    reflexivity.
Qed.

Search rev.

Theorem app_nil_r: forall a: natlist, a ++ [] = a.
Proof.
  intros a.
  induction a as [| h t H].
  - reflexivity.
  - simpl. rewrite -> H. reflexivity.
Qed.


Theorem rev_app_distr: forall a b: natlist, rev (a ++ b) = rev b ++ rev a.
Proof.
  intros a b.
  induction a as [| h t H].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> H. rewrite append_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall a: natlist, rev (rev a) = a.
Proof.
  intros a.
  induction a as [|t h H].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite H. simpl. reflexivity.
Qed.

Theorem app_assoc4: forall a b c d : natlist,
  a ++ (b ++ (c ++ d)) = ((a ++ b) ++ c) ++ d.
Proof.
  intros a b c d.
  rewrite append_assoc. rewrite append_assoc. reflexivity.
Qed.

Lemma nozeros_app: forall a b : natlist,
  nonzeros (a ++ b) = nonzeros a ++ nonzeros b.
Proof.
  intros a b.
  induction a as [| t h H].
  - reflexivity.
  - simpl. 
    induction t as [|t' iHt'].
    rewrite H. reflexivity.
    simpl. rewrite H. reflexivity.
Qed.
    
Fixpoint eqblist (a b: natlist) : bool :=
  match a, b with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | t1::h1, t2::h2 => if t1 =? t2 then eqblist h1 h2 else false
  end. 

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl: forall a: natlist, true = eqblist a a.
Proof.
  intros a.
  induction a as [|h t H].
  - reflexivity.
  - simpl.
    induction h as [| h' hH].
    * rewrite H. reflexivity.
    * simpl. rewrite hH. reflexivity.
Qed.

Theorem count_member_nonzero: forall (s: bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s.
  induction s as [|h t H].
  - reflexivity.
  - reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall s: bag,
  count 0 (remove_one 0 s) <=? count 0 s = true.
Proof.
  intros s.
  induction s as [| h t H].
  - reflexivity.
  - simpl.
    induction h as [| h' iH'].
    * simpl. rewrite leb_n_Sn. reflexivity.
    * simpl. rewrite H. reflexivity.
Qed.


Theorem count_distr: forall (a b: bag) (e: nat),
  count e (sum a b) = count e a + count e b.
Proof.
  intros a b e.
  induction a as [|h t H].
  - simpl. reflexivity.
  - simpl. rewrite H. rewrite plus_assoc. reflexivity.
Qed.

Lemma rev_nil: rev [] = [].
Proof. simpl. reflexivity. Qed.

Theorem rev_injective: forall a b: natlist, 
  rev a = rev b -> a = b.
Proof.
  intros a b H.
  rewrite <- rev_involutive. 
  replace (a) with (rev (rev a)).
  - rewrite H. reflexivity.
  - rewrite -> rev_involutive. reflexivity.
Qed.

Inductive natoption: Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Fixpoint hd_error (a : natlist) : natoption :=
  match a with 
  | nil => None
  | h :: t => Some h
  end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd: forall (a: natlist) (default: nat),
  head default a = option_elim default (hd_error a).
Proof.
  intros a d.
  induction a as [|ha ta H].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Inductive id: Type := | Id (n: nat).
Definition eqb_id (a b: id) := 
  match a, b with
  | Id x, Id y => x =? y
  end.

Theorem eqb_id_ref: forall x, true = eqb_id x x.
Proof.
  intros x.
  destruct x.
  - simpl.
    induction n.
    * reflexivity.
    * simpl. rewrite IHn. reflexivity.
Qed.


Inductive partial_map: Type :=
  | empty
  | record (i: id) (v: nat) (m: partial_map).

Definition update (d: partial_map) (x: id) (value: nat) : partial_map :=
  record x value d.

Fixpoint find (x: id) (d: partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y then Some v else find x d'
  end.

Theorem update_eq: forall (d: partial_map) (x: id) (v: nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  induction d as [|i' v' d' H].
  - simpl. 
    replace (eqb_id x x) with (true). reflexivity.
    rewrite <- eqb_id_ref. reflexivity.
  - simpl.
    replace (eqb_id x x) with (true). reflexivity.
    rewrite <- eqb_id_ref. reflexivity.
Qed.

Theorem update_neq: forall (d: partial_map) (x y: id) (o: nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

