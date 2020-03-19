Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.


Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* 当 auto 无法解决此目标时，它就什么也不做 *)
  auto.
  (* 可选的参数用来控制它的搜索深度（默认为 5） *)
  auto 6.
Qed.

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.
From Coq Require Import omega.Omega.
Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  info_auto using le_antisym.
Qed.