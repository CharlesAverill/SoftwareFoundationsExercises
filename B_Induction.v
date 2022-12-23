From LF Require Export A_Basics.

Theorem add_0_r_firsttry : forall n:nat,
    n + 0 = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)
        reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed. 

Theorem minus_n_n : forall n:nat,
    n - n = 0.
Proof.
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mul_0_r : forall n:nat,
    n * 0 = 0.
Proof.
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
    intros n m. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed. 

Theorem add_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros n m. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. rewrite -> add_0_r_firsttry. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p. induction n as [| n' IHn'].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n : nat) :=
    match n with 
    | 0 => 0
    | S n' => S (S (double n'))
    end.
Lemma double_plus : forall n : nat,
    double n = n + n.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
    (n =? n) = true.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat,
    even (S n) = negb (even n).
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.

(* 
    The difference between 'destruct' and 'induction' is that
    'induction' sets up an inductive hypothesis for us, providing 
    the utility that if we prove that P(0) holds and P(n') holding
    implies P(S n') holds for any n', then P(n) holds and we can
    declare our theorem proved. 'destruct' only splits a 
    hypothesis into cases, but does not set up the inductive
    hypothesis.
 *)


