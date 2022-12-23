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


Theorem mult_0_plus' : forall n m : nat,
    (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
        {
            rewrite add_comm. simpl. rewrite add_comm. simpl. reflexivity.
        }
    rewrite -> H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (n + m = m + n) as H.
        {
            rewrite add_comm. reflexivity.
        }
    rewrite -> H. reflexivity.
Qed.

(*
    Theorem: Addition is commutative

    Proof:
        - First, we must show that 0 + m = m + 0. 
          This follows from the definition of +
        - Next, suppose that n = S n', such that
          n' + m = m + n'. We must show that
          (S n') + m = m + (S n'). From the definition
          of +, we can rewrite this as 
          S (n' + m) = (S n') + m
          and again as
          S (n' + m) = S (n' + m)
          By the refl property, P(S n')
          is true
        
        Qed
*)

(*
    Theorem: (n =? n) = true for any n

    Proof:
        - First, we must show that (0 =? 0) = true.
          This is clear by the refl property.
        - Next, suppose that n = S n', such that
          (n' =? n') = true. We must prove that
          (S n' =? S n') = true. We can simplify
          this as 
          (n' =? n') = true, which is clear by
          the refl property.
        Qed
*)

Theorem add_shuffle3 : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> add_comm. rewrite <- add_assoc.
    assert (p + n = n + p) as H.
        {
            rewrite -> add_comm. reflexivity.
        }
    rewrite -> H. reflexivity.
Qed.

Theorem mul_n_Sk : forall n k : nat,
    n * (S k) = n + (n * k).
Proof.
    intros n k. induction n as [| n' IHn' ].
        - (* n = 0 *)
            simpl. reflexivity.
        - (* n = S n' *)
            simpl. rewrite -> IHn'. 
            rewrite -> add_assoc.
            rewrite -> add_assoc.
            assert (k + n' = n' + k) as H.
                {
                    rewrite -> add_comm. reflexivity.
                }
            rewrite -> H. reflexivity.
Qed.


Theorem mul_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. rewrite -> mul_0_r. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> mul_n_Sk. rewrite -> IHn'. reflexivity.
Qed.
