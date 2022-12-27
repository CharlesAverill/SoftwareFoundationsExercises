(* https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html *)

From LF Require Export A_Basics.

Theorem add_0_r : forall n:nat,
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
        simpl. rewrite -> add_0_r. reflexivity.
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
          By reflexivity, P(S n')
          is true
        
        Qed
*)

(*
    Theorem: (n =? n) = true for any n

    Proof:
        - First, we must show that (0 =? 0) = true.
          This is clear by reflexivity.
        - Next, suppose that n = S n', such that
          (n' =? n') = true. We must prove that
          (S n' =? S n') = true. We can simplify
          this as 
          (n' =? n') = true, which is clear by
          reflexivity.
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

Check leb.

Theorem n_le_sum_n_m : forall n m : nat,
    (n <=? n + m) = true.
Proof.
    intros n m. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
    n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
    intros n m p H. induction p as [| p' IHp' ].
    - (* p = 0 *)
        simpl. rewrite -> H. reflexivity.
    - (* p = S p' *)
        simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
    (n <=? n) = true.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
    0 =? (S n) = false.
Proof.
    intros n. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
    andb b false = false.
Proof.
    intros b. destruct b eqn : E.
    - (* b = true *) 
        simpl. reflexivity.
    - (* b = false *)
        simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
    (S n) =? 0 = false.
Proof.
    intros n. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 
    1 * n = n.
Proof.
    intros n. simpl. rewrite -> add_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
        (andb b c)
        (orb (negb b)
            (negb c))
    = true.
Proof.
    intros b c. destruct b eqn : Eb.
    - (* b = true *)        
        simpl. destruct c eqn : Ec1.
        -- reflexivity.
        -- reflexivity.
    - (* b = false *)
        simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p. induction n as [| n' IHn' ].
    - (* n = 0 *) 
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. rewrite -> add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
    intros n m p. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

Theorem add_shuffle3' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> add_comm. rewrite <- add_assoc.
    replace (p + n) with (n + p).
    - reflexivity.
    - rewrite -> add_comm. reflexivity.
Qed.

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B_1 Z
  | B_0 b => B_1 b
  | B_1 b => B_0 (incr b)
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
match m with
| Z => 0
| B_0 b => mult 2 (bin_to_nat b)
| B_1 b => plus 1 (mult 2 (bin_to_nat b))
end.

Theorem S_S_assoc : forall x y : nat,
  S x + S y = S (S (x + y)).
Proof.
    intros x y. induction x as [| x' IHx' ].
    - (* x = 0 *)
        simpl. reflexivity.
    - (* x = IHx' *)
        simpl. rewrite <- IHx'. simpl. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
    bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
    intros b. induction b as [| b' | b'' ].
    - (* b = Z *)
        simpl. reflexivity.
    - (* b = B_0 b' *)
        simpl. reflexivity.
    - (* b = B_1 b' *)
        simpl. rewrite -> IHb'', add_0_r, add_0_r, S_S_assoc.
        reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
    match n with
    | 0 => Z
    | S n' => incr (nat_to_bin n')
    end.

Example nat_to_bin_0: nat_to_bin 0 = Z.
Proof. simpl. reflexivity. Qed.
Example nat_to_bin_1: nat_to_bin 1 = B_1 (Z).
Proof. simpl. reflexivity. Qed.
Example nat_to_bin_100: nat_to_bin 100 = B_0 (B_0 (B_1 (B_0 (B_0 (B_1 (B_1 (Z))))))).
Proof. simpl. reflexivity. Qed.

Theorem nat_bin_nat : forall n, 
    bin_to_nat (nat_to_bin n) = n.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> bin_to_nat_pres_incr. 
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma double_incr : forall n : nat, 
    double (S n) = S (S (double n)).
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
    match b with 
    | Z => Z
    | _ => B_0 (b)
    end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
    intros b. destruct b.
    - (* b = Z *)
        simpl. reflexivity.
    - (* b = B_0 b' *)
        simpl. reflexivity.
    - (* b = B_1 b' *)
        simpl. reflexivity.
Qed.

(*
    Theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b.
    Abort.

    This theorem fails because there are an infinite amount of binary
    representations for any given number. This is accomplished by
    prepending 0s to the left side of the number (the right side for
    our reversed representation.)
*)

Fixpoint normalize (b:bin) : bin :=
    match b with
    | Z => Z
    | B_0 b' => double_bin (normalize b')
    | B_1 b' => B_1 (normalize b')
    end.

Example normalize_test_1 : normalize (B_0 (B_0 (Z))) = Z.
Proof. simpl. reflexivity. Qed.
Example normalize_test_2 : normalize (B_0 (B_1 (B_0 (Z)))) = B_0 (B_1 (Z)).
Proof. simpl. reflexivity. Qed.

Lemma nat_to_bin_double : forall n, 
    nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn', double_incr_bin. reflexivity.
Qed.

Lemma incr_double : forall b, 
    incr (double_bin b) = B_1 b.
Proof.
    intros b. destruct b eqn : E.
    - (* b = Z *)
        simpl. reflexivity.
    - (* b = B_0 b' *)
        simpl. reflexivity.
    - (* b = B_1 b' *)
        simpl. reflexivity.
Qed.

Theorem bin_nat_bin : forall b, 
    nat_to_bin (bin_to_nat b) = normalize b.
Proof.
    intros b. induction b as [| b' | b' ].
    - (* b = Z *)
        simpl. reflexivity.
    - (* b = B_0 b' *)
        simpl. rewrite -> add_0_r. 
        rewrite <- double_plus.
        rewrite -> nat_to_bin_double, IHb'. reflexivity.
    - (* b = B_1 b' *)
        simpl. rewrite -> add_0_r.
        rewrite <- double_plus.
        rewrite -> nat_to_bin_double, IHb', incr_double.
        reflexivity.
Qed.
