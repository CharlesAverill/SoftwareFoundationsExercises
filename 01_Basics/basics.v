Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday 
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday) friday.
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b_1:bool) (b_2:bool) : bool :=
  match b_1 with
  | true => b_2
  | false => false
  end.

Definition orb (b_1:bool) (b_2:bool) : bool :=
  match b_1 with
  | true => true
  | false => b_2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b_1:bool) (b_2:bool) : bool :=
  if b_1 then b_2
  else false.

Definition orb' (b_1:bool) (b_2:bool) : bool :=
  if b_1 then true
  else b_2.

Definition nandb (b_1:bool) (b_2:bool) : bool :=
  if b_1 then (if b_2 then false else true)
  else true.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b_1:bool) (b_2:bool) (b_3:bool) : bool := 
  if b_1 then (if b_2 then b_3 else false)
  else false.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check true
  : bool.
Check (negb true)
  : bool.
Check negb
  : bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition is_red (c : color) : bool :=
  match c with
  | black => false
  | white => true
  | primary red => true
  | primary _ => false
  end.

Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.

Inductive bit : Type :=
  | zero
  | one.

Inductive nybble : Type :=
  | bits (b_0 b_1 b_2 b_3 : bit).

Check (bits one zero one zero)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits zero zero zero zero) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits one zero one zero)).

Compute (all_zero (bits zero zero zero zero)).

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | Zero
  | Successor (n : nat).

Definition predecessor (n:nat) : nat :=
  match n with
  | Zero => Zero
  | Successor n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minus_two (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minus_two 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check minus_two : nat -> nat.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

Example test_odd3: odd (S 2) = true.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S p => mult n (factorial p)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
          | O => true
          | _ => false
          end
  | S n' => match m with
             | O => false
             | S m' => eqb n' m'
             end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => 
    match m with
    | O => false
    | S m' => leb n' m'
    end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3' : (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  (andb (n <=? m) (negb (n =? m))).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H_2.
  rewrite -> H.
  rewrite -> H_2.
  reflexivity. Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, 
  andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    -- reflexivity.
    -- reflexivity.
  - destruct c eqn:Ec.
    -- reflexivity.
    -- reflexivity.
Qed.

Theorem andb3_exchange : forall b c d,
  andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct c eqn:Ec.
  - reflexivity.
  - destruct b eqn:Ed.
    -- apply H.
    -- apply H.
Qed.

Theorem zero_nbeq_plus_1: forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(* Fixpoint decreasing_test (n m : nat) : nat :=
  match n with
  | O => m
  | S O => (decreasing_test O m)
  | S (S n') => (decreasing_test m (S n'))
  end. *)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H. rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H. rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    -- reflexivity.
    -- simpl. rewrite <- Eb. intros H. rewrite -> H. reflexivity.
  - destruct c eqn:Ec.
    -- simpl. rewrite <- Eb. intros H. rewrite -> H. reflexivity.
    -- reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B_0 (n : bin)
  | B_1 (n : bin).

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

Example test_bin_incr1 : (incr (B_1 Z)) = B_0 (B_1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B_0 (B_1 Z))) = B_1 (B_1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B_1 (B_1 Z))) = B_0 (B_0 (B_1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B_0 (B_1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (incr (B_1 Z)) = 1 + bin_to_nat (B_1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 : bin_to_nat (incr (incr (B_1 Z))) = 2 + bin_to_nat (B_1 Z).
Proof. simpl. reflexivity. Qed.
