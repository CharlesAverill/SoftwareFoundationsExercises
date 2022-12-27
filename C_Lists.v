(* https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html *)

From LF Require Export B_Induction.

Inductive natprod : Type :=
    | pair (n_1 n_2 : nat).

Check (pair 3 5) : natprod.

Definition first (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.

Definition second (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

Compute (first (pair 5 3)).
Compute (second (pair 5 3)).

Notation "( x , y )" := (pair x y).

Compute (first (3, 5)).
Compute (second (3, 5)).

Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

Theorem surjective_pairing : forall (p : natprod),
    p = (first p, second p).
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity.
Qed.

Theorem second_first_is_swap : forall (p : natprod),
    (second p, first p) = swap_pair p.
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity.
Qed.

Theorem first_swap_is_second : forall (p : natprod),
    first (swap_pair p) = second p.
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity.
Qed.

Inductive natlist : Type :=
    | empty
    | cons (n : nat) (l : natlist).

Check (cons 1 (cons 2 (cons 3 empty))) : natlist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := empty.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y empty) ..).

Fixpoint repeat (n count : nat) : natlist :=
    match count with 
    | 0 => empty
    | S count' => n :: (repeat n count')
    end.

Compute repeat 5 10.

Fixpoint length (l : natlist) : nat :=
    match l with 
    | empty => 0
    | cons n cdr => 1 + (length cdr)
    end.

Compute length (repeat 5 10).
Compute length empty.

Fixpoint append (l_1 l_2 : natlist) : natlist :=
    match l_1 with
    | empty => l_2
    | h :: t => h :: (append t l_2)
    end.

Compute append [1;2;3] [4;5;6].
Compute append [1;2;3] empty.

Notation "x ++ y" := (append x y) 
                     (at level 60, right associativity).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: empty ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ empty = [1;2;3].
Proof. reflexivity. Qed.

Definition car (default : nat) (l : natlist) : nat :=
    match l with
    | empty => default
    | h :: t => h
    end.

Definition cdr (l : natlist) : natlist :=
    match l with
    | empty => empty
    | h :: t => t
    end.

Example test_hd1: car 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: car 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: cdr [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | empty => empty
    | 0 :: t => nonzeros t
    | h :: t => h :: (nonzeros t)
    end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | empty => empty
    | h :: t => match (odd h) with
        | true => h :: (oddmembers t)
        | false => oddmembers t
        end
    end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
    length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers empty = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | empty => l2
    | h1 :: t1 => match l2 with 
        | empty => l1
        | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
        end
    end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
    match s with 
    | empty => 0
    | h :: t => (count v t) + match (v =? h) with
        | true => 1
        | false => 0
        end
    end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
    append.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
    v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
    match (count v s) with 
    | 0 => false
    | _ => true
    end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
    | empty => empty
    | h :: t => match (h =? v) with 
        | true => t
        | false => h :: remove_one v t
        end
    end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | empty => empty
    | h :: t => match (h =? v) with
        | true => remove_all v t
        | false => h :: remove_all v t
        end
    end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | empty => true
    | h :: t => match (member h s2) with
        | true => included t (remove_one h s2)
        | false => false
        end
    end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Lemma beq_nat_refl : forall n, 
    true = (n =? n).
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_inc_count : forall v : nat, forall s : bag,
    count v (add v s) = 1 + (count v s).
Proof.
    intros v s. simpl.
    rewrite <- beq_nat_refl.
    rewrite -> add_comm. reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
    [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (cdr l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. 
Qed.


