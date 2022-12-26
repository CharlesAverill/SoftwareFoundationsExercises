From LF Require Export A_Basics.
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

Fixpoint alternate (l1 l2 : natlist) : natlist.
    Admitted.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
