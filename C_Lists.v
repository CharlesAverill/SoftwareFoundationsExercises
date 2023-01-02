(* https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html *)

From LF Require Export B_Induction.

Module NatList.

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

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3. induction l1 as [| n l' IHl' ].
    - (* l1 = empty *)
        simpl. reflexivity.
    - (* l1 = cons n l1' *)
        simpl. rewrite -> IHl'. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | empty => empty
    | h :: t => rev t ++ [h]
    end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev empty = empty.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    (* WORKED IN CLASS *)
    intros l1 l2. induction l1 as [| n l1' IHl1'].
    - (* l1 = nil *)
        reflexivity.
    - (* l1 = cons *)
        simpl. rewrite -> IHl1'. reflexivity. 
Qed.

Theorem rev_length : forall l : natlist,
    length (rev l) = length l.
Proof.
    intros l. induction l as [| n l' IHl' ].
    - (* l = empty *)
        simpl. reflexivity.
    - (* l = cons n l' *)
        simpl.
        rewrite -> app_length, IHl', add_comm.
        simpl. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
Proof.
    intros l. induction l as [| n l' IHl' ].
    - (* l = empty *)
        simpl. reflexivity.
    - (* l = cons n l' *)
        simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros l1 l2. induction l1 as [| n1 l1' IHl1' ].
    - (* l1 = empty *)
        simpl. rewrite -> app_nil_r. reflexivity.
    - (* l1 = cons n l1' *)
        simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
    rev (rev l) = l.
Proof.
    intros l. induction l as [| n l' IHl' ].
    - (* l = empty *)
        simpl. reflexivity.
    - (* l = cons n l' *)
        simpl. rewrite -> rev_app_distr, IHl'.
        simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_assoc, app_assoc. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros l1 l2. induction l1 as [| n1 l1' IHl1' ].
    - (* l1 = empty *)
        simpl. reflexivity.
    - (* l1 = cons n1 l1' *)
        induction n1 as [| n1' IHn1' ].
        -- (* n1 = 0 *)
            simpl. rewrite -> IHl1'. reflexivity.
        -- (* n1 = S n' *)
            simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1 with
    | empty => match l2 with 
        | empty => true
        | _ => false
        end
    | h1 :: t1 => match l2 with
        | empty => false
        | h2 :: t2 => andb (eqb h1 h2) (eqblist t1 t2)
        end
    end.

Example test_eqblist1 : (eqblist empty empty = true).
Proof. reflexivity. Qed.
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
    true = eqblist l l.
Proof.
    intros l. induction l as [| n l' IHl' ].
    - (* l = empty *)
        simpl. reflexivity.
    - (* l = cons n l' *)
        simpl. rewrite -> eqb_refl. rewrite <- IHl'.
        simpl. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
    1 <=? (count 1 (1 :: s)) = true.
Proof.
    intros s. rewrite -> add_inc_count. 
    simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
    n <=? (S n) = true.
Proof.
    intros n. induction n as [| n' IHn' ].
    - (* n = 0 *)
        simpl. reflexivity.
    - (* n = S n' *)
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
    intros s. induction s as [| n s' IHs' ].
    - (* s = empty *)
        simpl. reflexivity.
    - (* s = cons n s' *)
        induction n as [| n' IHn' ].
        -- (* n = 0 *)
            simpl. rewrite -> add_comm. rewrite -> leb_n_Sn. reflexivity.
        -- (* n = S n' *)
            simpl. rewrite -> add_0_r, add_0_r, IHs'. reflexivity.
Qed.

Theorem bag_count_sum  : forall (s1 s2 : bag) (v : nat),
    count v (sum s1 s2) = (count v s1) + (count v s2).
Proof.
    intros s1 s2 v. induction s1 as [| n1 s1' IHs1' ].
    - (* s1 = empty *)
        simpl. reflexivity.
    - (* s1 = cons n s1' *)
        simpl. destruct (v =? n1).
        -- rewrite -> add_comm. assert (count v s1' + 1 = 1 + count v s1') as H.
            {
                rewrite -> add_comm. reflexivity.
            }
            rewrite -> H. rewrite -> IHs1'. rewrite -> add_assoc. reflexivity.
        -- rewrite -> add_0_r, add_0_r. rewrite -> IHs1'. reflexivity.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
    intros f n n1 n2 H. assert (n1 = f (f n1)) as Hn1.
        {
            rewrite <- n. reflexivity.
        }
    rewrite -> Hn1. 
    assert (n2 = f (f n2)) as Hn2.
        {
            rewrite <- n. reflexivity.
        }
    rewrite -> Hn2.
    rewrite -> H. reflexivity.
Qed.
    
Theorem rev_injective : forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
    intros l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite -> rev_involutive. reflexivity.
Qed.

Inductive natoption : Type :=
    | Some (n : nat)
    | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
    match l with
    | empty => None
    | h :: t => match n with 
        | O => Some h
        | S n' => nth_error t n'
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

Definition hd_error (l : natlist) : natoption :=
    match l with 
    | empty => None
    | h :: t => Some h
    end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l : natlist) (default : nat),
    car default l = option_elim default (hd_error l).
Proof.
    intros l default. induction l as [| h t ].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

End NatList.

Inductive id : Type :=
    | Id (n : nat).

Definition eqb_id (x1 x2 : id) : bool :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.

Theorem eqb_id_refl : forall (x : id), 
    eqb_id x x = true.
Proof.
    intros x. destruct x. simpl.
    rewrite -> eqb_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
    | empty
    | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
    record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record y v d' => if eqb_id x y
                       then Some v
                       else find x d'
    end.

Theorem update_eq : forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
    intros d x v. destruct x. simpl.
    rewrite -> eqb_refl. reflexivity.
Qed.

Theorem update_neq : forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
    intros d x y o H. simpl. rewrite -> H. reflexivity.
Qed.

End PartialMap.

Inductive baz : Type :=
    | Baz1 (x : baz)
    | Baz2 (y : baz) (b : bool).

(*
    The baz type cannot have any
    elements. Because both of its 
    constructors take in a baz instance,
    it is impossible to use either to
    construct a baz instance. 
*)
