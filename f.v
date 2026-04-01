(* Chapter 1 Basics *)
Require Import Nat.
Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Check day_rect.  (* types *)
Check day_ind.   (* props *)
Check day_rec.   (* sets  *)

Definition next_weekday (d:day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | _         => monday
  end.

Eval compute in next_weekday friday. (* monday *)
Eval compute in next_weekday (next_weekday saturday). (* tuesday *)

Example test_next_weekday : next_weekday (next_weekday saturday) = tuesday.
Proof. simpl. reflexivity. Qed.


(* Booleans *)
Module PlayGroundBool.
Inductive bool : Type :=
| true : bool
| false : bool.
End PlayGroundBool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: orb true false = true.
Proof. reflexivity. Qed.

Example test_orb2: orb false false = false.
Proof. reflexivity. Qed.

Example test_orb3: orb false true = true.
Proof. reflexivity. Qed.

Example test_orb4: orb true true = true.
Proof. reflexivity. Qed.


(* Exercise: * nandb *)
Definition nandb (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => false
    | _,    _    => true
  end.

Example test_nandb1: nandb true false = true.
Proof. reflexivity. Qed.

Example test_nandb2: nandb false false = true.
Proof. reflexivity. Qed.

Example test_nandb3: nandb false true = true.
Proof. reflexivity. Qed.

Example test_nandb4: nandb true true = false.
Proof. reflexivity. Qed.

(* Exercise: * andb3 *)
Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _,    _,    _    => false
  end.

Example test_andb31: andb3 true true true = true.
Proof. reflexivity. Qed.

Example test_andb32: andb3 false true true = false.
Proof. reflexivity. Qed.

Example test_andb33: andb3 true false true = false.
Proof. reflexivity. Qed.

Example test_andb34: andb3 true true false = false.
Proof. reflexivity. Qed.


(* Function Types *)

Check true.        (* bool *)
Check (negb true). (* bool *)
Check negb.        (* bool -> bool *)
Check andb.        (* bool -> bool -> bool *)


(* Numbers *)

Module Playground1.

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  Definition pred (n:nat) : nat :=
    match n with
      | O    => O
      | S n' => n'
    end.
End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O        => O
    | S O      => O
    | S (S n') => n'
  end.

Check S (S (S (S O))).      (* 4 : nat *)
Eval compute in minustwo 4. (* 2 : nat *)

Check S.        (* nat -> nat *)
Check pred.     (* nat -> nat *)
Check minustwo. (* nat -> nat *)

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O        => true
    | S O      => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb (S O) = true.
Proof. reflexivity. Qed.

Example test_oddb2: oddb (S (S (S (S 0)))) = false.
Proof. reflexivity. Qed.


Module Playground2.
  Fixpoint plus (n m : nat) : nat :=
    match n with
      | O    => m
      | S n' => S (plus n' m)
    end.

  Eval compute in plus (S (S (S O))) (S (S O)).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O    => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1: mult 3 3 = 9.
  Proof. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
      | O, _ => O
      | _, O => n
      | S n', S m' => minus n' m'
    end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O   => S O
    | S p => mult base (exp base p)
  end.

(* Exercise: * factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O    => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: factorial 3 = 6.
Proof. reflexivity. Qed.

Example test_factorial2: factorial 5 = mult 10 12.
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O       => true
    | S n', S m' => beq_nat n' m'
    | _, _       => false
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n, m with
    | O, _       => true
    | S n', S m' => ble_nat n' m'
    | _, _       => false
  end.

Example test_ble_nat1: ble_nat 2 2 = true.
Proof. reflexivity. Qed.

Example test_ble_nat2: ble_nat 2 4 = true.
Proof. reflexivity. Qed.

Example test_ble_nat3: ble_nat 4 2 = false.
Proof. reflexivity. Qed.


(* Exerice: ** blt_nat *)
Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: blt_nat 2 2 = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: blt_nat 2 4 = true.
Proof. reflexivity. Qed.

Example test_blt_nat3: blt_nat 4 2 = false.
Proof. reflexivity. Qed.


(* Proof by Simplification *)

Theorem plus_0_n : forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(* Theorem, Example, Lemma, Fact, Remark: all meant the same thing to Coq. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.


(* Proof by Rewriting *)

Theorem plus_id_example : forall n m : nat,
                            n = m ->
                            n + n = m + m.
Proof.
  intros n m.   (* Introduce things into the context *)
  intros H.     (* Introduce hypothesis into the context, and call it H *)
  rewrite -> H. (* Replace LHS H with RHS H in the goal *)
  reflexivity.
Qed.


(* Exercise: * plus_id_exercise *)
Theorem plus_id_exercise : forall n m o : nat,
                             n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite H1. rewrite <- H2.
  reflexivity.
Qed.


Theorem mult_0_plus : forall n m : nat,
                        (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_0_n.
  reflexivity.
Qed.


(* Exercise: ** mult_S_1 *)
Theorem mult_S_1 : forall n m : nat,
                     m = S n ->
                     m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.


(* Proof by Case Analysis *)

Theorem plus_1_neq_0_firsttry : forall n:nat,
                                  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* does nothing *)
Abort.

Theorem plus_1_neq_0 : forall n:nat,
                         beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.


Theorem negb_involutive : forall b:bool,
                            negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity. reflexivity.
Qed.


(* Exercise: * zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1 : forall n:nat,
                             beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.


(* More Exercises *)

(* Exercise: ** boolean functions *)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
                                    (forall (x : bool), f x = x) ->
                                    forall b:bool, f (f b) = b.
Proof.
  intros.
  destruct b.
  rewrite H. rewrite H. reflexivity.
  rewrite H. rewrite H. reflexivity.
Qed.

Theorem negation_fn_applied_twice :  forall (f : bool -> bool),
                                    (forall (x : bool), f x = negb x) ->
                                    forall b:bool, f (f b) = b.
Proof.
  intros.
  destruct b.
  rewrite H. rewrite H. rewrite negb_involutive. reflexivity.
  rewrite H. rewrite H. rewrite negb_involutive. reflexivity.
Qed.


(* Exercise: ** andb_eq_orb *)
Theorem andb_eq_orb : forall b c : bool,
                        andb b c = orb b c ->
                        b = c.
Proof.
  intros b c.
  destruct b.
  destruct c.
  intros H. reflexivity.
  intros H. simpl in H. rewrite H. reflexivity.

  destruct c.
  intros H. simpl in H. rewrite H. reflexivity.
  intros H. reflexivity.
Qed.


(* Exercise: *** binary *)
Inductive bin : Type :=
| zero       : bin
| twice      : bin -> bin
| twicePlus1 : bin -> bin.

Fixpoint increment (b:bin) : bin :=
  match b with
    | zero          => twicePlus1 b
    | twice b'      => twicePlus1 b'
    | twicePlus1 b' => twice (increment b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
    | zero          => O
    | twice b'      => mult 2 (bin_to_nat b')
    | twicePlus1 b' => plus 1 (mult 2 (bin_to_nat b'))
  end.

Example inc_bin_to_nat_1 : bin_to_nat (increment zero) = 1.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_2 : bin_to_nat (increment (twice zero)) = 1.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_3 : bin_to_nat (increment (twicePlus1 zero)) = 2.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_4 : bin_to_nat (increment (twice (twicePlus1 zero))) = 3.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_5 :
  bin_to_nat (increment (twice (twice (twicePlus1 zero)))) = 5.
Proof. reflexivity. Qed.


(* Exercise: ** optional decreasing *)

(* Write a simple fixpoint function on numbers that does terminate on all inputs
   but Coq won't accept because a term isn't decreasing
*)
(*
Fixpoint not_zero (n:nat) : nat :=
  match n with
    | O    => not_zero (S n) (* increases *)
    | S n' => S n'           (* returns same thing *)
  end.
*)

Theorem mul_comm:
  forall a b: nat,
  a*b = b * a.
Proof.
Admitted.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem eqb_refl: forall n:nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
  
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  reflexivity.
Qed.
  
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
  
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity.
Qed.

From LF Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
  
Notation "( x , y )" := (pair x y).
  
Definition fst (p: natprod): nat :=
  match p with
    | (x, y) => x
  end.

Definition snd (p: natprod): nat :=
  match p with
    | (x,y) => y
  end.
  
Compute (fst (pair 3 5)).
Compute (snd (pair 4 10)).

Definition swap_pair (p: natprod): natprod :=
  match p with
    | (x, y) => (y,x)
  end.
  
Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

Inductive natlist :=
  | nil
  | cons (n: nat) (l: natlist).
  
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count: nat) : natlist :=
  match count with
    | O => []
    | S count' => n::(repeat n count')
  end.
  
Compute (repeat 10 20).

Fixpoint len (l : natlist) : nat :=
  match l with
    | [] => O
    | n::l' => 1 + (len l')
  end.

Compute (len ([10; 20; 30; 1; 5])).

Fixpoint app (l1 l2: natlist) : natlist :=
  match l1 with
    | [] => l2
    | h::t => h::(app t l2)
  end.
  
Compute (app [10; 20; 30; 1; 5] [10; 20; 30; 1; 5]).

 Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. simpl. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. simpl. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof.  reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.


Fixpoint nonzeros (l:natlist) : natlist :=
  match l with 
    | [] => []
    | h::t => match h with
              | O => nonzeros t
              | x => x::(nonzeros t)
             end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity.
Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | [] => []
    | h::t => if (even h) then oddmembers t
              else h::(oddmembers t)
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  simpl.
  reflexivity.
Qed.


Definition countoddmembers (l:natlist) : nat :=
  len (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity.
Qed.


Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, nil => []
    | [], _ => l2
    | _, [] => l1
    | h1::t1, h2::t2 => h1::(h2::(alternate t1 t2))
  end.


Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
  simpl. reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.


Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | [] => O
    | h::t => if h =? v then 1 + (count v t)
              else (count v t)
  end.
  
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity.
Qed.

Definition add (v : nat) (s : bag) : bag :=
  v::s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.
Fixpoint member (v : nat) (s : bag) : bool := 
  match s with
    | [] => false
    | h::t => if h =? v then true
               else member v t
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | [] => []
    | h::t => if v =? h then t
              else h::(remove_one v t)
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

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if h =? v then remove_all v t
              else h::(remove_all v t)
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
    | [] => true
    | h::t => if (count h s1) <=? (count h s2) then included t s2
              else false
  end.
Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem add_inc_count : 
  forall n: nat, forall l : natlist,
  count n (add n l) = S (count n l).
Proof.
  intros n l.
  simpl. rewrite <- eqb_refl. reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_add_inc_count : option (nat*string) := None.

Theorem nil_app : ∀ l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.



