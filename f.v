(* Chapter 1 Basics *)
Require Import Nat.
From LF Require Export Induction.
From LF Require Export Lists.
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

Theorem plus_0_l : forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
  

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
  

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
  rewrite plus_0_l.
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

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
  

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite plus_0_r. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
  
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc. replace (n + m) with (m + n).
    - rewrite add_assoc. reflexivity.
    - rewrite add_comm. reflexivity.
Qed.

Theorem m_mul_sn : forall n m: nat,
  m * S n = m + m * n.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - reflexivity.
  - simpl. rewrite IHm'. rewrite add_shuffle3. reflexivity.
Qed.

Theorem mul_comm:
  forall n m: nat,
  n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite mult_0_r. reflexivity. 
  - simpl. rewrite m_mul_sn. rewrite IHn'. reflexivity.
Qed.

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

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite plus_0_r. reflexivity.
Qed.
  
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    -- reflexivity.
    -- reflexivity.
  - destruct c.
    -- reflexivity.
    -- reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p' IHp'].
  - rewrite !mult_0_r. reflexivity.
  - rewrite !m_mul_sn.
    rewrite add_assoc. rewrite (add_comm (n + n * p') (m)). rewrite add_assoc. rewrite (add_comm m n). rewrite IHp'.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite mult_plus_distr_r. reflexivity.
Qed.
  
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
  
Fixpoint incr (m:bin) : bin :=
  match m with
    | Z => B1 Z
    | B0 m' => B1 m'
    | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
    | Z => O
    | B0 m' => double (bin_to_nat m')
    | B1 m' => S (double (bin_to_nat m'))
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.
Example test_bin_incr7 : bin_to_nat (B0 (B0 (B0 (B1 Z)))) = 8.
Proof. reflexivity. Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  simpl.
  induction b as [| b' IHb' | b'' IHb''].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHb''. reflexivity. 
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
   | O => Z
   | S n' => incr (nat_to_bin n')
  end.
  
Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof. reflexivity. Qed.

Definition double_bin (b:bin) : bin :=
  match b with
    | Z => Z
    | b' => B0 b
  end.
  
Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b.
  destruct b as [| b' | b''].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Proof.
Abort.

Definition is_Z (b: bin) : bool :=
  match b with
    | Z => true
    | _ => false
  end.

Fixpoint normalize (b:bin) : bin :=
  match b with
    | Z => Z
    | B0 b' => double_bin (normalize b')
    | B1 b' => incr (double_bin (normalize b'))
  end.
  
Compute normalize (B1 (B0 (B0 (B0 (B1 (B1 (B0 (B0 (B0 (B0 Z)))))))))).

Lemma double_nat_to_bin: forall n: nat,
  nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite double_incr_bin. reflexivity.
Qed.  

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b.
  induction b as [| b' IHb' | b'' IHb''].
  - reflexivity.
  - simpl. rewrite double_nat_to_bin. rewrite IHb'. reflexivity.
  - simpl. rewrite double_nat_to_bin. rewrite IHb''. reflexivity.
Qed.

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
  simpl. rewrite eqb_refl. reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_add_inc_count : option (nat*string) := None.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_len_pred: forall l:natlist,
  pred (len l) = len (tl l).
Proof.
  intros l.
  destruct l as [| h t].
  - reflexivity.
  - reflexivity.
Qed.

Theorem app_assoc: forall l1 l2 l3:natlist,
  (l1++l2)++l3 = l1++(l2++l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| h1 t1 IHl1].
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.
  
  
Theorem repeat_double_firsttry: forall n c1 c2:nat,
  (repeat n c1) ++ (repeat n c2) = repeat n (c1+c2).
Proof.
  intros n c1 c2.
  induction c1 as [| c1' IHc1'].
  - reflexivity.
  - simpl. rewrite IHc1'. reflexivity.
Qed.
  
  
Fixpoint rev (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h::t => (rev t) ++ cons (h) []
  end.
  
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. simpl. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttr: forall l:natlist,
  len (rev l) = len l.
Proof.
  intros l.
  induction l as [| h t].
  - reflexivity.
  - simpl.
Abort.

Lemma app_len: forall l1 l2: natlist,
  len (l1 ++ l2) = len l1 + len l2.
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  len (rev l) = len l.
Proof.
  intros l.
  induction l as [| h t IHt].
    - reflexivity.
    - simpl. rewrite app_len. simpl. rewrite IHt.
      rewrite add_comm. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [ | h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHt1].
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHt1. rewrite app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IHt.
    reflexivity.
 Qed.
 
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as [| h1 t1 IHt1].
  - simpl. rewrite app_assoc. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - reflexivity.
  - simpl. destruct h1.
    -- rewrite IHt1. reflexivity.
    -- rewrite IHt1. reflexivity.
Qed.
    
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | [], [] => true
    | [], h::t => false
    | h::t, [] => false
    | h1::t1, h2::t2 => if h1 =? h2 then eqblist t1 t2
                        else false
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
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite eqb_refl. rewrite IHt.
    reflexivity.
Qed.
  
  
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s.
  destruct s as [| h t].
  - reflexivity.
  - reflexivity.
Qed.


Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity. 
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s as [| h t IHt].
  - reflexivity.
  - simpl. destruct h; simpl.
    -- rewrite leb_n_Sn. reflexivity.
    -- rewrite IHt. reflexivity. 
Qed.

Print count. Print sum.

Theorem bag_count_sum: forall s1 s2: bag, forall n: nat,
  count n (sum s1 s2) = count n s1 + count n s2.
Proof.
  intros s1 s2 n.
  induction s1 as [| h1 t1 IHt1].
  - reflexivity.
  - simpl. destruct (h1 =? n).
     -- rewrite IHt1. reflexivity.
     -- rewrite IHt1. reflexivity.
Qed.

Theorem involution_injective: forall (f: nat->nat),
  (forall n: nat, n = f (f n)) -> 
      (forall n1 n2: nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H1 n1 n2 H2.
  rewrite H1. rewrite <- H2. rewrite <- H1.
  reflexivity.
Qed.

Theorem rev_injective: forall (l1 l2: natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite rev_involutive.
  reflexivity.
Qed.
  
  
Inductive natoption: Type :=
  | Some (n: nat)
  | None.
  
Fixpoint nth_error (l:natlist) (n:nat):natoption :=
  match l with
   | nil => None
   | h::t => match n with
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
   | nil => None
   | h::t => Some h
  end.
  
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l.
  destruct l as [| h t]; reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id (n:nat).
  
Definition eqb_id (x1 x2:id) :=
  match x1, x2 with
    | Id y1, Id y2 => y1 =? y2
  end.

Theorem eqb_id_refl: forall i: id,
  eqb_id i i = true.
Proof.
  intros i.
  destruct i. simpl.
  rewrite eqb_refl. reflexivity.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map: Type :=
  | empty
  | record (i:id) (v:nat) (m:partial_map).
  
Definition update (d : partial_map)
                  (x:id) (value: nat) :=
  record x value d.
  
Fixpoint find (i: id) (d: partial_map): natoption :=
  match d with
   | empty => None
   | record k v d' => if eqb_id i k then Some v
                       else find i d'
  end.
  
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite eqb_id_refl.
  reflexivity.
Qed.


Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl. rewrite H. reflexivity.
Qed.

End PartialMap.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
  
Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint length {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length t)
  end.

Example test_length1: length (cons 1 (cons 2 (nil))) = 2.
Proof. reflexivity. Qed.

Example test_length2: length (cons true (nil)) = 1.
Proof. reflexivity. Qed.

Fixpoint app {X:Type} (l1 l2 : list X) : list X :=
  match l1 with
    | nil      => l2
    | cons h t => cons h (app t l2)
  end.
  


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
  
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | h::t => (rev t) ++ ([h])
  end.
Example test_rev1: rev (cons 1 (cons 2 (nil))) =
                   (cons 2 (cons 1 (nil))).
Proof. reflexivity. Qed.

Example test_rev2: @rev bool nil = nil.
Proof. reflexivity. Qed.
Theorem app_nil_r : forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h t IHt].
    - reflexivity.
    - simpl. rewrite IHt. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros X l m n.
  induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| h1 t1 IHt1].
    - simpl. rewrite app_nil_r. reflexivity.
    - simpl. rewrite IHt1. rewrite app_assoc. reflexivity. 
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h t].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHt. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.
  
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
  
Fixpoint combine {X Y: Type} (l1: list X) (l2 : list Y): list (X*Y) :=
  match l1, l2 with
    | [], _ => []
    | _, [] => []
    | h1::t1, h2::t2 => (h1, h2)::(combine t1 t2)
  end.
 
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : ((list X) * (list Y)) :=
  match l with
    | [] => ([], [])
    | (x, y)::t => match split t with
                    | (t1, t2) => (x::t1, y::t2)
                  end
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl.
  reflexivity.
Qed.

Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.

Fixpoint nth_error {X: Type} (l: list X) (n:nat) : option X := 
  match l with
    | [] => None
    | h::t => match n with
              | O => Some h
              | S n' => nth_error t n'
             end
  end.
  
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | h::t => Some h
  end.

Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

End OptionPlayground.

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).
  
Check @doit3times : forall X : Type, (X -> X) -> X -> X.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X: Type} (l: list X) (f: X -> bool) : list X :=
  match l with
    | [] => []
    | h::t => if f h then h::(filter t f)
              else filter t f
  end.
  
Example test_filter1: filter [1;2;3;4] evenb = [2;4].
Proof. reflexivity. Qed.

Example test_filter2':
    filter [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] (fun l => (length l) =? 1)
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.


Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X := (filter l test, filter l (fun x => if test x then false
                                                                          else true)).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f: X -> Y) (l : list X) : list Y :=
  match l with
    | [] => []
    | h::t => (f h)::(map f t)
  end.
  
Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. simpl. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. simpl. reflexivity.
Qed.

Lemma map_app_distr : forall (X Y: Type) (f: X -> Y) (l1 l2: list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - simpl. reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite map_app_distr. rewrite IHt. simpl. reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : list Y :=
  match l with
    | [] => []
    | h::t => (f h) ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.
  
  
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
  
Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Example foldexample4 :
  fold (fun l n => length l + n) [[1];[];[2;3;2];[4]] 0 = 5.
Proof. reflexivity. Qed.


Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat) => x.
 
Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.

Example test_plus3: plus3 10 = 13.
Proof. reflexivity. Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

Definition fold_length {X:Type} (l:list X) : nat :=
  fold (fun _ n => S n) l 0.
  
Theorem fold_length_correct:
  forall X (l:list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [|h t IHt].
  - reflexivity.
  - simpl. rewrite <- IHt. unfold fold_length. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x l => (f x)::l) l [].
  
Theorem fold_map_correct:
  forall X Y (l:list X) (f:X->Y),
  fold_map f l = map f l.
Proof.
  intros X Y l f.
  induction l as [| h t IHt].
  - reflexivity.
  - simpl. rewrite <- IHt. unfold fold_map. simpl. reflexivity.
Qed.







  
