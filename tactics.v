From LF Require Export Poly.
Require Import Nat.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.
  
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex : forall p,
  (forall n, evenb n = true -> evenb (S n) = false) ->
  (forall n, evenb n = false -> oddb n = true) ->
  evenb p = true ->
  oddb (S p) = true.
Proof.
  intros p h1 h2 h3.
  apply h2. apply h1. apply h3.
Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite H. symmetry. apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  - apply eq1.
  - apply eq2.
Qed.

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2.
  rewrite eq1. apply eq2.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (y:=[c;d]).
  - apply eq1.
  - apply eq2.
Qed.
  

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.
  

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p h1 h2.
  transitivity m.
  - apply h2.
  - apply h1.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as H'.
  apply H'.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  transitivity o.
  - apply H1.
  - symmetry in H2. apply H2.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j h1 h2.
  injection h1 as h1' h1''.
  rewrite <- h1'' in h2.
  injection h2 as h2'.
  transitivity z.
  - apply h1'.
  - symmetry. apply h2'.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.
  
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H.
  discriminate H.
Qed.

Check true.
Theorem eqb_0_l : forall n,
   0 =? n = Datatypes.true -> n = 0.
Proof.
  intros n H.
  destruct n as [| n'].
  - reflexivity.
  - discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal. apply H.
Qed.

Theorem S_inj : forall (n m : nat) (b : Datatypes.bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H. apply H.
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H.
  symmetry. apply H.
Qed.

Theorem specialize_example: forall n,
     (forall m, m*n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. 
Qed.

Lemma nth_error_always_none: forall (l : list nat),
  (forall i, nth_error l i = None) ->
  l = [].
Proof.
  intros l H.
  specialize H with (i := 0).
  destruct l. 
  - reflexivity.
  - simpl in H. discriminate.
Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2.
Qed.

Fixpoint double (n:nat):nat :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m H.
  induction n as [|n'].
  - destruct m.
    + reflexivity.
    + simpl in H. discriminate H.
  - destruct m.
    + discriminate H.
    + f_equal.
Abort.

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m H. destruct m.
     + reflexivity.
     + discriminate H.
  - intros m H. destruct m.
     + discriminate H.
     + simpl in H. injection H as H'. f_equal.
       apply IHn'. apply H'.
Qed.


Theorem eqb_true : forall n m,
  n =? m = Datatypes.true -> n = m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m H. destruct m.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m.
    + discriminate H.
    + f_equal. simpl in H. apply IHn' in H. apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - intros m H. destruct m.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m.
    + discriminate H.
    + simpl in H. injection H as H'. rewrite <- plus_n_Sm in H'.
      rewrite <- plus_n_Sm in H'. injection H' as H''. apply IHn' in H''.
      f_equal. apply H''.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
        (* We are stuck here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  - intros n H. destruct n.
    + reflexivity.
    + discriminate H.
  - intros n H. destruct n.
    + discriminate H.
    + f_equal. apply IHm'. simpl in H. injection H as H'.
      apply H'.
Qed.

Lemma sub_add_leb : forall n m, n <=? m = Datatypes.true -> (m - n) + n = m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m H. rewrite <- plus_n_O. destruct m.
    + reflexivity.
    + reflexivity.
  - intros m H. destruct m.
    + discriminate H.
    + simpl in H. simpl. rewrite <- plus_n_Sm. rewrite IHn'.
      * reflexivity.
      * apply H.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h t IHt].
  - reflexivity.
  - intros n H. destruct n.
    + discriminate H.
    + simpl. simpl in H. injection H as H'. apply IHt in H'. apply H'.
Qed.

Definition square n := n * n.

Print mul.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m). {
       rewrite mult_comm. apply mult_assoc.
  }
  rewrite mult_assoc. rewrite H. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.
  
Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m as [| m'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
  
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (n =? 3).
  - reflexivity.
  - destruct (n =? 5).
    + reflexivity.
    + reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IHt].
  - intros l1 l2 H. destruct l1.
    + destruct l2.
      * reflexivity.
      * discriminate H.
    + discriminate H.
  - intros l1 l2 H. destruct l1 as [|h1 t1].
    + destruct l2 as [|h2 t2].
      * simpl in H. destruct h as [x y]. destruct (split t) as [lx ly].
        discriminate H.
      * simpl in H. destruct h as [x y]. destruct (split t) as [lx ly].
        discriminate H.
    + destruct l2 as [| h2 t2].
      * simpl in H. destruct h as [x y]. destruct (split t) as [lx ly].
        discriminate H.
      * simpl in H. destruct h as [x y]. destruct (split t) as [lx ly].
        simpl. injection H as H1 H2 H3 H4. rewrite H1. rewrite H3.
        f_equal. apply IHt. rewrite H2. rewrite H4. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.
  
Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n H.
  unfold sillyfun1 in H.
  destruct (n =? 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:E.
    - apply eqb_true in E. rewrite E. reflexivity.
    - destruct (n =? 5) eqn:E2.
      + apply eqb_true in E2. rewrite E2. reflexivity.
      + discriminate eq.
 Qed.
 
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  destruct (f true) eqn:E.
  - rewrite E. apply E.
  - destruct (f false) eqn:E'.
    + apply E.
    + apply E'.
  - destruct (f false) eqn:E.
    + destruct (f true) eqn:E'.
      * apply E'.
      * apply E.
    + rewrite E. apply E.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [| n' IHn'].
    - destruct m as [| m'] eqn:E.
      + reflexivity.
      + reflexivity.
    - destruct m as [| m'] eqn:E.
      + reflexivity.
      + simpl. apply IHn'.
Qed.


Theorem eqb_trans : forall n m p,
  n =? m = Datatypes.true ->
  m =? p = Datatypes.true ->
  n =? p = Datatypes.true.
Proof.
  intros n m p h1 h2.
  apply eqb_true in h1.
  apply eqb_true in h2.
  assert (H: forall (a b: nat), a = b -> (a =? b) = Datatypes.true). {
    intros a.
    induction a as [| a'].
      - intros b H.
        + destruct b.
          * reflexivity.
          * discriminate H.
     - intros b H.
       + destruct b.
         * discriminate H.
         * simpl. apply IHa'. injection H as H'. apply H'. 
  }
  apply H.
  transitivity m.
  apply h1.
  apply h2.
Qed.

Print combine.

Definition split_combine_statement : Prop :=
  forall X Y l1 l2 (l : list (X*Y)),
    length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y l1 l2 l.
  generalize dependent l2.
  generalize dependent l1.
  induction l as [| h t IHt].
    - intros l1 l2 h1 h2. destruct l1 as [| x t1].
      + destruct l2 as [| y t2].
        * reflexivity.
        * discriminate h1.
      + destruct l2 as [| y t2].
        * discriminate h1.
        * discriminate h2.
   - intros l1 l2 h1 h2. destruct l1 as [| x t1].
     + destruct l2 as [| y t2].
       * discriminate h2.
       * discriminate h2.
     + destruct l2 as [| y t2].
       * discriminate h2.
       * simpl in h1. injection h1 as h1'.
         simpl in h2. injection h2 as h2' h2''.
         simpl. destruct h as [xx yy]. destruct (split t) as [lx ly].
         f_equal. {
           apply IHt in h1'. {
             injection h1' as lx_eq ly_eq.
             rewrite lx_eq.
             injection h2' as x_eq y_eq.
             rewrite x_eq.
             reflexivity.
           }
           { 
             apply h2''.
           }
         }
         {
            apply IHt in h1'. {
             injection h1' as lx_eq ly_eq.
             rewrite ly_eq.
             injection h2' as x_eq y_eq.
             rewrite y_eq.
             reflexivity.
            }
            {
              apply h2''.
            }
         }
Qed.
