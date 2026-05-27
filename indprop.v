Set Warnings "-notation-overridden".
From LF Require Export Logic.

Fixpoint div2 (n : nat) : nat :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.
  
Definition csf (n: nat) : nat :=
  if evenb n then div2 n else 3 * n + 1.

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even (n: nat) : evenb n = true ->
                      Collatz_holds_for (div2 n) ->
                      Collatz_holds_for n
  | Chf_odd (n: nat) : evenb n = false ->
                     Collatz_holds_for (3 * n + 1) ->
                     Collatz_holds_for n.


Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Conjecture collatz: forall (n:nat), n <> 0 -> Collatz_holds_for n.

Inductive le : nat -> nat -> Prop :=
  | le_n (n: nat) : le n n
  | le_n_m (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m).

Example le_3_5 : le 3 5.
Proof.
  apply le_n_m.
  apply le_n_m.
  apply le_n.
Qed.

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y: X) : R x y -> clos_trans R x y
  | t_trans (x y z: X) : clos_trans R x y -> clos_trans R y z -> clos_trans R x z.
  
Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
    po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.
  
Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.
  
Example ancestor_sage_cleo : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with (y:=Cleo).
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM.
Qed.

Inductive clos_refl_trans {X:Type} (R:X->X->Prop) : X->X->Prop :=
  | rt_step (x y: X) : R x y -> clos_refl_trans R x y
  | rt_refl (x: X) : clos_refl_trans R x x
  | rt_trans (x y z: X) : clos_refl_trans R x y -> clos_refl_trans R y z ->
                          clos_refl_trans R x z.

Definition cs (n m: nat) : Prop := csf n = m.

Definition cms (n m: nat) : Prop := clos_refl_trans cs n m.

Conjecture Collatz' : forall (n:nat), n <> 0 -> cms n 1.

Example collatz_16 : cms 16 1.
Proof.
  apply rt_trans with 8.
  - apply rt_step. reflexivity.
  - apply rt_trans with 4.
    + apply rt_step. reflexivity.
    + apply rt_trans with 2.
      * apply rt_step. reflexivity.
      * apply rt_step. reflexivity.
Qed.
  
Inductive clos_refl_trans_symm {X:Type} (R:X->X->Prop) : X->X->Prop :=
  | rts_step (x y: X) : R x y -> clos_refl_trans_symm R x y
  | rts_refl (x: X) : clos_refl_trans_symm R x x
  | rts_trans (x y z: X) : clos_refl_trans_symm R x y -> clos_refl_trans_symm R y z ->
                          clos_refl_trans_symm R x z
  | rts_symm (x y: X) : clos_refl_trans_symm R x y -> clos_refl_trans_symm R y x.
  

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Lemma ev_Even_firsttry : forall n,
  ev n -> even n.
Proof.
  unfold even.
  intros n H.
  destruct H as [] eqn:EE.
  - exists 0. reflexivity.
  Abort.

Theorem one_not_even' : ~ ev 1.
Proof. intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1. apply H3.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.
  
  
Lemma ev_Even_firsttry' : forall n,
  ev n -> even n.
Proof.
  unfold even.
  intros n E.
  induction E as [| n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k Hk].
    rewrite Hk. exists (S k). simpl. reflexivity.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IH.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even_firsttry'.
  - (* <- *) unfold even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2.
  induction H1 as [| n' H1' IH].
  - simpl. apply H2.
  - simpl. apply ev_SS. apply IH.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hsum Hn.
  induction Hn as [| n' Hn' IH].
  - simpl in Hsum. apply Hsum.
  - simpl in Hsum. inversion Hsum. apply IH. apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
Admitted.

Definition isDiagonal {X : Type} (R: X -> X -> Prop) :=
  forall x y, R x y -> x = y.
Proof.

Lemma closure_of_diagonal_is_diagonal: forall X (R: X -> X -> Prop),
  isDiagonal R ->
  isDiagonal (clos_refl_trans R).
Proof.
  intros X R IsDiag x y H.
  induction H as [x y H | x | x y z H IH H' IH'].
  - unfold isDiagonal in IsDiag. apply IsDiag. apply H.
  - reflexivity.
  - transitivity y.
     + apply IH.
     + apply IH'.
Qed.


Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).


Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H. induction H as [ | | n' m' Hn' IHn' Hm' IHm'].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply IHn'.
      * apply IHm'.
  - intros H. induction H as [ | n' Hn' IHn'].
    + apply ev'_0.
    + replace (S (S n')) with (2 + n').
      * apply ev'_sum. apply ev'_2. apply IHn'.
      * reflexivity.
Qed.

 Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Lemma Perm3_In : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> In x l1 -> In x l2.
Proof.
  intros X x l1 l2 Hperm Hin.
  induction Hperm as [ a b c | a b c | l1 l2 l3 H1 IH1 H2 IH2].
  - unfold In. unfold In in Hin.
    destruct Hin as [Hax | [Hbx | [Hcx | Hfalse]]].
    + right. left. apply Hax.
    + left. apply Hbx.
    + right. right. left. apply Hcx.
    + destruct Hfalse.
  - unfold In in Hin. unfold In.
    destruct Hin as [Hax | [Hbx | [Hcx | Hfalse]]].
    + left. apply Hax.
    + right. right. left. apply Hbx.
    + right. left. apply Hcx.
    + destruct Hfalse.
  - apply IH2. apply IH1. apply Hin.
Qed.


Lemma Perm3_symm : forall (X : Type) (l1 l2 : list X),
  Perm3 l1 l2 -> Perm3 l2 l1.
Proof.
  intros X l1 l2 Hperm.
  induction Hperm as [ a b c | a b c | l1 l2 l3 H1 IH1 H2 IH2].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply perm3_trans with l2.
    + apply IH2.
    + apply IH1.
Qed.


Lemma Perm3_NotIn : forall (X : Type) (x : X) (l1 l2 : list X),
    Perm3 l1 l2 -> ~In x l1 -> ~In x l2.
Proof.
  intros X x l1 l2 Hperm Hin H.
  apply Hin.
  apply Perm3_In with (l1 := l2).
  - apply Perm3_symm.
    apply Hperm.
  - apply H.
Qed.

Example Perm3_example2 : ~ Perm3 [1;2;3] [1;2;4].
Proof.
  intros H.
  apply Perm3_In with (x:=3) in H.
  - unfold In in H.
    + destruct H as [H13 | [H23 | [H34 | Hfalse]]].
      * discriminate H13.
      * discriminate H23.
      * discriminate H34.
      * destruct Hfalse.
  - unfold In. right. right. left. reflexivity.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hno as [ n | n o' H IH].
  - apply Hmn.
  - apply le_n_m.
    apply IH.
    apply Hmn.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_n_m. apply IH.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [ n | n m H IH].
  - apply le_n.
  - apply le_n_m. apply IH.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  induction m as [ | m' IH].
  - destruct n.
  
