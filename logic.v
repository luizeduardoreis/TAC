Require Import Nat.
From LF Require Import Poly.
Require Import Setoids.Setoid.
Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  apply conj.
  - destruct n.
    + reflexivity.
    + discriminate H.
  - destruct m.
    + reflexivity.
    + rewrite <- plus_n_Sm in H. discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros.
  apply plus_is_O in H.
  destruct H as [Hn _].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.
  
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros.
  destruct H as [_ HQ].
  apply HQ.
Qed.


Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply conj.
    - apply HQ.
    - apply HP.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  apply conj.
    - apply conj.
      + apply HP.
      + apply HQ.
    - apply HR.
Qed.

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. symmetry. apply mult_n_O.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B H.
  left.
  apply H.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [| n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n'] m H.
  - left. reflexivity.
  - right. simpl in H. apply plus_is_O in H.
    apply proj1 in H. apply H.
Qed.


Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Theorem not_implies_our_not : forall (P:Prop),
 ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  unfold not.
  intros P H Q HP.
  apply H in HP. destruct HP.
Qed.

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HnotP].
  unfold not in HnotP.
  apply HnotP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros H1.
  apply H1 in H.
  destruct H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros P Q H H1 H2.
  apply H1. apply H. apply H2.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  unfold not.
  intros P [HP HPF].
  apply HPF. apply HP.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros.
  apply conj.
  - intros H1. apply H. left. apply H1.
  - intros H1. apply H. right. apply H1.
Qed.

Lemma not_S_pred_n : ~(forall n : nat, S (pred n) = n).
Proof.
  unfold not.
  intros.
  specialize (H 0).
  discriminate H.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  unfold not in H.
    - exfalso. apply H. reflexivity.
    - reflexivity.
Qed.

Lemma True_is_true: True.
Proof. apply I. Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with
    | O => True
    | S _ => False
  end.
  
Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn 0). {
     simpl. apply I.
  }
  rewrite contra in H. simpl in H. apply H.
Qed.

Definition list_fn (X : Type) (l: list X) : Prop :=
  match l with
    | [] => True
    | x::xs => False
  end.

Arguments list_fn {X}.

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x::xs).
Proof.
  intros X x xs H.
  assert (Hnil: @list_fn X []). {
    simpl. apply I. 
  }
  rewrite H in Hnil. simpl in Hnil. apply Hnil.
Qed.

Print "<->".

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HQ HP].
  apply conj.
    - apply HP.
    - apply HQ.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros [].
  - apply conj.
    + intros H. exfalso. apply H. reflexivity.
    + intros H. discriminate H.
  - apply conj.
    + reflexivity.
    + intros H H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R.
  intros Hiff H2 H3.
  apply H2.
  apply Hiff in H3.
  apply H3.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R.
  intros Hiff H1 H2.
  apply Hiff in H2. apply H1 in H2.
  apply H2.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  apply conj.
    - intros HP.
      apply HP.
    - intros HP.
      apply HP.
Qed.
  
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HiffPQ HiffQR.
  apply conj.
    - intros HP.
      apply HiffQR. apply HiffPQ.
      apply HP.
    - intros HR.
      apply HiffPQ.
      apply HiffQR.
      apply HR.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  apply conj.
    - intros [HP | [HQ HR]].
      + apply conj.
        * left. apply HP.
        * left. apply HP.
      + apply conj.
        * right. apply HQ.
        * right. apply HR.
   - intros [[HP1 | HQ] [HP2 | HR]].
     + left. apply HP1.
     + left. apply HP1.
     + left. apply HP2.
     + right. apply conj.
       * apply HQ.
       * apply HR.
Qed.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.


Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  rewrite plus_assoc.
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P Hforall [x E].
  apply E. apply Hforall.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
    - intros [a [HPa | HQa]].
      + left. exists a. apply HPa.
      + right. exists a. apply HQa.
    - intros [[a HPa] | [b HQb]].
      + exists a. left. apply HPa.
      + exists b. right. apply HQb.
Qed.

Lemma sub_add_leb : forall n m, n <=? m = true -> (m - n) + n = m.
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

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  intros n m H.
  exists (m - n).
  rewrite plus_comm.
  symmetry. apply sub_add_leb.
  apply H.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - intros m [a Ha]. destruct m.
    + simpl in Ha. discriminate Ha.
    + simpl. simpl in Ha. apply IHn'.
      exists a. injection Ha as Ha'.
      apply Ha'.
Qed.

Fixpoint In {A: Type} (x: A) (l: list A) : Prop :=
  match l with
    | [] => False
    | h::t => (h = x) \/ (In x t)
  end.
  
Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H2n | [H4n | []]].
  - rewrite <- H2n. exists 1. reflexivity.
  - rewrite <- H4n. exists 2. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x H.
  induction l as [|h t IHt].
  - destruct H.
  - simpl. destruct H as [H_eq_h | Hin].
    + left. f_equal. apply H_eq_h.
    + right. apply IHt. apply Hin.
Qed.

Theorem In_map' :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.


Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
    - induction l as [|h t IHt].
      + intros [].
      + intros [Heq | Hin].
        * exists h. split. {
          apply Heq.
        } {
          simpl. left. reflexivity.
        }
        * simpl. apply IHt in Hin. destruct Hin as [a [Hina Hina']].
          exists a. split. {
            apply Hina.
          } {
            right. apply Hina'.
          }
    - induction l as [| h t IHt].
      + intros [a H]. destruct H. destruct H0.
      + simpl. intros [a Ha]. destruct Ha as [H_eq_y [H_eq_a | Hin]].
        * left. rewrite H_eq_a. apply H_eq_y.
        * right. apply IHt. exists a. split. apply H_eq_y. apply Hin.
Qed.


Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l.
  induction l as [|h t IHt].
    - intros l' a.
      simpl. split.
      + intros H. right.
        apply H.
      + intros [[] | H].
        apply H.
    - intros l' a. simpl. rewrite IHt. rewrite or_assoc. reflexivity.
Qed.


Theorem In_map_iff' :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  induction l as [| h t IHt].
  - simpl. split.
    + intros H. destruct H.
    + intros [a [Ha Hfalse]].
      apply Hfalse.
  - simpl. rewrite IHt. split.
    + intros [H | [a [H_eq_y Hin]]].
      * exists h. split. {
        apply H.
      } {
        left. reflexivity.
      }
      * exists a. split. { apply H_eq_y. }
        { right. apply Hin. }
    + intros [a [H_eq_y [H_eq_a | Hin]]].
      * left. rewrite H_eq_a. apply H_eq_y.
      * right. exists a. split. { apply H_eq_y. } { apply Hin. }
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
    | [] => True
    | h::t => (P h) /\ (All P t)
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  induction l as [| h t IHt].
    - simpl. split.
      + intros H. apply I.
      + intros H x H2. destruct H2.
    - simpl. split.
      + intros H. split.
        * apply H. left. reflexivity.
        * rewrite <- IHt. intros x. intros H1. apply H. right. apply H1.
      + intros [H1 H2] x [H_eq_x | Hin].
        * rewrite <- H_eq_x. apply H1.
        * rewrite <- IHt in H2. apply H2 in Hin. apply Hin.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (x: nat) => if oddb x then Podd x else Peven x.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even. destruct (oddb n).
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1. rewrite H2 in H1.
  apply H1.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.


Check plus_comm : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

Fixpoint soma_list (l : list nat) : nat :=
  match l with
    | [] => 0
    | h::t => h + (soma_list t)
  end.

Theorem app_soma_list : forall (l1 l2 : list nat),
  soma_list l1 + soma_list l2 = soma_list (l1 ++ l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt1. rewrite plus_assoc. reflexivity.
Qed.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros n y z.
  rewrite plus_comm.
  assert (H: y + z = z + y). {
    rewrite plus_comm. reflexivity.
  }
  rewrite H. reflexivity.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (plus_comm (z + y) (x)).
  rewrite (plus_comm z y).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H Hnot.
  rewrite Hnot in H.
  destruct H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l. apply (in_not_nil nat 42).
Qed.

Lemma in_not_nil_42' :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.


Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
Qed.

Print Assumptions functional_extensionality.

 Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_rev : forall (X: Type) (l1 l2: list X),
  rev_append l1 l2 = (rev l1) ++ l2.
Proof.
  intros X l1.
  induction l1 as [| h1 t1 IHt1].
    - reflexivity.
    - intros l2. simpl. rewrite IHt1. rewrite <- app_assoc.
      simpl. reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  unfold tr_rev.
  destruct l as [|h t].
  - reflexivity.
  - simpl. apply rev_append_rev.
Qed.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P b H.
  destruct b.
  - left. apply H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof. Admitted.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.


  
