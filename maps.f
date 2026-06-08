Require Import Arith.
Require Import Bool.
Require Import String.
Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.

Check String.eqb_refl.

Check String.eqb_eq.
Check String.eqb_neq.
Check String.eqb_spec.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
  
Definition t_update {A: Type} (m: total_map A)
            (x: string) (v: A) :=
    fun x' => if String.eqb x x' then v else m x'.
    
Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Compute examplemap "t".

Notation "'__' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := ( false).

Notation "x '!->' v ';' m" := (t_update m x v)
                                (at level 100, v constr at level 100, right associativity).
  
Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    __ !-> false
  ).


Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (__ !-> v) x = v.
Proof.
  intros A x v.
  unfold t_empty.
  reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update.
  destruct (x=?x)%string eqn:E.
  - reflexivity.
  - apply String.eqb_neq in E.
    exfalso. apply E. reflexivity.
Qed.


Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold t_update.
  rewrite <- String.eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality.
  intros x0.
  unfold t_update.
  destruct (x=?x0)%string eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros A m x.
  apply functional_extensionality.
  intros x0.
  unfold t_update.
  destruct (x=?x0)%string eqn:E.
  - apply String.eqb_eq in E.
    rewrite E. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality.
  intros x.
  unfold t_update.
  destruct (x1=?x)%string eqn:E.
  - 
  
