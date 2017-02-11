Require Export Coq.Classes.RelationPairs.
Require Import SetoidList.
Require Import Relations Morphisms.
Require Import Equivalence.

Instance pointwise_preorder:
  forall A {B : Type} (RB : relation B),
  PreOrder RB -> PreOrder (pointwise_relation A RB).
Proof.
  intros.
  destruct H.
  constructor.
  + apply pointwise_reflexive; auto.
  + apply pointwise_transitive; auto.
Qed.

Inductive option00_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option00: option00_relation R None None
| Some_Some_option00: forall a b, R a b -> option00_relation R (Some a) (Some b).

Inductive option01_relation {A: Type} (R: relation A): relation (option A):=
| None_None_option01: option01_relation R None None
| None_Some_option01: forall a, option01_relation R None (Some a)
| Some_Some_option01: forall a b, R a b -> option01_relation R (Some a) (Some b).

Instance option00_reflexive {A: Type} (R: relation A) {_: Reflexive R}: Reflexive (option00_relation R).
Proof.
  hnf; intros.
  destruct x.
  + constructor; reflexivity.
  + constructor.
Qed.

Instance option01_reflexive {A: Type} (R: relation A) {_: Reflexive R}: Reflexive (option01_relation R).
Proof.
  hnf; intros.
  destruct x.
  + constructor; reflexivity.
  + constructor.
Qed.

Instance option00_transitive {A: Type} (R: relation A) {_: Transitive R}: Transitive (option00_relation R).
Proof.
  hnf; intros.
  hnf; intros.
  inversion H0; inversion H1; subst; try first [congruence | constructor].
  inversion H6; subst.
  etransitivity; eauto.
Qed.

Instance option01_transitive {A: Type} (R: relation A) {_: Transitive R}: Transitive (option01_relation R).
Proof.
  hnf; intros.
  hnf; intros.
  inversion H0; inversion H1; subst; try first [congruence | constructor].
  inversion H6; subst.
  etransitivity; eauto.
Qed.

Instance option00_preorder {A: Type} (R: relation A) {_: PreOrder R}: PreOrder (option00_relation R)
  := Build_PreOrder _ (option00_reflexive R) (option00_transitive R).

Instance option01_preorder {A: Type} (R: relation A) {_: PreOrder R}: PreOrder (option01_relation R)
  := Build_PreOrder _ (option01_reflexive R) (option01_transitive R).

Inductive sum00_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum00_ll a1 a2: RA a1 a2 -> sum00_relation RA RB (inl a1) (inl a2)
  | sum00_rr b1 b2: RB b1 b2 -> sum00_relation RA RB (inr b1) (inr b2).

Inductive sum01_relation {A B: Type} (RA: relation A) (RB: relation B): relation (A + B) :=
  | sum01_ll a1 a2: RA a1 a2 -> sum01_relation RA RB (inl a1) (inl a2)
  | sum01_lr a b: sum01_relation RA RB (inl a) (inr b)
  | sum01_rr b1 b2: RB b1 b2 -> sum01_relation RA RB (inr b1) (inr b2).

Instance sum00_reflexive {A B: Type} (RA: relation A) (RB: relation B) {_: Reflexive RA} {_: Reflexive RB}: Reflexive (sum00_relation RA RB).
Proof.
  hnf; intros.
  destruct x; constructor; auto.
Qed.

Instance sum01_reflexive {A B: Type} (RA: relation A) (RB: relation B) {_: Reflexive RA} {_: Reflexive RB}: Reflexive (sum01_relation RA RB).
Proof.
  hnf; intros.
  destruct x; constructor; auto.
Qed.

Instance sum00_transitive {A B: Type} (RA: relation A) (RB: relation B) {_: Transitive RA} {_: Transitive RB}: Transitive (sum00_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; inversion H2; subst;
  constructor;
  etransitivity; eauto.
Qed.

Instance sum01_transitive {A B: Type} (RA: relation A) (RB: relation B) {_: Transitive RA} {_: Transitive RB}: Transitive (sum01_relation RA RB).
Proof.
  hnf; intros.
  inversion H1; subst; inversion H2; subst;
  constructor;
  etransitivity; eauto.
Qed.

Instance sum00_preorder {A B: Type} (RA: relation A) (RB: relation B) {_: PreOrder RA} {_: PreOrder RB}: PreOrder (sum00_relation RA RB) :=
  Build_PreOrder _ (sum00_reflexive RA RB) (sum00_transitive RA RB).

Instance sum01_preorder {A B: Type} (RA: relation A) (RB: relation B) {_: PreOrder RA} {_: PreOrder RB}: PreOrder (sum01_relation RA RB) :=
  Build_PreOrder _ (sum01_reflexive RA RB) (sum01_transitive RA RB).

Definition true_relation (A: Type): relation A := fun _ _ => True.

Instance true_reflexive (A: Type): Reflexive (true_relation A).
Proof.
  hnf; intros.
  hnf; auto.
Qed.

Instance true_transitive (A: Type): Transitive (true_relation A).
Proof.
  hnf; intros.
  hnf; auto.
Qed.

Instance true_preorder (A: Type): PreOrder (true_relation A) :=
  Build_PreOrder _ (true_reflexive A) (true_transitive A).

