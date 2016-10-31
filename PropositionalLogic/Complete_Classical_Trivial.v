Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition MCS (Var: Type): Type := sig (maximal_consistent (ClassicalPropositionalLogic.G Var)).

Definition canonical_model {Var: Type} (Phi: MCS Var): @model _ (TrivialSemantics.SM Var) :=
  fun p => (proj1_sig Phi (PropositionalLanguage.varp p)).

Lemma truth_lemma {Var: Type}: forall (Phi: MCS Var) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  revert x.
  pose proof @MCS_element_derivable _ _ _ _ _ (ClassicalPropositionalLogic.cpG Var) (proj1_sig Phi) (proj2_sig Phi).
  pose proof @TrivialSemantics.mendelson_consistent Var.
  pose proof @classic_mendelson_consistent _ _ _ _  _ (ClassicalPropositionalLogic.cpG Var).
  apply (@truth_lemma_from_syntactic_reduction  _ _ (PropositionalLanguage.nMendelsonReduction) _ _ H1 H0 _ _ H).
  intros.
  clear H0 H1.
  induction x; try solve [inversion H2].
  + destruct H2.
    specialize (IHx1 H0).
    specialize (IHx2 H1).
Abort.