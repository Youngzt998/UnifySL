Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Lemma derivable_to_provable {L: Language}{Gamma: ProofTheory L}{nSC: NormalSequentCalculus L Gamma}: 
forall x, |-- x <-> (Empty_set _) |-- x.
Proof.
  intros. rewrite provable_derivable. reflexivity.
Qed.

Lemma consequence_to_valid {L: Language} {MD: Model} {SM: Semantics L MD}{MC: ModelClass MD}:
forall x, valid MC x <-> consequence MC (Empty_set _) x.
Proof.
  intros. unfold valid, consequence. split.
  - intros. apply (H m H0).
  - intros. apply (H m H0). 
    intros. destruct H1.
Qed.


  
  
Definition Lindenbaum_constructable_weakly {A: Type}  (P cP: Ensemble A -> Prop): Prop :=
  forall psi, P (Singleton _ psi) -> exists Psi: sig cP, Included _ (Singleton _ psi) (proj1_sig Psi) /\ P (proj1_sig Psi).

Section Completeness_weak_from_Lindenbaum_constructable_formular.
Context {L: Language}
        {Gamma: ProofTheory L}
        {nSC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kMC: Kmodel -> Prop}
        .
Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis LIN_CD_Weakly:  Lindenbaum_constructable_weakly (consistent) cP.
Hypothesis TRUTH: forall x: expr, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x).
Hypothesis CANON: kMC M.

Lemma general_complete_weakly: weakly_complete Gamma SM (KripkeModelClass _ kMC).
Proof.
  hnf.
  assert (forall x,  ~ |-- x -> ~ valid (KripkeModelClass MD kMC) x).
  Focus 2. {
    intros.
    apply Classical_Prop.NNPP.
    intro.
    destruct (H x H1 H0).
  } Unfocus.
  
  intros. intro. unfold Lindenbaum_constructable_weakly in LIN_CD_Weakly.
  unfold valid in H0.
  assert (consistent (Singleton _ ))

Admitted.
End Completeness_weak_from_Lindenbaum_constructable_formular.
  
  
  
  


Section Completeness_weak_from_Lindenbaum_constructable_set.
Context {L: Language}
        {Gamma: ProofTheory L}
        {nSC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kMC: Kmodel -> Prop}
        .
Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis LIN_CD_Weakly:  forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Hypothesis TRUTH: forall x: expr, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x).
Hypothesis CANON: kMC M.

Lemma general_complete_weak: weakly_complete Gamma SM (KripkeModelClass _ kMC).
Proof.
  intros.
  assert (forall x, ~ (Empty_set _) |-- x -> ~ consequence (KripkeModelClass _ kMC) (Empty_set _) x).
  Focus 2. {
    hnf. intros.
    Print Classical_Prop.
    apply Classical_Prop.NNPP. intro.
    rewrite consequence_to_valid in H0.
    rewrite derivable_to_provable in H1.
    apply (H x H1 H0).
  } Unfocus.
  
  intros. Print deduction_weaken0. Print provable_derivable. Locate NormalSequentCalculus.
  destruct (LIN_CD_Weakly x (Empty_set _) H) as [Psi [? ?]].
  destruct (su_bij _ _ rel Psi) as [n HH].
  specialize (fun x => TRUTH x _ _ HH). clear HH.
  
  assert ((forall x, (Empty_set _) x -> KRIPKE: M, n |= x) /\ ~ KRIPKE: M, n |= x).
  Focus 2. {
    intro. hnf in H3.
    specialize (H3 (KRIPKE: M, n) ltac:(constructor; apply CANON)).
    tauto.
  } Unfocus.
  
  split.
  - intros. destruct H2.
  - rewrite TRUTH.
    intro. apply H1. apply derivable_assum. auto.
Qed.

End Completeness_weak_from_Lindenbaum_constructable_set.
  
  
  
  
  
  