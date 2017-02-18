Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Definition at_least_derivable_closed
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> derivable_closed Phi.

Definition at_least_consistent
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> consistent Phi.

Definition at_least_orp_witnessed
           {L: Language}
           {nL: NormalLanguage L}
           {pL: PropositionalLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> orp_witnessed Phi.

Definition Linderbaum_derivable
           {L: Language}
           {nL: NormalLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi x, ~ Phi |-- x -> exists Psi: sig P, Included _ Phi (proj1_sig Psi) /\ ~ (proj1_sig Psi) |-- x.

Section Canonical.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
(*        {kiSM: KripkeIntuitionisticSemantics L MD M SM} *)
        {kpSM: KripkePropositionalSemantics L MD M SM}.

Context (P: context -> Prop)
        (rel: bijection (Kworlds M) (sig P)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Lemma denote_monotonic (x: expr):
  (forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)) ->
  upwards_closed_Kdenote (Kdenotation M x).
Proof.
  intros.
  hnf; intros.
  change (KRIPKE: M, m |= x).
  change (KRIPKE: M, n |= x) in H1.
  destruct (im_bij _ _ rel n) as [Phi ?].
  destruct (im_bij _ _ rel m) as [Psi ?].
  erewrite H in H1 |- * by eauto.
  eapply H_R in H0; eauto.
  apply H0; auto.
Qed.
    
Instance po_R: PreOrder (@KI.Krelation _ R).
Proof.
  constructor.
  + hnf; intros m.
    destruct (im_bij _ _ rel m) as [Phi ?].
    apply (H_R _ _ _ _ H H).
    hnf; intros; auto.
  + hnf; intros m1 m2 m3.
    destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    destruct (im_bij _ _ rel m3) as [Phi3 ?].
    rewrite (H_R _ _ _ _ H H0).
    rewrite (H_R _ _ _ _ H0 H1).
    rewrite (H_R _ _ _ _ H H1).
    clear; unfold Included, Ensembles.In; firstorder.
Qed.

Lemma truth_lemma_falsep (CONSI: at_least_consistent P):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= falsep <-> proj1_sig Phi falsep).
Proof.
  intros.
  rewrite sat_falsep.
  pose proof proj2_sig Phi.
  pose proof CONSI _ H0.
  rewrite consistent_spec in H1.
  split; [intros [] |].
  intro; apply H1.
  apply derivable_assum; auto.
Qed.
        
Lemma truth_lemma_andp
      (DER: at_least_derivable_closed P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x && y <-> proj1_sig Phi (x && y)).
Proof.
  intros.
  rewrite sat_andp.
  rewrite DCS_andp_iff by (apply DER, (proj2_sig Phi)).
  apply Morphisms_Prop.and_iff_morphism; auto.
Qed.

Lemma truth_lemma_orp
      (DER: at_least_derivable_closed P)
      (ORP: at_least_orp_witnessed P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x || y <-> proj1_sig Phi (x || y)).
Proof.
  intros.
  rewrite sat_orp.
  rewrite DCS_orp_iff.
    2: apply DER, (proj2_sig Phi).
    2: apply ORP, (proj2_sig Phi).
  apply Morphisms_Prop.or_iff_morphism; auto.
Qed.

Lemma truth_lemma_impp
      (DER: at_least_derivable_closed P)
      (LIN_DER: Linderbaum_derivable P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
  intros.
  rewrite sat_impp.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)).
    rewrite <- deduction_theorem.
    apply NNPP; intro.
    apply LIN_DER in H1.
    destruct H1 as [Psi [? ?]].
    apply H2; clear H2.
    assert (Included _ (proj1_sig Phi) (proj1_sig Psi)) by (intros ? ?; apply H1; left; auto).
    assert (proj1_sig Psi x) by (apply H1; right; constructor; auto).
    clear H1.
    destruct (su_bij _ _ rel Psi) as [n ?].
    rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Psi)).
    rewrite <- (IHx _ _ H1) in H3.
    rewrite <- (IHy _ _ H1).
    apply H0; auto.
    erewrite H_R by eauto.
    auto.
  + destruct (im_bij _ _ rel n) as [Psi ?].
    rewrite (IHx _ _ H3) in H2.
    rewrite (IHy _ _ H3).
    rewrite derivable_closed_element_derivable in H2 |- * by (apply DER, (proj2_sig Psi)).
    eapply deduction_modus_ponens; [exact H2 |].
    rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Psi)).
    erewrite H_R in H1 by eauto.
    apply H1; auto.
Qed.

Lemma classical_canonical_ident
      {cpGamma: ClassicalPropositionalLogic L Gamma}
      (DER: at_least_derivable_closed P)
      (ORP: at_least_orp_witnessed P)
      (CONSI: at_least_consistent P):
  IdentityKripkeIntuitionisticModel (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel m) as [Phi ?].
  destruct (im_bij _ _ rel n) as [Psi ?].
  erewrite H_R in H by eauto.
  assert (Phi = Psi); [| subst; eapply (in_bij _ _ rel); eauto].
  clear rel H_R m n H0 H1.

  apply sig_context_ext.
  intros; split; [apply H; auto |].
  intros.
  pose proof derivable_excluded_middle (proj1_sig Phi) x.
  rewrite <- derivable_closed_element_derivable in H1 by (apply DER, (proj2_sig Phi)).
  apply ORP in H1; [| apply (proj2_sig Phi)].
  destruct H1; auto.
  exfalso.
  apply H in H1; unfold Ensembles.In in H1.
  rewrite derivable_closed_element_derivable in H0, H1 by (apply DER, (proj2_sig Psi)).
  pose proof deduction_modus_ponens _ _ _ H0 H1.
  revert H2; change (~ proj1_sig Psi |-- FF).
  rewrite <- consistent_spec.
  apply CONSI, (proj2_sig Psi).
Qed.

Lemma Godel_Dummett_canonical_no_branch
      {gdpGamma: GodelDummettPropositionalLogic L Gamma}
      (DER: at_least_derivable_closed P)
      (ORP: at_least_orp_witnessed P):
  NoBranchKripkeIntuitionisticModel (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  destruct (im_bij _ _ rel m1) as [Psi1 ?].
  destruct (im_bij _ _ rel m2) as [Psi2 ?].
  erewrite !H_R in H, H0 by eauto.
  do 2 erewrite H_R by eauto.
  clear rel H_R m1 m2 n H1 H2 H3.

  apply NNPP; intro.
  apply not_or_and in H1; destruct H1.
  apply not_all_ex_not in H1.
  apply not_all_ex_not in H2.
  destruct H1 as [x1 ?], H2 as [x2 ?].
  pose proof derivable_impp_choice (proj1_sig Phi) x1 x2.
  rewrite <- derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Phi)).
  apply ORP in H3; [| apply (proj2_sig Phi)].
  destruct H3; pose proof H3; apply H in H3; apply H0 in H4.
  + rewrite derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Psi1)).
    rewrite derivable_closed_element_derivable in H4 by (apply DER, (proj2_sig Psi2)).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H3).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H4).
    rewrite <- !derivable_closed_element_derivable in H5 by (apply DER, (proj2_sig Psi1)).
    rewrite <- !derivable_closed_element_derivable in H6 by (apply DER, (proj2_sig Psi2)).
    clear - H1 H2 H5 H6.
    tauto.
  + rewrite derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Psi1)).
    rewrite derivable_closed_element_derivable in H4 by (apply DER, (proj2_sig Psi2)).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H3).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H4).
    rewrite <- !derivable_closed_element_derivable in H5 by (apply DER, (proj2_sig Psi1)).
    rewrite <- !derivable_closed_element_derivable in H6 by (apply DER, (proj2_sig Psi2)).
    clear - H1 H2 H5 H6.
    tauto.
Qed.

Lemma DeMorgan_canonical_branch_join
      {dmpGamma: DeMorganPropositionalLogic L Gamma}
      (DER: at_least_derivable_closed P)
      (ORP: at_least_orp_witnessed P)
      (CONSI: at_least_consistent P)
      (LIN_DER: Linderbaum_derivable P):
  BranchJoinKripkeIntuitionisticModel (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  destruct (im_bij _ _ rel m1) as [Psi1 ?].
  destruct (im_bij _ _ rel m2) as [Psi2 ?].
  erewrite !H_R in H, H0 by eauto.
  assert (exists Psi: sig P, Included _ (proj1_sig Psi1) (proj1_sig Psi) /\
                             Included _ (proj1_sig Psi2) (proj1_sig Psi)).
  Focus 2. {
    destruct H4 as [Psi [? ?]].
    destruct (su_bij _ _ rel Psi) as [m ?].
    exists m.
    erewrite !H_R by eauto; auto.
  } Unfocus.
  clear rel H_R m1 m2 n H1 H2 H3.

  assert (~ (Union _ (proj1_sig Psi1) (proj1_sig Psi2)) |-- FF).
  + intro.
    apply derivable_closed_union_derivable in H1; [| apply DER, (proj2_sig Psi2)].
    destruct H1 as [x [? ?]].
    rewrite derivable_closed_element_derivable in H1 by (apply DER, (proj2_sig Psi2)).
    pose proof derivable_weak_excluded_middle (proj1_sig Phi) x.
    rewrite <- derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Phi)).
    apply ORP in H3; [| apply (proj2_sig Phi)].
    destruct H3.
    - apply H0 in H3; unfold Ensembles.In in H3.
      rewrite derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Psi2)).
      pose proof deduction_modus_ponens _ _ _ H1 H3.
      revert H4; change (~ proj1_sig Psi2 |-- FF).
      rewrite <- consistent_spec.
      apply CONSI, (proj2_sig Psi2).
    - apply H in H3; unfold Ensembles.In in H3.
      rewrite derivable_closed_element_derivable in H3 by (apply DER, (proj2_sig Psi1)).
      pose proof deduction_modus_ponens _ _ _ H2 H3.
      revert H4; change (~ proj1_sig Psi1 |-- FF).
      rewrite <- consistent_spec.
      apply CONSI, (proj2_sig Psi1).
  + apply LIN_DER in H1.
    destruct H1 as [Psi [? ?]]; exists Psi.
    split; intros ? ?; apply H1; [left | right]; auto.
Qed.

End Canonical.