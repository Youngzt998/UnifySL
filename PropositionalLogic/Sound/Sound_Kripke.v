Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Lemma sound_modus_ponens {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= (x --> y) -> KRIPKE: M, m |= x -> KRIPKE: M, m |= y.
Proof.
  intros.
  rewrite sat_impp in H.
  specialize (H m).
  apply H; auto.
  reflexivity.
Qed.

Lemma sound_axiom1 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x --> y --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  eapply sat_mono; eauto.
Qed.

Lemma sound_axiom2 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y z: expr,
    forall m,
      KRIPKE: M, m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  assert (n <= n1) by (etransitivity; eauto).

  rewrite sat_impp in H0.
  specialize (H0 n1 H5 H4).
  rewrite sat_impp in H2.
  specialize (H2 n1 H3 H4).

  rewrite sat_impp in H0.
  specialize (H0 n1 ltac:(reflexivity) H2).
  auto.
Qed.

Lemma sound_andp_intros {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x --> y --> x && y.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  rewrite sat_andp.
  split.
  + eapply sat_mono; eauto.
  + auto.
Qed.

Lemma sound_andp_elim1 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x && y --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_andp in H0.
  tauto.
Qed.

Lemma sound_andp_elim2 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x && y --> y.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_andp in H0.
  tauto.
Qed.

Lemma sound_orp_intros1 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x --> x || y.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_orp.
  tauto.
Qed.

Lemma sound_orp_intros2 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= y --> x || y.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_orp.
  tauto.
Qed.

Lemma sound_orp_elim {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y z: expr,
    forall m,
      KRIPKE: M, m |= (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  rewrite sat_orp in H4.
  destruct H4.
  + rewrite sat_impp in H0.
    apply H0; auto.
    etransitivity; eauto.
  + rewrite sat_impp in H2.
    apply H2; auto.
Qed.

Lemma sound_falsep_elim {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x: expr,
    forall m,
      KRIPKE: M, m |= FF --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  pose proof sat_falsep n.
  tauto.
Qed.

Lemma sound_excluded_middle_ident {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {ikiM: IdentityKripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x: expr,
    forall m, KRIPKE: M, m |= x || ~~ x.
Proof.
  intros.
  unfold negp.
  rewrite sat_orp, sat_impp.
  destruct (Classical_Prop.classic (KRIPKE: M, m |= x)); auto.
  right; intros.
  apply ikiM in H0; subst n.
  tauto.
Qed.

Lemma sound_impp_choice_no_branch {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {nkiM: NoBranchKripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x y: expr,
    forall m, KRIPKE: M, m |= (x --> y) || (y --> x).
Proof.
  intros.
  rewrite sat_orp, !sat_impp.
  apply Classical_Prop.NNPP; intro.
  apply not_or_and in H; destruct H.
  apply not_all_ex_not in H.
  apply not_all_ex_not in H0.
  destruct H as [n1 ?], H0 as [n2 ?].
  apply imply_to_and in H.
  apply imply_to_and in H0.
  destruct H, H0.
  apply imply_to_and in H1.
  apply imply_to_and in H2.
  destruct H1, H2.
  destruct (Korder_no_branch n1 n2 m H H0).
  + pose proof (sat_mono _ _ x H5).
    tauto.
  + pose proof (sat_mono _ _ y H5).
    tauto.
Qed.

Lemma sound_weak_excluded_middle_branch_join {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {po_R: PreOrder Krelation} {bkiM: BranchJoinKripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall x: expr,
    forall m, KRIPKE: M, m |= ~~ x || ~~ ~~ x.
Proof.
  intros.
  unfold negp.
  rewrite sat_orp, !sat_impp.
  apply Classical_Prop.NNPP; intro.
  apply not_or_and in H; destruct H.
  apply not_all_ex_not in H.
  apply not_all_ex_not in H0.
  destruct H as [n1 ?], H0 as [n2 ?].
  apply imply_to_and in H.
  apply imply_to_and in H0.
  destruct H, H0.
  apply imply_to_and in H1.
  apply imply_to_and in H2.
  destruct H1 as [? _], H2 as [? _].
  destruct (Korder_branch_join n1 n2 m H H0) as [n [? ?]].
  eapply sat_mono in H2; [| eassumption].
  eapply sat_mono in H1; [| eassumption].
  rewrite sat_impp in H2.
  apply (H2 n) in H1; [| reflexivity].
  apply sat_falsep in H1; auto.
Qed.
