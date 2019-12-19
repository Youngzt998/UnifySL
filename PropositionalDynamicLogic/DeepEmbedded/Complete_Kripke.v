Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimunLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.

Require Import Logic.PropositionalDynamicLogic.Syntax.
Require Import Logic.PropositionalDynamicLogic.Complete.Fischer_Ladner.
Require Import Logic.PropositionalDynamicLogic.ProofTheory.PropositionalDynamicLogic.
Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.PropositionalDynamicLanguage.
Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.ProofTheories.
Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.Fischer_Ladner_Closure.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import PropositionalDynamicLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.





Section Complete.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}.

Existing Instances 
PropositionalDynamicLanguage.L
PropositionalDynamicLanguage.Pro
PropositionalDynamicLanguage.ProOp
PropositionalDynamicLanguage.minL 
PropositionalDynamicLanguage.pL
PropositionalDynamicLanguage.pdL
ProofTheories.G
ProofTheories.AX
ProofTheories.minAX
ProofTheories.ipG
ProofTheories.cpG
ProofTheories.pdlk
flc
.

Context {SC: NormalSequentCalculus PropositionalDynamicLanguage.L G}
        {bSC: BasicSequentCalculus L G}
        {minSC: MinimunSequentCalculus _ G}
        {ipSC: IntuitionisticPropositionalSequentCalculus _ G}
        {cpSC:ClassicalPropositionalSequentCalculus _ G}
        .

Locate FL_axiom_impp_property.

Lemma consistent_exclude_falsep: forall A, consistent A <-> ~ A |-- FF.
Proof.
  intros. split.
  - intros. destruct H. intro. apply H;apply (deduction_falsep_elim A x H0).
  - intros. hnf. apply NNPP. intro.
    pose proof (not_ex_not_all _ _ H0).
    apply H; apply H1 .
Qed.

Lemma consistent_lemma: forall A x, consistent A -> A |-- x -> consistent (A;;x).
Proof.
  intros. rewrite consistent_exclude_falsep in *. intro.
  destruct H. pose proof (deduction_impp_intros A x FF H1).
  apply (deduction_modus_ponens _ _ _ H0 H).
Qed.

Lemma FL_negation_property: 
forall psi x A, FL_Atom psi A -> Ensembles.In _ (FL_closure_construction psi) x -> A x \/ A (x --> falsep).
Proof.
  intros.
  apply Classical_Prop.NNPP. intro.
  destruct (not_or_and _ _ H1).
  destruct H.
  destruct (classic (A|-- x)).
  - pose proof (consistent_lemma A x FL_axiom_consist H).
    apply (FL_axiom_maximal x H0 H2 H4).
  - assert(A|-- x--> FF). {
      admit.
      (* ok if use excluded_middle ? *)
    }
    pose proof (FL_axiom_maximal (x --> FF) ).
Admitted.


Lemma immp_property: forall psi A, FL_Atom psi A ->  FL_axiom_impp_property psi A.
Proof.
  (* what property? *)
Admitted.

Goal forall Phi x y z, Phi |-- x || y -> Phi |-- x --> z -> Phi |-- y --> z -> Phi |-- x || y --> z.
Abort.

Lemma orp_property: forall psi A, FL_Atom psi A ->  FL_axiom_orp_property psi A.
Proof.
  intros. destruct H. hnf. intros. split.
  - intros. pose proof derivable_assum A (x||y) H0.
    apply Classical_Prop.NNPP. intro.
    destruct (not_or_and _ _ H2).
    pose proof FL_closed_orp _ (FL_closure_is_FL_closed psi) x y H as [].
    assert (consistent (A;;x)\/consistent (A;;y)). {
      apply NNPP. intro.
      destruct (not_or_and _ _ H7).
      admit.
    }
    (* to be fixed *)
    admit.
  - pose proof derivable_assum A x; pose proof derivable_assum A y. 
    intros [|].
    + pose proof H0 H2. pose proof deduction_orp_intros1 A x y H3.
      pose proof FL_closure_is_FL_closed psi.
      pose proof FL_closed_orp _ H5 x y.
      unfold Ensembles.In.
      apply Classical_Prop.NNPP. intro.
      assert (A (x || y --> falsep)). {
        pose proof FL_negation_property psi (x || y) A.
        admit.
      }
      pose proof derivable_assum A (x || y --> FF) H8.
      rewrite <- deduction_theorem in H9.
      pose proof consistent_lemma A (x || y) FL_axiom_consist H4.
      destruct H10. apply H10.
      pose proof derivable_falsep_elim (A;; x || y) x0.
      pose proof deduction_modus_ponens (A;; x || y) FF x0 H9 H11.
      auto.
Admitted.

Lemma andp_property: forall psi A, FL_Atom psi A ->  FL_axiom_andp_property psi A.
Proof.
  intros. destruct H. hnf. intros. split.
  - intros. 
    pose proof derivable_assum A _ H0.
    pose proof deduction_modus_ponens A (x&&y) x H1 (derivable_andp_elim1 A x y).
    pose proof deduction_modus_ponens A (x&&y) y H1 (derivable_andp_elim2 A x y).
    pose proof consistent_lemma A x FL_axiom_consist H2.
    pose proof consistent_lemma A y FL_axiom_consist H3.
    pose proof FL_closed_andp _ (FL_closure_is_FL_closed psi) x y H as [].
    split.
    + apply NNPP. intro.
      apply (FL_axiom_maximal x H6 H8 H4).
    + apply NNPP. intro.
      apply (FL_axiom_maximal y H7 H8 H5).
  - intros [].
    pose proof derivable_assum A x H0.
    pose proof derivable_assum A y H1.
    apply NNPP. intro.
    pose proof deduction_andp_intros A x y H2 H3.
    pose proof consistent_lemma A (x&&y) FL_axiom_consist H5.
    apply (FL_axiom_maximal (x&&y) H H4 H6).
Qed.


Existing Instances provable_impp_rewrite
                   provable_impp_refl
                   provable_proper_impp
                   derivable_proper_impp
                   impp_proper_impp.

(* test rewrite *)
Goal forall  (Phi: context) y1 y2,
  |-- y1 --> y2 ->
  |-- y1 ->
  |-- y2.
Proof.
  intros.
  try rewrite -> H.
  auto.
Abort.

Definition canonical_frame: Type. Admitted.


Lemma TRUTH: Prop. Admitted.
        
Theorem complete_propositional_dynamic_logic_Kripke: Prop. Admitted.
