Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.

Require Import Logic.PropositionalDynamicLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.

Section TruthLemma.
Locate ClassicalPropositionalSequentCalculus.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kminSM: KripkeMinimunSemantics L MD M SM}
        {kpSM: KripkePropositionalSemantics L MD M SM}.

