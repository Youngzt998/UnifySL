Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalDynamicLogic.Syntax.


Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import PropositionalDynamicLanguageNotation.

Class PropositionalDynamicLogicK 
(L: Language){minL: MinimunLanguage L}{pL: PropositionalLanguage L}
(Pro: Program){ProOp: ProgramOperation L Pro}{pdL: PropositionalDynamicLanguage L Pro}
(Gamma: ProofTheory L)
{minAX: MinimunAxiomatization L Gamma}
{ipGamma: IntuitionisticPropositionalLogic L Gamma}
{cpGamma: ClassicalPropositionalLogic L Gamma} 
 := {
  rule_N: forall x pi, |-- x -> |-- [pi]x;
  axiom_K: forall x y pi, |-- [pi] (x --> y) --> ( [pi]x --> [pi]y );
  axiom_choice: forall x p q, |-- [p\\//q] x <--> [p]x && [q]x;
  axiom_composition: forall x p q, |-- [p-;-q]x <--> [p][q]x;
  axiom_iteration: forall x pi, |-- [pi*]x <--> (x && [pi][pi*]x );
  axiom_test: forall x y, |-- [y?]x <--> (y --> x);
  axiom_induction: forall x pi, |-- [pi*](x --> [pi]x) --> (x --> [pi*]x)
}.



Class PropositionalDynamicSequentCalculusK 
(L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L}
(Pro: Program){ProOp: ProgramOperation L Pro}{pdL: PropositionalDynamicLanguage L Pro}
(Gamma: ProofTheory L) 
{bSC: BasicSequentCalculus L Gamma} 
{minSC: MinimunSequentCalculus L Gamma} 
{ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
{cpGamma: ClassicalPropositionalSequentCalculus L Gamma} := {
  deduction_axiom_K: forall Phi x y pi, Phi |-- [pi](x --> y) -> Phi |-- [pi]x --> [pi]y
}.


Check axiom_K.

Section DerivableRulesFromSequentCalculus1.
Context {L: Language}
        {Pro: Program}
        {ProOp: ProgramOperation L Pro}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {pdL: PropositionalDynamicLanguage L Pro}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}
        {pdKSC: PropositionalDynamicSequentCalculusK L Pro Gamma}
        .

Lemma derivable_rule_N: forall Phi x pi, Phi |-- x ->  Phi |-- [pi] x.
Proof. Admitted.

Lemma derivable_axiom_K: forall Phi x y pi, Phi |-- [pi] (x --> y) --> ( [pi]x --> [pi]y ).
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_axiom_K.
  
  pose proof (deduction_axiom_K (Empty_set _) x y pi).
Admitted.
  

Lemma derivable_axiom_choice: forall Phi x p q, Phi |--  [p\\//q] x <--> [p]x && [q]x.
Proof. Admitted.

Lemma derivable_axiom_composition: forall Phi x p q, Phi |-- [p-;-q]x <--> [p][q]x.
Proof. Admitted.

Lemma derivable_axiom_iteration: forall Phi x pi, Phi |-- [pi*]x <--> (x && [pi][pi*]x ).
Proof. Admitted.

Lemma derivable_axiom_test: forall Phi x y, Phi |-- [y?]x <--> (y --> x).
Proof. Admitted.

Lemma derivable_axiom_induction: forall Phi x pi, Phi |-- [pi*](x --> [pi]x) --> (x --> [pi*]x).
Proof. Admitted.


End DerivableRulesFromSequentCalculus1.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {Pro: Program}
        {ProOp: ProgramOperation L Pro}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {pdL: PropositionalDynamicLanguage L Pro}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}
        {pdSC: PropositionalDynamicSequentCalculusK L Pro Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {cpAX: ClassicalPropositionalLogic L Gamma}
        .

Lemma SequentCalculus2Axiomatization_pdkSC: PropositionalDynamicLogicK L Pro Gamma.
Proof.
  intros.
  constructor.
  - intros. rewrite provable_derivable in *. apply (derivable_rule_N _ _ _ H).
  - intros. rewrite provable_derivable in *. apply derivable_axiom_K.
  - intros. rewrite provable_derivable in *. apply derivable_axiom_choice .
  - intros. rewrite provable_derivable in *. apply derivable_axiom_composition.
  - intros. rewrite provable_derivable in *. apply derivable_axiom_iteration.
  - intros. rewrite provable_derivable in *. apply derivable_axiom_test.
  - intros. rewrite provable_derivable in *. apply derivable_axiom_induction.
Qed.

End SequentCalculus2Axiomatization.

