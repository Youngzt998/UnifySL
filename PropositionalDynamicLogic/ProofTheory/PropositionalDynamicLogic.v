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

Check forall x y, |-- y --> x --> x.
Check forall x y pi, |-- [pi] (x --> y) --> ( [pi]x --> [pi]y ).
Check forall x p q, |-- [p -;- q] x <--> [p][q]x.
Check forall x p q, |-- [p\\//q] x <--> [p]x || [q]x.
Check forall x pi, |-- [pi*]x <--> (x || [pi][pi*]x ).
Check forall x pi, |-- [pi*](x --> [pi]x) --> (x --> [pi*]x).

Class PropositionalDynamicLogicK 
(L: Language){minL: MinimunLanguage L}{pL: PropositionalLanguage L}
(Pro: Program){ProOp: ProgramOperation Pro}{pdL: PropositionalDynamicLanguage L Pro}
(Gamma: ProofTheory L)
{minAX: MinimunAxiomatization L Gamma}
{ipGamma: IntuitionisticPropositionalLogic L Gamma}
{cpGamma: ClassicalPropositionalLogic L Gamma} 
 := {
  axiom_K: forall x y pi, |-- [pi] (x --> y) --> ( [pi]x --> [pi]y );
  axiom_choice: forall x p q, |-- [p\\//q] x <--> [p]x || [q]x;
  axiom_composition: forall x p q, |-- [p-;-q]x <--> [p][q]x;
  axiom_iteration: forall x pi, |-- [pi*]x <--> (x || [pi][pi*]x );
  axiom_induction: forall x pi, |-- [pi*](x --> [pi]x) --> (x --> [pi*]x)
}.



Class PropositionalDynamicSequentCalculusK 
(L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L}
(Pro: Program){ProOp: ProgramOperation Pro}{pdL: PropositionalDynamicLanguage L Pro}
(Gamma: ProofTheory L) 
{bSC: BasicSequentCalculus L Gamma} 
{minSC: MinimunSequentCalculus L Gamma} 
{ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
{cpGamma: ClassicalPropositionalSequentCalculus L Gamma} := {
  deduction_axiom_K: forall Phi x y pi, Phi |-- [pi](x --> y) -> Phi |-- [pi]x --> [pi]y
}.


Goal  forall (L: Language){minL: MinimunLanguage L}{pL: PropositionalLanguage L}
(Gamma: ProofTheory L){minAX: MinimunAxiomatization L Gamma}{ipGamma: IntuitionisticPropositionalLogic L Gamma} 
(Pro: Program){ProOp: ProgramOperation Pro}{pdL: PropositionalDynamicLanguage L Pro}  
x y pi, |-- [pi](x --> y --> x).

intros.
pose proof axiom1 x y. Abort.

Check axiom_K.

Section DerivableRulesFromSequentCalculus1.
Context {L: Language}
        {Pro: Program}
        {ProOp: ProgramOperation Pro}
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
        .


Lemma derivable_axiom_K: forall Phi x y pi, Phi |-- [pi] (x --> y) --> ( [pi]x --> [pi]y ).
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_axiom_K.
  
  pose proof (deduction_axiom_K (Empty_set _) x y pi).
  
  

Lemma derivable_axiom_choice: forall x p q, |-- [p\\//q] x <--> [p]x || [q]x.
Proof. Admitted.

Lemma derivable_axiom_composition: forall x p q, |-- [p-;-q]x <--> [p][q]x.
Proof. Admitted.

Lemma derivable_axiom_iteration: forall x pi, |-- [pi*]x <--> (x || [pi][pi*]x ).
Proof. Admitted.

Lemma derivable_axiom_induction: forall x pi, |-- [pi*](x --> [pi]x) --> (x --> [pi*]x).
Proof. Admitted.


End DerivableRulesFromSequentCalculus1.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {Pro: Program}
        {ProOp: ProgramOperation Pro}
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

Lemma SequentCalculus2Axiomatization_pdSC: PropositionalDynamicLogicK L Pro Gamma.
Proof.
  intros.
  constructor.
  - apply derivable_axiom_K.
  - apply derivable_axiom_choice.
  - apply derivable_axiom_composition.
  - apply derivable_axiom_iteration.
  - apply derivable_axiom_induction.
Qed.

End SequentCalculus2Axiomatization.

