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
Check forall x p q, |-- [p-q] x <--> [p][q]x.
Check forall x p q, |-- [p\\//q] x <--> [p]x || [q]x.
Check forall x pi, |-- [pi*]x <--> (x || [pi][pi*]x ).
Check forall x pi, |-- [pi*](x --> [pi]x) --> (x --> [pi*]x).

Class PropositionalDynamicLogicK 
(L: Language){minL: MinimunLanguage L}{pL: PropositionalLanguage L}
(Gamma: ProofTheory L){minAX: MinimunAxiomatization L Gamma}{ipGamma: IntuitionisticPropositionalLogic L Gamma} 
(Pro: Program){ProOp: ProgramOperation Pro}{pdL: PropositionalDynamicLanguage L Pro} := {
  axiom_K: forall x y pi, |-- [pi] (x --> y) --> ( [pi]x --> [pi]y );
  axiom_choice: forall x p q, |-- [p\\//q] x <--> [p]x || [q]x;
  axiom_composition: forall x p q, |-- [p-q]x <--> [p][q]x;
  axiom_iteration: forall x pi, |-- [pi*]x <--> (x || [pi][pi*]x );
  axiom_induction: forall x pi, |-- [pi*](x --> [pi]x) --> (x --> [pi*]x)
}.

Check axiom_K.