Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalDynamicLogic.Syntax.


Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class PropositionalVariables: Type := {
  Var: Type
}.

Class ProgramVariables: Type :={
  BaseP: Type
}.

Inductive program {Sigma: PropositionalVariables}{ProV: ProgramVariables}: Type :=
  | choice: program -> program -> program
  | composition: program -> program -> program
  | iteration: program -> program
  | test: expr -> program
  | basep: BaseP -> program
with
 expr {Sigma: PropositionalVariables} {ProV: ProgramVariables}: Type :=
  | impp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | andp: expr -> expr -> expr
  | falsep : expr
  | boxp: program -> expr -> expr
  | varp : Var -> expr
.

Arguments program Sigma ProV: clear implicits.
Arguments expr Sigma ProV: clear implicits.


Instance L {Sigma: PropositionalVariables} {ProV: ProgramVariables}: Language 
:= Build_Language (expr Sigma ProV).

Instance Pro {Sigma: PropositionalVariables} {ProV: ProgramVariables}: Program
:= Build_Program (program Sigma ProV).

Instance minL {Sigma: PropositionalVariables} {ProV: ProgramVariables}: MinimunLanguage L
:= Build_MinimunLanguage L impp.

Instance pL {Sigma: PropositionalVariables} {Pro: ProgramVariables}: PropositionalLanguage L
:= Build_PropositionalLanguage L andp orp falsep.

Instance pdL {Sigma: PropositionalVariables} {ProV: ProgramVariables}: PropositionalDynamicLanguage L Pro
:= Build_PropositionalDynamicLanguage L Pro boxp.


Lemma formula_countable: forall {Sigma}{ProV}, Countable Var -> Countable BaseP -> Countable (expr Sigma ProV).
Proof. Admitted.







