Require Import Logic.GeneralLogic.Base.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalDynamicLogic.Syntax.


Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalDynamicLanguageNotation.
Import KripkeModelFamilyNotation.

Module Semantics.

Class Relation (worlds: Type)(Pro: Program): Type :=
  Krelation: program -> worlds -> worlds -> Prop.

Definition boxp {worlds: Type}{Pro: Program}{R: Relation worlds Pro}
(pi: program)(X: Ensemble worlds): Ensemble worlds :=
fun m => forall n, Krelation pi m n -> X n.

End Semantics.

Class KripkeModalSemantics 
(L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L}
(Pro: Program) {pdL: PropositionalDynamicLanguage L Pro} 
(MD: Model) {kMD: KripkeModel MD} 
(M: Kmodel) {R: Relation (Kworlds M)} 
(SM: Semantics L MD): Type := {
  
}.