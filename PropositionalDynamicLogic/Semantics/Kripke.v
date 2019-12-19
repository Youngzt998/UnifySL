Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Relations_1.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalDynamicLogic.Syntax.


Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalDynamicLanguageNotation.
Import KripkeModelFamilyNotation.


(* Module PDL_KM.

Class Relation (prog: Type)(worlds: Type): Type :=
  Krelation: prog -> worlds -> worlds -> Prop.

End PDL_KM. *)


Module Semantics. 

Definition boxp {prog: Type}{worlds: Type}{R_M: prog -> Relation worlds}
(pi: prog)(X: Ensemble worlds): Ensemble worlds :=
fun m => forall n, R_M pi m n -> X n.

End Semantics.
Locate Kdenotation. Print Kdenotation. Check @Semantics.boxp.

Class KripkePropositionalDynamicSemantics 
(L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L}
(Pro: Program) {pdL: PropositionalDynamicLanguage L Pro} 
(MD: Model) {kMD: KripkeModel MD} 
(M: Kmodel) 
{R_M: program -> Relation (Kworlds M)} 
(SM: Semantics L MD): Type := {

  denote_boxp: forall (pi:program) (x: expr), Same_set _ (Kdenotation M ([pi] x) ) (@Semantics.boxp program (Kworlds M) R_M  pi (Kdenotation M x)  )

}.
Print KripkeModel.
Lemma sat_boxp
{L:Language}{minL: MinimunLanguage L}{pL: PropositionalLanguage L}
{Pro: Program}{pdL: PropositionalDynamicLanguage L Pro}
{MD: Model}{kMD: KripkeModel MD}{M:Kmodel}
{R_M: program -> Relation (Kworlds M)}
{SM: Semantics L MD}{kpdSM: @KripkePropositionalDynamicSemantics L minL pL Pro pdL MD kMD M R_M SM}:
forall m x pi, KRIPKE: M, m |= [pi] x <-> (forall n, R_M pi m n -> KRIPKE: M, n |= x).
Proof.
  intros.
  unfold satisfies.
  pose proof denote_boxp pi x as H.
  destruct H as [H1 H2].
  split. unfold Semantics.boxp in H1. unfold Included in H1. unfold Ensembles.In in H1.
  - apply (H1 m).
  - apply (H2 m).
Qed.

















