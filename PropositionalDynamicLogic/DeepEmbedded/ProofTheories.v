Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalDynamicLogic.Syntax.
Require Import Logic.PropositionalDynamicLogic.ProofTheory.PropositionalDynamicLogic.
Require Logic.PropositionalDynamicLogic.DeepEmbedded.PropositionalDynamicLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.

Import PropositionalLanguageNotation.
Import PropositionalDynamicLanguageNotation.


Section PropositionalDynamicLogic.

Context {Sigma: PropositionalDynamicLanguage.PropositionalVariables}
        {ProV: PropositionalDynamicLanguage.ProgramVariables}.
        
Existing Instances 
PropositionalDynamicLanguage.L
PropositionalDynamicLanguage.Pro
PropositionalDynamicLanguage.ProOp
PropositionalDynamicLanguage.minL 
PropositionalDynamicLanguage.pL
PropositionalDynamicLanguage.pdL
.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| excluded_middle: forall x, provable (x || (x --> FF))
| rule_N: forall x pi, provable x -> provable ([pi]x)
| axiom_K: forall x y pi, provable ([pi] (x --> y) --> ( [pi]x --> [pi]y ))
| axiom_choice: forall x p q, provable ([p\\//q] x <--> [p]x && [q]x)
| axiom_composition: forall x p q, provable ([p-;-q]x <--> [p][q]x)
| axiom_iteration: forall x pi, provable ([pi*]x <--> (x && [pi][pi*]x ))
| axiom_test: forall x y, provable ([y?]x <--> (y --> x))
| axiom_induction: forall x pi, provable ([pi*](x --> [pi]x) --> (x --> [pi*]x))
.

Instance G: ProofTheory PropositionalDynamicLanguage.L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization PropositionalDynamicLanguage.L G := Build_AxiomaticProofTheory_AX provable.

Instance minAX: MinimunAxiomatization PropositionalDynamicLanguage.L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic PropositionalDynamicLanguage.L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance cpG: ClassicalPropositionalLogic PropositionalDynamicLanguage.L G.
Proof.
  constructor.
  apply excluded_middle.
Qed.

Instance pdlk: PropositionalDynamicLogicK PropositionalDynamicLanguage.L PropositionalDynamicLanguage.Pro G.
Proof.
  constructor.
  + apply rule_N.
  + apply axiom_K.
  + apply axiom_choice.
  + apply axiom_composition.
  + apply axiom_iteration.
  + apply axiom_test.
  + apply axiom_induction.
Qed.

End PropositionalDynamicLogic.
