Require Import Coq.Logic.Classical_Prop.

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


Import PropositionalDynamicLanguageNotation.

Require Import Coq.Sets.Ensembles.
Local Open Scope logic_base.
Local Open Scope kripke_model.
Section Fischer_Ladner_Closed.


Context {L: Language}
        {Pro: Program}
        {ProOp: ProgramOperation L Pro}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {pdL: PropositionalDynamicLanguage L Pro}
        {G: ProofTheory L}
        .

Record FL_closed (X: Ensemble expr):Prop :={
  FL_closed_impp: forall x y, In expr X (impp x y) -> In _ X x /\ In _ X y;
  FL_closed_orp: forall x y, In _ X (orp x y) -> In _ X x /\ In _ X y;
  FL_closed_andp: forall x y, In _ X (andp x y) -> In _ X x /\ In _ X y;
  FL_closed_falsep: In _ X (falsep);
  FL_closed_boxp: forall x pi, In _ X (boxp pi x) -> In _ X x;
  FL_closed_boxp_choice: forall x p q, In _ X (boxp (choice p q) x) -> In _ X (andp (boxp p x) (boxp q x));
  FL_closed_boxp_composition: forall x p q, In _ X (boxp (composition p q) x) -> In _ X (boxp p (boxp q x));
  FL_closed_boxp_iteration: forall x pi, In _ X (boxp (iteration pi) x) -> In _ X (boxp pi (boxp (iteration pi) x));
  FL_closed_boxp_test: forall x y, In _ X (boxp (test y) x) -> In _ X x /\  In _ X y;
}.

Class FL_closed_set: Type :={
  FL_closure_construction (psi: expr): Ensemble expr
}.

Definition FL_closure_construction_is_FL_closed (flc: FL_closed_set): Prop := 
forall psi, FL_closed (FL_closure_construction psi).

Record FL_Atom {flc: FL_closed_set} (psi:expr) (A: Ensemble expr): Prop :={
  FL_axiom_included: Included _ A (FL_closure_construction psi);
  FL_axiom_consist: consistent A;
  FL_axiom_maximal: forall x, In _ (FL_closure_construction psi) x -> ~ In _ A x -> ~ (consistent (A;;x));
}.

Class Atom_set: Type :={
  Atom_construction (psi: expr): Ensemble expr
}.


Definition atom_construction_is_atom (flc: FL_closed_set) (atc: Atom_set): Prop :=
forall psi, FL_Atom psi (Atom_construction psi).


Definition FL_axiom_existence {flc: FL_closed_set}: Prop :=
forall psi, consistent (Singleton _ psi) -> exists A, FL_Atom psi A /\ Included _ (Singleton _ psi) A.



(* target property of FL_axioms *)
Definition FL_axiom_impp_property {flc: FL_closed_set} (psi: expr) (A:Ensemble expr): Prop :=
forall x y, In _  (FL_closure_construction psi) (impp x y) -> (In _ A (impp x y) <-> (In _ A x -> In _ A y)).

Definition FL_axiom_orp_property {flc: FL_closed_set} (psi: expr) (A:Ensemble expr): Prop :=
forall x y, In _  (FL_closure_construction psi) (orp x y) -> (In _ A (orp x y) <-> In _ A x \/ In _ A y).

Definition FL_axiom_andp_property {flc: FL_closed_set} (psi: expr)(A:Ensemble expr): Prop :=
forall x y, In _  (FL_closure_construction psi) (andp x y) -> (In _ A (andp x y) <-> In _ A x /\ In _ A y).

Definition FL_axiom_falsep_property (psi: expr)(A:Ensemble expr): Prop :=
In _ A falsep <-> False.

Definition FL_axiom_boxp_choice_property {flc: FL_closed_set}(psi: expr)(A:Ensemble expr): Prop :=
forall x p q, In _  (FL_closure_construction psi) (boxp (choice p q) x) -> In _ A (boxp (choice p q) x) <-> In _ A (boxp p x) \/ In _ A (boxp q x).

Definition FL_axiom_boxp_composition_property {flc: FL_closed_set}(psi: expr)(A:Ensemble expr): Prop :=
forall x p q, In _  (FL_closure_construction psi) (boxp (composition p q) x) -> In _ A (boxp (composition p q) x) <-> In _ A (boxp p (boxp q x)).

Definition FL_axiom_boxp_iteration_property {flc: FL_closed_set}(psi: expr)(A:Ensemble expr): Prop :=
forall x pi, In _  (FL_closure_construction psi) (boxp (iteration pi) x) -> In _ A (boxp (iteration pi) x) <-> In _ A (boxp pi (boxp (iteration pi) x)).

Definition FL_axiom_boxp_test_property {flc: FL_closed_set}(psi: expr)(A:Ensemble expr): Prop. Admitted.



End Fischer_Ladner_Closed.