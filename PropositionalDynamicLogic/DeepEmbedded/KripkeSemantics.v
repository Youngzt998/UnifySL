Require Import Coq.Sets.Relations_1.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalDynamicLogic.Syntax.
Require Import Logic.PropositionalDynamicLogic.Semantics.Kripke.

Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.PropositionalDynamicLanguage.

Locate PropositionalDynamicLanguage.
Import PropositionalDynamicLanguage.


Section KripkeSemantics.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}.

Record frame: Type :={
  underlying_set:> Type;
  underlying_relation:> relation underlying_set;
  underlying_modal_relation:> program Sigma ProV  -> relation underlying_set
}.

Infix "<=" := (underlying_relation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f:frame) := @Ensemble (underlying_set f).
Locate Relation.
Locate KM.
Definition denotation (F: frame) (eval: Var -> sem F): expr Sigma ProV -> sem F. Admitted.
(*   fix denotation (x: expr Sigma ProV): sem F:=
  match x with
  | andp y z => @Semantics.andp F (denotation y) (denotation z)
  | orp y z => @Semantics.orp F (denotation y) (denotation z)
  | impp y z => @Semantics.impp F (underlying_relation F) (denotation y) (denotation z)
  | falsep => @Semantics.falsep F
  | boxp pi x => @Semantics.boxp ProgramVariables F (underlying_modal_relation F pi ) (denotation) (* TBD *)
  | varp p => eval p
  end.
 *)


Record Kmodel: Type :={
  underlying_frame :> frame;
  sem_var:> Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model:> Kmodel;
  elm: underlying_model;
}.

Instance MD: Model := Build_Model model.

Instance kMD: KripkeModel MD := Build_KripkeModel _ Kmodel (fun M => M) (fun M m => Build_model M m).

(* Context (M: Kmodel). Compute Kworlds M. *)

Instance R (M: Kmodel): Relation (Kworlds M) := @underlying_relation M.

Instance R_M (M: Kmodel): program Sigma ProV -> Relation (Kworlds M) := @underlying_modal_relation M.


Print upwards_closed_Kdenote.

Instance SM: Semantics L MD :=
Build_Semantics L MD (fun x M => (denotation M (sem_var M) x) (elm M)).

Definition Kmodel_Monotonic: Kmodel -> Prop := fun M =>
  forall v: Var, upwards_closed_Kdenote (sem_var M v).

Definition Kmodel_PreOrder: Kmodel -> Prop := fun M =>
  PreOrder (@Krelation _ (R M)).

Instance kiSM (M: Kmodel) {_: Kmodel_Monotonic M} {_: Kmodel_PreOrder M}:
  KripkeIntuitionisticSemantics L MD M SM.
Proof.
  hnf in H, H0.
  constructor; intros.
  induction x.
(*   + apply Semantics.andp_closed; auto.
  + apply Semantics.orp_closed; auto.
  + apply (Semantics.impp_closed _ _ IHx1 IHx2).
  + apply Semantics.falsep_closed.
  + apply H. *)
Admitted.

Instance kminSM (M: Kmodel): KripkeMinimunSemantics L MD M SM.
Proof.
(*   apply Build_KripkeMinimunSemantics.
  intros; apply Same_set_refl.
Defined.

 *)
Admitted.


Instance kpSM (M: Kmodel): KripkePropositionalSemantics L MD M SM.
Proof.
(*   apply Build_KripkePropositionalSemantics.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Defined.
 *)
Admitted.
 
Instance pdlSM (M: Kmodel): 



















