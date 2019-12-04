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

Record frame: Type :={
  underlying_set:> Type;
  underlying_relation:> relation underlying_set;
  
  underlying_modal_relation: relation underlying_set
}.

Infix "<=" := (underlying_relation _): TheKripkeSemantics.
Local Open Scope TheKripkeSemantics.

Definition sem (f:frame) := @Ensemble (underlying_set f).

Section KripkeSemantics.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}.

Definition denotation (F: frame) (eval: Var -> sem F): expr Sigma ProV -> sem F :=
  fix denotation (x: expr Sigma ProV): sem F:=
  match x with
  | andp y z => @Semantics.andp F (denotation y) (denotation z)
  | orp y z => @Semantics.orp F (denotation y) (denotation z)
  | impp y z => @Semantics.impp F (underlying_relation F) (denotation y) (denotation z)
  | falsep => @Semantics.falsep F
  | boxp pi x=> @Semantics.boxp
  | varp p => eval p
  end.

