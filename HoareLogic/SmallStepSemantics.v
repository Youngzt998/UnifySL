Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Coq.Relations.Relation_Operators.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class SmallStepSemantics_cmd cmd {P: ProgrammingLanguage cmd} (state: Type): Type := {
  step_cmd: cmd * state -> MetaState (cmd * state) -> Prop
}.

Definition step_cmd_safe
           {cmd: Type}
           {P: ProgrammingLanguage cmd}
           (state: Type)
           {SSS: SmallStepSemantics_cmd cmd state}
           (cs: cmd * state):
  Prop :=
  ~ step_cmd cs Error.

Definition step_cmd_term_norm
           {cmd: Type}
           {P: ProgrammingLanguage cmd}
           {state: Type}
           {SSS: SmallStepSemantics_cmd cmd state}
           (cs: cmd * state):
  Prop :=
  ~ step_cmd cs Error /\ ~ step_cmd cs NonTerminating.

Class SmallStepSemantics {cmd stack} cont {P: ProgrammingLanguage cmd} {CS: ControlStack stack} {Cont: Continuation cont} (state: Type): Type := {
  step: cont * state -> MetaState (cont * state) -> Prop
}.

Definition step_safe
           {cmd stack cont}
           {P: ProgrammingLanguage cmd}
           {CS: ControlStack stack}
           {Cont: Continuation cont}
           {state: Type}
           {SSS: SmallStepSemantics cont state}
           (cs: cont * state):
  Prop :=
  ~ step cs Error.

Definition step_term_norm
           {cmd stack cont}
           {P: ProgrammingLanguage cmd}
           {CS: ControlStack stack}
           {Cont: Continuation cont}
           {state: Type}
           {SSS: SmallStepSemantics cont state}
           (cs: cont * state):
  Prop :=
  ~ step cs Error /\ ~ step cs NonTerminating.

Class SASmallStepSemantics {cmd stack} cont {P: ProgrammingLanguage cmd} {CS: ControlStack stack} {Cont: Continuation cont} (state: Type) {J: Join state} {state_R: Relation state} (SSS: SmallStepSemantics cont state): Type := {
  frame_property: forall (m mf m': cont * state) n', join (snd m) (snd mf) (snd m') -> step_safe m -> step m' n' -> exists n nf, snd nf <= snd mf /\ @lift_join _ (@prod_Join cont state (equiv_Join) J) n (Terminating nf) n' /\ step m n
}.

(*
Record denote
       {P: ProgrammingLanguage}
       {state: Type}
       {SSS: SmallStepSemantics P state}
       (c: cmd)
       (tr: trace state): Prop :=
{
  ctr: trace (cmd * state);
  ctr_sequential: sequential_trace ctr;
  ctr_sound: sound_trace step ctr;
  s: state;
  mcs: MetaState (cmd * state);
  ctr_begin_end_state: begin_end_state (c, s) ctr mcs;
  end_state_valid: match mcs with
                   | NonTerminating => True
                   | Error => True
                   | Terminating (c', s') => forall mcs'', ~ step (c', s') mcs''
                   end;
  tr_ctr: tr = ctrace2trace ctr
}.
*)

Definition access {cmd stack cont} {P: ProgrammingLanguage cmd} {CS: ControlStack stack} {Cont: Continuation cont} {state: Type} {SSS: SmallStepSemantics cont state} (s: state) (c: cont) (ms: MetaState state) :=
  exists nf: cmd, normal_form nf /\ clos_refl_trans _ (lift_relation step) (Terminating (c, s)) (lift_function (pair (Creturn nf empty_stack)) ms) \/
  ms = NonTerminating /\ exists cs: nat -> cont * state, cs 0 = (c, s) /\ forall k, step (cs k) (Terminating (cs (S k))).

Module ImpSmallStepSemantics (D: FORWARD).

Export D.

(*
Class ImpSmallStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {state_R: Relation state} (SSS: SmallStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Krelation_stable_Kdenote (fun s => eval_bool s b);
  step_defined: forall c s, c <> Sskip -> exists mcs, step (c, s) mcs;
  step_Sskip: forall s mcs, step (Sskip, s) mcs <-> False;
  step_Ssequence: forall c1 c2 s mcs,
    step (Ssequence c1 c2, s) mcs ->
    (exists ms', c1 = Sskip /\ forward (Terminating s) ms' /\ mcs = lift_function (pair c2) ms') \/
    (exists mcs', step (c1, s) mcs' /\ mcs = lift_function (fun cs => (Ssequence (fst cs) c2, snd cs)) mcs');
  step_Sifthenelse: forall b c1 c2 s mcs,
    step (Sifthenelse b c1 c2, s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair c1) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair c2) ms');
  step_Swhile: forall b c s mcs,
    step (Swhile b c, s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ssequence c (Swhile b c))) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair Sskip) ms')
}.
*)

Class ImpSmallStepSemantics {cmd stack} cont {P: ProgrammingLanguage cmd} {iP: ImperativeProgrammingLanguage cmd} {CS: ControlStack stack} {lCS: LinearControlStack stack} {Cont: Continuation cont} {iCont: ImperativeProgrammingLanguageContinuation cont} (state: Type) {state_R: Relation state} (SSS: SmallStepSemantics cont state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Krelation_stable_Kdenote (fun s => eval_bool s b);
  step_Ceval_normalform: forall c cs s mcs,
    normal_form c ->
    step (Ceval c cs, s) mcs ->
    mcs = Terminating (Creturn c cs, s);
  step_Ceval_Ssequence: forall c1 c2 cs s mcs,
    step (Ceval (Ssequence c1 c2) cs, s) mcs ->
    mcs = Terminating (Ceval c1 (cons (Fsequence c2) cs), s);
  step_Ceval_Sifthenelse: forall b c1 c2 cs s mcs,
    step (Ceval (Sifthenelse b c1 c2) cs, s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c1 cs)) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c2 cs)) ms');
  step_Ceval_Swhile: forall b c cs s mcs,
    step (Ceval (Swhile b c) cs, s) mcs ->
    mcs = Terminating (Creturn Sskip (cons (Fwhile b c) cs), s);
  step_Creturn_normalform_emptystack: forall c s mcs,
    normal_form c -> (step (Creturn c empty_stack, s) mcs <-> False);
  step_Creturn_Sskip_Fsequence: forall c cs s mcs,
    step (Creturn Sskip (cons (Fsequence c) cs), s) mcs ->
    mcs = Terminating (Ceval c cs, s);
  step_Creturn_Sskip_Fwhile: forall b c cs s mcs,
    step (Creturn Sskip (cons (Fwhile b c) cs), s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c (cons (Fwhile b c) cs))) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Creturn Sskip cs)) ms');
}.

Class ImpSmallStepSemantics_SbreakScontinue {cmd stack} cont {P: ProgrammingLanguage cmd} {iP: ImperativeProgrammingLanguage cmd} {iP_breakccontinue: ImperativeProgrammingLanguage_SbreakScontinue cmd} {CS: ControlStack stack} {lCS: LinearControlStack stack} (Cont: Continuation cont) {iCont: ImperativeProgrammingLanguageContinuation cont} (state: Type) {state_R: Relation state} (SSS: SmallStepSemantics cont state) {iSSS: ImpSmallStepSemantics cont state SSS}: Type := {
  step_Creturn_Sbreak_Fsequence: forall c cs s mcs,
    step (Creturn Sbreak (cons (Fsequence c) cs), s) mcs ->
    mcs = Terminating (Creturn Sbreak cs, s);
  step_Creturn_Sbreak_Fwhile: forall b c cs s mcs,
    step (Creturn Sbreak (cons (Fwhile b c) cs), s) mcs ->
    mcs = Terminating (Creturn Sskip cs, s);
  step_Creturn_Scontinue_Fsequence: forall c cs s mcs,
    step (Creturn Scontinue (cons (Fsequence c) cs), s) mcs ->
    mcs = Terminating (Creturn Scontinue cs, s);
  step_Creturn_Scontinue_Fwhile: forall b c cs s mcs,
    step (Creturn Scontinue (cons (Fwhile b c) cs), s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c (cons (Fwhile b c) cs))) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Creturn Sskip cs)) ms');
}.

End ImpSmallStepSemantics.

Module Partial := ImpSmallStepSemantics (ProgramState.Partial).

Module Total := ImpSmallStepSemantics (ProgramState.Total).

(*
Instance Total2Partial_ImpSmallStepSemantics {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} (state: Type) {state_R: Relation state} {SSS: SmallStepSemantics P state} (iSSS: Total.ImpSmallStepSemantics P state SSS): Partial.ImpSmallStepSemantics P state SSS.
Proof.
  refine (Partial.Build_ImpSmallStepSemantics _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _ _ _).
  + apply Total.step_defined.
  + apply Total.step_Sskip.
  + intros.
    pose proof Total.step_Ssequence c1 c2 s mcs H
      as [[ms' [? [? ?]]] | [ms' [? ?]]].
    - left; exists ms'; split; [| split]; auto.
      apply Total2Partial_forward; auto.
    - right; exists ms'; auto.
  + intros.
    pose proof Total.step_Sifthenelse b c1 c2 s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
  + intros.
    pose proof Total.step_Swhile b c s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
Qed.
*)

Instance Total2Partial_ImpSmallStepSemantics {cmd stack cont} {P: ProgrammingLanguage cmd} {iP: ImperativeProgrammingLanguage cmd} {CS: ControlStack stack} {lCS: LinearControlStack stack} {Cont: Continuation cont} {iCont: ImperativeProgrammingLanguageContinuation cont} (state: Type) {state_R: Relation state} {SSS: SmallStepSemantics cont state} (iSSS: Total.ImpSmallStepSemantics cont state SSS): Partial.ImpSmallStepSemantics cont state SSS.
Proof.
  Print Partial.Build_ImpSmallStepSemantics.
  refine (Partial.Build_ImpSmallStepSemantics _ _ _ _ _ _ _ _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _ _ _ _ _).
  + apply Total.step_Ceval_normalform.
  + apply Total.step_Ceval_Ssequence.
  + intros.
    pose proof Total.step_Ceval_Sifthenelse b c1 c2 cs s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
  + apply Total.step_Ceval_Swhile.
  + apply Total.step_Creturn_normalform_emptystack.
  + apply Total.step_Creturn_Sskip_Fsequence.
  + intros.
    pose proof Total.step_Creturn_Sskip_Fwhile b c cs s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
Qed.