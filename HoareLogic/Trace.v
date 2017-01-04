Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.HoareLogic.ProgramState.

Definition trace (state: Type): Type := stream (state * MetaState state).

Identity Coercion trace_stream: trace >-> stream.

Definition sequential_trace {state: Type} (tr: trace state) : Prop :=
  forall k s ms s' ms',
    tr k = Some (s, ms) ->
    tr (S k) = Some (s' , ms') ->
    ms = Terminating s'.

Definition sound_trace {state: Type} (R: state -> MetaState state -> Prop) (tr: trace state) : Prop :=
  forall k s ms,
    tr k = Some (s, ms) ->
    R s ms.

Lemma trace_app_sequential1 {state: Type}: forall (tr1 tr2: trace state),
  sequential_trace (stream_app tr1 tr2) ->
  sequential_trace tr1.
Proof.
  intros.
  hnf; intros.
  specialize (H k s ms s' ms').
  erewrite stream_app_spec1' in H by eauto.
  erewrite stream_app_spec1' in H by eauto.
  apply H; auto.
Qed.

Lemma trace_app_sequential2 {state: Type}: forall (tr1 tr2: trace state),
  is_fin_stream tr1 ->
  sequential_trace (stream_app tr1 tr2) ->
  sequential_trace tr2.
Proof.
  intros.
  hnf; intros.
  rewrite is_fin_stream_spec in H.
  destruct H as [n ?].
  specialize (H0 (k + n) s ms s' ms').
  change (S (k + n)) with (S k + n) in H0.
  erewrite stream_app_spec2 in H0 by eauto.
  erewrite stream_app_spec2 in H0 by eauto.
  apply H0; auto.
Qed.

Lemma trace_app_sound1 {state: Type}: forall R (tr1 tr2: trace state),
  sound_trace R (stream_app tr1 tr2) ->
  sound_trace R tr1.
Proof.
  intros.
  hnf; intros.
  specialize (H k s ms).
  erewrite stream_app_spec1' in H by eauto.
  apply H; auto.
Qed.

Lemma trace_app_sound2 {state: Type}: forall R (tr1 tr2: trace state),
  is_fin_stream tr1 ->
  sound_trace R (stream_app tr1 tr2) ->
  sound_trace R tr2.
Proof.
  intros.
  hnf; intros.
  rewrite is_fin_stream_spec in H.
  destruct H as [n ?].
  specialize (H0 (k + n) s ms).
  erewrite stream_app_spec2 in H0 by eauto.
  apply H0; auto.
Qed.

Inductive begin_end_state {state: Type}: state -> trace state -> MetaState state -> Prop :=
| begin_end_empty: forall s, begin_end_state s empty_stream (Terminating s)
| begin_end_fin: forall s ms s' ms' tr n,
    is_n_stream (S n) tr ->
    tr 0 = Some (s, ms) ->
    tr n = Some (s', ms') ->
    begin_end_state s tr ms'
| begin_end_inf: forall s ms tr,
    is_inf_stream tr ->
    tr 0 = Some (s, ms) ->
    begin_end_state s tr NonTerminating.

Definition begin_state {state: Type} (tr: trace state) (s: state): Prop :=
  exists ms, begin_end_state s tr ms.

Definition end_state {state: Type} (tr: trace state) (ms: MetaState state): Prop :=
  exists s, begin_end_state s tr ms.

Definition traces (state: Type): Type := Ensemble (trace state).

Definition traces_app {state: Type} (d1 d2: traces state): traces state :=
  fun tr =>
    (exists tr1 tr2, d1 tr1 /\ d2 tr2 /\ tr = stream_app tr1 tr2) \/
  (exists tr1, d1 tr1 /\ (end_state tr1 NonTerminating \/ end_state tr1 Error) /\ tr = tr1).

Fixpoint traces_power {state: Type} (d: traces state) (n: nat): traces state :=
  match n with
  | 0 => is_empty_stream
  | S n => traces_app (traces_power d n) d
  end.

Definition traces_pstar {state: Type} (d: traces state): traces state :=
  fun tr => exists n, traces_power d n tr.

Definition traces_pomega {state: Type} (d: traces state): traces state :=
  fun tr => exists f, tr = stream_capp f /\ forall n, d (f n).

Lemma traces_app_mono {state: Type}: forall (d1 d2 d3 d4: traces state),
  Included _ d1 d3 ->
  Included _ d2 d4 ->
  Included _ (traces_app d1 d2) (traces_app d3 d4).
Proof.
  intros.
  unfold Included, Ensembles.In in *; intros tr ?.
  destruct H1.
  + destruct H1 as [tr1 [tr2 [? [? ?]]]].
    left; exists tr1, tr2; auto.
  + destruct H1 as [tr1 [? [? ?]]].
    right; exists tr1; auto.
Qed.

Lemma traces_power_mono {state: Type}: forall (d1 d2: traces state) (n: nat),
  Included _ d1 d2 ->
  Included _ (traces_power d1 n) (traces_power d2 n).
Proof.
  intros.
  induction n.
  + hnf; intros; auto.
  + simpl.
    apply traces_app_mono; auto.
Qed.

Lemma traces_pstar_mono {state: Type}: forall (d1 d2: traces state),
  Included _ d1 d2 ->
  Included _ (traces_pstar d1) (traces_pstar d2).
Proof.
  intros.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H0 as [n ?].
  exists n.
  revert tr H0.
  apply traces_power_mono; auto.
Qed.

Lemma traces_pomega_mono {state: Type}: forall (d1 d2: traces state),
  Included _ d1 d2 ->
  Included _ (traces_pomega d1) (traces_pomega d2).
Proof.
  intros.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H0 as [f [? ?]].
  exists f; split; auto.
  intros; apply H, H1.
Qed.

Module Type DECREASE_TRACE.

Declare Module D: DECREASE.

Parameter decrease_trace: forall {state: Type} {kiM: KripkeIntuitionisticModel state}, traces state.

Parameter decrease_trace_with_test: forall {state: Type} {kiM: KripkeIntuitionisticModel state} (P: state -> Prop), traces state.

End DECREASE_TRACE.

Module DecreaseTrace (D: DECREASE) <: DECREASE_TRACE with Module D := D.

Module D := D.
Export D.

Definition decrease_trace {state: Type} {kiM: KripkeIntuitionisticModel state}: traces state :=
  fun tr => is_fin_stream tr /\ forall n s ms, tr n = Some (s, ms) -> decrease (Terminating s) ms.

Definition decrease_trace_with_test {state: Type} {kiM: KripkeIntuitionisticModel state} (P: state -> Prop) : traces state :=
  fun tr => decrease_trace tr /\ exists s, begin_state tr s /\ P s.

End DecreaseTrace.

Module Partial := DecreaseTrace (ProgramState.Partial).
Module Total := DecreaseTrace (ProgramState.Total).

Lemma Total2Partial_decrease_trace
      {state: Type}
      {kiM: KripkeIntuitionisticModel state}:
  Included _ Total.decrease_trace Partial.decrease_trace.
Proof.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H as [? ?].
  split; auto.
  intros.
  apply Total2Partial_decrease, (H0 n); auto.
Qed.

Lemma Total2Partial_decrease_trace_with_test
      {state: Type}
      {kiM: KripkeIntuitionisticModel state}
      (P: state -> Prop):
  Included _
   (Total.decrease_trace_with_test P)
   (Partial.decrease_trace_with_test P).
Proof.
  unfold Included, Ensembles.In; intros tr ?.
  destruct H as [? ?].
  split; auto.
  apply Total2Partial_decrease_trace; auto.
Qed.
