Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.NatChoice.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.lib.Stream.StreamSplit.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.
Require Import Logic.HoareLogic.SimpleSmallStepSemantics.
Require Import Logic.HoareLogic.SmallStepSemantics.
Require Import Logic.HoareLogic.LocalTraceSemantics.
Require Import Logic.HoareLogic.BigStepSemantics.

Module SSS_SimpleSSS.

Instance SSS_SimpleSSS
         {P: ProgrammingLanguage}
         {state: Type}
         (SSSS: SimpleSmallStepSemantics P state)
         (final_state: cmd * state -> Prop):
  SmallStepSemantics P state :=
  Build_SmallStepSemantics _ _ (SimpleSmallStepSemantics.step final_state).

End SSS_SimpleSSS.

Module LTS_SSS.

Instance LTS_SSS
         {P: ProgrammingLanguage}
         {iP: ImperativeProgrammingLanguage P}
         {state: Type}
         (SSS: SmallStepSemantics P state):
  LocalTraceSemantics P state.
Proof.
  refine (Build_LocalTraceSemantics _ _ SmallStepSemantics.denote _ _).
  + intros.
    destruct (classic (exists mcs, step (c, s) mcs)).
    - destruct H as [mcs ?].
      pose (Q := fun p: option ((cmd * state) *
                                MetaState (cmd * state)) =>
                 match p with
                 | Some (cs, mcs) => step cs mcs
                 | None => True
                 end).
      pose (R := fun p1 p2: option ((cmd * state) *
                                    MetaState (cmd * state)) =>
                   match p1, p2 with
                   | None, Some _ => False
                   | None, None => True
                   | Some (_, Error), None => True
                   | Some (_, NonTerminating), None => True
                   | Some (_, Terminating cs), None => ~ exists mcs, step cs mcs
                   | Some (_, mcs), Some (cs, _) => mcs = Terminating cs
                   end).
      destruct (nat_coinduction' Q R (Some ((c, s), mcs)) H) as [_ctr [? [? ?]]].
      * clear c s mcs H.
        intros [[cs [| | cs']] |] ?.
       ++ exists None; simpl; auto.
       ++ exists None; simpl; auto.
       ++ destruct (classic (exists mcs, step cs' mcs)) as [[mcs ?] | ?].
         -- exists (Some (cs', mcs)); simpl; auto.
         -- exists None; simpl; auto.
       ++ exists None; simpl; auto.
      * assert (forall k1 k2, k1 < k2 -> _ctr k1 = None -> _ctr k2 = None).
        Focus 1. {
          intros.
          assert (k1 <= k2) by omega; clear H3.
          induction H5.
          + auto.
          + specialize (H1 m).
            rewrite IHle in H1; simpl in H1.
            destruct (_ctr (S m)); auto; tauto.
        } Unfocus.
        pose (ctr := exist _ _ctr H3: trace (cmd * state)).
        change _ctr with (stream_get ctr) in H0, H1, H2.
        clearbody ctr; clear _ctr H3.
        exists (stream_map (fun p => match p with ((c, s), mcs) => (s, lift_function snd mcs) end) ctr).
        destruct (n_stream_or_inf_stream ctr) as [[[| k] ?] | ?].
       ++ exfalso; destruct H3 as [? _]; congruence.
       ++ destruct (ctr k) eqn:?H; [| pose proof (proj2 H3 k (le_n _)); congruence].
          destruct p as [cs' mcs'].
          refine (conj (SmallStepSemantics.Build_denote _ _ _ c _ ctr _ _ s mcs' _ _ eq_refl) _).
         -- clear k c s mcs cs' mcs' H0 H H3 H4.
            hnf; intros.
            specialize (H1 k); subst R; simpl in H1.
            rewrite H, H0 in H1.
            destruct ms; tauto.
         -- clear k c s mcs cs' mcs' H0 H H3 H4.
            hnf; intros.
            specialize (H2 k); subst Q; simpl in H2.
            rewrite H in H2; auto.
         -- eapply begin_end_fin; eauto.
         -- clear c s mcs H0 H.
            destruct H3 as [? _].
            specialize (H1 k); subst R; simpl in H1.
            rewrite H, H4 in H1.
            destruct mcs'; auto.
            destruct p; firstorder.
         -- destruct cs' as [c' s'].
            exists (lift_function snd mcs'); eapply begin_end_fin.
           ** apply stream_map_n_stream; eauto.
           ** rewrite stream_map_spec, H0.
              reflexivity.
           ** rewrite stream_map_spec, H4.
              reflexivity.
       ++ refine (conj (SmallStepSemantics.Build_denote _ _ _ c _ ctr _ _ s NonTerminating _ _ eq_refl) _).
         -- clear c s mcs H0 H H3.
            hnf; intros.
            specialize (H1 k); subst R; simpl in H1.
            rewrite H, H0 in H1.
            destruct ms; tauto.
         -- clear c s mcs H0 H H3.
            hnf; intros.
            specialize (H2 k); subst Q; simpl in H2.
            rewrite H in H2; auto.
         -- eapply begin_end_inf; eauto.
         -- auto.
         -- exists NonTerminating; eapply begin_end_inf.
           ** apply stream_map_inf_stream; eauto.
           ** rewrite stream_map_spec, H0.
              reflexivity.
    - exists empty_stream.
      refine (conj (SmallStepSemantics.Build_denote _ _ _ c empty_stream empty_stream _ _ s (Terminating (c, s)) _ _ _) _).
      * hnf; intros.
        rewrite empty_stream_spec in H0; congruence.
      * hnf; intros.
        rewrite empty_stream_spec in H0; congruence.
      * apply begin_end_empty.
      * firstorder.
      * symmetry; apply stream_map_empty_stream.
      * exists (Terminating s).
        apply begin_end_empty.
  + intros.
    destruct H as [? ? _ _ _ _ _ ?].
    hnf; intros.
    unfold ctrace2trace in tr_ctr.
    rewrite tr_ctr, stream_map_spec in H, H0.
    specialize (ctr_sequential k).
    destruct (ctr k) as [[[c0 s0] mcs] |]; [| congruence].
    inversion H; subst s0 ms; clear H.
    destruct (ctr (S k)) as [[[c'0 s'0] mcs'] |]; [| congruence].
    inversion H0; subst s'0 ms'; clear H0.
    specialize (ctr_sequential _ _ _ _ eq_refl eq_refl).
    subst mcs; auto.
Defined.

Lemma trace_split2
        {P: ProgrammingLanguage}
        {iP: ImperativeProgrammingLanguage P}
        {state: Type}:
  forall R (ctr: trace (cmd * state)) c c' s mcs,
    sequential_trace ctr ->
    sound_trace R ctr ->
    begin_end_state (c, s) ctr mcs ->
    (exists ctr1 ctr2 s',
       sequential_trace ctr1 /\
       sound_trace R ctr1 /\
       begin_end_state (c, s) ctr1 (Terminating (c', s')) /\
       sound_trace (fun cs _ => fst cs <> c') ctr1 /\
       sequential_trace ctr2 /\
       sound_trace R ctr2 /\
       begin_end_state (c', s') ctr2 mcs /\
       ctr = stream_app ctr1 ctr2) \/
    sound_trace (fun cs _ => fst cs <> c') ctr.
Proof.
  intros.
  destruct (cut2_exists ctr (fun csmcs => fst (fst csmcs) = c')).
  + destruct H2 as [ctr1 [ctr2 [? [? [? [[[c0 s'] mcs0] [? ?]]]]]]].
    left; exists ctr1, ctr2, s'.
    simpl in H6; subst c0 ctr.
    split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    - apply trace_app_sequential1 in H; auto.
    - apply trace_app_sound1 in H0; auto.
    - admit.
    - hnf; intros.
      exact (H4 k _ H3).
    - apply trace_app_sequential2 in H; auto.
    - apply trace_app_sound2 in H0; auto.
    - admit.
    - auto.
  + right.
    hnf; intros.
    exact (H2 k _ H3).
Admitted.

Lemma trace_split_head
        {P: ProgrammingLanguage}
        {iP: ImperativeProgrammingLanguage P}
        {state: Type}:
  forall R (ctr: trace (cmd * state)) c s mcs,
    sequential_trace ctr ->
    sound_trace R ctr ->
    begin_end_state (c, s) ctr mcs ->
    exists mcs',
    R (c, s) mcs' /\
    match mcs' with
    | Terminating (c', s') => 
       exists ctr',
       sequential_trace ctr' /\
       sound_trace R ctr' /\
       begin_end_state (c', s') ctr' mcs /\
       ctr = stream_app (singleton_trace (c, s) mcs') ctr'
    | _ => ctr = singleton_trace (c, s) mcs'
    end.
Admitted.

Module Partial.

Export SmallStepSemantics.Partial.
Export LocalTraceSemantics.Partial.
Export BigStepSemantics.Partial.

Lemma Ssequence_fin_left {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {niP: NormalImperativeProgrammingLanguage P} {state: Type} {kiM: KripkeIntuitionisticModel state} {SSS: SmallStepSemantics P state} {iSSS: ImpSmallStepSemantics P state SSS}:
  forall (ctr: trace (cmd * state)) c c0 s1 cs,
    sequential_trace ctr ->
    sound_trace step ctr ->
    sound_trace (fun cs _ => fst cs <> Ssequence Sskip c) ctr ->
    begin_end_state (Ssequence c0 c, s1) ctr (lift_function (pair (Ssequence Sskip c)) cs) ->
    exists ctr',
      sequential_trace ctr' /\
      sound_trace step ctr' /\
      begin_end_state (c0, s1) ctr' (lift_function (pair Sskip) cs) /\
      ctrace2trace ctr' = ctrace2trace ctr.
Admitted.

Lemma Ssequence_progress_left {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {niP: NormalImperativeProgrammingLanguage P} {state: Type} {kiM: KripkeIntuitionisticModel state} {SSS: SmallStepSemantics P state} {iSSS: ImpSmallStepSemantics P state SSS}:
  forall (ctr: trace (cmd * state)) c c0 s1 mcs,
    sequential_trace ctr ->
    sound_trace step ctr ->
    sound_trace (fun cs _ => fst cs <> Ssequence Sskip c) ctr ->
    begin_end_state (Ssequence c0 c, s1) ctr mcs ->
    (exists c2 s2, mcs = Terminating (Ssequence c2 c, s2)) \/
    mcs = NonTerminating \/ mcs = Error.
Admitted.

Instance iLTS_SSS {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {niP: NormalImperativeProgrammingLanguage P} {state: Type} {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state) {iSSS: ImpSmallStepSemantics P state SSS}: ImpLocalTraceSemantics P state (LTS_SSS SSS).
Proof.
  refine (Build_ImpLocalTraceSemantics _ _ _ _ _ _ SmallStepSemantics.Partial.eval_bool_stable _ _ _ _).
  + intros.
    destruct H as [ctr _ ? ? mcs' ? _ ?].
    inversion ctr_begin_end_state.
    - subst.
      unfold ctrace2trace.
      rewrite stream_map_empty_stream.
      apply empty_stream_is_empty.
    - rename ms into mcs.
      subst.
      exfalso.
      pose proof ctr_sound 0 (Sskip, s) mcs H0.
      rewrite step_Sskip in H2; auto.
    - rename ms into mcs.
      subst.
      exfalso.
      pose proof ctr_sound 0 (Sskip, s) mcs H0.
      rewrite step_Sskip in H1; auto.
  + intros.
    destruct H.
    destruct (trace_split2 step ctr _ (Ssequence Sskip c2) _ _ ctr_sequential ctr_sound ctr_begin_end_state).
    - destruct H as [ctr1 [ctrd2 [s' [? [? [? [? [? [? [? ?]]]]]]]]]].
      left; exists (ctrace2trace ctr1), (ctrace2trace ctrd2).
      subst ctr.
      split; [| split]; [| | auto].
      * destruct (Ssequence_fin_left _ _ _ _ (Terminating s') H H0 H2 H1) as [ctr1' [? [? [? ?]]]].
        apply (SmallStepSemantics.Build_denote _ _ _ _ _ ctr1' H6 H7 _ _ H8).
       ++ simpl; intros; rewrite step_Sskip; auto.
       ++ symmetry; auto.
      * destruct (trace_split_head step ctrd2 _ _ _ H3 H4 H5) as [cs [? ?]].
        apply step_Ssequence in H6.
        destruct H6;
          [| destruct H6 as [? [? ?]]; rewrite step_Sskip in H6; tauto].
        destruct H6 as [ms [_ [? ?]]].
        subst cs; destruct ms; simpl in H7.
       ++ right.
          exists (singleton_trace s' Error).
          split; [| split].
         -- apply singleton_trace_decrease; auto.
         -- right; exists s'.
            apply begin_end_state_singleton_trace.
         -- subst.
            stream_extensionality k; destruct k as [| [| ]]; auto.
       ++ right.
          exists (singleton_trace s' NonTerminating).
          split; [| split].
         -- apply singleton_trace_decrease; auto.
         -- left; exists s'.
            apply begin_end_state_singleton_trace.
         -- subst.
            stream_extensionality k; destruct k as [| [| ]]; auto.
       ++ destruct H7 as [ctr2 [? [? [? ?]]]].
          left; exists (singleton_trace s' (Terminating s0)), (ctrace2trace ctr2).
          subst ctrd2.
          split; [| split].
         -- apply singleton_trace_decrease; auto.
         -- apply (SmallStepSemantics.Build_denote _ _ _ _ _ ctr2 H7 H8 _ _ H9); auto.
         -- unfold ctrace2trace.
            rewrite stream_map_stream_app.
            f_equal.
            stream_extensionality k; destruct k as [| [| ]]; auto.
      * subst tr.
        unfold ctrace2trace.
        rewrite stream_map_stream_app.
        reflexivity.
    - right.
      exists tr.
      assert (mcs = NonTerminating \/ mcs = Error).
      Focus 1. {
        destruct (Ssequence_progress_left ctr _ _ _ _
                   ctr_sequential ctr_sound H ctr_begin_end_state);
          [exfalso | auto].
        destruct H0 as [?c [?s ?]].
        subst mcs.
        pose proof step_defined (Ssequence c c2) s0 (Ssequence_Sskip _ _).
        clear - end_state_valid H0; firstorder.
      } Unfocus.
      split; [| split]; auto.
      * set (cs := lift_function snd mcs).
        assert (mcs = lift_function (pair (Ssequence Sskip c2)) cs) by (destruct H0; subst; auto).
        rewrite H1 in ctr_begin_end_state.
        destruct (Ssequence_fin_left _ _ _ _ _ ctr_sequential ctr_sound H ctr_begin_end_state) as [ctr' [? [? [? ?]]]].
        apply (SmallStepSemantics.Build_denote _ _ _ _ _ ctr' H2 H3 _ _ H4).
       ++ clear H1; destruct H0; subst; simpl; auto.
       ++ congruence.
      * destruct H0; [left | right]; subst; exists s;
        apply begin_end_state_ctrace in ctr_begin_end_state; auto.
  + intros.
    destruct H.
    destruct (trace_split_head step ctr _ _ _ ctr_sequential ctr_sound ctr_begin_end_state) as [cs [? ?]].
    apply step_Sifthenelse in H.
    destruct H as [[? ?] | [? ?]]; [left | right];
    destruct H1 as [ms [? ?]]; subst cs.
    - destruct ms; [right | right | left].
      * exists (singleton_trace s Error).
        split; [| split].
       ++ apply singleton_trace_decrease_test; auto.
       ++ right; exists s.
          apply begin_end_state_singleton_trace.
       ++ simpl in H0.
          subst.
          stream_extensionality k; destruct k as [| [| ]]; auto.
      * exists (singleton_trace s NonTerminating).
        split; [| split].
       ++ apply singleton_trace_decrease_test; auto.
       ++ left; exists s.
          apply begin_end_state_singleton_trace.
       ++ simpl in H0.
          subst.
          stream_extensionality k; destruct k as [| [| ]]; auto.
      * simpl in H0.
        destruct H0 as [ctr' [? [? [? ?]]]].
        exists (singleton_trace s (Terminating s0)), (ctrace2trace ctr').
        split; [| split].
       ++ apply singleton_trace_decrease_test; auto.
       ++ apply (SmallStepSemantics.Build_denote _ _ _ _ _ ctr' H0 H2 _ _ H3); auto.
       ++ subst.
          unfold ctrace2trace.
          rewrite stream_map_stream_app.
          f_equal.
          stream_extensionality k; destruct k as [| [| ]]; auto.
    - destruct ms; [right | right | left].
      * exists (singleton_trace s Error).
        split; [| split].
       ++ apply singleton_trace_decrease_test; auto.
       ++ right; exists s.
          apply begin_end_state_singleton_trace.
       ++ simpl in H0.
          subst.
          stream_extensionality k; destruct k as [| [| ]]; auto.
      * exists (singleton_trace s NonTerminating).
        split; [| split].
       ++ apply singleton_trace_decrease_test; auto.
       ++ left; exists s.
          apply begin_end_state_singleton_trace.
       ++ simpl in H0.
          subst.
          stream_extensionality k; destruct k as [| [| ]]; auto.
      * simpl in H0.
        destruct H0 as [ctr' [? [? [? ?]]]].
        exists (singleton_trace s (Terminating s0)), (ctrace2trace ctr').
        split; [| split].
       ++ apply singleton_trace_decrease_test; auto.
       ++ apply (SmallStepSemantics.Build_denote _ _ _ _ _ ctr' H0 H2 _ _ H3); auto.
       ++ subst.
          unfold ctrace2trace.
          rewrite stream_map_stream_app.
          f_equal.
          stream_extensionality k; destruct k as [| [| ]]; auto.
  + 
Abort.

End Partial.
End LTS_SSS.

Module BSS_LTS.

Instance BSS_LTS
         {P: ProgrammingLanguage}
         {state: Type}
         (LTS: LocalTraceSemantics P state):
  BigStepSemantics P state.
Proof.
  refine (Build_BigStepSemantics _ _ LocalTraceSemantics.access _).
  intros.
  pose proof denote_defined c s as [tr [? ?]].
  destruct H0 as [ms ?].
  exists ms, tr.
  auto.
Defined.

End BSS_LTS.