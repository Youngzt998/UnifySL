Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.

Section Lindenbaum.

Context {A: Type}
        (CA: Countable A)
        (init: Ensemble A)
        (P: Ensemble A -> Prop).

Hypothesis H_init: P init.

Hypothesis P_Proper: Proper (Same_set A ==> iff) P.

Fixpoint LindenbaumChain (n: nat): Ensemble A :=
  match n with
  | 0 => init
  | S n => fun a => LindenbaumChain n a \/ CA a n /\ P (Union _ (LindenbaumChain n) (Singleton _ a))
  end.

Definition LindenbaumConstruction: Ensemble A :=
  fun a => exists n, LindenbaumChain n a.

Lemma Lindenbaum_included_n_m: forall n m,
  n <= m ->
  Included _ (LindenbaumChain n) (LindenbaumChain m).
Proof.
  intros.
  induction H.
  + exact (fun x H => H).
  + refine (fun x H => _ (IHle x H)).
    clear.
    unfold Ensembles.In; intros; simpl.
    left.
    auto.
Qed.

Lemma Lindenbaum_included_n_omega: forall n,
  Included _ (LindenbaumChain n) LindenbaumConstruction.
Proof.
  intros.
  intros ? ?.
  exists n; auto.
Qed.

Lemma Lindenbaum_included:
  Included _ init LindenbaumConstruction.
Proof.
  apply (Lindenbaum_included_n_omega 0).
Qed.

Lemma Lindenbaum_pointwise_finite_decided: forall a n,
  CA a n ->
  (LindenbaumChain (S n) a) <-> (LindenbaumConstruction a).
Proof.
  intros.
  split; [apply (Lindenbaum_included_n_omega (S n)) | intros].
  destruct H0 as [m ?].
  destruct (le_dec m (S n)); [revert H0; apply Lindenbaum_included_n_m; auto |].
  assert (S n <= m) by omega; clear n0.
  induction H1; auto.
  apply IHle; clear IHle.
  simpl in H0.
  destruct H0; auto.
  destruct H0 as [? _]; exfalso.
  pose proof pf_inj _ _ CA a _ _ H H0.
  omega.
Qed.

Lemma Lindenbaum_finite_witness:
  forall xs, Forall LindenbaumConstruction xs ->
    exists n, Forall (LindenbaumChain n) xs.
Proof.
  intros.
  induction H.
  + exists 0.
    constructor.
  + destruct IHForall as [n ?H].
    destruct (im_inj _ _ CA x) as [m ?].
    exists (max n (S m)).
    constructor.
    - erewrite <- Lindenbaum_pointwise_finite_decided in H by eauto.
      revert H; apply (Lindenbaum_included_n_m (S m)).
      apply Max.le_max_r.
    - revert H1.
      apply Forall_impl; intro.
      apply Lindenbaum_included_n_m.
      apply Max.le_max_l.
Qed.

Lemma Lindenbaum_preserve_n:
  forall n, P (LindenbaumChain n).
Proof.
  intros.
  induction n; auto.
  simpl.
  destruct (classic (exists a, CA a n /\ P (Union A (LindenbaumChain n) (Singleton A a)))).
  + destruct H as [a [? ?]].
    eapply P_Proper; [| exact H0].
    rewrite Same_set_spec.
    intros a0.
    rewrite Union_spec, Singleton_spec.
    assert (CA a0 n -> a = a0).
    {
      intros.
      apply (in_inj _ _ CA a a0 n); auto.
    }
    assert (a = a0 -> P (Union A (LindenbaumChain n) (Singleton A a0))).
    {
      intros.
      subst; auto.
    }
    assert (a = a0 -> CA a0 n).
    {
      intros.
      subst; auto.
    }
    tauto.
  + eapply P_Proper; [| exact IHn].
    rewrite Same_set_spec.
    intros a0.
    firstorder.
Qed.

Lemma Lindenbaum_preserve_omega:
  finite_captured P ->
  subset_preserved P ->
  P LindenbaumConstruction.
Proof.
  intros.
  apply H.
  intros.
  apply Lindenbaum_finite_witness in H1.
  destruct H1 as [n ?].
  rewrite Forall_forall in H1.
  eapply H0; [exact H1 |].
  apply Lindenbaum_preserve_n.
Qed.

End Lindenbaum.