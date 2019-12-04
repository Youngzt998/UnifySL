
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

Section Fischer_Ladner_Closed.


Context {L: Language}
        {Pro: Program}
        {ProOp: ProgramOperation L Pro}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {pdL: PropositionalDynamicLanguage L Pro}

        .

Record FL_closed (X: Ensemble expr):Prop :={
  FL_closed_impp: forall x y, In expr X (impp x y) -> In _ X x /\ In _ X y;
  FL_closed_orp: forall x y, In _ X (orp x y) -> In _ X x /\ In _ X y;
  FL_closed_andp: forall x y, In _ X (andp x y) -> In _ X x /\ In _ X y;
  FL_closed_falsep: In _ X (falsep);
  FL_closed_boxp: forall x pi, In _ X (boxp pi x) -> In _ X x;
  FL_closed_boxp_choice: forall x p q, In _ X (boxp (choice p q) x) -> In _ X (orp (boxp p x) (boxp q x));
  FL_closed_boxp_composition: forall x p q, In _ X (boxp (composition p q) x) -> In _ X (boxp p (boxp q x));
  FL_closed_boxp_iteration: forall x pi, In _ X (boxp (iteration pi) x) -> In _ X (boxp pi (boxp (iteration pi) x));
  FL_closed_boxp_test: forall x y, In _ X (boxp (test y) x) -> In _ X x /\  In _ X y;
}.

Class FL_closed_set: Type :={
  FL_closure_construction (psi: expr): Ensemble expr
}.

Definition FL_closure_construction_is_FL_closed (flc: FL_closed_set): Prop := 
forall psi, FL_closed (FL_closure_construction psi).

Record FL_axiom {flc: FL_closed_set} (psi:expr) (A: Ensemble expr): Prop :={
  FL_axiom_included: Included _ A (FL_closure_construction psi);
  (* FL_axiom_consist: consistent A; *)
  (* FL_axiom_MCS: forall B, Included _ B FL_closure_construction /\ Included _ A B -> ~ (consistent B);*)
}.

Definition FL_axiom_existence {flc: FL_closed_set}:Prop :=
forall psi, exists A, FL_axiom psi A.

End Fischer_Ladner_Closed.




Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.PropositionalDynamicLanguage.

Section FL_closure.

Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}.

Fixpoint FL_closure (x: expr Sigma ProV): Ensemble (expr Sigma ProV):=
  Union _ (Singleton _ x)
  match x with
  | impp y z => Union _ (FL_closure y) (FL_closure z)
  | orp y z => Union _ (FL_closure y) (FL_closure z)
  | andp y z => Union _ (FL_closure y) (FL_closure z)
  | falsep => Singleton _ (falsep)
  | boxp pi x => 
      Union _ (Singleton _ x)
      match pi with
      | choice p q => Singleton _ (orp (boxp p x)(boxp q x))
      | composition p q => Singleton _ (boxp p (boxp q x))
      | iteration p => Singleton _ (boxp p (boxp pi x))
      | test y => Singleton _ y
      | basep p => Empty_set _
      end
  | varp v => Singleton _ (varp v)
  end.



Lemma FL_closure_include_self: forall x, In _ (FL_closure x) x.
Proof.
  intros x. 
  destruct x; apply Union_introl; apply In_singleton.
Qed.

Lemma FL_closure_ensure_impp: 
forall x y psi, In _ (FL_closure psi) (impp x y) ->
In _ (FL_closure psi) x /\ In _ (FL_closure psi) y.
Proof. 
  induction psi.
  - intros H. simpl in H.
    remember (impp x y) as e. destruct H. 
    + rewrite Heqe in H.
      remember (impp x y) as f. destruct H. 
      rewrite Heqf. split.
      * simpl. apply Union_intror. apply Union_introl. apply FL_closure_include_self.
      * simpl. apply Union_intror. apply Union_intror. apply FL_closure_include_self.
    + rewrite Heqe in H.
      remember (impp x y) as f. destruct H. 
      * rewrite <- Heqe in H. split.
        ** simpl. apply Union_intror. apply Union_introl. apply (IHpsi1 H).
        ** simpl. apply Union_intror. apply Union_introl. apply (IHpsi1 H).
      * rewrite <- Heqe in H. split.
        ** simpl. apply Union_intror. apply Union_intror. apply (IHpsi2 H).
        ** simpl. apply Union_intror. apply Union_intror. apply (IHpsi2 H).
  (* almost the same *)
  - admit.
  - admit.
  - admit.
  - induction p.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - intros H. simpl in H.
    remember (impp x y) as e. destruct H.
    + rewrite Heqe in H. remember (impp x y) as f. destruct H. inversion Heqf.
    + rewrite Heqe in H. remember (impp x y) as f. destruct H. inversion Heqf.
    
Admitted.

Lemma FL_closure_ensure_orp: 
forall psi x y, In _ (FL_closure psi) (orp x y) ->
In _ (FL_closure psi) x /\ In _ (FL_closure psi) y.
Proof. Admitted.


Lemma FL_closure_ensure_andp: 
forall psi x y, In _ (FL_closure psi) (andp x y) ->
In _ (FL_closure psi) x /\ In _ (FL_closure psi) y.
Proof. Admitted.

Lemma FL_closure_ensure_falsep: 
forall psi, In _ (FL_closure psi) falsep.
Proof. Admitted.

Lemma FL_closure_ensure_boxp: 
forall psi x pi , In _ (FL_closure psi) (boxp pi x) ->
In _ (FL_closure psi) x.
Proof. Admitted.

Lemma FL_closure_ensure_boxp_choice: 
forall psi x p q ,
In (expr Sigma ProV) (FL_closure psi) (boxp (choice p q) x) ->
In (expr Sigma ProV) (FL_closure psi) (orp (boxp p x) (boxp q x)).
Proof. Admitted.

Lemma FL_closure_ensure_boxp_composition: 
forall psi x p q,
In (expr Sigma ProV) (FL_closure psi) (boxp (composition p q) x) ->
In (expr Sigma ProV) (FL_closure psi) (boxp p (boxp q x)).
Proof. Admitted.

Lemma FL_closure_ensure_boxp_iteration:
forall psi x pi,
In (expr Sigma ProV) (FL_closure psi) (boxp (iteration pi) x) ->
In (expr Sigma ProV) (FL_closure psi) (boxp pi (boxp (iteration pi) x)).
Proof. Admitted.

Lemma FL_closure_ensure_boxp_test:
forall psi x y,
In (expr Sigma ProV) (FL_closure psi) (boxp (test y) x) ->
In (expr Sigma ProV) (FL_closure psi) x /\
In (expr Sigma ProV) (FL_closure psi) y.
Proof. Admitted.

End FL_closure.




Section FL_closure_is_FL_closed.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}
        
        .

Instance L {Sigma: PropositionalVariables} {ProV: ProgramVariables}: Language 
:= Build_Language (expr Sigma ProV).

Instance Pro {Sigma: PropositionalVariables} {ProV: ProgramVariables}: Program
:= Build_Program (program Sigma ProV).


Instance ProOp {Sigma: PropositionalVariables} {ProV: ProgramVariables}: ProgramOperation L Pro
:= Build_ProgramOperation L Pro choice composition iteration test.

Instance minL {Sigma: PropositionalVariables} {ProV: ProgramVariables}: MinimunLanguage L
:= Build_MinimunLanguage L impp.

Instance pL {Sigma: PropositionalVariables} {Pro: ProgramVariables}: PropositionalLanguage L
:= Build_PropositionalLanguage L andp orp falsep.

Instance pdL {Sigma: PropositionalVariables} {ProV: ProgramVariables}: PropositionalDynamicLanguage L Pro
:= Build_PropositionalDynamicLanguage L Pro boxp.

Instance flc: FL_closed_set:= Build_FL_closed_set FL_closure.

Lemma FL_closure_is_FL_closed: FL_closure_construction_is_FL_closed flc.
Proof.
  intros psi. constructor.
  - intros x y. apply (FL_closure_ensure_impp x y psi).
  - apply FL_closure_ensure_orp.
  - apply FL_closure_ensure_andp.
  - apply FL_closure_ensure_falsep.
  - apply FL_closure_ensure_boxp.
  - apply FL_closure_ensure_boxp_choice.
  - apply FL_closure_ensure_boxp_composition.
  - apply FL_closure_ensure_boxp_iteration.
  - apply FL_closure_ensure_boxp_test.
Qed.

Lemma Lindenbaum_lemma: FL_axiom_existence.
Proof.
  hnf. intros.
Admitted.


End FL_closure_is_FL_closed.












