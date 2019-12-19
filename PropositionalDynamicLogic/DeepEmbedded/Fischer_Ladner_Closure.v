Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
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
Require Import Logic.PropositionalDynamicLogic.Complete.Fischer_Ladner.

Import PropositionalDynamicLanguageNotation.

Require Import Coq.Sets.Ensembles.


Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.PropositionalDynamicLanguage.
Require Import Logic.PropositionalDynamicLogic.DeepEmbedded.ProofTheories.


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
      | choice p q => Singleton _ (andp (boxp p x)(boxp q x))
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
In (expr Sigma ProV) (FL_closure psi) (andp (boxp p x) (boxp q x)).
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

Existing Instances 
PropositionalDynamicLanguage.L
PropositionalDynamicLanguage.Pro
PropositionalDynamicLanguage.ProOp
PropositionalDynamicLanguage.minL 
PropositionalDynamicLanguage.pL
PropositionalDynamicLanguage.pdL
ProofTheories.G
ProofTheories.AX
ProofTheories.minAX
ProofTheories.ipG
ProofTheories.cpG
ProofTheories.pdlk
.

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


End FL_closure_is_FL_closed.




Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.lib.Countable.

Section Atom_construction.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}
        .
Definition exp:= expr Sigma ProV.



Check LindenbaumChain.
Print context.

(* 
  construction idea (psi is consistent): 
  F(psi):= {psi} ∪ G( {psi}, psi )
  
  result = {psi}
  match psi:
  if psi == x --> y:
    if result ∪ {x} is consistent:
      result = result ∪ {x}
    if result ∪ {y} is consistent:
      result = result ∪ {y}
  ...
  F()
*)
Import Classical.
Local Open Scope logic_base.
Local Open Scope syntax.
Context {P:context -> Prop}
        .

(* might be too complicated... *)
Fixpoint construct_axiom (psi: exp)(init: Ensemble exp): Ensemble exp:=
  fun a => init a \/
  match psi with
  | impp x y | orp x y | andp x y (* if its ok to add psi, then add is; else drop it *)
     =>   (  P(init;;psi) /\ (  (construct_axiom x (init;;psi)) a \/ (construct_axiom y (Union _ (init;;psi) (construct_axiom x (init;;psi)) )) a ) )
        \/(~ P(init;;psi) /\ (  (construct_axiom x  init      ) a \/ (construct_axiom y (Union _  init       (construct_axiom x  init      ) )) a ) )

  | falsep => False
  | boxp pi x =>    (* TBD *)
      match pi with
      | choice p q => False     (* TBD *)
      | composition p q => False  (* TBD *)
      | iteration p => False      (* TBD *)
      | test y => False           (* TBD *)
      | basep p => False          (* TBD *)
      end
  | varp v => (a = varp v /\ P (Union _ init (Singleton _ a)))     (* TBD *)
  end.



Definition axiom (psi: exp):= construct_axiom psi (Singleton _ psi).

Lemma axiom_construction_include_sefl: forall psi, In _ (axiom psi) psi.
Proof.
  intros;hnf. 
  destruct psi; left; apply In_singleton.
Qed.

Lemma axiom_construction_is_inside_FL_closure: forall psi, Included _ (axiom psi) (FL_closure psi).
Proof.
  intros. unfold Included, In, axiom. intros. destruct psi.
  - destruct x.
    + simpl. destruct H as [ | [ [] | [] ]].
      * left. apply H.
      *
  (* should be ok ... ? *)
Admitted.

Lemma axiom_construction_reserve_P: forall psi, P (Singleton _ psi) -> P (axiom psi).
Proof.
  intros. destruct psi.
  (* should be ok ... ? *)
Admitted.

(* use which equivalent definition ? *)
Lemma axiom_construction_is_maximal_trial_1: forall psi x, In _ (FL_closure psi) x -> P (axiom psi ;; x) -> In _ (axiom psi) x.
Proof. Admitted.

Lemma axiom_construction_is_maximal_trial_2: forall psi x, In _ (FL_closure psi) x -> ~ In _ (axiom psi) x -> ~ P (axiom psi;;x).
Proof. Admitted.

Lemma axiom_construction_reserve_maximal: forall psi Phi, Included _ Phi (FL_closure psi) -> Included _ (axiom psi) (Phi) -> ~ P Phi.
Proof.
  intros psi Phi H1 H2 H3.
Admitted.

Check FL_closure_is_FL_closed.


End Atom_construction.

Section Lindenbaum_construction.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}
        .

Existing Instances 
PropositionalDynamicLanguage.L
PropositionalDynamicLanguage.Pro
PropositionalDynamicLanguage.ProOp
PropositionalDynamicLanguage.minL 
PropositionalDynamicLanguage.pL
PropositionalDynamicLanguage.pdL
ProofTheories.G
ProofTheories.AX
ProofTheories.minAX
ProofTheories.ipG
ProofTheories.cpG
ProofTheories.pdlk
flc
.


Hypothesis Countable_expr: Countable exp.
Definition cP:= consistent.

Definition Lindenbaum_single_construction (psi: exp): Ensemble exp := LindenbaumConstruction Countable_expr (Singleton _ psi) consistent.

Locate exp.

Definition Atom_construction (psi: exp): Ensemble exp := Intersection _ (FL_closure psi) (Lindenbaum_single_construction psi).


Instance atc: Atom_set:= Build_Atom_set Atom_construction .

Lemma intersection_is_in_FL_closure:
forall psi, Included Base.expr (Atom_construction psi) (FL_closure_construction psi).
Proof. Admitted.

Lemma intersection_is_consistent:
forall psi, consistent (Fischer_Ladner.Atom_construction psi).
Proof. Admitted.

Lemma intersection_is_maximal:
forall psi x,
In _ (FL_closure_construction psi) x ->
~ In _ (Atom_construction psi) x ->
~ consistent (Union _ (Fischer_Ladner.Atom_construction psi) (Singleton Base.expr x)).
Proof.
  intros. unfold consistent. 
  apply (all_not_not_ex exp). intros x0.
  intro; apply H1; clear H1.
  unfold Atom_construction, In in H0.
  
  

  
Admitted.

Lemma intersection_is_atom: atom_construction_is_atom flc atc.
Proof.
  hnf. intros. 
  constructor.
  - apply intersection_is_in_FL_closure.
  - apply intersection_is_consistent.
  - apply intersection_is_maximal.
Qed.


End Lindenbaum_construction.


Section LindenbaumLemma.
Context {Sigma: PropositionalVariables}
        {ProV: ProgramVariables}
        .
        
Hypothesis c_e: Countable exp.

Existing Instances 
PropositionalDynamicLanguage.L
PropositionalDynamicLanguage.Pro
PropositionalDynamicLanguage.ProOp
PropositionalDynamicLanguage.minL 
PropositionalDynamicLanguage.pL
PropositionalDynamicLanguage.pdL
ProofTheories.G
ProofTheories.AX
ProofTheories.minAX
ProofTheories.ipG
ProofTheories.cpG
ProofTheories.pdlk
flc
atc
.

Lemma Lindenbaum_lemma: FL_axiom_existence.
Proof.
  hnf. intros.
  exists (Atom_construction c_e psi).
  split.
  - apply intersection_is_atom.
  - simpl. constructor.
    + inversion H0. admit.  (* ok *)
    + inversion H0.
      pose proof @Lindenbaum_included exp c_e (Singleton _ psi) consistent.
      rewrite <- H1.
      admit. (* ok *)
Admitted.



End LindenbaumLemma.



