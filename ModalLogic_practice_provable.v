Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.


Module ModalLogicFirstTry.

Module ModalLogicProvable.

Inductive expr:Type:=
  | PropVar: nat -> expr
  | truep: expr
  | notp: expr -> expr
  | orp: expr -> expr->expr
  | box: expr->expr.
Definition diamond (p:expr):= notp (box (notp p)).
Definition falsep := notp truep.
Definition andp (p q:expr):=notp (orp(notp p)(notp q)).
Definition impp (p q:expr):= orp (notp p) q.
Definition iffp(p q :expr):= andp (impp p q)(impp q p).

Notation "x && y":= (andp x y)(at level 40, left associativity).
Notation "x || y":= (orp x y)(at level 50, left associativity).
Notation "x --> y":= (impp x y)(at level 55, right associativity).
Notation "x <--> y" := (iffp x y) (at level 60, no associativity).
Notation "~~ x" := (notp x) (at level 35).
Notation "'FF'" := falsep.
Notation "'TT'" := truep.
Reserved Notation "|-- P " (at level 71, no associativity).

Inductive provable:expr -> Prop:=
| axiom1: forall x y, |-- (x --> (y --> x))
| axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, |-- (x --> y --> x && y)
| andp_elim1: forall x y, |-- (x && y --> x)
| andp_elim2: forall x y, |-- (x && y --> y)
| orp_intros1: forall x y, |-- (x --> x || y)
| orp_intros2: forall x y, |-- (y --> x || y)
| orp_elim: forall x y z, |-- ((x --> z) --> (y --> z) --> (x || y --> z))
| notp_elim: forall x, |-- (~~ ~~ x) --> x
| falsep_elim: forall x, |-- (FF --> x)
| truep_intros: |-- TT
| modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y
| K_axiom: forall x y,|-- box (x --> y) --> box x --> box y
| N_rule: forall x, |-- x -> |-- box x
where "|-- P" := (provable P).
End ModalLogicProvable.


Module ModalLogicProvableLemma.

Import ModalLogicProvable.

Print Language.
Locate expr.

Instance L_test1: Language := {expr:=expr}.
Instance L_text2: Language. Proof. exact (Build_Language expr). Qed.
Instance L_text3: Language. Proof. constructor. exact expr. Qed.

Check provable_impp_trans.

Instance L:Language:= Build_Language expr. Locate impp.
Instance minL:MinimunLanguage L:= Build_MinimunLanguage L impp.

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance AX: NormalAxiomatization L G := Build_AxiomaticProofTheory_AX provable.

Check provable_impp_trans.

Instance minAX: MinimunAxiomatization L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Check provable_impp_trans.


Lemma impp_trans: forall x y z, |-- (x --> y) --> (y --> z) --> (x --> z).
Proof.
  intros.
  pose proof provable_impp_trans.
  apply H.
Qed.

Lemma impp_trans_detachment: forall x y z, |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof. 
  intros x y z H1 H2.
  pose proof impp_trans x y z as H3.
  pose proof modus_ponens (x --> y) ((y --> z) --> (x --> z)) H3 H1 as H4.
  pose proof modus_ponens (y --> z) (x --> z) H4 H2 as H5.
  exact H5.
Qed.

Lemma impp_exchange: forall x y z, |-- (x --> y --> z) --> (y --> x --> z).
Proof.
  intros.
  pose proof provable_impp_arg_switch.
  apply H.
Qed.

(*this should choose one? not clear...  
  can get impp_compress from impp_andp...?   but it's not like what i learned... *)
Lemma impp_andp: forall x y z, |-- (x --> y --> z) --> ((x && y) --> z).
Proof. 
  intros x y z.
  pose proof axiom2 (x --> y--> z) x ((x && y) --> z).
Admitted.

Lemma impp_compress: forall x y, |-- (x --> x --> y) --> (x --> y).
Proof.
  intros x y. 
  pose proof impp_andp x x y.
Admitted.
(*seems axioms above *)


Lemma impp_trans_3_2: forall x y z a, 
                      |-- (x --> y --> z) --> (z --> a) --> (x --> y --> a).
Proof. 
  intros x y z a.
Admitted.

Lemma impp_refl: forall x, |-- x --> x.
Proof. 
  intros.
  pose proof axiom2 x (x-->x) x.
  pose proof axiom1 x (x-->x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  exact H3.
Qed.

Lemma add_head: forall x y p, |-- (x --> y) --> (p --> x) --> (p --> y).
Proof.
  intros x y p.
  pose proof impp_trans p x y as H1.
  pose proof impp_exchange (p --> x) (x --> y) (p --> y) as H2.
  pose proof modus_ponens _ _ H2 H1 as H3.
  exact H3.
Qed.

Lemma add_head_3: forall x y z p, |--(x --> y --> z) 
                                   --> (p --> x) --> (p --> y) --> (p --> z).
Proof.
  intros x y z p.
  pose proof impp_exchange (p --> x)(x --> y --> z)((p --> y) --> p --> z) as H1.
  pose proof add_head x (y --> z) p as H2.
  pose proof axiom2 p y z as H3.
  pose proof impp_trans_3_2 
             (x --> y --> z) (p --> x) (p --> y --> z) ((p --> y) --> p --> z) as H4.
  pose proof modus_ponens _ _ H4 H2 as H5.
  pose proof modus_ponens _ _ H5 H3 as H6.
  exact H6.
Qed.

Lemma impp_andp_intros: forall x y z, |-- (x --> y) --> (x --> z) --> (x --> y && z).
Proof. 
  intros x y z.
  pose proof (add_head_3 y z (y && z) x) as H1.
  pose proof modus_ponens 
             (y --> z --> y && z) 
             ((x --> y) --> (x --> z) --> x --> y && z)
             H1
             (andp_intros y z)
             as H2.
  exact H2.
Qed.

Lemma box_immp_refl: forall x, |-- box x --> box x.
Proof. intros x. apply (impp_refl (box x)). Qed.

Lemma K_axiom_detachment: forall x y, |-- box (x-->y) -> |-- box x -> |-- box y.
Proof. 
  intros x y H1 H2.
  pose proof modus_ponens (box (x-->y)) ((box x)--> (box y)) (K_axiom x y) H1 as H3.
  apply (modus_ponens (box x) (box y) H3 H2).
Qed.

Lemma box_truep_intros:|-- box TT.
Proof. apply ( N_rule TT truep_intros) . Qed.

Lemma modus_ponens_rev_try: forall x y, (|--x -> |--y) -> (|-- x --> y).
Proof. intros x y H1. Abort.

Lemma box_andp_intros: forall x y, |-- box (x --> y --> (x && y)).
Proof. intros x y. apply (N_rule (x --> y --> x && y) (andp_intros x y)). Qed.

Lemma box_andp_elim1: forall x y, |-- box (x && y --> x).
Proof. intros x y. apply (N_rule (x && y --> x) (andp_elim1 x y)). Qed.

Lemma box_andp_elim2: forall x y, |-- box (x && y --> y).
Proof. intros x y. apply (N_rule (x && y --> y) (andp_elim2 x y)). Qed.

Lemma box_andp_elim1_split: forall x y, |-- box (x && y) --> box x.
Proof. 
  intros x y. 
  pose proof K_axiom (x && y) x as H1.
  pose proof modus_ponens 
             (box (x && y --> x))  
             (box (x && y) --> box x) 
             H1
             (box_andp_elim1 x y)
             as H2.
  exact H2.
Qed.

Lemma box_andp_elim2_split: forall x y, |-- box (x && y) --> box y.
Proof. 
  intros x y. 
  pose proof K_axiom (x && y) y as H1.
  pose proof modus_ponens 
             (box (x && y --> y))  
             (box (x && y) --> box y) 
             H1
             (box_andp_elim2 x y)
             as H2.
  exact H2.
Qed.


Lemma box_andp_split: forall x y, |-- box (x && y) --> (box x) && (box y).
Proof.
  intros x y.
  pose proof andp_intros (box x) (box y) as H1.
  pose proof box_andp_elim1_split x y as H2.
  pose proof box_andp_elim2_split x y as H3.
  pose proof impp_andp_intros (box (x && y)) (box x) (box y) as H4.
  pose proof modus_ponens 
             (box (x && y) --> box x)
             ((box (x && y) --> box y) --> box (x && y) --> box x && box y)
             H4 H2
             as H5.
  pose proof modus_ponens
             (box (x && y) --> box y)
             (box (x && y) --> box x && box y)
             H5 H3
             as H6.
  exact H6.
Qed.

(* learn from the textbook*)
(* need impp_andp, impp_trans *)
Lemma box_andp_merge: forall x y, |-- (box x) && (box y) --> box (x && y).
Proof.
  intros x y.
  pose proof andp_intros x y as H1.
  pose proof box_andp_intros x y as H2.
  pose proof K_axiom as H3.
  pose proof (H3 (x) (y --> x && y)) as H4.
  pose proof modus_ponens (box (x --> y --> x && y)) (box x --> box (y --> x && y)) H4 H2 as H5.
  pose proof (H3 y (x && y)) as H6.
  pose proof (impp_trans_detachment (box x) (box (y --> x && y))  ((box y --> box (x && y)))) 
             H5 H6 as H7.
  pose proof (impp_andp (box x) (box y) (box (x&&y))) as H8.
  apply (modus_ponens (box x --> box y --> box (x && y)) 
                      (box x && box y --> box (x && y)) 
                       H8 H7).
Qed.

Lemma box_andp_intros_split: forall x y, |-- box x --> box y --> box (x && y).
Proof. 
  intros x y.
  pose proof andp_intros (box x) (box y) as H1.
  pose proof box_andp_merge x y as H2.
  pose proof impp_trans_3_2 (box x) (box y) (box x && box y) (box (x && y)) as H3.
  pose proof modus_ponens _ _ H3 H1 as H4.
  pose proof modus_ponens _ _ H4 H2 as H5.
  exact H5.
Qed.

Lemma box_orp_intros1: forall x y, |-- box (x --> x||y ).
Proof.
  intros x y.
  apply (N_rule (x --> x || y) (orp_intros1 x y) ).
Qed.

Lemma box_orp_intros2: forall x y, |-- box (y --> x||y ).
Proof.
  intros x y.
  apply (N_rule (y --> x || y) (orp_intros2 x y) ).
Qed.

Lemma box_orp_intros1_split: forall x y, |-- box x --> box (x || y).
Proof. 
  intros x y. 
  pose proof (K_axiom x (x||y)) as H1.
  pose proof modus_ponens  (box (x --> x || y))   (box x -->  (box (x || y) ) ) H1 as H2.
  apply (H2 (box_orp_intros1 x y)).
Qed.

Lemma box_orp_intros2_split: forall x y, |-- box y --> box (x || y).
Proof. 
  intros x y. 
  pose proof (K_axiom y (x||y)) as H1.
  pose proof modus_ponens  (box (y --> x || y))   (box y -->  (box (x || y) ) ) H1 as H2.
  apply (H2 (box_orp_intros2 x y)).
Qed.


Lemma box_orp_merge: forall x y, |-- box x || box y --> box (x || y) .
Proof. 
  intros x y.
  pose proof ( orp_elim (box x) (box y) (box (x || y))) as H1.
  pose proof modus_ponens 
              ( box x --> box (x || y) ) 
              ((box y --> box (x || y)) --> box x || box y --> box (x || y) ) 
              H1
              (box_orp_intros1_split x y)
             as H2.
  pose proof modus_ponens
              ( box y --> box (x || y) )
              ( box x || box y --> box (x || y) )
             H2
             (box_orp_intros2_split x y)
             as H3.
  exact H3.
Qed.

(* I don't think this one is provable...*)
Lemma box_orp_split: forall x y, |-- box (x || y) -->  (box x) || (box y) .
Proof.
  intros x y.
Abort.

Lemma box_to_diamond: forall x, |-- box x --> diamond x.
Proof. intros x. unfold diamond. Admitted.

Lemma not_box_to_diamond: forall x, |-- (~~ (box x)) --> diamond (~~ x).
Proof. intros x. unfold diamond. Admitted.

Lemma box_compress: forall x, |-- box (box x) --> box x.
Proof. Admitted.

Lemma not_diamond_imp_box_not:forall x, |-- ~~ (diamond x) --> box (~~ x).
Proof. intros x. unfold diamond. apply (notp_elim (box (~~ x))). Qed.

End ModalLogicProvableLemma.
End ModalLogicFirstTry.
