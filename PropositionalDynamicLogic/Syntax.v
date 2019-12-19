Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Import PropositionalLanguageNotation.
Local Open Scope syntax.

Class Program : Type:={
  program: Type;
}.

Class PropositionalDynamicLanguage (L:Language)(Pro: Program):Type:={
  boxp: program -> expr -> expr
}.


Class ProgramOperation (L:Language)(Pro:Program):Type:= {
  choice: program -> program -> program;
  composition: program -> program -> program;
  iteration: program -> program;
  test: expr -> program
}.



Definition diamond{L:Language} {MinL: MinimunLanguage L}{PL: PropositionalLanguage L} {Pro: Program} {PDL: PropositionalDynamicLanguage L Pro} (x: expr)(pi: program)
: expr := ~~ (boxp pi (~~ x)).


Module PropositionalDynamicLanguageNotation.

Notation "[ pi ] x" := (boxp pi x) (at level 30, left associativity) : syntax.
Notation "< pi > x" := (diamond pi x) (at level 30, left associativity) : syntax.

Notation "pi1 \\// pi2" := (choice pi1 pi2) (at level 31, left associativity) : syntax.
Notation " pi1 -;- pi2" := (composition pi1 pi2) (at level 29, no associativity) : syntax.
Notation " pi * " := (iteration pi) (at level 28) : syntax.
Notation " y ? " := (test y) (at level 28) : syntax.


End PropositionalDynamicLanguageNotation.