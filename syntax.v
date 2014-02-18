(** * Encoding of the syntax of [cwhile] and its SOS. *)
Require Export generic.

(** Identifiers and locations/states *)

Definition id := nat.

(** Syntax of arithmetic expressions supporting only [nat] values for now. *)

Inductive aexp : Type := 
| ANum : nat -> aexp
| AId : id -> aexp 
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Corollary aexp_eq_dec :
  forall x y:aexp,
    {x=y}+{x<>y}.
Proof.
  decide equality;auto with arith.
Qed.

Hint Resolve aexp_eq_dec : utils.

(** Definition of Boolean expressions *)

Inductive bexp : Type := 
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLt : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Corollary bexp_eq_dec :
  forall x y:bexp,
    {x=y}+{x<>y}.
Proof.
  decide equality;auto with utils arith.
Qed.

Hint Resolve bexp_eq_dec : utils.

(** * Formal definition of CWhile's syntax *)

Inductive stmt : Type :=
| Stmt_Skip             : stmt
| Stmt_Ass              : id -> aexp -> stmt
| Stmt_Seq              : stmt -> stmt -> stmt
| Stmt_If               : bexp -> stmt -> stmt -> stmt
| Stmt_While            : bexp -> stmt -> stmt
| Stmt_Wait             : bexp -> stmt -> stmt
| Stmt_Par              : stmt -> stmt -> stmt.

Lemma stmt_eq_dec : 
  forall x y:stmt,
    {x=y}+{x<>y}.
Proof.
  decide equality;auto with utils arith.
Qed.

(** Notations for our programming language. *)

Notation "'skip'" := 
  Stmt_Skip.
Notation "l '::=' a" := 
  (Stmt_Ass l a) (at level 60).
Notation "c1 ; c2" := 
  (Stmt_Seq c1 c2) (at level 80, right associativity).
Notation "'while' b 'do' c 'end'" := 
  (Stmt_While b c) (at level 80, right associativity).
Notation "'ifb' e1 'then' e2 'else' e3 'fi'" := 
  (Stmt_If e1 e2 e3) (at level 80, right associativity).
Notation "'par' c1 'with' c2 'end'" := 
  (Stmt_Par c1 c2)(at level 80, right associativity).
Notation "'wait' b 'do' c 'end'" :=
  (Stmt_Wait b c)(at level 80).

(** Some inequalities that may be usefull in  proof construction. *)

Lemma seq_diff_l : 
  forall c d:stmt,
    ~(c = (c;d)).
Proof.
  double induction c d;intro;try discriminate;
  intros;intro;
  match goal with 
    | H : ?X = (?X;_) |- _ => inv H
  end.
Qed.

Lemma seq_diff_r : 
  forall c d:stmt,
    ~(c = (d;c)).
Proof.
  double induction c d;intro;try discriminate;
  intros;intro;
  match goal with 
    | H : ?X = (_;?X) |- _ => inv H
  end.
Qed.