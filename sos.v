Require Export generic syntax.

(** * States and evaluation of Boolean and arithmetic expressions, in a denotational way. *)

Definition st := id -> nat.

(** The empty configuration/state --> this must be changed to the [option] monad *)

Definition empty_st : st := 
  fun _ => 0.

(** Update function for states *)

Definition upd (s : st) (V:id) (n : nat) : st :=
  fun V' => if eq_nat_dec V V' then n else s V'.

(** * Arithmetic expression evaluation *)

Section ArithmeticExpressions.
  
  (** Evaluation function. *)
  (* begin show *)
  Function aeval (st : st) (e : aexp) {struct e} : nat :=
    match e with
      | ANum n => n
      | AId i => st i
      | APlus a1 a2 => (aeval st a1) + (aeval st a2)
      | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
      | AMult a1 a2 => (aeval st a1) * (aeval st a2)
    end.

  Function blt_nat (n m : nat) {struct n} : bool :=
    match n with
      | O => 
        match m with
          | S _ => true
          | _ => false
        end
      | S n' =>
        match m with
          | O => false
          | S m' => blt_nat n' m'
        end
    end.
  (* end show *)

End ArithmeticExpressions.


Section BooleanExpressions.

  Definition neg (b: bexp) :=
    match b with 
      | BTrue => BFalse 
      | BFalse => BTrue 
      | _ => BFalse (*shouldn't happen*) 
    end.
  
  Definition and (b b':bexp) :=
    match b, b' with 
      | BTrue, BTrue => BTrue 
      | _,_ => BFalse 
    end.
  
  Function  beval (st : st) (e : bexp){struct e} : bexp :=
    match e with
      | BTrue => BTrue
      | BFalse => BFalse
      | BEq a1 a2 => 
        if beq_nat (aeval st a1) (aeval st a2) then BTrue else BFalse
      | BLt a1 a2 => 
        if blt_nat (aeval st a1) (aeval st a2) then BTrue else BFalse
      | BNot b1 => neg (beval st b1)
      | BAnd b1 b2 => and (beval st b1) (beval st b2)
    end.

  (** Decidability of the evaluation of Boolean formulas. *)

  Lemma beval_dec : forall x:bexp,forall s:st,
    {beval s x = BTrue}+{beval s x = BFalse}.
  Proof.
    intros.
    functional induction (beval s x);firstorder;
      repeat 
        (match goal with
           | H: beval _ _ = _ |- _ => try rewrite H;clear H;simpl
         end);auto.
  Qed.

End BooleanExpressions.

Hint Resolve aexp_eq_dec bexp_eq_dec.


(** Assertions about configurations *)

Section Assertions.

  (** Definition of assertion. *)

  Definition assrt := st -> Prop.

  (** Boolean predicate as an assertion. *)

  Definition b2assrt (b:bexp) : assrt :=
    fun st => beval st b = BTrue.

  Lemma b2assrt_dec : forall b s,
    {b2assrt b s}+{~b2assrt b s}.
  Proof.
    intros.
    unfold b2assrt.
    destruct(beval_dec b s);auto.
  Qed.

End Assertions.

Notation "s [ x ← v ]" := (upd s x v)(at level 0). 

(** Definitions to combine configurations. *)

Section AssertionCombinators.

  Definition assg_subs v a Q : assrt :=
    fun (s : st) => Q (s [v ← (aeval s a)]).

  Definition assrtT (be: bexp) : assrt :=
    fun s => b2assrt be s.
  
  Definition assrtF (be: bexp) : assrt :=
    fun s => ~b2assrt be s.
  
  Definition assrtAnd (P Q: assrt) : assrt :=
    fun s => P s /\ Q s.

  Definition assrtOr (P Q: assrt) : assrt :=
    fun s => P s \/ Q s.

  Definition assrtImp (P Q: assrt) : Prop :=
    forall s, P s -> Q s.

  Definition assrt_eq e v :=
    fun s => aeval s e = v.

  Definition assrt_lt e v :=
    fun s => aeval s e < v.

  Definition assrt_leq e v :=
    assrtOr (assrt_eq e v) (assrt_lt e v).

  Definition assrt_geq v e :=
    fun s => aeval s e >= v.

  Definition assrt_gt v e :=
    fun s => aeval s e > v.

End AssertionCombinators.

(** Notations for assertions. *)

Infix "[∨]" := (assrtOr)(at level 40).
Infix "[∧]" := (assrtAnd)(at level 40).
Infix "[→]" := (assrtImp)(at level 40).
Notation "[⊤] b" := (assrtT b)(at level 60).
Notation "[⊥] b" := (assrtF b)(at level 60).
Infix "[∼]" := (assrt_eq)(at level 40).
Infix "[<]" := (assrt_lt)(at level 40).
  
(** Relations on states. *)

Definition StR := relation st.

(** The identity relation. *)

Definition ID : StR :=
  fun x y => x = y.

(** Universal relation. *)

Definition TT : StR :=
  fun _ _ => True.

(** * Structural operational semantics for CWhile *)

Definition not_par(c:stmt) :=
  forall c1 c2, c <> par c1 with c2 end.

Inductive step : (stmt*st) -> (stmt*st) -> Prop :=
|S_Ass: forall s v a, step ((v ::= a),s) (skip,s [v ← aeval s a])
                  
|S_SeqStep : forall  s c1 c1' s' c2, 
               step  (c1,s) (c1',s') -> step  ((c1;c2),s) ((c1';c2),s')
                        
|S_SeqFinish : forall  s c2, step  ((skip;c2),s) (c2,s)
                          
|S_IfFalse : forall  s c1 c2 b,
               ~b2assrt b s -> step  (ifb b then c1 else c2 fi,s) (c2,s)
                        
|S_IfTrue : forall  s c1 c2 b,
              b2assrt b s -> step  (ifb b then c1 else c2 fi,s) (c1,s)
                       
|S_While : forall  s b c ,
             step (while b do c end,s) (ifb b then (c;while b do c end) else skip fi,s).

Inductive cstep : (stmt * st) -> (stmt * st) -> Prop :=

 |CS_Ass: forall s v a,

            cstep ((v ::= a),s) (skip,s [v ← aeval s a])
                  
 |CS_SeqStep : forall  s c1 c1' s' c2,
                 cstep  (c1,s) (c1',s') ->
                 cstep  ((c1;c2),s) ((c1';c2),s')
                        
 |CS_SeqFinish : forall  s c2,
                   cstep  ((skip;c2),s) (c2,s)
                          
 |CS_IfFalse : forall  s c1 c2 b,
                 ~b2assrt b s ->
                 cstep  (ifb b then c1 else c2 fi,s) (c2,s)
                        
 |CS_IfTrue : forall  s c1 c2 b,
                b2assrt b s ->
                cstep  (ifb b then c1 else c2 fi,s) (c1,s)
                       
 |CS_While : forall  s b c ,
               cstep (while b do c end,s) (ifb b then (c;while b do c end) else skip fi,s)
                          
 |CS_Par1 : forall s c1 c1' c2 s' ,
              cstep  (c1,s) (c1',s') -> 
              cstep  (par c1 with c2 end,s) (par c1' with c2 end,s')
                     
 |CS_Par2 : forall s c1 c2 c2' s',
              cstep (c2,s) (c2',s') ->
              cstep (par c1 with c2 end,s) (par c1 with c2' end,s')
                    
 |CS_Par_end : forall s,
                 cstep (par skip with skip end,s) (skip,s)
                       
 |CS_Wait : forall b c s s',
              b2assrt b s ->
              star _ (cstep) (c,s) (skip,s') ->
              cstep (wait b do c end,s) (skip,s').

Notation "x ⇒ y" := (cstep x y)(at level 45).

Hint Constructors cstep.