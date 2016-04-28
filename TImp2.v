Require Export CaseLtac Arith Omega Coq.Program.Equality.

Module Id. 

(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers.  We use [sumbool] to define a computable
    equality operator on [Id]. *)

Inductive t : Type :=
  T : string -> t.

Theorem eq_id_dec : forall id1 id2 : t, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (string_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined. 


Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
  Case "x = x". 
    reflexivity.
  Case "x <> x (impossible)". 
    destruct n. reflexivity. Qed.

End Id.

Definition id := Id.t.

Definition txnid := Id.t.

Definition state := id -> nat.

Definition effect := state -> state.

Definition empty_state : state :=
  fun _ => 0.

Definition id_eff : effect := fun st => st.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if Id.eq_id_dec x x' then n else st x'.

Definition txn_log := txnid -> bool.

Definition empty_txn_log : txn_log := fun _ => false.

Definition commit (tl : txn_log) (n : id) : txn_log :=
  fun n' => if Id.eq_id_dec n n' then true else tl n'.

Check (1,2). 

Definition context := prod state txn_log.

Definition empty_ctx : (context) := (empty_state, empty_txn_log).

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp.

Fixpoint aeval (st: state)(a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  end.

Fixpoint beval (st : state)(b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  end.
(** ** Syntax *)

(**  c ::= SKIP
         | x ::= a
         | c ;; c
         | WHILE b DO c END       <-- Removed
         | IFB b THEN c ELSE c FI
]] 
*)
Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  (*| CIf : bexp -> com -> com -> com*)
  | CPar : com -> com -> com
  | CTxn : txnid -> (effect * com) -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
(*
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
*)
Notation "c1 ||| c2" :=
  (CPar c1 c2) (at level 100, right associativity).
Notation "'TXN' << n >> { c }" :=
  (CTxn n (id_eff,c)) (at level 60, right associativity).
Notation "'TXNF' << n >> { F [ c ] }" :=
  (CTxn n (F,c)) (at level 70, right associativity).

Lemma seq_cons_invertibility: forall c1 c2, (c1;;c2) = c2 -> False.
Proof.
  Admitted.

Module Test1.

Definition X := Id.T "x".
Definition Y := Id.T "y".
Definition Z := Id.T "z".

(* X := X + 2 *)
Definition par_plus : com :=
  TXN <<Id.T "txnL">> {X ::= (APlus (AId X) (ANum 1))} ||| TXN <<Id.T "txnR">> {X ::= (APlus (AId X) (ANum 2))}.

End Test1.

Reserved Notation "x '-t->' y" (at level 40).

Inductive txn_step : (com * state * effect) -> ((option com) * effect) -> Prop :=
  | TS_Skip : forall (st : state)(F : effect), 
               (SKIP, st, F) -t-> (None, F)
  | TS_Ass : forall (st : state)(F: effect)(a : aexp)(n : nat)(x : id),
              aeval st a = n -> 
              (x ::= a, st, F) -t-> 
                   (None, fun st => update (F st) x n)
  | TS_Seq1 : forall c1 c1' c2 st F F',
               (c1, st, F) -t-> (Some c1', F') ->
               (c1;;c2, st, F) -t-> (Some (c1';;c2), F')
  | TS_Seq2 : forall c1 c2 st F F',
               (c1, st, F) -t-> (None, F') ->
               (c1;;c2, st, F) -t-> (Some c2, F')
  where "x '-t->' y" := (txn_step x y).

Reserved Notation "x '--->' y" (at level 50).

Definition com_step_relation := (com * context) -> ((option com) * context) -> Prop.

Inductive step : com_step_relation :=
  | S_Skip : forall (ctx : context)(F : effect), 
               (SKIP, ctx) ---> (None, ctx)
  | S_Ass : forall (tl:txn_log)(st : state)(F: effect)(a : aexp)(n : nat)(x : id),
              aeval st a = n -> 
              (x ::= a, (st,tl)) ---> (None, (update st x n,tl))
  | S_Seq1 : forall c1 c1' c2 ctx ctx',
               (c1, ctx) ---> (Some c1', ctx') ->
               (c1;;c2, ctx) ---> (Some (c1';;c2), ctx')
  | S_Seq2 : forall c1 c2 ctx ctx',
               (c1, ctx) ---> (None, ctx') ->
               (c1;;c2, ctx) ---> (Some c2, ctx')
  | S_Par1 : forall c1 c1' c2 ctx ctx',
               (c1, ctx) ---> (Some c1', ctx') ->
               (c1 ||| c2, ctx) ---> (Some (c1' ||| c2), ctx')
  | S_Par2 : forall c1 c2 c2' ctx ctx',
               (c2, ctx) ---> (Some c2', ctx') ->
               (c1 ||| c2, ctx) ---> (Some (c1 ||| c2'), ctx')
  | S_Par3 : forall c1 c2 ctx ctx',
               (c1, ctx) ---> (None, ctx') ->
               (c1 ||| c2, ctx) ---> (Some c2, ctx')
  | S_Par4 : forall c1 c2 ctx ctx',
               (c2, ctx) ---> (None, ctx') ->
               (c1 ||| c2, ctx) ---> (Some c1, ctx')
  (*| S_Txn1 : forall c c' st F,
               (c,st,id_eff) -t-> (Some c',F) ->
               (TXN {c}, st) ---> (Some (TXNF {F[c']}), st)
  | S_Txn2 : forall c st F,
               (c,st,id_eff) -t-> (None,F) ->
               (TXN {c}, st) ---> (None, st)*)
  | S_TxnF1 : forall n c c' st tl F F',
                (c,st,F) -t-> (Some c',F') ->
                (TXNF <<n>> {F[c]}, (st,tl)) ---> (Some (TXNF <<n>> {F[c']}), (st,tl))
  | S_TxnF2 : forall n c st tl F F',
                (c,st,F) -t-> (None,F') ->
                (TXNF <<n>> {F[c]}, (st,tl)) ---> (None, (F' st, commit tl n))
  where "x '--->' y" := (step x y).

(** Multi-step reduction *)

Reserved Notation " t '--->*' t' "(at level 40).

Inductive multi_step : (com * context) -> ((option com) * context) -> Prop :=
  | base_step  : forall c opc' ctx ctx', 
                    (c,ctx) ---> (opc',ctx') ->
                    (c,ctx) --->* (opc',ctx')
  | trans_step : forall c c' opc'' ctx ctx' ctx'',
                    (c,ctx) ---> (Some c',ctx') ->
                    (c',ctx') --->* (opc'',ctx'')  ->
                    (c,ctx) --->* (opc'',ctx'')
  where "t '--->*' t' " := (multi_step t t').

Notation "c1 '/' ctx '||' ctx'" := ((c1,ctx) --->* (None,ctx'))
(at level 40, ctx at level 39).

(** ** Assertions *)

Definition Assertion := context -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall ctx, P ctx -> Q ctx.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.


Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall ctx ctx',
    (c / ctx || ctx')  ->
    P ctx ->
    Q ctx'.

Notation "{{ P }} c {{ Q }}" := 
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Definition relation (X: Type) := X->X->Prop.

Definition ccrelation := relation context.

Inductive rstar {X:Type} (R: relation X) : relation X :=
  | rstar_refl  : forall (x : X), rstar R x x
  | rstar_trans : forall (x y z : X),
                    R x y ->
                    rstar R y z ->
                    rstar R x z.
Notation "R '^*'" := (rstar R) (at level 60).

Inductive refl_closure {X:Type} (R : relation X) : relation X :=
  | rclos_refl : forall (x : X), refl_closure R x x.

Notation "'ID+' R" := (refl_closure R) (at level 60).

SearchPattern (_*_ -> _).

Print fst.

Definition foo : (nat*nat) -> nat := fun p => let (x,_) := p in x.

Check (fun x y => x).

Definition interleaved_step (R : ccrelation) (c:com) (ctx:context) 
        (opc:option com) (ctx':context) : Prop :=
                 (c,ctx) ---> (opc,ctx') \/ (opc = Some c /\ R ctx ctx').

Notation " 'RSTEP' '(' c ',' ctx ')' '-(' R ')->' '(' opc ',' ctx' ')'" := 
  (interleaved_step R c ctx opc ctx') (at level 40, c at level 39).


Inductive interleaved_multi_step (R : ccrelation) (c : com) (ctx : context) 
          (opc' : option com) (ctx' : context) : Prop := 
 | interleaved_base : RSTEP (c,ctx) -(R)-> (opc',ctx') ->
                      interleaved_multi_step R c ctx opc' ctx'
 | interleaved_trans : forall c1 ctx1,
                        (c,ctx) ---> (Some c1,ctx1) ->
                        interleaved_multi_step R c1 ctx1 opc' ctx' ->
                        interleaved_multi_step R c ctx opc' ctx'.

Check interleaved_multi_step_ind.
Check list_ind.

Notation " 'R*STEP' '(' c , ctx ')' '-(' R ')->*' '(' opc ',' ctx' ')'" := 
  (interleaved_multi_step R c ctx opc ctx')(at level 40).

Definition step_guaranteed (R G :ccrelation) (c :com) (ctx : context) :=
  (forall opc' ctx', (c,ctx) ---> (opc',ctx') -> G ctx ctx')
    /\
  (forall c' opc'' ctx' ctx'',  R*STEP (c,ctx) -(R)->* (Some c',ctx') ->
                              (c',ctx') ---> (opc'',ctx'') ->
                              G ctx' ctx'').

Definition RG_quintuple (R G : ccrelation)(P : Assertion) (c:com)
           (Q : Assertion): Prop :=
  forall st, P st ->
         (* All terminating states st' satisfy the post-condition *) 
         (forall st', R*STEP (c,st) -(R)->* (None,st')  -> Q st')
         (* Every transition starting from st satisfies the guarantee *)
      /\ (step_guaranteed R G c st).

Notation "{{ R ',' P }} c {{ G ',' Q }}" := 
  (RG_quintuple R G P c Q) (at level 90, c at next level).

