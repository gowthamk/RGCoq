Require Export CaseLtac Arith Omega.

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

Definition state := id -> nat.

Definition effect := state -> state.

Definition empty_state : state :=
  fun _ => 0.

Definition id_eff : effect := fun st => st.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if Id.eq_id_dec x x' then n else st x'.

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
  | CTxn : (effect * com) -> com.

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
Notation "'TXN' { c }" :=
  (CTxn (id_eff,c)) (at level 60, right associativity).
Notation "'TXNF' { F [ c ] }" :=
  (CTxn (F,c)) (at level 70, right associativity).


Module Test1.

Definition X := Id.T "x".
Definition Y := Id.T "y".
Definition Z := Id.T "z".

(* X := X + 2 *)
Definition par_plus : com :=
  TXN {X ::= (APlus (AId X) (ANum 1))} ||| TXN {X ::= (APlus (AId X) (ANum 2))}.

End Test1.

Print option.

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

Reserved Notation "x '--->' y" (at level 40).

Definition com_step_relation := (com * state) -> ((option com) * state) -> Prop.

Inductive step : com_step_relation :=
  | S_Skip : forall (st : state)(F : effect), 
               (SKIP, st) ---> (None, st)
  | S_Ass : forall (st : state)(F: effect)(a : aexp)(n : nat)(x : id),
              aeval st a = n -> 
              (x ::= a, st) ---> (None, update st x n)
  | S_Seq1 : forall c1 c1' c2 st st',
               (c1, st) ---> (Some c1', st') ->
               (c1;;c2, st) ---> (Some (c1';;c2), st')
  | S_Seq2 : forall c1 c2 st st',
               (c1, st) ---> (None, st') ->
               (c1;;c2, st) ---> (Some c2, st')
  | S_Par1 : forall c1 c1' c2 st st',
               (c1, st) ---> (Some c1', st') ->
               (c1 ||| c2, st) ---> (Some (c1' ||| c2), st')
  | S_Par2 : forall c1 c2 c2' st st',
               (c2, st) ---> (Some c2', st') ->
               (c1 ||| c2, st) ---> (Some (c1 ||| c2'), st')
  | S_Par3 : forall c1 c2 st st',
               (c1, st) ---> (None, st') ->
               (c1 ||| c2, st) ---> (Some c2, st')
  | S_Par4 : forall c1 c2 st st',
               (c2, st) ---> (None, st') ->
               (c1 ||| c2, st) ---> (Some c1, st')
  (*| S_Txn1 : forall c c' st F,
               (c,st,id_eff) -t-> (Some c',F) ->
               (TXN {c}, st) ---> (Some (TXNF {F[c']}), st)
  | S_Txn2 : forall c st F,
               (c,st,id_eff) -t-> (None,F) ->
               (TXN {c}, st) ---> (None, st)*)
  | S_TxnF1 : forall c c' st F F',
                (c,st,F) -t-> (Some c',F') ->
                (TXNF {F[c]}, st) ---> (Some (TXNF {F[c']}), st)
  | S_TxnF2 : forall c st F F',
                (c,st,F) -t-> (None,F') ->
                (TXNF {F[c]}, st) ---> (None, F' st)
  where "x '--->' y" := (step x y).

(** Multi-step reduction *)

Reserved Notation " t '--->*' t' "(at level 40).

Inductive multi_step : (com * state) -> ((option com) * state) -> Prop :=
  | base_step  : forall c opc' st st', 
                    (c,st) ---> (opc',st') ->
                    (c,st) --->* (opc',st')
  | trans_step : forall c c' opc'' st st' st'',
                    (c,st) ---> (Some c',st') ->
                    (c',st') --->* (opc'',st'')  ->
                    (c,st) --->* (opc'',st'')
  where "t '--->*' t' " := (multi_step t t').

Notation "c1 '/' st '||' st'" := ((c1,st) --->* (None,st'))
(at level 40, st at level 39).

(** ** Assertions *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.


Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
    c / st || st'  ->
    P st ->
    Q st'.

Notation "{{ P }} c {{ Q }}" := 
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Module Test2.

Include Test1.

(* Let us sanity-check our small-step semantics *)
Theorem par_plus_inv : 
  {{fun st => st X = 0 }}
    par_plus
  {{fun st => st X = 3 }}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H.
  + Case "base_step".
    clear H1 c H3 st0 H5 st'0 H4 opc'.
    unfold par_plus in H2.
    inversion H2.
  + Case "base_multi".
    clear H1 c H3 opc'' H2 st0 H5 st''.
    unfold par_plus in H4.
    inversion H4.
    - SCase "ParTxnF1".
      inversion H2.
      inversion H10.
    - SCase "ParTxnF2".
      inversion H2.
      inversion H10.
    - SCase "ParTxnF3".
      inversion H2.
      inversion H10.
      rewrite <- H7 in H6.
      inversion H6.
      * inversion H21.
        inversion H26.
        clear H1 H3 H6 H21 H26.
        inversion H2. inversion H3. rewrite <- H37. rewrite <- H31.
        unfold id_eff. simpl. rewrite H0. simpl. unfold id_eff. simpl.
        rewrite <- H19 in H13. rewrite <- H13. unfold id_eff. 
        unfold update. simpl. rewrite <- H15. simpl. intuition.
      * inversion H23.
        inversion H27.
    - SCase "ParTxnF4".
      rewrite <- H7 in H6.
      inversion H6. 
      * inversion H10.
        inversion H15.
        inversion H2.
        inversion H26.
        unfold id_eff. rewrite <- H31. rewrite <- H20.
        unfold update. simpl. rewrite <- H35 in H29; rewrite <- H29.
        unfold id_eff. unfold update. simpl. rewrite <- H31. simpl.
        rewrite H0. reflexivity.
      * inversion H12.
        inversion H16.
Qed.

End Test2.

Definition relation (X: Type) := X->X->Prop.

Definition ssrelation := relation state.

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

Definition interleaved_step : ssrelation -> com_step_relation :=
  fun R p1 p2 => let (c,st) := p1 in
                 let (opc,st') := p2 in
                 (c,st) ---> (opc,st') \/ (opc = Some c /\ R st st').

Notation " t1 '-(' R ')->' t2 " := (interleaved_step R t1 t2) (at level 40).

Reserved Notation " t1 '-(' R ')->*' t2 "(at level 40).

Inductive interleaved_multi_step (R : ssrelation)  : com_step_relation :=
 | interleaved_base : forall c opc st st',
                        (c,st) -(R)-> (opc,st') ->
                        ((c,st) -(R)->* (opc,st'))
 | interleaved_trans : forall c c' opc st st1 st',
                        (c,st) ---> (Some c',st1) ->
                        (c',st1) -(R)->* (opc,st') ->
                        (c,st) -(R)->* (opc,st')
  where " t1 '-(' R ')->*' t2 " := (interleaved_multi_step R t1 t2).

Definition step_guaranteed (R G :ssrelation) (c :com) (st : state) :=
  (forall st', (c,st) ---> (None,st') -> G st st')
    /\
  (forall c' opc'' st' st'', (c,st) -(R)->* (Some c',st') ->
                              (c',st') ---> (opc'',st'') ->
                              G st' st'').

Definition RG_quintuple (R G : ssrelation)(P : Assertion) (c:com)
           (Q : Assertion): Prop :=
  forall st st',
    P st ->
    (c,st) -(R)->* (None,st')  ->
    Q st' /\ (step_guaranteed R G c st).

Notation "{{ R ',' P }} c {{ G ',' Q }}" := 
  (RG_quintuple R G P c Q) (at level 90, c at next level).

Definition stable (P : Assertion) (R : ssrelation) :=
  forall st st', P st /\ R st st'-> P st'. 

Definition subsumes_states (P Q : Assertion) (G : ssrelation) :=
  forall st st', P st -> Q st' -> G st st'.

Notation "'(' P ',' Q ')' '∈' G" := (subsumes_states P Q G) (at level 90).

Theorem rg_asgn: forall R P G Q X a,
    stable P (R^*) -> 
    {{P}} X::=a {{Q}} ->
    stable Q (R^*) ->
    (P,Q) ∈ G -> 
    {{R,P}} X::=a {{G,Q}}.
Proof.
  unfold RG_quintuple.
  intros R P G Q X a H H0 H1 H2 st st' H3 H4.
  inversion H4.
  + Case "interleaved_base".
    split.
    - SCase "PostCondition".
      unfold interleaved_step in H6.
      inversion H6.
      unfold hoare_triple in H0.
      apply H0 with (st:=st). 
      constructor. assumption. 
      assumption.
      inversion H10. inversion H11.
    - SCase "Guarantee".
      unfold step_guaranteed.
      split.
      * SSCase "SingleStep".
        intros.
        unfold subsumes_states in H2.
        apply H2 with (st:=st)(st':=st'1).
        assumption.
        (* From here, the proof is same as the previous case. *)
        (* How do I say that in coq? *)
        unfold hoare_triple in H0.
        apply H0 with (st:=st). 
        constructor. assumption. 
        assumption.
      * SSCase "Multistep".
        intros. 
        (* Proof strategy is to show P st'1 and Q st'', and then
           rely on subsumes_states property of G. *)
        induction H10.
        (* Base Case *)
        inversion H13. inversion H17.
        inversion H17; clear H17.
        (* We now have R st st'1 *)
        inversion H18. rewrite H20 in H11.
        assert (opc'' = None).
          inversion H11. reflexivity.
        rewrite H17 in H11.      
        unfold subsumes_states in H2.
        apply H2 with (st:=st'1)(st':=st'').
        unfold stable in H.
        apply H with (st:=st)(st':=st'1).
        intuition. apply rstar_trans with (y:= st'1). assumption.
        apply rstar_refl.
        (* From here, the proof is (almost) same as the first case. *)
        (* How do I say that in coq? *)
        unfold hoare_triple in H0.
        apply H0 with (st:=st'1). 
        constructor. assumption. 
        unfold stable in H.
        apply H with (st:=st)(st':=st'1).
        intuition. apply rstar_trans with (y:= st'1). assumption.
        apply rstar_refl.
  + Case "interleaved_trans".
    inversion H10.
Qed.

    unfold stable in H1.    
    apply H1 with (st:=st5)(st':=st').
    split.
    clear H7 opc'' H8 st6 H6 st1 H5 c H14.
    inversion H13.
    apply H1 with (st:=st6)(st':=st5).
    split. 