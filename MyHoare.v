(* A definition of a small imperative language, and hoare logic for that language *)

Require Export CaseLtac Arith Omega.

Module Id. 

(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers.  We use [sumbool] to define a computable
    equality operator on [Id]. *)

Inductive t : Type :=
  T : string -> t.

Check eq_nat_dec.
Check 2=2.

SearchPattern (Prop -> Prop -> Set).
SearchAbout sumbool.
Check string_dec.
Check sumbool.
Print sumbool.
Definition two_eq_two : {2 = 2} + { 2<> 2}.
left. reflexivity. 
Defined.

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


(** The following lemmas will be useful for rewriting terms involving [eq_id_dec]. *)

Eval compute in if 2 then 2 else 3.

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
  Case "x = x". 
    reflexivity.
  Case "x <> x (impossible)". 
    destruct n. reflexivity. Qed.

(** **** Exercise: 1 star, optional (neq_id)  *)
Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Id.

Definition id := Id.t.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

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
  | CIf : bexp -> com -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Module Test1.

Definition X := Id.T "x".
Definition Y := Id.T "y".
Definition Z := Id.T "z".

(* X := X + 2 *)
Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

End Test1.

(** *** Operational Semantics 
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st || (update st x n)

                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

*)
Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  where "c1 '/' st '||' st'" := (ceval c1 st st').

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
(* Note: If you want to use the triple notation in other files, then open 
   hoare_spec_scope in that file. *)
Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. unfold hoare_triple. intros.
  apply H.
Qed.

Check (2=2) /\ ~(2=3).

(* Hoare rule conseq as theorem *)
Theorem hoare_ante_strengthening : forall (P' P Q :Assertion) (c : com),
  {{P}} c {{Q}} /\ (P' ->> P) -> {{P'}} c {{Q}}.
Proof.
  intros.
  inversion H.
  clear H.
  unfold hoare_triple.
  unfold hoare_triple in H0.
  intros.
  unfold assert_implies in H1.
  apply H0 with (st := st)(st' := st'). 
  + assumption.
  +. apply H1. assumption. 
Qed.

Theorem hoare_coseq_weakening : forall (P Q Q' :Assertion) (c : com),
  {{P}} c {{Q}} /\ (Q ->> Q') -> {{P}} c {{Q'}}.
Proof.
  intros.
  inversion H; clear H.
  unfold hoare_triple.  
  unfold hoare_triple in H0.
  intros.
  unfold assert_implies in H1.
  apply H1.
  apply H0 with (st := st); assumption.
Qed.  

Theorem hoare_weakening : forall (P' P Q Q' : Assertion) (c : com),
  {{P}} c {{Q}} /\ (P' ->> P) /\ (Q ->> Q') -> {{P'}} c {{Q'}}.
Proof.
  intros.
  inversion H; clear H.
  inversion H1; clear H1.
  + assert ({{P'}} c {{Q}}) as HAnte.
    apply hoare_ante_strengthening with (P:=P).
    auto.
  apply hoare_coseq_weakening with (P:=P')(Q:=Q).
  auto.
Qed.

(* Hoare rule as theorem for SKIP *)
Theorem hoare_skip : forall (P : Assertion), {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple. intros.
  inversion H.
  rewrite <- H3.
  assumption.
Qed.

(* Substituting a for X in P *)
Definition assn_sub (X:id) (a:aexp) (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall (Q : Assertion) (X : id) (a : aexp),
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple. intros.
  unfold assn_sub in H0.
  inversion H; subst.
  assumption.
Qed.

Theorem hoare_seq : forall (P Q R : Assertion) (c1 c2 : com),
  {{P}} c1 {{Q}} -> {{Q}} c2 {{R}} -> {{P}} c1;;c2 {{R}}.                     
Proof.
  unfold hoare_triple.
  intros. inversion H1.
  apply H0 with (st := st'0).
  + assumption.
  + apply H with (st := st)(st' := st'0). assumption. assumption.  
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  Case "b is true".
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(** * Hoare Rules proved as theorems above *)


(**
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 

*)

Module Test2.

Definition X := Id.T "x".
Definition Y := Id.T "y".
Definition Z := Id.T "z".

Lemma plus_trivial1 : forall (a b : nat), a = b + (a - b).
Proof.
  Admitted.
  

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H; clear H H3 st0 H5 st'0;
  inversion H7; clear H1 H2 H3 H4 st0;
  unfold aeval in H9; unfold update;
  simpl; rewrite <- H9. 
  + apply plus_trivial1.
  + reflexivity. 
Qed.

Definition swap_program : com :=
   (X ::= APlus (AId X) (AId Y);;
    Y ::= AMinus (AId X) (AId Y);;
    X ::= AMinus (AId X) (AId Y)).

Theorem swap_1 : forall (a b : nat),
  {{fun st => st X = a /\ st Y = b}}
    X ::= APlus (AId X) (AId Y)
  {{fun st => st X = a + b /\ st Y = b}}.
Proof.
  intros. 
  apply hoare_ante_strengthening with 
  (P := (fun st => st X = a + b /\ st Y = b)[X |-> APlus (AId X) (AId Y)]). 
  split.
  + apply hoare_asgn.  
  + unfold assert_implies.
    intros. unfold assn_sub.
    simpl. unfold update.
    simpl. intuition.
Qed.

Theorem swap_2 : forall (a b : nat),
  {{fun st => st X = a + b /\ st Y = b}}
    Y ::= AMinus (AId X) (AId Y)
  {{fun st => st X = a + b /\ st Y = a}}.
Proof.
  intros.
  apply hoare_ante_strengthening with
    (P := (fun st => st X = a + b /\ st Y = a)[Y |-> AMinus (AId X) (AId Y)]).
  split.
  + apply hoare_asgn.
  + unfold assert_implies.
    intros. unfold assn_sub.
    unfold update.
    simpl. intuition.
Qed.

Theorem swap_3 : forall (a b : nat),
  {{fun st => st X = a + b /\ st Y = a}}
    X ::= AMinus (AId X) (AId Y)
  {{fun st => st Y = a /\ st X = b}}.
Proof.
  intros.
  apply hoare_ante_strengthening with
    (P := (fun st => st Y = a /\ st X = b)[X |-> AMinus (AId X) (AId Y)]).
  split.
  + apply hoare_asgn.
  + unfold assert_implies.
    intros. unfold assn_sub.
    unfold update.
    simpl. intuition.
Qed.

(* The proof technique for the above three steps of swap is essentially the same *)

Theorem swap_exercise : forall (a b :nat),
  {{fun st => st X = a /\ st Y = b}} 
  swap_program
  {{fun st => st Y = a /\ st X = b}}.
Proof.
  intros.
  unfold swap_program.
  apply hoare_seq with (Q := fun st => st X = a + b /\ st Y = b).
    apply swap_1.
  apply hoare_seq with (Q := fun st => st X = a + b /\ st Y = a).
    apply swap_2.
  apply swap_3.
Qed.

End Test2.