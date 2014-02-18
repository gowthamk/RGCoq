

(** * Classic Hoare logic deductive system. This proof systems is used to handle the [atomic] command, since this one does not admit parallel constructions. *)

Inductive triple (G:Env) : assrt -> stmt -> assrt -> Prop :=
| triple_Skip: 
  forall P, 
    triple G P skip P
| triple_Assgn : 
  forall v a P,
    (forall s, G s (upd s v (aeval s a))) ->
    triple G (assg_subs v a P) (v ::= a) P
| triple_If: 
  forall P c1 c2 Q b, 
    triple G (([⊤]b)[∧]P) c1 Q -> 
    triple G (([⊥]b)[∧]P) c2 Q -> 
    triple G P (ifb b then c1 else c2 fi) Q
| triple_Sequence: 
  forall c1 c2 P K Q, 
    triple G P c1 K -> 
    triple G K c2 Q -> 
    triple G P (c1;c2) Q
| triple_Conseq: 
  forall P P' Q Q' G' c, 
    (assrtImp P P') ->
    (assrtImp Q' Q) ->
    (rstImp G' G) ->
    triple G' P' c Q' ->
    triple G P c Q 
| triple_Loop :
  forall P b c,
    triple G (([⊤]b)[∧](P)) c P ->
    triple G P (while b do c end) (([⊥]b)[∧]P).

(**  * Deductive system for the rely/guarantee principle *)
Inductive triple_rg (R G:StR) : assrt -> stmt -> assrt -> Prop :=
| RSkip: 
  forall (P Q:assrt), 
    Reflexive G -> 
    stable R P -> 
    stable R Q -> 
    P[→]Q ->
    triple_rg R G P skip Q
| RAsgn : 
  forall v a P Q,
    stable R P -> 
    stable R Q ->
    (forall s, G s (upd s v (aeval s a))) ->
    (forall s, P s -> Q (upd s v (aeval s a))) ->
    triple_rg R G P (v ::= a) Q
| RAtom :
  forall (P Q:assrt) c,
    Reflexive G -> 
    (forall x y, star _ G x y -> G x y) ->
    stable R P ->
    stable R Q ->
    (*G_val P c G Q -> *)
    triple G P c Q ->
    triple_rg R G P (atomic(c)) Q
| RIf: 
  forall P c1 c2 Q b, 
    Reflexive G ->
    stable R (assrtT b) ->
    stable R (assrtF b) ->
    stable R P ->
    triple_rg R G (([⊤]b)[∧]P) c1 Q -> 
    triple_rg R G (([⊥]b)[∧]P) c2 Q -> 
    triple_rg R G P (ifb b then c1 else c2 fi) Q
| RSequence: 
  forall c1 c2 P K Q, 
    Reflexive G ->
    triple_rg R G P c1 K -> 
    triple_rg R G K c2 Q -> 
    triple_rg R G P (c1;c2) Q
| RConseq: 
  forall (R' G':Env) P P' Q Q' c, 
    triple_rg R' G' P' c Q' ->
    assrtImp P P' ->
    assrtImp Q' Q ->
    rstImp R R' ->
    rstImp G' G ->
    triple_rg R G P c Q
| RLoop :
  forall P b c,
    Reflexive G ->
    stable R (assrtT b) ->
    stable R (assrtF b) ->
    stable R P ->
    triple_rg R G (([⊤]b)[∧](P)) c P ->
    triple_rg R G P (while b do c end) (([⊥]b)[∧]P)
| RConcur : 
 forall (Rl Rr Gl Gr:StR) P Q1 Q2 Q cr cl,
   Reflexive Gl -> 
   Reflexive Gr ->
   rstImp R (rstAnd Rl Rr) -> 
   rstImp (rstOr Gl Gr) G ->
   rstImp (rstOr Rl Gl) Rr ->
   rstImp (rstOr Rr Gr) Rl ->
   (assrtAnd Q1 Q2)[→]Q ->
   stable (rstOr Rr Gr) Q1 ->
   stable (rstOr Rl Gl) Q2 ->
   stable (rstOr Rr Gr) P ->
   stable (rstOr Rl Gl) P ->
   triple_rg Rl Gl P cl Q1 ->
   triple_rg Rr Gr P cr Q2 ->
   triple_rg R G P (par cl with cr end) Q.

Notation "{{  R  , G  }}  ⊢  {{  P  }}  c {{  Q  }}" := 
  (triple_rg R G P c Q)(at level 40).

Notation "{{  R  , G  }}  ⊧  {{  P  }}  c {{  Q  }}" := 
  (HG_val R G P c Q)(at level 40).

(** * "Next version's" specification of the deductive system *)
(** Here we use the rely and guarantee as indexes for the inductive predicate. *)

(* Inductive triple_rg_new (R G:Env) : assrt -> stmt -> assrt -> Prop := *)
(* | RSkip_new:  *)
(*   forall P Q:assrt,  *)
(*     stable R P -> P[→]Q -> triple_rg_new R G P skip Q *)
(* | RAsgn_new :  *)
(*   forall v a P Q, *)
(*     stable R P ->  *)
(*     stable R Q -> *)
(*     (forall s, G s (upd s v (aeval s a))) -> *)
(*     (forall s, P s -> Q (upd s v (aeval s a))) -> *)
(*     triple_rg_new R G P (v ::= a) Q *)
(* | RAtom_new : *)
(*   forall (P Q:assrt) c, *)
(*     stable R P -> *)
(*     stable R Q -> *)
(*     G_val P c G Q ->  *)
(*     triple_rg_new R G P (atomic(c)) Q *)
(* | RIf_new:  *)
(*   forall P c1 c2 Q b,  *)
(*     stable R (assrtT b) -> *)
(*     stable R (assrtF b) -> *)
(*     stable R P -> *)
(*     triple_rg_new R G (([⊤]b)[∧]P) c1 Q ->  *)
(*     triple_rg_new R G (([⊥]b)[∧]P) c2 Q ->  *)
(*     triple_rg_new R G P (ifb b then c1 else c2 fi) Q *)
(* | RSequence_new :  *)
(*   forall c1 c2 P K Q,  *)
(*     triple_rg_new R G P c1 K ->  *)
(*     triple_rg_new R G K c2 Q ->  *)
(*     triple_rg_new R G P (c1;c2) Q *)
(* | RConseq_new:  *)
(*   forall (R':Env)(G':StR) P P' Q Q' c,  *)
(*     triple_rg_new R' G' P' c Q' -> *)
(*     assrtImp P P' -> *)
(*     assrtImp Q' Q -> *)
(*     rstImp R R' -> *)
(*     rstImp G' G -> *)
(*     triple_rg_new R G P c Q *)
(* | RLoop_new : *)
(*   forall  P b c, *)
(*     stable R (assrtT b) -> *)
(*     stable R (assrtF b) -> *)
(*     stable R P -> *)
(*     triple_rg_new R G (([⊤]b)[∧](P)) c P -> *)
(*     triple_rg_new R G P (while b do c end) (([⊥]b)[∧]P) *)
(* | RConcur_new :  *)
(*  forall (Rl Rr Gl Gr:StR) P Q1 Q2 cr cl, *)
(*    (** Decompose the enviroment into the environments of the two parallel processes. *) *)
(*    rstImp R Rr -> *)
(*    rstImp R Rl -> *)
(*    rstImp (rstOr Gl Gr) G -> *)
(*    rstImp (rstOr Rl Gl) Rr -> *)
(*    rstImp (rstOr Rr Gr) Rl -> *)
(*    stable (rstOr Rr Gr) Q1 -> *)
(*    stable (rstOr Rl Gl) Q2 -> *)
(*    stable (rstOr Rr Gr) P -> *)
(*    stable (rstOr Rl Gl) P -> *)
(*    triple_rg_new Rl Gl P cl Q1 -> *)
(*    triple_rg_new Rr Gr P cr Q2 -> *)
(*    triple_rg_new R G P (par cl with cr end) (assrtAnd Q1 Q2). *)



  
