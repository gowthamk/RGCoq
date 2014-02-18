Require Export syntax sos reductions.

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
| RWait :
  forall (P Q:assrt) c b,
    Reflexive G -> 
    stable R ([⊤]b) ->
    (forall x y, star _ G x y -> G x y) ->
    stable R P ->
    stable R Q ->
    (*G_val P c G Q -> *)
    triple G P c Q ->
    triple_rg R G P (wait b do c end) Q
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



  
