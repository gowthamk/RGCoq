(** * Main definitions to be used in the rest of the formalization. *)
Require Export syntax sos.
Require Export Classes.RelationClasses.

(** A simple notation for relations over terms of type [st]. *)

Notation "'Env'" := StR.

(** Definitions to combine relations over states. These definitions will be needed for specifying the logical properties for the deductive system. *)

Section RelationCombinators.
 
  Definition rstOr (R G:StR) : StR :=
    fun s s' => R s s' \/ G s s'.

  Definition rstAnd (R G:StR) : StR :=
    fun s s' => R s s' /\ G s s'.

  Definition rstImp (R G:StR) : Prop :=
    forall s s', R s s' -> G s s'.

  Definition rstComp (R G:StR) :=
    fun s s'' =>
      exists s', R s s' /\ G s' s''.

  Lemma rstOr_refl : 
    forall (R1 R2 R3:StR),
      Reflexive R1 ->
      Reflexive R2 ->
      rstImp (rstOr R1 R2) R3 ->
      Reflexive R3.
  Proof.
    intros.
    red.
    intro.
    apply H1.
    left;auto.
  Qed.

End RelationCombinators.

Infix "<{∪}>" := rstOr(at level 45).
Infix "<{∩}>" := rstAnd(at level 45).
Infix "<{⊆}>" := rstImp(at level 45).
Infix "<{⊙}>" := rstComp(at level 45).

(** * Stability conditions *)

Section Stability.

  (* The environment performs a change in the state but this change does not 
     interferes with validity of the predicate given as argument. *)
  
  Definition stable (R:Env)(P:assrt) := 
    forall x y, P x /\ R x y -> P y.

  (** Stability extends to [n] compositions and to the closure of [R]. *)

  Lemma stable_starn :
    forall n R P,
      stable R P ->
      stable (starn _ R n) P.
  Proof.
    induction n.
    intros.
    red.
    intros.
    destruct H0.
    inv H1.
    intros.
    red;intros.
    destruct H0.
    inv H1.
    generalize H;intro.
    apply IHn with R P in H.
    red in H.
    assert(P y0).
    eapply H2;eauto.
    apply (H y0 y (conj H5 H4)).
  Qed.

  (** Trivially, if we know that for all [n] the stability condition
  is true, then it is also true for the reflexive-transitive closure. *)

  Lemma stable_star :
    forall R P,
      stable R P ->
      stable (star _ R) P.
  Proof.
    red;intros.
    destruct H0.
    apply star2starn in H1.
    destruct H1 as [n H1].
    eapply stable_starn;eauto.
  Qed.

  Lemma stable_and :
    forall R1 R2 P,
      stable R1 P ->
      stable R2 P -> stable (rstAnd R1 R2) P.
  Proof.
    intros.
    red;intros.
    destruct H1.
    destruct H2.
    red in H;specialize H with x y.
    eapply H;auto.
  Qed.

  Lemma stable_impl :
    forall R1 R2 P,
      stable R2 P ->
      rstImp R1 R2 ->
      stable R1 P.
  Proof.
    intros;red;intros.
    destruct H1.
    eapply H.
    split;eauto.
  Qed.

End Stability.

(** Notion of one-step and several step reduction(s) of a 
    program under possible intereference. *)

Section Reductions.

  (** Interference: When the environment interferes, it just changes
  the state but does not alter the body of the program being
  executed. *)
  
  Definition interf R :=
    fun x y:(stmt*st) => 
      (fst x) = (fst y) /\ R (snd x)  (snd y).

  (** Transition under possible interference: Either the program
  reduces, or the environment interferes. *)

  Definition prog_red R :=
    fun x y => x ⇒ y \/ interf R x y.

  (** Finitely many reductions under interference: n steps of
  execution under interference. *)

  Definition prog_red_n (n:nat) R :=
    fun x y => starn (stmt*st) (prog_red R) n x y.

  Definition prog_red_star R :=
    fun x y => star (stmt*st) (prog_red R) x y.

End Reductions.

Infix "-( R )->" := (interf R)(at level 50).
Notation "x -( R )⋆-> y" := (star (stmt*st) (prog_red R) x y)(at level 45).
Notation "x -( R )^( n )-> y" := (starn (stmt*st) (prog_red R) n x y)(at level 45).

Lemma star_n_impl :
  forall n R R' x y,
    rstImp R R' ->
    x -(R)^(n)-> y -> x -(R')^(n)-> y.
Proof.
  induction n;intros.
  inv H0.
  constructor.
  inv H0.
  destruct H2.
  constructor 2 with y0.
  left;auto.
  eapply IHn;eauto.
  destruct H1.
  destruct x;destruct y0.
  simpl in *.
  subst.
  constructor 2 with (s1,s2).
  right;split;auto.
  eapply IHn;eauto.
Qed.

Lemma star_impl_rely :
  forall R R' x y,
    rstImp R R' -> x -(R)⋆-> y -> x -(R')⋆-> y.
Proof.
  induction 2;intros.
  constructor.
  destruct H0.
  constructor 2 with y.
  left;auto.
  assumption.
  constructor 2 with y.
  right.
  red in H0.
  red.
  destruct H0;split;eauto.
  assumption.
Qed.

Lemma rstAnd_split : 
  forall R1 R2:StR,
  forall x y, star _ (prog_red (rstAnd R1 R2)) x y -> 
              star _ (prog_red R1) x y /\ star _ (prog_red R2) x y. 
Proof.  
  induction 1.  split;auto.  destruct IHstar.  split.
  destruct H.  constructor 2 with y.  left;auto.  assumption.  
  destruct H.  destruct H3.  constructor 2 with y.  right.  
  destruct x;destruct y.  split;auto.  assumption.
  destruct H.
  econstructor 2 with y.
  left;auto.
  assumption.
  destruct H.
  destruct x;destruct y.
  constructor 2 with (s1,s2).
  destruct H3.
  right;split;auto.
  assumption.
Qed.

(** Definition the guarantee condition. It should specify the following behavior: 
     - all the program reductions [(c,x) =c=> (c',x')] must satisfy a given
       guarantee relation [G], i.e., if [(c,x) =c=> (c',x')] then [G x x'].
 *)

Definition within (R G:StR)(c:stmt)(s:st) :=
  forall y c' , star _ (prog_red R) (c,s) (c',y) ->
                forall c'' z, (c',y) ⇒ (c'',z) -> G y z.

Definition within_n(R G:StR)(c:stmt)(s:st)(n:nat) :=
  forall y c' , starn _ (prog_red R) n (c,s) (c',y) ->
                forall c'' z, (c',y) ⇒ (c'',z) -> G y z.

Lemma all_within_n :
  forall R G c s,
    (forall n, within_n R G c s n) -> within R G c s.
Proof.
  intros.
  red;intros.
  do_star2starn H0.
  apply H in H0.
  eapply H0;auto.
  apply H1.
Qed.


(** Simple syntactical notation for the notion of within. *)

Notation "<< R , G , c , x >>" := (within R G c x)(at level 0).
Notation "<< R , G , c , x [ n ]>>" := (within_n R G c x n)(at level 0).

(** Notion of Hoare validity. *)

Section HoareValidity.

  Definition HG (P:assrt)(c:stmt)(Q:assrt) :=
    forall x, 
      P x -> forall s', star _ step (c,x) (skip,s') -> Q s'.

  Definition HG_val (R G:Env)(P:assrt)(c:stmt)(Q:assrt) :=
    forall x,
      P x ->
      (forall s', star _ (prog_red R) (c,x) (skip,s') ->  Q s')
        /\ within R G c x.

  Definition HG_val' (R G:Env)(P:assrt)(c:stmt)(Q:assrt) :=
    forall x,
      P x ->
      (forall s', star _ (prog_red R) (c,x) (skip,s') ->  Q s')
        /\ (forall s', star _ (prog_red R) (c,x) (skip,s') ->  within R G c x).
  
  Definition G_val (P:assrt)(c:stmt)(G:StR)(Q:assrt) :=
    forall x, 
      P x ->
      (forall s', star _ (prog_red ID) (c,x) (skip,s') ->  Q s' /\ star _ G x s').

End HoareValidity.