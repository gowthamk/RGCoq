(** * Main proofs for the program reduction over programs of [cWhile]. *)
Require Export syntax sos reductions hoare.
Require Export Classes.RelationClasses. 

(** Basic properties on reductions over the [skip] command. *)

Section BasicPropertiesForSkip.
  
  Lemma starn_skip_skip :
    forall n R s c' y,
      starn (stmt * st) (prog_red R) n (skip, s) (c', y) ->
      c' = skip.
  Proof.
    induction n;intros.
    inv H.
    inv H.
    destruct2 y0 H1.
    inv H0.
    destruct H0;simpl in *.
    symmetry in H0;subst.
    apply IHn in H2.
    assumption.
  Qed.

  Lemma star_skip_skip:
    forall R s c' y,
      (skip,s) -(R)⋆-> (c',y) -> c' = skip.
  Proof.
    intros.
    do_star2starn H.
    eapply starn_skip_skip;eauto.
  Qed.

  Lemma star_skip_means_R_star :
    forall R s s',
      star _ (prog_red R) (skip,s) (skip,s') ->
      star _ R s s'.
  Proof.
    intros.
    dependent induction H.
    constructor.
    
    destruct2 y H.
    inv H.
    destruct H.
    simpl in *.
    symmetry in H;subst.
    constructor 2 with s1.
    assumption.
    apply IHstar;auto.
  Qed.

  Lemma starn_skip_inv :
    forall n x1,
      starn (stmt * st) (prog_red ID) n (skip, x1) (skip, x1).
  Proof.
    induction n;intros.
    constructor.
    constructor 2 with (skip,x1).
    right;unfold ID;split;auto.
    apply IHn.
  Qed.

  Lemma star_skip_inv :
    forall s,
      (skip,s) -(ID)⋆-> (skip,s).
  Proof.
    intros.
    constructor.
  Qed.

  Lemma reflexive_ID_eq :
    forall x y,
    star st ID x y -> x = y.
  Proof.
    induction 1;intros.
    reflexivity.
    red in H.
    subst.
    reflexivity.
  Qed.

  Lemma reflexive_assg_G_val :
    forall v a s0 s',
    star (stmt * st) (prog_red ID) (v ::= a, s0) (skip, s') ->
    s' = (s0) [v ← aeval s0 a].
  Proof.
    intros.
    dependent induction H.
    destruct2 y H.
    inv H.
    apply  star_skip_means_R_star in H0.
    apply reflexive_ID_eq in H0.
    symmetry;auto.
    destruct H.
    simpl in *.
    subst.
    apply IHstar.
    red in H1;subst.
    reflexivity.
    reflexivity.
  Qed.

  Lemma skip_false :
    forall x v a s',
      star (stmt * st) cstep (skip, (x) [v ← aeval x a]) (skip, s') ->
      s' = (x) [v ← aeval x a].
  Proof.
    intros.
    inv H.
    inv H0.
  Qed.

  Lemma star_and_l :
    forall Rl Rr s0 s',
      star st (rstAnd Rl Rr) s0 s' ->
      star (stmt * st) (prog_red Rl) (skip, s0) (skip, s').
  Proof.
    intros *.
    induction 1;auto.
    destruct H.
    constructor 2 with (skip,y).
    right;split;auto.
    assumption.
  Qed.
  
  Lemma star_and_r :
    forall Rl Rr s0 s',
      star st (rstAnd Rl Rr) s0 s' ->
      star (stmt * st) (prog_red Rr) (skip, s0) (skip, s').
  Proof.
    intros *.
    induction 1;auto.
    destruct H.
    constructor 2 with (skip,y).
    right;split;auto.
    assumption.
  Qed.

End BasicPropertiesForSkip.


(** Inversion lemmas for reductions over [ifb] conditionals. *)

Section IfInvLemmas.

  Lemma star_if_inv_true :
    forall R b c1 c2 s1 s2,
      stable R ([⊤]b) ->
      star _ (prog_red R) (ifb b then c1 else c2 fi,s1) (skip,s2) ->
      b2assrt b s1 ->
      star _ (prog_red R) (c1,s1) (skip,s2).
  Proof.
    intros.
    dependent induction H0.

    destruct2 y H2.
    inv H2.
    destruct H2.
    simpl in *.
    symmetry in H2.
    subst.
    constructor 2 with (c1,s0).
    right;split;auto.
    eapply IHstar;eauto.
    eapply H;eauto.
  Qed.

  Lemma star_if_inv_true_n :
    forall n R b c1 c2 s1 s2,
      stable R ([⊤]b) ->
      starn _ (prog_red R) n (ifb b then c1 else c2 fi,s1) (skip,s2) ->
      b2assrt b s1 ->
      exists m, 
      starn _ (prog_red R) m (c1,s1) (skip,s2) /\ m <= n.
  Proof.
    induction n;intros.
    inv H0.

    inv H0.
    destruct2 y H3.
    inv H2.
    exists n;split;auto with arith.

    destruct H2.
    simpl in *.
    symmetry in H2.
    subst.
    assert(b2assrt b s0) by (eapply H;split;eauto).
    pose proof IHn _ _ _ _ _ _ H H4 H2.
    destruct H5.
    destruct H5.
    exists (S x).
    split;auto with arith.
    constructor 2 with (c1,s0);auto.
    right;split;auto.
  Qed.

  Lemma star_if_inv_false :
    forall R b c1 c2 s1 s2,
      stable R ([⊥]b) ->
      star _ (prog_red R) (ifb b then c1 else c2 fi,s1) (skip,s2) ->
      ~b2assrt b s1 ->
      star _ (prog_red R) (c2,s1) (skip,s2).
  Proof.
    intros.
    dependent induction H0.

    destruct2 y H2.
    inv H2.
    destruct H2.
    simpl in *.
    symmetry in H2.
    subst.
    constructor 2 with (c2,s0).
    right;split;auto.
    eapply IHstar;eauto.
    eapply H;eauto.
  Qed.

End  IfInvLemmas.

(** Lemmas for reductions over atomic execution of commands. *)

Section AtomicReduction.

  Lemma red_atomic_imp_skip :
    forall b c c' s s',
      (wait b do c end,s) ⇒ (c',s') ->
      c' = skip.
  Proof.
    intros.
    dependent induction H.
    reflexivity.
  Qed.

  Lemma star_id_implies_star_cstep :
    forall x s y,
      star _ (prog_red ID) (x,s) (skip,y) ->
      star _ (cstep) (x,s) (skip,y).
  Proof.
    induction 1.
    constructor.

    destruct H.
    constructor 2 with y0;auto.
    unfold interf in H.
    destruct H.
    rewrite (surjective_pairing x0) in H |- *.
    simpl in H.
    rewrite H.
    red in H1.
    rewrite H1.
    rewrite <- surjective_pairing.
    assumption.
  Qed.

  Lemma star_id_implies_star_cstep_gen :
    forall x s x' y,
      star _ (prog_red ID) (x,s) (x',y) ->
      star _ (cstep) (x,s) (x',y).
  Proof.
    induction 1.
    constructor.

    destruct H.
    constructor 2 with y0;auto.
    unfold interf in H.
    destruct H.
    rewrite (surjective_pairing x0) in H |- *.
    simpl in H.
    rewrite H.
    red in H1.
    rewrite H1.
    rewrite <- surjective_pairing.
    assumption.
  Qed.

  Lemma star_id_implies_star_cstep_inv :
    forall x s y,
      star _ (cstep) (x,s) (skip,y) ->
      star _ (prog_red ID) (x,s) (skip,y).
  Proof.
    induction 1.
    constructor.

    constructor 2 with y0;auto.
    left;auto.
  Qed.

  Lemma red_atomic_implies_cstep :
    forall b c c' s s',
      (wait b do c end,s) ⇒ (c',s') ->  star _ (prog_red ID) (c,s) (c',s').
  Proof.
    intros.
    dependent induction H.
    eapply star_id_implies_star_cstep_inv.
    assumption.
  Qed.
  
  Lemma star_does_atomic :
    forall R b x y s,
      b2assrt b s ->
      star _ (prog_red ID) (x,s) (skip,y) ->
      star _ (prog_red R) (wait b do x end,s) (skip,y).
  Proof.
    intros.
    dependent induction H0.
    constructor 2 with (skip,y);auto.
    left.
    constructor;auto.
    
    destruct2 y0 H1.
    econstructor 2 with (skip,y).
    left.
    econstructor.
    assumption.
    constructor 2 with (s0,s1).
    assumption.
    apply star_id_implies_star_cstep.
    assumption.
    auto.
    destruct H1.
    simpl in *;subst.
    red in H2.
    subst.
    apply IHstar;auto.
  Qed.
  
  Lemma star_does_atomic_inv :
    forall R b x y s,
      star _ (prog_red R) (wait b do x end,s) (skip,y) ->
      exists s' s'', 
        star _ R s s' /\ 
        star _ (prog_red ID) (x,s') (skip,s'') /\
        star _ R s'' y.
  Proof.
    intros.
    dependent induction H.
    
    destruct2 y0 H.
    inv H.
    apply star_id_implies_star_cstep_inv in H7.
    exists s s1.
    split;auto.
    split;auto.
    apply star_skip_means_R_star in H0.
    assumption.

    destruct H.
    simpl in *.
    symmetry in H.
    subst.
    pose proof IHstar b _ _ _ refl_equal refl_equal.
    destruct H.
    destruct H.
    destruct H.
    destruct H2.
    exists x0 x1.
    split;auto.
    constructor 2 with s1.
    assumption.
    assumption.
  Qed.

  Lemma atomic_implies_skip :
    forall R b c x c' y,
      star (stmt * st) (prog_red R) (wait b do c end, x) (c', y) ->
      (c' = wait b do c end) \/ c' = skip.
  Proof.
    intros.
    dependent induction H.
    left;auto.
    
    destruct2 y0 H.
    inv H.
    do_star2starn H0.
    apply starn_skip_skip in H0.
    right;auto.

    destruct H;simpl in *.
    symmetry in H.
    subst.
    eapply IHstar.
    reflexivity.
    reflexivity.
  Qed.

  Lemma atomic_atomic_implies_Rstar :
    forall R b c x y,
      star (stmt * st) (prog_red R) (wait b do c end, x) (wait b do c end, y) ->
      star _ R x y.
  Proof.
    intros.
    dependent induction H.
    constructor.

    destruct2 y0 H.
    inv H.
    do_star2starn H0.
    apply starn_skip_skip in H0.
    discriminate.
    destruct H.
    simpl in *.
    symmetry in H.
    subst.
    constructor 2 with s0.
    assumption.
    eapply IHstar;eauto.
  Qed.
    
End AtomicReduction.

(** Inversion lemmas for the sequencial composition of programs. *)

Section ProgramReductionSequence.

  Variables R G : Env.

  Lemma sequence_compose :
    forall cl s s',
      star _ (prog_red R) (cl,s) (skip,s') ->
      forall cr s'',
        star _ (prog_red R) (cr,s') (skip,s'') ->
        star _ (prog_red R) (cl;cr,s) (skip,s'').
  Proof.
    intros.
    dependent induction H.
    constructor 2 with (cr,s').
    left;auto.
    assumption.
    destruct2 y H.
    constructor 2 with (s0;cr,s1).
    left.
    constructor;auto.
    eapply IHstar;eauto.
    destruct H.
    simpl in *.
    subst.
    constructor 2 with (s0;cr,s1).
    right;split;auto.
    eapply IHstar;eauto.
  Qed.

  Lemma sequence_reduces_in_parts_3: 
   forall R cl cr s t,
      star _ (prog_red R) (cl;cr,s) (skip,t) ->
      exists s',
        star _ (prog_red R) (cl,s) (skip,s') /\
             star _ (prog_red R) (cr,s') (skip,t).
  Proof.
    intros.
    dependent induction H.
    
    destruct2 y H.
    inv H.
    pose proof IHstar c1' cr s1 t refl_equal refl_equal.
    destruct H1 as [s' [H4 H5]].
    exists s'.
    split;auto.
    constructor 2 with (c1',s1).
    left;auto.
    apply H4.

    exists s1.
    split;auto.

    destruct H.
    simpl in *.
    symmetry in H.
    subst.
    pose proof IHstar cl cr s1 t refl_equal refl_equal.
    destruct H as [s' [H3 H4]].
    exists s'.
    split.
    constructor 2 with (cl,s1).
    right.
    split;auto.
    apply H3.
    apply H4.
  Qed.

  Lemma sequence_reduces_in_parts_sequential_n: 
    forall n cl cr s t,
      starn _ (prog_red R) n (cl;cr,s) (skip,t) ->
      exists s',
        star _ (prog_red R) (cl,s) (skip,s') /\
             exists n1, starn _ (prog_red R) n1 (cr,s') (skip,t) /\ n1 <= n.
  Proof.
    induction n;intros.
    inv H.

    inv H.
    destruct2 y H1.
    inv H0.
    pose proof IHn _ _ _ _ H2.
    destruct H1.
    destruct H1.
    destruct H4.
    exists x.
    split.
    constructor 2 with (c1',s1).
    left;auto.
    assumption.
    exists x0.
    destruct H4.
    split;auto with arith.
    exists s1.
    split;auto.
    exists n.
    split;auto with arith.

    destruct H0.
    simpl in *.
    symmetry in H0.
    subst.
    pose proof IHn _ _ _ _ H2.
    destruct H0.
    destruct H0.
    destruct H3.
    destruct H3.
    exists x.
    split.
    constructor 2 with (cl,s1).
    right;split;auto.
    assumption.
    exists x0.
    split;auto with arith.
  Qed.

  Lemma sequence_reduces_skip :
    forall R b c c' x s',
      star (stmt * st) (prog_red R) (skip; while b do c end, x) (c', s') ->
      (c' = (skip;while b do c end))  \/ 
      star _ (prog_red R) (while b do c end,x) (c',s').
  Proof.
    intros.
    dependent induction H.
    left;auto.

    destruct2 y H.
    inv H.
    inv H2.
    right;auto.
    destruct H.
    simpl in *.
    symmetry in H.
    subst.
    pose proof IHstar b c c' s0 s' refl_equal refl_equal.
    destruct H;auto.
    right.
    constructor 2 with (while b do c end,s0).
    right;split;auto.
    assumption.
  Qed.

End ProgramReductionSequence.

Section CommandReasoningLemmas.

  Lemma rel_from_skipn :
    forall n R s s',
      starn _ (prog_red R) n (skip,s) (skip,s') ->
      starn _ R n s s'.
  Proof.
    induction n;intros.
    inv H.
    constructor.

    inv H.
    destruct2 y H1.
    inv H0.
    destruct H0;simpl in *;subst.
    constructor 2 with s1;auto.
  Qed.

  Lemma while_true_cond :
    forall R b c s s',
      b2assrt b s ->
      stable R ([⊤]b) -> 
      star _ (prog_red R) (while b do c end,s) (skip,s') ->
      star _ (prog_red R) (c;while b do c end,s) (skip,s').
  Proof.
    intros.
    dependent induction H1.
    destruct y;destruct H2.
    simpl in *.
    inv H2.
    pose proof star_if_inv_true R b (c; while b do c end) skip s1 s' H0 H1 H.
    assumption.
    destruct H2.
    simpl in *.
    symmetry in H2;subst.
    constructor 2 with (c; while b do c end, s1).
    right.
    red.
    auto.
    apply IHstar;auto.
    eapply H0;eauto.
  Qed.

  Lemma while_true_cond_step :
    forall R b c s,
      b2assrt b s ->
      stable R ([⊤]b) -> 
      star _ (prog_red R) (while b do c end,s) (c;while b do c end,s).
  Proof.
    intros.
    constructor 2 with ((ifb b then c;while b do c end else skip fi),s).
    left.
    constructor.
    constructor 2 with (c;while b do c end,s).
    left.
    constructor;auto.
    constructor.
  Qed.
  
  Lemma goes_by_star_same_command :
    forall R c s s',
      star _ R s s' ->
      star _ (prog_red R) (c,s) (c,s').
  Proof.
    intros.
    dependent induction H.
    constructor.
    econstructor 2 with (c,y).
    right.
    red.
    split.
    reflexivity.
    simpl.
    assumption.
    assumption.
  Qed.

  Lemma goes_by_star_same_rel :
    forall R c c' s s',
      star _ (prog_red R) (c,s) (c',s') ->
      forall s'', star _ R s' s'' ->
      star _ (prog_red R) (c,s) (c',s'').
  Proof.
    intros.
    dependent induction H0.
    assumption.
    apply IHstar.
    eapply star_trans.
    apply H.
    econstructor 2 with (c',y).
    right.
    red.
    split.
    reflexivity.
    simpl.
    assumption.
    constructor.
  Qed.

  Lemma while_true_cond_weak :
    forall R b c s s',
      b2assrt b s ->
      stable R ([⊤]b) -> 
      star _ (prog_red R) (while b do c end,s) (skip,s') ->
      exists s'',
        star _ R s s'' /\ 
        star _ (prog_red R) (ifb b then c;while b do c end else skip fi ,s'') (skip,s').
  Proof.
    intros.
    dependent induction H1.
    destruct y;destruct H2.
    simpl in *.
    inv H2.
    exists s1.
    split;auto.

    destruct H2.
    simpl in *.
    symmetry in H2.
    subst.
    assert(b2assrt b s1).
    eapply H0;eauto.
    pose proof IHstar s' s1 c b H2 H0 refl_equal refl_equal.
    destruct H4.
    destruct H4.
    exists x.
    split.
    constructor 2 with s1.
    assumption.
    assumption.
    assumption.
  Qed.

  Lemma while_false_cond :
    forall R b c s s',
      ~b2assrt b s ->
      stable R ([⊤]b) -> 
      stable R ([⊥]b) -> 
      star _ (prog_red R) (while b do c end,s) (skip,s') ->
      star _ (prog_red R) (skip,s) (skip,s').
  Proof.
    intros.
    dependent induction H2.
    destruct y;destruct H3.
    simpl in *.
    inv H3.
    pose proof star_if_inv_false R b (c; while b do c end) skip s1 s' H1 H2 H.
    assumption.
    destruct H3.
    simpl in *.
    symmetry in H3;subst.
    constructor 2 with (skip, s1).
    right.
    red.
    auto.
    eapply IHstar;eauto.
    intro.
    eapply H1.
    split;eauto.
    assumption.
  Qed.

  Lemma while_split :
    forall R b c s s',
      star _ (prog_red R) (while b do c end,s) (skip,s') ->
      exists s'',exists c',
        star _ (prog_red R) (while b do c end,s) (c',s'') /\
        star _ (prog_red R) (c',s'') (skip,s').
  Proof.
    intros.
    dependent induction H.
    destruct y;destruct H.
    inv H.
    exists s1 (ifb b then c; while b do c end else skip fi).
    split;auto.
    econstructor.
    left.
    apply H.
    constructor.
    destruct H.
    simpl in *.
    symmetry in H.
    subst.
    pose proof IHstar b c s1 s' refl_equal refl_equal.
    destruct H as [s'' [c'' [H2 H3]]].
    exists s'' c''.
    split;auto.
    econstructor 2 with (while b do c end,s1).
    right.
    red.
    simpl.
    split;auto.
    assumption.
  Qed.

  Lemma hoare_while_aux :
    forall R (G:StR) (P:assrt) c b,
      (forall x, G x x) ->
      stable R ([⊤]b) ->
      stable R ([⊥]b) ->
      stable R P ->
      HG_val R G (assrtT b[∧]P) c P ->
      forall s, P s ->
      (forall s', star _ (prog_red R) (while b do c end, s) (skip,s') ->
             forall p p',
             star _ (prog_red R) p p' ->
             fst p  = (while b do c end) ->
             fst p' = skip -> 
             P (snd p) ->  (([⊥]b)[∧]P) (snd p')).
  Proof.
    intros until p.
    intros p' Hr.
    pattern p, p'.
    eapply RT_ind_gen;eauto.
    
    intros.
    rewrite H6 in H7;discriminate.

    intros.
    destruct x as (x,m1).
    destruct y as (y,m2).
    destruct z as (z,m3).
    simpl in *.
    subst.
    destruct H6.    
    inv H6.
    inv H7.
    destruct H9.
    inv H9.
    pose proof rel_from_skipn _ _ _ _ H10.
    pose proof stable_star _ _ H2.
    pose proof stable_star _ _ H1.
    split.
    eapply H14;split;eauto.
    eapply starn2star with n0;auto.
    eapply H13.
    split;eauto.
    eapply starn2star with n0;auto.
    cut(exists t, star _ (prog_red R) (c,m2) (skip,t) /\
                       exists m, starn _ (prog_red R) m (while b do c end,t) (skip,m3)
                                       /\ m <= (S n0)).
    intros.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    assert((([⊤]b)[∧]P) m2).
    split;auto.
    pose proof H3 _ H15.
    destruct H16.
    eapply H8.
    apply H14.
    apply H13.
    auto.
    auto.
    simpl.
    apply H16.
    assumption.

    pose proof sequence_reduces_in_parts_sequential_n _ _ _ _ _ _ H10.
    destruct H12.
    exists x.
    destruct H12.
    split;auto.
    destruct H13.
    exists x0.
    destruct H13;auto.

    destruct2 y H9.
    simpl in *.
    symmetry in H9.
    subst.
    destruct(b2assrt_dec b s1).
    pose proof H10.
    do_starn2star H10.
    
    pose proof star_if_inv_true_n _ _ _ _ _ _ _ H0 H9 b0.
    destruct H10.
    destruct H10.
    cut(exists t, star _ (prog_red R) (c,s1) (skip,t) /\
                   exists m, starn _ (prog_red R) m (while b do c end,t) (skip,m3)
                                       /\ m <= (S n0)).
    intro.
    destruct H15.
    destruct H15.
    destruct H16.
    destruct H16.
    eapply H8.
    apply H17.
    apply H16.
    reflexivity.
    reflexivity.
    simpl.
    assert(P s1).
    eapply H2;eauto.
    assert((([⊤]b)[∧]P) s1).
    split;auto.
    pose proof H3 _ H19.
    destruct H20.
    apply H20.
    apply H15.


    pose proof sequence_reduces_in_parts_sequential_n _ _ _ _ _ _ H10.
    destruct H15.
    destruct H15.
    destruct H16.
    destruct H16.
    exists x0.
    split;auto.
    exists x1.
    split;auto with arith.
    omega.
    
    pose proof H10.
    do_starn2star H9.
    pose proof star_if_inv_false _ _ _ _ _ _ H1 H13 n.
    do_star2starn H9.
    pose proof rel_from_skipn _ _ _ _ H9.
    pose proof stable_star _ _ H2.
    pose proof stable_star _ _ H1.
    split.
    eapply H16;split;eauto.
    eapply starn2star with n1;auto.
    eapply H15.
    split;eauto.
    eapply starn2star with (S n1);auto.
    constructor 2 with s1.
    assumption.
    assumption.

    destruct H6.
    simpl in *.
    symmetry in H6.
    subst.
    assert(n<=n) by auto with arith.
    pose proof H8 _ _ H6 H7 refl_equal refl_equal.
    apply H10.
    simpl.
    eapply H2.
    split;eauto.
  Qed.
    
  Lemma hoare_while :
    forall R (G:StR) (P:assrt) c b,
      (forall x, G x x) ->
      stable R ([⊤]b) ->
      stable R ([⊥]b) ->
      stable R P ->
      HG_val R G (assrtT b[∧]P) c P ->
      forall s, P s ->
      (forall s', star _ (prog_red R) (while b do c end, s) (skip,s') ->  
                  (assrtF b[∧]P) s').
  Proof.
    intros.
    inv H5.
    destruct2 y H6.
    inv H6.
    pose proof hoare_while_aux R G P c b H H0 H1 H2 H3 _ H4 _ H5.
    specialize H8 with (while b do c end,s1) (skip,s').
    simpl in H8.
    eapply H8;auto.

    destruct H6.
    simpl in *.
    symmetry in H6.
    subst.
    pose proof hoare_while_aux R G P c b H H0 H1 H2 H3 _ H4 _ H5.
    specialize H6 with (while b do c end,s1) (skip,s').
    simpl in H6.
    apply H6;auto.
    eapply H2;split;eauto.
  Qed.

  (* (** The soundness lemma for the while loop construct for the sequential part of CWhile. *) *)

  Lemma hoare_while_aux_ID :
    forall (G:StR) (P:assrt) c b,
      G_val (assrtT b[∧]P) c G P ->
      forall s, P s ->
      (forall s', star _ (prog_red ID) (while b do c end, s) (skip,s') ->
             forall p p',
             star _ (prog_red ID) p p' ->
             fst p  = (while b do c end) ->
             fst p' = skip ->
             P (snd p) ->  (([⊥]b)[∧]P) (snd p') /\ star st G (snd p) (snd p')).
  Proof.
    intros until p.
    intros p' Hr.
    pattern p, p'.
    eapply RT_ind_gen;eauto.
    
    intros.
    rewrite H3 in H2;discriminate.

    intros.
    destruct x as (x,m1).
    destruct y as (y,m2).
    destruct z as (z,m3).
    simpl in *.
    subst.
    destruct H2.
    inv H2.
    inv H3.
    destruct H5.
    inv H5.
    assert(m2=m3).
    do_starn2star H6.
    apply star_skip_means_R_star in H8.
    apply reflexive_ID_eq in H8.
    assumption.

    rewrite <- H8.
    split;auto.
    split;auto.


    cut(exists t, star _ (prog_red ID) (c,m2) (skip,t) /\
                       exists m, starn _ (prog_red ID) m (while b do c end,t) (skip,m3)
                                       /\ m <= (S n0)).
    intros.
    destruct H8.
    destruct H8.
    destruct H9.
    destruct H9.
    assert((([⊤]b)[∧]P) m2).
    split;auto.
    pose proof H _ H11 _ H8.
    destruct H12.
    split.
    eapply H4.
    apply H10.
    apply H9.
    auto.
    auto.
    simpl.
    apply H12.
    pose proof H4 (while b do c end, x) _ H10 H9 refl_equal refl_equal H12.
    destruct H15.
    simpl in *.
    eapply star_trans;eauto.
   
    pose proof sequence_reduces_in_parts_sequential_n _ _ _ _ _ _ H6.
    destruct H8.
    exists x.
    destruct H8.
    split;auto.
    destruct H9.
    exists x0.
    destruct H9;auto.

    destruct2 y H5.
    simpl in *.
    symmetry in H5.
    subst.
    destruct(b2assrt_dec b s1).
    pose proof H6.
    do_starn2star H6.

    assert(stable ID ([⊤]b)).
    red.
    intros.
    destruct H6.
    red in H10.
    subst;auto.

    pose proof star_if_inv_true_n _ ID _ _ _ _ _ H6 H5 b0.
    destruct H10.
    destruct H10.
    cut(exists t, star _ (prog_red ID) (c,s1) (skip,t) /\
                   exists m, starn _ (prog_red ID) m (while b do c end,t) (skip,m3)
                                       /\ m <= (S n0)).
    intro.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    split.
    eapply H4.
    apply H14.
    apply H13.
    reflexivity.
    reflexivity.
    simpl.
    assert(P s1).
    red in H8;subst;auto.
    assert((([⊤]b)[∧]P) s1).
    split;auto.
    pose proof H _ H16 _ H12.
    destruct H17;auto.
    red in H.
    red in H8.
    rewrite H8 in H7.
    assert((([⊤]b)[∧]P) s1).
    split;auto.
    pose proof H _ H15 _ H12.
    destruct H16.

    pose proof H4 (while b do c end, x0) _ H14 H13 refl_equal refl_equal H16.
    destruct H18.
    simpl in H19.
    rewrite H8.
    eapply star_trans;eauto.

    pose proof sequence_reduces_in_parts_sequential_n _ _ _ _ _ _ H10.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    exists x0.
    split;auto.
    exists x1.
    split;auto with arith.
    omega.
    
    pose proof H6.
    do_starn2star H5.
    assert(stable ID ([⊥]b)).
    red.
    intros.
    destruct H5.
    red in H10;auto.
    subst;auto.
    pose proof star_if_inv_false _ _ _ _ _ _ H5 H9 n.
    do_star2starn H10.
    pose proof rel_from_skipn _ _ _ _ H10.
    assert(s1=m3).
    do_starn2star H11.
    apply reflexive_ID_eq in H12.
    assumption.
    split.
    split.
    rewrite <- H12;auto.
    rewrite <- H12.
    red in H8.
    rewrite H8 in H7;auto.
    rewrite <- H12.
    red in H8.
    rewrite H8.
    constructor.

    destruct H2.
    simpl in *.
    symmetry in H2.
    subst.
    assert(n<=n) by auto with arith.
    pose proof H4 _ _ H2 H3 refl_equal refl_equal.
    split.
    apply H6.
    simpl.
    red in H5.
    subst;auto.
    simpl in H6.
    red in H5.
    subst.
    apply H6 in H7.
    destruct H7;auto.
  Qed.

  Lemma hoare_while_ID :
    forall (G:StR) (P:assrt) c b,
      G_val (assrtT b[∧]P) c G P ->
      forall s, P s ->
      (forall s', star _ (prog_red ID) (while b do c end, s) (skip,s') ->
                  (assrtF b[∧]P) s' /\ star _ G s s').
  Proof.
    intros.
    inv H1.
    destruct2 y H2.
    inv H2.
    pose proof hoare_while_aux_ID G P c b H _ H0 _ H1.
    specialize H4 with (while b do c end,s1) (skip,s').
    simpl in H4.
    eapply H4;auto.

    destruct H2.
    simpl in *.
    symmetry in H2.
    subst.
    pose proof hoare_while_aux_ID G P c b H _ H0 _ H1.
    specialize H2 with (while b do c end,s1) (skip,s').
    simpl in H2.
    red in H4.
    subst.
    apply H2;auto.
  Qed.

  (** Basic [skip||skip] reduction *)
  
  Lemma par_skip_l_red_skip :
    forall n R cl s s',
      starn _ (prog_red R) n (cl,s) (skip,s') ->
      star _  (prog_red R) (par cl with skip end,s) (skip,s').
  Proof.
    induction n;intros.
    inv H.
    constructor 2 with (skip,s');auto.
    left.
    constructor.

    inv H.
    destruct y;destruct H1.
    constructor 2 with (par s0 with skip end,s1).
    left.
    constructor.
    assumption.
    eapply IHn.
    assumption.
    
    destruct H0;simpl in *;subst.
    constructor 2 with (par s0 with skip end, s1).
    right;split;auto.
    eapply IHn;auto.
  Qed.

  Lemma par_skip_r_red_skip :
    forall n R cr s s',
      starn _ (prog_red R) n (cr,s) (skip,s') ->
      star _  (prog_red R) (par skip with cr end,s) (skip,s').
  Proof.
    induction n;intros.
    inv H.
    constructor 2 with (skip,s');auto.
    left.
    constructor.

    inv H.
    destruct y;destruct H1.
    constructor 2 with (par skip with s0 end,s1).
    left.
    constructor.
    assumption.
    eapply IHn.
    assumption.
    
    destruct H0;simpl in *;subst.
    constructor 2 with (par skip with s0 end, s1).
    right;split;auto.
    eapply IHn;auto.
  Qed.

    Lemma par_skip_skip_red_skip :
    forall n R cl cl' cr s s',
      starn _ (prog_red R) n (cl,s) (cl',s') ->
      star _  (prog_red R) (par cl with cr end,s) (par cl' with cr end,s').
  Proof.
    induction n;intros.
    inv H.
    constructor.

    inv H.
    destruct y;destruct H1.
    constructor 2 with (par s0 with cr end, s1).
    left.
    constructor;auto.
    eapply IHn;auto.

    destruct H0.
    constructor 2 with (par cl with cr end,s1).
    right;split;auto.
    simpl in *;subst.
    eapply IHn;eauto.
  Qed.

  Lemma par_decompose_left :
    forall n R cl cl' s s',
      starn _ (prog_red R) n (cl,s) (cl',s') ->
      forall s'' cr cr', star _ (prog_red R) (par cl' with cr end,s') 
                                             (par cl' with cr' end,s'') ->
      star _  (prog_red R) (par cl with cr end,s) (par cl' with cr' end,s'').
  Proof.
    induction n;intros.
    inv H.
    
    inv H.
    destruct y;destruct H2;simpl in *.
    constructor 2 with (par s0 with cr end,s1).
    left.
    constructor.
    assumption.
    eapply IHn;eauto.

    destruct H1;simpl in *;subst.
    constructor 2 with (par s0 with cr end,s1).
    right;split;auto.
    eapply IHn;eauto.
  Qed.

  Lemma par_decompose_right :
    forall n R cr cr' s s',
      starn _ (prog_red R) n (cr,s) (cr',s') ->
      forall s'' cl cl', star _ (prog_red R) (par cl with cr' end,s') 
                                             (par cl' with cr' end,s'') ->
      star _  (prog_red R) (par cl with cr end,s) (par cl' with cr' end,s'').
  Proof.
    induction n;intros.
    inv H.
    
    inv H.
    destruct y;destruct H2;simpl in *.
    constructor 2 with (par cl with s0 end,s1).
    left.
    constructor.
    assumption.
    eapply IHn;eauto.

    destruct H1;simpl in *;subst.
    constructor 2 with (par cl with s0 end,s1).
    right;split;auto.
    eapply IHn;eauto.
  Qed.

End CommandReasoningLemmas.

 (** Naive tactic to destroy and name the parts of the term representing the
    conclusion of [HG_val] *)

Ltac simpl_HG K H :=
  let H1 := fresh "H" in
    pose proof (H _ K) as H1;
  let H2 := fresh "H" in 
    let H3 := fresh "H" in 
      destruct H1 as [H2 H3];
  let n := fresh "n" in
    let s := fresh "s" in 
      let H4 := fresh "H" in
        let H5 := fresh "H" in 
          destruct H2 as [n [s [H4 H5]]].
