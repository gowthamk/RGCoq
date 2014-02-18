Require Export generic synt_and_sos main_defs prog_reductions.

(** Monotony of [whithin] w.r.t. program reductions without
interference. This means that if a command [x] guarantees something,
then doing a program reduction, the guarantee remains intact. *)
Section WithinSimpleProperties.

  Lemma within_cstep_red_step :
    forall R G x x0 x1 x2,
      (x, x0) ⇒ (x1, x2) ->
      << R , G , x  , x0 >> ->
      << R , G , x1 , x2 >>.
  Proof.
    intros.
    unfold within.
    intros until c''.
    do_star2starn H1.
    revert n y c' c'' H1.
    induction n;intros.
    inv H1.
    eapply H0.
    constructor 2 with (c',y).
    left;auto.
    constructor.
    apply H2.
    inv H1.
    destruct y0;destruct H4;simpl in *.

    eapply H0.
    constructor 2 with (x1,x2).
    left;auto.
    do_starn2star H1.
    apply H4.
    apply H2.
    destruct H3.
    simpl in *.
    subst.
        
    eapply H0.
    constructor 2 with (s,x2).
    left;auto.
    eapply starn2star with (S n).
    apply H1.
    apply H2.
  Qed.

  (** Monotony of [whithin] w.r.t. one step of inteference. The guarantees remain intact since the interference of the environment is not accounted. Only the state of execution is possibly changed. *)

  Lemma within_R_interf_step :
    forall (R G:Env) x x0 x2,
      R x0 x2 ->
      within R G x x0 ->
      within R G x x2.
  Proof.
    intros.
    unfold within.
    intros until c''.
    do_star2starn H1.
    revert n y c' c'' H1.
    induction n;intros.
    inv H1.
    eapply H0.
    constructor 2 with (c',y).
    right;split;auto.
    do_starn2star H1.
    apply H3.
    apply H2.

    inv H1.
    destruct y0;destruct H4;simpl in *.
    eapply H0.
    constructor 2 with (x,x2).
    right;split;auto.
    do_starn2star H1.
    apply H4.
    apply H2.

    eapply H0.
    constructor 2 with (x,x2).
    right;split;auto.
    do_starn2star H1.
    apply H4.
    apply H2.
  Qed.

  (** Monotony of [whithin] w.r.t. both program reduction and interference. This lemma incoorporates the two previous lemmas. *)

  Lemma within_interf_step :
    forall R G x x0 x1 x2,
      interf R (x, x0) (x1, x2) ->
      <<R,G,x,x0>> ->
      <<R,G,x1,x2>>.
  Proof.
    intros.
    unfold within.
    intros until c''.
    do_star2starn H1.
    revert n y c' c'' H1.
    induction n;intros.
    inv H1.
    eapply H0.
    constructor 2 with (c',y).
    right;auto.
    constructor.
    apply H2.

    inv H1.
    destruct y0;destruct H4;simpl in *.
    eapply H0.
    constructor 2 with (x1,x2).
    right;auto.
    do_starn2star H1.
    apply H4.
    apply H2.

    eapply H0.
    constructor 2 with (x1,x2).
    right;auto.
    destruct H3;simpl in *;subst.
    do_starn2star H1.
    apply H3.
    apply H2.
  Qed.

  (** Monotony of [within] w.r.t. one step reduction with interference. *)

  Lemma within_prog_red :
    forall R G x x0 x1 x2,
      prog_red R (x, x0) (x1, x2) ->
      <<R,G,x,x0>> ->
      <<R,G,x1,x2>>.
  Proof.
    intros.
    destruct H;
      [eapply within_cstep_red_step |
       eapply within_interf_step];
    eauto.
  Qed.

  Lemma within_prog_red_star :
    forall R G x x0 x1 x2,
      star _ (prog_red R) (x, x0) (x1, x2) ->
      << R , G , x  , x0 >> ->
      << R , G , x1 , x2 >>.
  Proof.
    intros.
    dependent induction H.
    assumption.

    destruct y.
    eapply IHstar.
    reflexivity.
    reflexivity.
    eapply within_prog_red.
    apply H.
    assumption.
  Qed.

End WithinSimpleProperties.

(** One step of computation with intereference is in [R \/ G]. If a step of computation is carried out, it may be due to program reduction or due to the interference. This implies that the states may be related by the union of the interference and the effect of the program reduction. *)

Section WithinAndClosures.

  Lemma correct_reduction_wrt_guarantee_one_step :
    forall R G c c' s s',
      prog_red R (c,s) (c',s') -> <<R,G,c,s>> -> rstOr R G s s'.
  Proof.
    intros.
    destruct H.
    red in H0.
    assert(star _ (prog_red R) (c,s) (c,s)).
    constructor.
    pose proof H0 _ _ H1.
    apply H2 in H.
    right;auto.
    red in H.
    destruct H;simpl in *.
    left;auto.
  Qed.

  (** One step of computation without interference is in
  [G]. Obviously, if a reduction is performed then the states must be
  related by the guarantee, since it subsumes the program
  reduction. *)

  Lemma correct_reduction_step_guarantee :
    forall R G c c' s s',
      (c,s) ⇒ (c',s') ->
      <<R,G,c,s>> -> G s s'.
  Proof.
    intros.
    red in H0.
    assert(star _ (prog_red R) (c,s) (c,s)) by constructor.
    pose proof H0 _ _ H1.
    apply H2 in H.
    assumption.
  Qed.
  
  Lemma correct_reduction_wrt_guarantee_one_step_within :
    forall R G c c' s s',
      star _ (prog_red R) (c,s) (c',s') -> <<R,G,c,s>> -> <<R,G,c',s'>>.
  Proof.
    intros.
    dependent induction H.
    assumption.
    red;intros.
    destruct y;destruct H.
    pose proof correct_reduction_step_guarantee R G c s0 s s1 H H0.
    pose proof IHstar s0 c' s1 s' refl_equal refl_equal.
    eapply H5.
    2:apply H2.
    2:apply H3.
    eapply within_cstep_red_step.
    apply H.
    assumption.
    destruct H.
    simpl in *.
    subst.
    eapply H0.
    2:apply H3.
    eapply star_trans.
    constructor 2 with (s0,s1).
    right;red;auto.
    apply H1.
    assumption.
  Qed.
  
  (** Computation of a program from a state [s] to a state [s'] can be
   described by the reflexive-transitive closure of [R \/ G]. *)

  Lemma correct_reduction_wrt_rely_and_guarante :
    forall R G c c' s s',
    star _ (prog_red R) (c,s) (c',s') -> <<R,G,c,s>> -> star _ (rstOr R G) s s'.
  Proof.
    intros.
    do_star2starn H.
    revert n c c' s s' H H0.
    induction n;intros.
    inv H.
    constructor.

    inv H.
    destruct H2.
    destruct y.
    constructor 2 with s1.
    right;auto.
    eapply H0.
    constructor.
    apply H1.
    eapply IHn.
    apply H3.
    eapply within_cstep_red_step;eauto.
    
    destruct y.
    destruct H1;simpl in *;subst.
    constructor 2 with s1.
    left;auto.
    eapply IHn.
    apply H3.
    eapply within_interf_step;eauto.
    red;auto.
  Qed.
  
  (** Guarantee containment. *)

  Lemma guarantee_impl :
    forall R1 R2,
      rstImp R2 R1 ->
      forall G c s, <<R1,G,c,s>> -> <<R2,G,c,s>>.
  Proof.
    intros.
    unfold within.
    intros until c''.
    do_star2starn H1.
    intros.
    eapply H0 with c' c''.
    2:apply H2.
    clear H2 z.
    revert n y c s H0 c' c'' H1.
    induction n;intros.
    
    inv H1.
    constructor.
    
    inv H1.
    destruct y0;destruct H3.
    constructor 2 with (s0,s1).
    left;auto.
    eapply IHn.
    eapply within_cstep_red_step.
    apply H2.
    assumption.
    apply c'.
    assumption.
    destruct H2.
    simpl in *;subst.
    constructor 2 with (s0,s1).
    right.
    split;auto.
    apply IHn.
    eapply within_R_interf_step.
    apply H.
    apply H3.
    assumption.
    exact c'.
    assumption.
  Qed.
  
End WithinAndClosures.

Section WithinSkip.

  Lemma guarantee_SKIP_aux :
    forall R c1 c2 s s1 s2,
      star _ (prog_red R) (c1,s) (c2,s1) ->
      R s1 s2 ->
      star _ (prog_red R) (c1,s) (c2,s2).
  Proof.
    intros.
    dependent induction H.
    constructor 2 with (c2,s2);auto.
    right;split;auto.
    destruct H.
    destruct y.
    constructor 2 with (s0,s3);auto.
    left;auto.
    eapply IHstar;eauto.
    destruct y;destruct H;simpl in *.
    subst.
    constructor 2 with (s0,s3).
    right;split;auto.
    eapply IHstar;eauto.
  Qed.

  (** [SKIP] always respect the guarantee *)

  Lemma guarantee_SKIP :
    forall R G s,
      << R, G, skip , s >>.
  Proof.
    red.
    intros.
    dependent induction H.
    inv H0.

    destruct y0;destruct H.
    inv H.
    destruct H;simpl in *.
    symmetry in H.
    subst.
    eapply IHstar.
    reflexivity.
    reflexivity.
    apply H0.
  Qed.

End WithinSkip.
  
Section WithinIf.
  
  Lemma within_if_true :
    forall R G (b:bexp) s,
      stable R (assrtT b) ->
      Reflexive G ->
      forall ct, 
        <<R,G,ct,s>> ->  b2assrt b s ->
                 forall cf, 
                   <<R,G,ifb b then ct else cf fi,s>>.
  Proof.
    unfold within at 2.
    intros.
    dependent induction H3.
    inv H4.
    eapply H0.
    
    destruct H5.
    inv H5.
    eapply H1.
    apply H3.
    eapply H4.
    red in H5.
    simpl in H5.
    destruct H5.
    eapply IHstar.
    apply H0.
    Focus 5.
    reflexivity.
    Focus 4.
    rewrite surjective_pairing at 1.
    rewrite <- H5.
    reflexivity.
    eapply  within_R_interf_step.
    apply H6.
    apply H1.
    apply H.
    eapply H.
    split.
    apply H2.
    apply H6.
    apply H4.
  Qed.
   
  Lemma within_if_false :
    forall R G (b:bexp) s,
      stable R (assrtF b) ->
      Reflexive G ->
      forall cf, 
        <<R,G,cf,s>> -> assrtF b s ->
                 forall ct, 
                   <<R,G,ifb b then ct else cf fi,s>>.
  Proof.
    unfold within at 2.
    intros.
    dependent induction H3.
    inv H4.
    eapply H0.
    
    destruct H5.
    inv H5.
    eapply H1.
    apply H3.
    eapply H4.
    red in H5.
    simpl in H5.
    destruct H5.
    eapply IHstar.
    apply H0.
    Focus 5.
    reflexivity.
    Focus 4.
    rewrite surjective_pairing at 1.
    rewrite <- H5.
    reflexivity.
    eapply  within_R_interf_step.
    apply H6.
    apply H1.
    apply H.
    eapply H.
    split.
    apply H2.
    apply H6.
    apply H4.
  Qed.

End WithinIf.

Section WithinSequence.
 
  Lemma within_seq_fst :
    forall  R G cl s s',
      Reflexive G ->
      star _ (prog_red R) (cl,s) (skip,s') ->
      forall cr, 
        <<R,G,cr,s'>> -> <<R,G,skip;cr,s'>>.
  Proof.
    unfold within at 2.
    intros.
    dependent induction H2.
    inv H3.
    inv H4.
    apply H.

    destruct H4.
    inv H4.
    inv H9.
    inv H4.
    inv H6.
    eapply H1.
    apply H2.
    apply H3.
    destruct H4.
    simpl in *.
    eapply IHstar.
    apply H.
    Focus 4.
    reflexivity.
    Focus 3.
    rewrite surjective_pairing at 1.
    rewrite <- H4.
    reflexivity.
    Focus 3.
    apply H3.
    simpl in *.
    Focus 2.
    eapply  within_R_interf_step.
    apply H5.
    simpl.
    assumption.
    eapply star_trans.
    apply H0.
    constructor 2 with (skip,snd y0).
    red.
    right.
    red.
    simpl.
    split;auto.
    constructor.
  Qed.

  Lemma within_seq_skip :
    forall R G c s,
      Reflexive G ->
      <<R,G,skip;c,s>> -> <<R,G,c,s>>.
  Proof.
    intros.
    red;intros.
    dependent induction H1.
    eapply H0.
    constructor 2 with (c',y).
    left;auto.
    constructor.
    apply  H2.

    destruct y0;destruct H3.
    eapply H0.
    constructor 2 with (c,s).
    left;auto.
    constructor 2 with (s0,s1).
    left;auto.
    apply H1.
    apply H2.
    
    destruct H3;simpl in *.
    subst.
    eapply H0.
    constructor 2 with (s0,s).
    left;auto.
    constructor 2 with (s0,s1).
    right;split;auto.
    apply H1.
    apply H2.
  Qed.

  (** If a sequence [c1;c2] verifies a given guarante [G] then its parts must also verify [G]. *)

  Lemma within_seq_inv :
    forall R G c1 c2 s,
      Reflexive G -> 
      <<R,G,c1;c2,s>> ->
                  <<R,G,c1,s>> /\
                            forall s', star _ (prog_red R) (c1,s) (skip,s') ->
                                            <<R,G,c2,s'>>.
  Proof.
    intros.
    split;intros.
    red;intros.
    dependent induction H1.
    eapply H0.
    constructor.
    constructor.
    apply H2.
    destruct y0;destruct H3.
    assert((c1;c2,s) ⇒ (s0;c2,s1)).
    constructor;auto.
    pose proof within_cstep_red_step _ _ _ _ _ _ H4 H0.
    pose proof IHstar _ _ H H5 y c' refl_equal refl_equal _ _ H2.
    assumption.
    destruct H3.
    simpl in *.
    pose proof within_R_interf_step _ _ _ _ _ H4 H0.
    subst.
    pose proof IHstar _ _ H H5 _ _ refl_equal refl_equal _ _ H2.
    assumption.

    dependent induction H1.
    apply within_seq_skip;auto.
    destruct2 y H2.
    assert((c1;c2,s) ⇒ (s0;c2,s1)).
    constructor;auto.
    pose proof within_cstep_red_step _ _ _ _ _ _ H3 H0.
    pose proof IHstar _ _ H H4 _ refl_equal refl_equal. 
    assumption.
    destruct H2;simpl in *;subst.
    pose proof within_R_interf_step _ _ _ _ _ H3 H0.
    pose proof IHstar _ _ H H2 _ refl_equal refl_equal.
    assumption.
  Qed.

  (** The following lemma ensures how to construct a proof of the guarantee of a sequence. Basically, if [c1] ensures a guarantee and, in all possible states where it terminates is execution, if the execution of [c2] also ensures guarantee, then the sequence [c1;c2] ensures a full coverage of the guarantee. *)

  Lemma within_seq :
    forall R G c1 c2 s,
      Reflexive G -> 
      <<R,G,c1,s>> ->
               (forall n s', starn _ (prog_red R) n (c1,s) (skip,s') ->
                             <<R,G,c2,s'>>) ->
               <<R,G,c1;c2,s>>.
  Proof.
    intros.
    red;intros.
    do_star2starn H2.
    revert n s c1 c2 y c' c'' z H0 H1 H3 H2.
    induction n;intros.
    inv H2.
    inv H3.
    eapply H0.
    constructor.
    apply H5.
    apply H.

    inv H2.
    destruct2 y0 H5.
    inv H4.
    cut(<<R,G,c1',s1>>).
    intro.
    pose proof IHn s1 _ c2 y c' c'' z H5.
    eapply H8.
    intros.
    red;intros.
    eapply H1.
    constructor 2 with (c1',s1).
    left;auto.
    apply H9.
    apply H10.
    apply H11.
    apply H3.
    apply H6.
    eapply within_cstep_red_step.
    apply H7.
    assumption.
    eapply H1.
    constructor.
    eapply starn2star with n.
    apply H6.
    apply H3.
    destruct H4.
    simpl in *.
    subst.
    cut(<< R, G, c1, s1 >>).
    intro.
    pose proof IHn s1 c1 c2 y c' c'' z H4.
    eapply H7.
    intros;red;intros.
    eapply H1.
    constructor 2 with (c1,s1).
    right;split;auto.
    apply H8.
    apply H9.
    apply H10.
    apply H3.
    apply H6.
    eapply within_R_interf_step.
    apply H5.
    assumption.
  Qed.

End WithinSequence.

Section WithinWhile.

  Lemma while_middle :
    forall R G b c s,
      Reflexive G ->
      stable R ([⊤]b) ->
      b2assrt b s ->
      <<R,G,ifb b then c;while b do c end else skip fi,s>> -> <<R,G,while b do c end,s>>.
  Proof.
    intros.
    red;intros.
    dependent induction H3.
    inv H4.
    apply H.

    destruct2 y0 H5.
    inv H5.
    eapply H2.
    apply H3.
    apply H4.
    destruct H5.
    simpl in *.
    symmetry in H5.
    subst.
    eapply IHstar.
    7:apply H4.
    apply H.
    4:reflexivity.
    4:reflexivity.
    apply H0.
    eapply H0;eauto.
    red;intros.
    eapply H2.
    constructor 2 with (ifb b then c; while b do c end else skip fi, s1).
    right;split;auto.
    apply H5.
    apply H7.
  Qed.

  Lemma while_middle_false :
    forall R G b c s,
      Reflexive G ->
      stable R ([⊥]b) ->
      ~b2assrt b s ->
      <<R,G,ifb b then c;while b do c end else skip fi,s>> ->
      <<R,G,while b do c end,s>>.
  Proof.
    red;intros.
    dependent induction H3.
    inv H4.
    apply H.

    destruct2 y0 H5.
    inv H5.
    eapply H2.
    apply H3.
    apply H4.
    destruct H5.
    symmetry in H5;simpl in *;subst.
    eapply IHstar.
    apply H.
    apply H0.
    3:reflexivity.
    3:reflexivity.
    3:apply H4.
    eapply H0;eauto.
    eapply within_R_interf_step;eauto.
  Qed.

  (* Section yu. *)
  (*   Variables R G : Env. *)
  (*   Hypothesis Gr : Reflexive G. *)

  (*   Check RT_ind_gen. *)

  (*   Axiom RT_ind_gen_2 *)
  (*    : ∀X : Type, *)
  (*      ∀R : X → X → Prop, *)
  (*      ∀P : X -> Prop, *)
  (*      (∀x : X, P x) *)
  (*      → (∀x y z : X, *)
  (*         ∀n : nat, *)
  (*         R x y *)
  (*         → starn X R n y z *)
  (*           → (∀y1 : X, ∀k : nat, k ≤ n → starn X R k y1 z → P y1) → P x) *)
  (*        → (∀x y : X, star X R x y → P x). *)
      
    (* Lemma guarantee_ind_while : *)
  (*   forall R G b c s s',  *)
  (*     stable R ([⊤]b) -> *)
  (*     stable R ([⊥]b) -> *)
  (*     (forall c' s', star _ (prog_red R) (while b do c end,s) (c',s') -> <<R,G,c',s'>>) -> *)
  (*             star _ (prog_red R) (while b do c end,s) (skip,s') ->  *)
  (*             <<R,G,while b do c end,s>>. *)
  (*  Proof. *)
  (*    intros. *)
  (*    dependent induction H2;intros. *)

  (*    destruct2 y H3. *)
  (*    inv H3. *)
  (*    destruct(b2assrt_dec b s1). *)
  (*    pose proof star_if_inv_true_n _ _ _ _ _ _ _ H H2. *)
  (*    eapply IHn with (S n). *)
  (*    apply H. *)
  (*    apply H. *)
  (*    inv H3. *)
  (*    red;intros. *)

      
  Lemma while_guarantee :
    forall (R : Env)(G : Env)(P : assrt) c b,
    Reflexive G ->
    stable R ([⊤]b) ->
    stable R ([⊥]b) ->
    stable R P ->
    {{ R , G }} ⊧ {{ ([⊤]b)[∧]P }} c {{ P }} ->
    forall s,
      P s ->
      forall s', star _ (prog_red R) (while b do c end,s) (skip,s') ->
                 <<R,G,while b do c end,s>>.
  Proof.
    intros.
    pose proof hoare_while R G P c b H H0 H1 H2 H3 _ H4 _ H5.
    destruct(b2assrt_dec b s).
    eapply while_middle;auto.
    eapply within_if_true;auto.
    eapply within_seq;auto.
    assert((([⊤]b)[∧]P) s).
    split;auto.
    pose proof H3 _ H7.
    destruct H8.
    assumption.
    intros.
    red;intros.
    admit.
    eapply while_middle_false;eauto.
    eapply within_if_false;auto.
    apply guarantee_SKIP.
  Qed.

End WithinWhile.

  Lemma within_par_skip_left :
    forall R G cr s,
      Reflexive G ->
      <<R,G,cr,s>> ->
      <<R,G,(par skip with cr end),s>>.
  Proof.
    unfold within at 2.
    intros.
    dependent induction H1.
    inv H2.
    inv H3.
    eapply H0.
    constructor.
    apply H3.
    apply H.

    destruct y0;destruct H3.
    inv H3.
    inv H5.
    cut(<<R,G,c2',s1>>).
    intro.
    pose proof IHstar c2' s1.
    clear IHstar.
    eapply H6.
    assumption.
    assumption.
    reflexivity.
    reflexivity.
    apply H2.
    exact(within_cstep_red_step R G _ _ _ _ H5 H0).
    eapply H0.
    apply H1.
    apply H2.

    destruct H3.
    simpl in *.
    symmetry in H3.
    subst.
    eapply IHstar.
    assumption.
    Focus 2.
    reflexivity.
    Focus 2.
    reflexivity.
    exact(within_R_interf_step R G cr _ _ H4 H0).
    apply H2.
  Qed.

  Lemma within_par_skip_right :
    forall R G cl s,
      Reflexive G ->
      <<R,G,cl,s>> ->
      <<R,G,(par cl with skip end),s>>.
  Proof.
    unfold within at 2.
    intros.
    dependent induction H1.
    inv H2.
    eapply H0.
    constructor.
    apply H3.
    inv H3.
    apply H.

    destruct y0;destruct H3.
    inv H3.
    cut(<<R,G,c1',s1>>).
    intro.
    pose proof IHstar c1' s1.
    clear IHstar.
    eapply H6.
    assumption.
    assumption.
    reflexivity.
    reflexivity.
    apply H2.
    exact(within_cstep_red_step R G _ _ _ _ H5 H0).
    inv H5.
    eapply H0.
    apply H1.
    apply H2.

    destruct H3.
    simpl in *.
    symmetry in H3.
    subst.
    eapply IHstar.
    assumption.
    Focus 2.
    reflexivity.
    Focus 2.
    reflexivity.
    exact(within_R_interf_step R G cl _ _ H4 H0).
    apply H2.
  Qed.

 (** Within and parallel composition. *)
   
  Lemma within_par_both:
    forall R G Gr Gl cl cr s,
      Reflexive G ->
      <<(rstOr R Gr),Gl,cl,s>> ->
      <<(rstOr R Gl),Gr,cr,s>> ->
      rstImp (rstOr Gl Gr) G ->
      <<R,G,par cl with cr end,s>>.
  Proof.
    intros.
    red;intros.
    dependent induction H3.
    
    inv H4.
    apply H2.
    left.
    eapply H0.
    constructor.
    apply H5.
    apply H2.
    right.
    eapply H1.
    constructor.
    apply H5.
    apply H.
    
    
    destruct y0.
    destruct H5.
    inv H5.
    
    assert(Gl s s1).
    eapply H0.
    constructor.
    apply H7.
    assert((rstOr R Gl) s s1).
    right;auto.
    pose proof within_R_interf_step (rstOr R Gl) Gr cr _ _ H8 H1.
    assert(<<rstOr R Gr,Gl,c1',s1>>).
    pose proof within_cstep_red_step (rstOr R Gr) Gl _ _ _ _ H7.
    apply H10.
    assumption.
    pose proof IHstar c1' cr s1 H H10 H9 H2 y c' refl_equal refl_equal c'' _ H4.
    assumption.
    
    assert(Gr s s1).
    eapply H1.
    constructor.
    apply H7.
    assert((rstOr R Gr) s s1).
    right;auto.
    pose proof within_R_interf_step (rstOr R Gr) Gl cl _ _ H8 H0.
    assert(<<rstOr R Gl,Gr,c2',s1>>).
    eapply within_cstep_red_step.
    apply H7.
    assumption.
    pose proof IHstar cl c2' s1 H H9 H10 H2 _ _ refl_equal refl_equal c'' _ H4.
    assumption.
    
    apply H2.
    right.
    eapply H1.
    2:apply H4.
    pose proof star_R_star_incl _ (prog_red R) (prog_red (rstOr R Gl)).
    eapply H6.
    
    intros.
    destruct H7.
    left;auto.
    right.
    destruct H7.
    red.
    split;auto.
    left;auto.
    apply H3.
    
    destruct H5.
    simpl in *.
    symmetry in H5.
    subst.
    eapply IHstar.
    5:reflexivity.
    5:reflexivity.
    4:apply H2.
    4:apply H4.
    apply H.
    assert((rstOr R Gr) s s1).
    left;auto.
    pose proof within_R_interf_step (rstOr R Gr) Gl cl s s1 H5 H0.
    assumption.
    assert((rstOr R Gl) s s1).
    left;auto.
    pose proof within_R_interf_step (rstOr R Gl) Gr cr s s1 H5 H1.
    assumption.
  Qed.

  Lemma par_reduces_to_skip_left :
    forall Rl Rr Gl Gr cl cr x s',
      rstImp (rstOr Rl Gl) Rr ->
      rstImp (rstOr Rr Gr) Rl ->
      <<Rl,Gl,cl,x>> -> <<Rr,Gr,cr,x>> ->
      star (stmt * st) (prog_red (rstAnd Rl Rr)) 
           (par cl with cr end, x) (skip, s') ->
      (exists cr',exists x',
                   star _ (prog_red Rl) (cl,x) (skip,x') /\
                   star _ (prog_red (rstAnd Rl Rr)) (par skip with cr' end,x')
                                       (skip,s') /\
                     star _ (prog_red Rr) (cr,x) (cr',x')).
  Proof.          
    intros.
    do_star2starn H3.
    revert n cl cr x s' H1 H2 H3.
    induction n;intros.
    inv H3.
    
    inv H3.
    destruct2 y H5.
    inv H4.
    assert(<< Rl, Gl, c1', s0 >>) by (eapply within_cstep_red_step;eauto).
    assert((prog_red Rl) (cl,x) (c1',s0)).
    left;auto.
    pose proof correct_reduction_wrt_guarantee_one_step _ _ _ _ _ _ H8 H1.
    assert(Rr x s0).
    apply H.
    assumption.
    assert(<< Rr, Gr, cr, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn _ cr _ s' H5 H11 H6.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    exists x0.
    exists x1.
    split;auto.
    constructor 2 with (c1',s0).
    left;auto.
    assumption.
    split;auto.
    constructor 2 with (cr,s0).
    right;split;auto.
    assumption.

   

    assert(<< Rr, Gr, c2', s0 >>) by (eapply within_cstep_red_step;eauto).
    assert((prog_red Rr) (cr,x) (c2',s0)).
    left;auto.
    pose proof correct_reduction_wrt_guarantee_one_step _ _ _ _ _ _ H8 H2.
    assert(Rl x s0).
    apply H0.
    assumption.
    assert(<< Rl, Gl, cl, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn cl c2' _ s' H11 H5 H6.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    exists x0.
    exists x1.
    split;auto.
    constructor 2 with (cl,s0).
    right;split;auto.
    assumption.
    split;auto.
    constructor 2 with (c2',s0).
    left;auto.
    assumption.

    do_starn2star H6.
    apply star_skip_means_R_star  in H5.
    exists skip.
    exists s'.
    split;auto.
    apply star_and_l in H5.
    assumption.
    split.
    constructor 2 with (skip,s').
    left.
    constructor.
    constructor.

    apply star_and_r in H5.
    assumption.
    
    destruct H4.
    simpl in *.
    symmetry in H4.
    subst.
    destruct H5.
    assert(<< Rl, Gl, cl, s0 >>) by (eapply within_R_interf_step;eauto).
    assert(<< Rr, Gr, cr, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn _ _ _ _ H7 H8 H6.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    exists x0 x1.
    split;auto.
    constructor 2 with (cl,s0).
    right;split;auto.
    assumption.
    split;auto.
    constructor 2 with (cr,s0).
    right;split;auto.
    assumption.
  Qed.     

  Lemma par_reduces_to_skip_right :
    forall Rl Rr Gl Gr cl cr x s',
      rstImp (rstOr Rl Gl) Rr ->
      rstImp (rstOr Rr Gr) Rl ->
      <<Rl,Gl,cl,x>> -> <<Rr,Gr,cr,x>> ->
      star (stmt * st) (prog_red (rstAnd Rl Rr)) 
           (par cl with cr end, x) (skip, s') ->
      (exists cl',exists x',
                   star _ (prog_red Rr) (cr,x) (skip,x') /\
                   star _ (prog_red (rstAnd Rl Rr)) (par cl' with skip end,x')
                                       (skip,s') /\
                     star _ (prog_red Rl) (cl,x) (cl',x')).
  Proof.          
    intros.
    do_star2starn H3.
    revert n cl cr x s' H1 H2 H3.
    induction n;intros.
    inv H3.
    
    inv H3.
    destruct2 y H5.
    inv H4.
    assert(<< Rl, Gl, c1', s0 >>) by (eapply within_cstep_red_step;eauto).
    assert((prog_red Rl) (cl,x) (c1',s0)).
    left;auto.
    pose proof correct_reduction_wrt_guarantee_one_step _ _ _ _ _ _ H8 H1.
    assert(Rr x s0).
    apply H.
    assumption.
    assert(<< Rr, Gr, cr, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn _ cr _ s' H5 H11 H6.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    exists x0.
    exists x1.
    split;auto.
    constructor 2 with (cr,s0).
    right;split;auto.
    assumption.
    split;auto.
    constructor 2 with (c1',s0).
    left;auto.
    assumption.

    assert(<< Rr, Gr, c2', s0 >>) by (eapply within_cstep_red_step;eauto).
    assert((prog_red Rr) (cr,x) (c2',s0)).
    left;auto.
    pose proof correct_reduction_wrt_guarantee_one_step _ _ _ _ _ _ H8 H2.
    assert(Rl x s0).
    apply H0.
    assumption.
    assert(<< Rl, Gl, cl, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn cl c2' _ s' H11 H5 H6.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    exists x0.
    exists x1.
    split;auto.
    constructor 2 with (c2',s0).
    left;auto.
    assumption.
    split;auto.
    constructor 2 with (cl,s0).
    right;split;auto.
    assumption.

    do_starn2star H6.
    apply star_skip_means_R_star  in H5.
    exists skip.
    exists s'.
    split;auto.
    apply star_and_r in H5.
    assumption.
    split.
    constructor 2 with (skip,s').
    left.
    constructor.
    constructor.

    apply star_and_l in H5.
    assumption.
    
    destruct H4.
    simpl in *.
    symmetry in H4.
    subst.
    destruct H5.
    assert(<< Rl, Gl, cl, s0 >>) by (eapply within_R_interf_step;eauto).
    assert(<< Rr, Gr, cr, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn _ _ _ _ H7 H8 H6.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    exists x0 x1.
    split;auto.
    constructor 2 with (cr,s0).
    right;split;auto.
    assumption.
    split;auto.
    constructor 2 with (cl,s0).
    right;split;auto.
    assumption.
  Qed.                                          

  Lemma par_reduces_to_skip_and :
    forall Rl Rr Gl Gr cl cr x s',
      rstImp (rstOr Rl Gl) Rr ->
      rstImp (rstOr Rr Gr) Rl ->
      <<Rl,Gl,cl,x>> -> <<Rr,Gr,cr,x>> ->
      star (stmt * st) (prog_red (rstAnd Rl Rr)) 
           (par cl with cr end, x) (skip, s') ->
      (exists cr',exists x',
                   star _ (prog_red Rl) (cl,x) (skip,x') /\
                   star _ (prog_red (rstAnd Rl Rr)) (par skip with cr' end,x')
                                       (skip,s')) /\
      (exists cl',exists x',
                   star _ (prog_red Rr) (cr,x) (skip,x') /\
                   star _ (prog_red (rstAnd Rl Rr)) (par cl' with skip end,x')
                   (skip,s')).
  Proof.
    intros.
    do_star2starn H3.
    revert n cl cr x s' H1 H2 H3.
    induction n;intros.
    inv H3.
    
    inv H3.
    destruct2 y H5.
    inv H4.
    assert(<< Rl, Gl, c1', s0 >>) by (eapply within_cstep_red_step;eauto).
    assert((prog_red Rl) (cl,x) (c1',s0)).
    left;auto.
    pose proof correct_reduction_wrt_guarantee_one_step _ _ _ _ _ _ H8 H1.
    assert(Rr x s0).
    apply H.
    assumption.
    assert(<< Rr, Gr, cr, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn _ cr _ s' H5 H11 H6.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H13.
    split.
    exists x0.
    exists x1.
    split;auto.
    constructor 2 with (c1',s0).
    left;auto.
    assumption.

    exists x2.
    exists x3.
    split;auto.
    constructor 2 with (cr,s0).
    right;split;auto.
    assumption.

    assert(<< Rr, Gr, c2', s0 >>) by (eapply within_cstep_red_step;eauto).
    assert((prog_red Rr) (cr,x) (c2',s0)).
    left;auto.
    pose proof correct_reduction_wrt_guarantee_one_step _ _ _ _ _ _ H8 H2.
    assert(Rl x s0).
    apply H0.
    assumption.
    assert(<< Rl, Gl, cl, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn cl c2' _ s' H11 H5 H6.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H13.
    split.
    exists x0.
    exists x1.
    split;auto.
    constructor 2 with (cl,s0).
    right;split;auto.
    assumption.
    exists x2.
    exists x3.
    split;auto.
    constructor 2 with (c2',s0).
    left;auto.
    assumption.

    do_starn2star H6.
    apply star_skip_means_R_star  in H5.
    split.
    exists skip.
    exists s'.
    split;auto.
    apply star_and_l in H5.
    assumption.
    constructor 2 with (skip,s').
    left.
    constructor.
    constructor.
    exists skip.
    exists s'.
    split;auto.
    apply star_and_r in H5.
    assumption.
    constructor 2 with (skip,s').
    left.
    constructor.
    constructor.
    
    destruct H4.
    simpl in *.
    symmetry in H4.
    subst.
    destruct H5.
    assert(<< Rl, Gl, cl, s0 >>) by (eapply within_R_interf_step;eauto).
    assert(<< Rr, Gr, cr, s0 >>) by (eapply within_R_interf_step;eauto).
    pose proof IHn _ _ _ _ H7 H8 H6.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H9.
    destruct H10.
    destruct H10.
    destruct H10.
    split.
    exists x0 x1.
    split;auto.
    constructor 2 with (cl,s0).
    right;split;auto.
    assumption.
    exists x2 x3.
    split;auto.
    constructor 2 with (cr,s0).
    right;split;auto.
    assumption.
  Qed.
      




