Require Export generic synt_and_sos main_defs prog_reductions guarantees.

Lemma stengthening :
  forall R R' G G' P P' Q Q' c,
    assrtImp P P' ->
    assrtImp Q' Q ->
    rstImp R R' ->
    rstImp G' G ->
    {{R',G'}} ⊧ {{P'}} c {{Q'}} ->
    {{R,G}} ⊧ {{P}} c {{Q}}.
Proof.
  intros *.
  intros Hp Hq Hr Hg.
  intro.
  red.
  intros .
  split.
  intros.
  dependent induction H1.
  apply Hp in H0.
  pose proof H _ H0.
  destruct H1.
  apply Hq.
  apply H1.
  constructor.
  apply Hp in H0.
  apply H in H0.
  destruct H0.
  apply Hq.
  apply H0.
  destruct H2.

  constructor 2 with y.
  left;auto.
  
  eapply star_impl_rely.
  apply Hr.
  assumption.
  destruct H2.
  simpl in *.
  subst.
  destruct y;simpl in *.
  constructor 2 with (s,s0).
  right;split;auto.
  eapply star_impl_rely.
  apply Hr.
  assumption.

  red;intros.
  apply Hg.
  apply Hp in H0.
  pose proof H _ H0.
  destruct H3.
  eapply H4.
  eapply star_impl_rely.
  apply Hr.
  apply H1.
  apply H2.
Qed.

Lemma triple_correct :
  forall P c G Q,
    triple G P c Q -> G_val P c G Q.
Proof.
  induction 1;intros.
  red;intros.
  apply star_skip_means_R_star in H0.
  apply reflexive_ID_eq in H0.
  subst.
  split;auto.

  red;intros.
  inv H1.
  destruct2 y H2.
  inv H2.
  apply star_skip_means_R_star in H3.
  apply reflexive_ID_eq in H3.
  subst.
  split;eauto.
  
  destruct H2.
  simpl in *.
  subst.
  red in H4.
  subst.
  apply reflexive_assg_G_val in H3.
  subst.
  split;eauto.

  assert(stable ID ([⊤]b)).
  red.
  intros.
  destruct H1.
  red in H2.
  subst.
  assumption.

  red;intros.
  destruct(b2assrt_dec b x).
  assert((([⊤]b)[∧]P) x).
  split;auto.
  pose proof IHtriple1 _ H4.
  apply H5.
  
  pose proof star_if_inv_true ID b c1 c2 x s' H1 H3 b0.
  assumption.

  assert(stable ID ([⊥]b)).
  red.
  intros.
  destruct H4.
  red in H5.
  subst.
  assumption.

  assert((([⊥]b)[∧]P) x) by (split;auto).
  pose proof IHtriple2 _ H5.
  apply H6.
  pose proof star_if_inv_false ID b c1 c2 x s' H4 H3 n.
  assumption.

  red;intros.
  pose proof IHtriple1 _ H1.
  apply sequence_reduces_in_parts_3 in H2.
  destruct H2.
  destruct H2.
  pose proof H3 _ H2.
  destruct H5.
  pose proof IHtriple2 _ H5 _ H4.
  destruct H7.
  split;eauto.
  eapply star_trans.
  apply H6.
  assumption.
  red;intros.
  apply H in H3.
  apply IHtriple in H3.
  apply H3 in H4.
  destruct H4.
  apply H0 in H4.
  split;auto.
  eapply star_R_star_incl.
  apply H1.
  assumption.

  red;intros.
  eapply hoare_while_ID;eauto.
Qed.

Section Sequential_Hoare_soundness.

(** End Sequential_Hoare_soundness. *)

Lemma auxy :
  forall Rl Gl Rr Gr s0 s',
    star st (rstAnd Rl Rr) s0 s' ->
    star _ (rstAnd (rstOr Rl Gl) (rstOr Rr Gr)) s0 s'.
Proof.
  intros *.
  induction 1;auto.
  destruct H0.
  econstructor 2 with x0.
  destruct H.
  split.
  left;auto.
  left;auto.
  constructor.
  destruct H.
  destruct H0.
  constructor 2 with x0.
  split;auto.
  left;auto.
  left;auto.
  assumption.
Qed.

Lemma soundness_rg_skip :
  forall R : Env, forall G : relation st, forall P Q : assrt,
  forall H : Reflexive G, forall H0 : stable R P, forall H2:stable R Q,forall H3:P[→]Q,
  forall x : st, forall H1 : P x,
    (∀s' : st, star (stmt * st) (prog_red R) (skip, x) (skip, s') → Q s')
      ∧ << R, G, skip, x >>.
Proof.
  split;intros.
  apply star_skip_means_R_star in H4.
  pose proof stable_star _ _ H2.
  eapply H5;eauto.
  
  apply guarantee_SKIP.
Qed.

Lemma soundness_rg_assg :
  forall (v : id)(a : aexp)(P : assrt)(R : Env)(Q : assrt)(G : Env),
    forall (H : stable R P)(H0 : stable R Q)(H1 : ∀s : st, G s (s) [v ← aeval s a]),
      forall (H2 : ∀s : st, P s → Q (s) [v ← aeval s a])(x : st)(H3 : P x),
   (∀s' : st, star (stmt * st) (prog_red R) (v ::= a, x) (skip, s') → Q s')
   ∧ << R, G, v ::= a, x >>.
Proof.
  split;intros.

  do_star2starn H4.
  revert n x H3 s' H4.
  induction n;intros.
  inv H4.
  inv H4.
  destruct2 y H6.
  inv H5.
  do_starn2star H7.
  apply star_skip_means_R_star in H6.
  pose proof stable_star _ _ H0.
  eapply H7.
  split.
  2:apply H6.
  apply H2.
  assumption.
  destruct H5.
  simpl in *.
  rewrite <- H5 in H7.
  assert(P s0).
  eapply H.
  split;eauto.
  pose proof IHn s0 H8 s' H7.
  assumption.
 
  red;intros.
  do_star2starn H4.
  revert n x H3 y c' c'' z H5 H4.
  induction n;intros.
  inv H4.
  inv H5.
  apply H1.
  inv H4.
  destruct2 y0 H7.
  inv H6.
  apply starn_skip_skip in H8.
  subst.
  inv H5.
  destruct H6.
  simpl in *.
  rewrite <- H6 in H8.
  assert(P s0).
  eapply H.
  split;eauto.
  pose proof IHn _ H9 _ _ _ _ H5 H8.
  assumption.
Qed.

Lemma soundness_rg_atom :
  forall (R : Env)(G : Env)(P : assrt)(Q : assrt)(c : stmt)(H : Reflexive G),
    forall (H0 : ∀x y : st, star st G x y → G x y)(H1 : stable R P)(H2 : stable R Q),
      forall (H3 : triple G P c Q)(x : st)(H4 : P x),
   (∀s' : st, star (stmt * st) (prog_red R) (atomic(c), x) (skip, s') → Q s')
   ∧ << R, G, atomic(c), x >>.
Proof.
  split;
  intros.
  apply star_does_atomic_inv in H5.
  destruct H5 as [s1 [s2 [H6 [H7 H8]]]].
  pose proof stable_star _ _ H2.
  eapply H5.
  split.
  2:apply H8.
  assert(P s1). 
  pose proof stable_star _ _ H1.
  eapply H9;eauto.
  Check triple_correct.
  pose proof triple_correct P c G Q H3 _ H9 s2 H7.
  destruct H10.
  assumption.

  red;intros.
  pose proof H5.
  apply atomic_implies_skip in H5.
  destruct H5.
  subst.
  pose proof red_atomic_imp_skip _ _ _ _ H6.
  subst.
  apply red_atomic_implies_cstep in H6.
  pose proof star_does_atomic R c z y H6.
  pose proof atomic_atomic_implies_Rstar _ _ _ _ H7.
  clear H5.
  assert(P y).
  pose proof stable_star _ _ H1.
  eapply H5.
  split;eauto.
  pose proof triple_correct P c G Q H3 _ H5 _ H6.
  destruct H9.
  apply H0 in H10.
  assumption.
  subst.
  inv H6.
Qed.

Lemma soundness_rg_if :
  forall (R : Env)(G : Env)(P : assrt)(c1 : stmt)(c2 : stmt)(Q : assrt)(b : bexp),
    forall (H : Reflexive G)(H0 : stable R ([⊤]b))(H1 : stable R ([⊥]b))(H2 : stable R P),
      forall (H3 : {{ R , G }} ⊢ {{ ([⊤]b)[∧]P }} c1 {{ Q }}),
        forall (H4 : {{ R , G }} ⊢ {{ ([⊥]b)[∧]P }} c2 {{ Q }}),
          forall (IHtriple_rg1 : {{ R , G }} ⊧ {{ ([⊤]b)[∧]P }} c1 {{ Q }}),
            forall (IHtriple_rg2 : {{ R , G }} ⊧ {{ ([⊥]b)[∧]P }} c2 {{ Q }})(x : st)(H5 : P x),
   (∀s' : st,
    star (stmt * st) (prog_red R) (ifb b then c1 else c2 fi, x) (skip, s')
    → Q s') ∧ << R, G, ifb b then c1 else c2 fi, x >>.
Proof.
  split;intros.
  dependent induction H6.
  destruct2 y H7.
  inv H7.
  assert((([⊥]b)[∧]P) s0).
  split;auto.
  pose proof IHtriple_rg2 s0 H8.
  destruct H10.
  pose proof H10 _ H6.
  assumption.

  assert((([⊤]b)[∧]P) s0).
  split;auto.
  pose proof IHtriple_rg1 s0 H8.
  destruct H10.
  apply H10;auto.
  destruct H7;simpl in *.
  symmetry in H7;subst.
  assert(P s0).
  eapply H2;split;eauto.
  pose proof IHstar c1 c2 b H H0 H1 H2 H3 H4 
             IHtriple_rg1 IHtriple_rg2 s0 H7 s' refl_equal refl_equal.
  assumption.
 
  destruct(b2assrt_dec b x) as [Bt | Bf];
             [ assert((assrtT b[∧]P) x) by (split;auto) | 
               assert((assrtF b[∧]P) x) by (split;auto)];
             [ pose proof (IHtriple_rg1 _ H6) as H7 | 
               pose proof (IHtriple_rg2 _ H6) as H7 ];destruct H7.
  eapply within_if_true;auto.
  eapply within_if_false;auto.
Qed.

Lemma soundness_rg_seq :
  forall (R : Env)(G : Env)(c1 : stmt)(c2 : stmt)(P : assrt)(K : assrt)(Q : assrt),
    forall (H : Reflexive G)(H0 : {{ R , G }} ⊢ {{ P }} c1 {{ K }}),
      forall (H1 : {{ R , G }} ⊢ {{ K }} c2 {{ Q }}),
        forall (IHtriple_rg1 : {{ R , G }} ⊧ {{ P }} c1 {{ K }}),
          forall (IHtriple_rg2 : {{ R , G }} ⊧ {{ K }} c2 {{ Q }})(x : st)(H2 : P x),
   (∀s' : st, star (stmt * st) (prog_red R) (c1; c2, x) (skip, s') → Q s')
   ∧ << R, G, c1; c2, x >>.
Proof.
  split;intros.

  apply sequence_reduces_in_parts_3 in H3.
  destruct H3 as [s [H4 H5]].
  pose proof IHtriple_rg1 _ H2.
  destruct H3.
  apply H3 in H4.
  pose proof IHtriple_rg2 _ H4.
  destruct H7.
  apply H7;auto.

  eapply within_seq.
  apply H.
  pose proof IHtriple_rg1 _ H2.
  destruct H3.
  assumption.
  pose proof IHtriple_rg1 _ H2.
  destruct H3.
  intros.
  do_starn2star H5.
  apply H3 in H6.
  pose proof IHtriple_rg2 _ H6.
  destruct H5.
  assumption.
Qed.

Lemma soundness_rg_conseq :
  forall (R : Env)(R' : Env)(G : Env)(G' : Env)(P : assrt)(P' : assrt)(Q : assrt)(Q' : assrt),
    forall (c : stmt)(H : {{ R' , G' }} ⊢ {{ P' }} c {{ Q' }})(H0 : P[→]P')(H1 : Q'[→]Q),
      forall (H2 : rstImp R R')(H3 : rstImp G' G),
      forall (IHtriple_rg : {{ R' , G' }} ⊧ {{ P' }} c {{ Q' }})(x : st)(H4 : P x),
   (∀s' : st, star (stmt * st) (prog_red R) (c, x) (skip, s') → Q s')
   ∧ << R, G, c, x >>.
Proof.
  split;
  pose proof stengthening R R' G G' P P' Q Q' c H0 H1 H2 H3 IHtriple_rg.
  apply H5 in H4.
  destruct H4.
  assumption.

  pose proof stengthening R R' G G' P P' Q Q' c H0 H1 H2 H3 IHtriple_rg.
  apply H5 in H4.
  destruct H4.
  assumption.
Qed.

Lemma soundness_rg_while :
  forall (R : Env)(G : Env)(P : assrt)(b : bexp)(c : stmt),
    forall (H : Reflexive G)(H0 : stable R ([⊤]b))(H1 : stable R ([⊥]b))(H2 : stable R P),
      forall (H3 : {{ R , G }} ⊢ {{ ([⊤]b)[∧]P }} c {{ P }}),
        forall (IHtriple_rg : {{ R , G }} ⊧ {{ ([⊤]b)[∧]P }} c {{ P }})(x : st)(H4 : P x),
   (∀s' : st,
    star (stmt * st) (prog_red R) (while b do c end, x) (skip, s')
    → (([⊥]b)[∧]P) s') ∧ << R, G, while b do c end, x >>.
Proof.
  split. eapply hoare_while;eauto.  admit.
Qed.

Lemma soundness_rg_par :
  forall (Rl : Env)(Rr : Env)(Gl : Env)(Gr : Env)(G : Env)(P : assrt)(Q1 : assrt),
    forall (Q2 : assrt)(cr : stmt)(cl : stmt)(H : Reflexive Gl)(H0 : Reflexive Gr),
      forall (H1 : rstImp (rstOr Gl Gr) G)(H2 : rstImp (rstOr Rl Gl) Rr),
      forall (H3 : rstImp (rstOr Rr Gr) Rl)(H4 : stable (rstOr Rr Gr) Q1),
        forall (H5 : stable (rstOr Rl Gl) Q2)(H6 : stable (rstOr Rr Gr) P),
          forall (H7 : stable (rstOr Rl Gl) P)(H8 : {{ Rl , Gl }} ⊢ {{ P }} cl {{ Q1 }}),
            forall (H9 : {{ Rr , Gr }} ⊢ {{ P }} cr {{ Q2 }}),
              forall (IHtriple_rg1 : {{ Rl , Gl }} ⊧ {{ P }} cl {{ Q1 }}),
                forall (IHtriple_rg2 : {{ Rr , Gr }} ⊧ {{ P }} cr {{ Q2 }}),
                  forall (x : st)(H10 : P x),
   (∀s' : st,
    star (stmt * st) (prog_red (rstAnd Rl Rr)) (par cl with cr end, x)
      (skip, s') → (Q1[∧]Q2) s')
   ∧ << rstAnd Rl Rr, G, par cl with cr end, x >>.
Proof.
  split.
  intros.
  pose proof IHtriple_rg1 _ H10.
  pose proof IHtriple_rg2 _ H10.
  destruct H12.
  destruct H13.
  (* Left part *)
  pose proof par_reduces_to_skip_left Rl Rr Gl Gr cl cr x s' H2 H3 H14 H15 H11.
  destruct H16.
  destruct H16.
  destruct H16.
  destruct H17.
  assert(<<Rr,Gr,x0,x1>>).
  eapply within_prog_red_star.
  apply H18.
  assumption.
  pose proof within_par_skip_left _ _ _ _ H0 H19.
  pose proof rstAnd_split _ _ _ _ H17.
  destruct H21.
  split.

  pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H16 H14.
  clear H21.
  pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H22 H20.
  pose proof stable_star _ _ H4.
  eapply H24.
  split;eauto.
  (* right part *)
  pose proof par_reduces_to_skip_right Rl Rr Gl Gr cl cr x s' H2 H3 H14 H15 H11.
  destruct H23.
  destruct H23.
  destruct H23.
  destruct H24.
  assert(<<Rl,Gl,x2,x3>>).
  eapply within_prog_red_star.
  apply H25.
  assumption.
  pose proof within_par_skip_right _ _ _ _ H H26.
  pose proof rstAnd_split _ _ _ _ H24.
  destruct H28.

  pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H23 H15.
  clear H21.
  pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H28 H27.
  pose proof stable_star _ _ H5.
  eapply H31.
  split;eauto.
  
  (** Guarantee parallel. *)
  eapply within_par_both.
  eapply(rstOr_refl Gl Gr);eauto.
  3:apply H1.
  pose proof IHtriple_rg1 _ H10.
  destruct H11.
  clear H11.
  eapply guarantee_impl with Rl.
  red;intros.
  destruct H11.
  destruct H11.
  apply H11.
  assert((rstOr Rr Gr) s s').
  right.
  assumption.
  apply H3 in H13.
  assumption.
  assumption.
  pose proof IHtriple_rg2 _ H10.
  destruct H11.
  clear H11.
  eapply guarantee_impl with Rr.
  red;intros.
  destruct H11.
  destruct H11.
  apply H13.
  assert((rstOr Rl Gl) s s').
  right.
  assumption.
  apply H2 in H13.
  assumption.
  assumption.
Qed.

Theorem soundness_rg :
  forall R G P Q c,
    {{R,G}} ⊢ {{P}} c {{Q}} ->
    {{R,G}} ⊧ {{P}} c {{Q}}.
Proof.
  induction 1;red;intros(*;split*).

  (* SKIP *)
  apply soundness_rg_skip with P;auto.

  (* Assignment *)
  eapply soundness_rg_assg with P;auto.
 
  (* Atomic execution. *)
  apply soundness_rg_atom with P;auto.
  
  (* Conditional *)
  apply soundness_rg_if with P;auto.
  
  (* Sequence *)
  apply soundness_rg_seq with P K;auto.
  
  (* Consequence *)
  eapply soundness_rg_conseq;eauto.
  
  (** While loop *)
  eapply soundness_rg_while;eauto.

  (** Parallel computation rule *)
  pose proof soundness_rg_par Rl Rr Gl Gr G P Q1 Q2 cr cl H H0 H2 H3 H4 H6 H7 H8 H9 H10 H11
                              IHtriple_rg1 IHtriple_rg2 _ H12.
  destruct H13.
  split;auto.
  intros.
  apply H5.
  apply H13.
  eapply star_impl_rely.
  apply H1.
  assumption.
  eapply guarantee_impl.
  apply H1.
  assumption.
Qed.

End Sequential_Hoare_soundness.

Section TESTE.
  Variables R G:Env.
  Variable c : stmt.

  Axiom cool :
    forall (P:Env -> Env -> stmt -> st -> Prop),
      (forall n c s a b c' s', 
         (prog_red R) (c,s) (a,b) -> starn _ (prog_red R) n (a,b)  (c',s') -> 
                           (forall m d e c' s', m <= n -> starn _ (prog_red R) m (d,e) (c',s') ->
                                            P R G d e) -> P R G a b) ->
      forall c s c' s', star _ (prog_red R) (c,s) (c',s') -> P R G c s.
  
  Goal forall c b s, <<R,G,c,s>> -> forall s', star _ (prog_red R) (while b do c end,s) (skip,s') -> (forall p q p0 q0 , p = (while b do c end) ->  p0 = skip -> q = s -> q0 = s' -> star _ (prog_red R) (p,q) (p0,q0) ->  <<R,G,p,q>>).
  Proof.
    intros until p.
    intros q p0 q0 H1 H2 H3 H4.
    intro.
    pattern p,q. 
    eapply (cool (fun R G x y => star _ (prog_red R) (x,y) (p0,q0) -> <<R,G,x,y>>)).
    2:apply H5.
    2:apply H5.
    intros.
    subst.
    subst.
    intros.
    destruct H4.
    inv H4;try congruence.
    inv H1.
    revert p0 q0 H1 H2 H3.
    pattern p , q.
    eapply cool with (c:=while b do c end)(s:=s).
    2:apply H0.
    intros.
    inv H1.
    destruct H1.
    red.
    intros.
    eapply H.
    inv H1.
    intros.
    destruct H0.
    inv H1.
    red;intros.
    eapply H2.
    2:apply H1.
    omega.
    change k with (snd (while b do c0 end,k)).
    eapply H2 with 0.
    omega.
    inv H0.
    inv H1.
    inv H1.
    destruct H0.
    red;intros.
    simpl in H3.
    inv H3.
    inv H4.
    admit.
    destruct H5.
    inv H5.
    eapply H2.
    Focus 3.
    simpl.
    change k with (snd (while b do c0 end,k)) in H3.
    apply H3.
    destruct H5.
    inv H5.


Section Examples.

  Section Example1.
    Variable x:id.
    Definition R := fun a b:st => aeval a (AId (x)) <= aeval b (AId x).
    Definition G := fun a b:st => aeval a (AId x) <= aeval b (AId x).
    
    Goal {{R,G}} ⊢ {{assrt_geq x (ANum 0)}} 
         par 
          x ::= APlus (AId x) (ANum 1)
         with 
          x ::= APlus (AId x) (ANum 2)
         end
         {{(assrt_geq x (ANum 2))}}.
    Proof.
      eapply RConcur with (Rl:=R)(Rr:=R)(Gl:=G)(Gr:=G)
                          (Q1:=(assrt_geq x (ANum 1)))(Q2:=(assrt_geq x (ANum 2)));
                          first [(now (red;firstorder)) | (red;unfold G;intros;omega) |idtac];
      eapply RAsgn;first [(now (red;firstorder))|
                          now(unfold G;simpl;intros;unfold upd;destruct(eq_nat_dec x x);omega)|
                          now(intros;red in *;simpl in *;auto)].
    Qed.
  End Example1.

  Section ExAssg.
    Variable x : id.
    Definition R1 := fun s y => aeval s (AId x) > 0 -> aeval y (AId x) >= aeval s (AId x). 
    Definition G1 := fun _ _:st => True.

    Goal {{R1,G1}} ⊢ {{fun _ => True}}x ::= (ANum 10) {{fun s => aeval s (AId x) >= 10}}.
    Proof.
      constructor.
      repeat red;auto.
      repeat red;simpl;intros.
      destruct H.
      unfold R1 in H0.
      simpl in H0.
      omega.
      unfold G1.
      trivial.
      intros.
      simpl.
      unfold upd;simpl.
      destruct(eq_nat_dec x x);intuition.
    Qed.

  End ExAssg.

  Section ExAtomic.
    Variable x : id.
    Definition R2 := fun s s' => aeval s (AId x) > 0 -> aeval s' (AId x) >= aeval s (AId x).
    Definition G2 := fun s s' => aeval s' (AId x) <= aeval s (AId x).

    Goal {{R2,G2}} ⊢ {{fun s => 0 <= aeval s (AId x)}}
         atomic(ifb BLt (ANum 0) (AId x) then (x::=AMinus (AId x) (ANum 1)) else skip fi)
         {{fun s => 0 <= aeval s (AId x)}}.
    Proof.
      Print assg_subs.
      Check triple_Assgn.
      constructor.
      red. unfold G2.
      auto.
      intros.
      induction H.
      constructor.
      red in IHstar.
      red in H.
      red.
      simpl in *.
      omega.
      unfold R2,stable;simpl.
      intros.
      omega.
      unfold R2,stable;simpl.
      intros.
      omega.
      eapply triple_Conseq with (assg_subs x (AMinus (AId x) (ANum 1)) (fun s : st => 0 <= aeval s (AId x))) (fun s : st => 0 ≤ aeval s (AId x)) G2.
      simpl.
      red.
      simpl.
      unfold assg_subs.
      simpl.
      intros.
      omega.
      red;auto.
      red;auto.
      constructor.
      simpl.
      eapply triple_Conseq with (assg_subs x (AMinus (AId x) (ANum 1)) (fun s : st => 0 <= aeval s (AId x))) (fun s : st => 0 ≤ aeval s (AId x)) G2.
      red;simpl.
      intros.
      destruct H;auto.
      red;auto.
      red;auto.
      Print triple_Sequence.
      set(L:=(fun s : st => 0 ≤ aeval s (AId x))).
      apply triple_Assgn.
      intros.
      unfold G2.
      simpl.
      unfold upd.
      destruct(eq_nat_dec x x).
      omega.
      omega.
      simpl.
      eapply triple_Conseq with ((fun s : st => 0 <= aeval s (AId x))) (fun s : st => 0 ≤ aeval s (AId x)) G2;try now(red;auto).
      red;intros.
      destruct H.
      red in H0.
      simpl in *.
      omega.
      constructor.
    Qed.
     
  End ExAtomic.

