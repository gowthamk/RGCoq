Require Export generic synt_and_sos main_defs prog_reductions guarantees.

Lemma stengthening :
  forall R R' G G' P P' Q Q' c,
    assrtImp P P' ->
    assrtImp Q' Q ->
    rstImp R R' ->
    rstImp G' G ->
    [|R',G'|] |= [|P'|] c [|Q'|] ->
    HG_val' R G P c Q.
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
  eapply star_n_impl.
  apply Hr.
  assumption.
  destruct H2.
  simpl in *.
  subst.
  destruct y;simpl in *.
  constructor 2 with (s,s0).
  right;split;auto.
  eapply star_n_impl.
  apply Hr.
  assumption.

  red;intros.
  apply Hg.
  apply Hp in H0.
  pose proof H _ H0.
  destruct H4.
  eapply H5.
  eapply star_n_impl.
  apply Hr.
  apply H2.
  apply H3.
Qed.

Lemma aver :
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

  assert(stable ID ([T]b)).
  red.
  intros.
  destruct H1.
  red in H2.
  subst.
  assumption.

  red;intros.
  destruct(b2assrt_dec b x).
  assert((([T]b)[/\]P) x).
  split;auto.
  pose proof IHtriple1 _ H4.
  apply H5.
  
  pose proof star_if_inv_true ID b c1 c2 x s' H1 H3 b0.
  assumption.

  assert(stable ID ([F]b)).
  red.
  intros.
  destruct H4.
  red in H5.
  subst.
  assumption.

  assert((([F]b)[/\]P) x) by (split;auto).
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

(* Lemma soundness_rg_skip : *)
(*   forall R : Env, forall G : relation st, forall P : assrt, *)
(*     forall H : Reflexive G, forall H0 : stable R P, forall x : st, forall H1 : P x, *)
(*       (∀s' : st, star (stmt * st) (prog_red R) (skip, x) (skip, s') → P s') *)
(*         ∧ << R, G, skip, x >>. *)
(* Proof. *)
(*   split;intros. *)
(*   apply star_skip_means_R_star in H2. *)
(*   pose proof stable_star _ _ H0. *)
(*   eapply H3;eauto. *)
  
(*   apply guarantee_SKIP. *)
(* Qed. *)

(* Lemma soundness_rg_assg : *)
(*   forall (v : id)(a : aexp)(P : assrt)(R : Env)(Q : assrt)(G : Env), *)
(*     forall (H : stable R P)(H0 : stable R Q)(H1 : ∀s : st, G s (s) [v <== aeval s a]), *)
(*       forall (H2 : ∀s : st, P s → Q (s) [v <== aeval s a])(x : st)(H3 : P x), *)
(*    (∀s' : st, star (stmt * st) (prog_red R) (v ::= a, x) (skip, s') → Q s') *)
(*    ∧ << R, G, v ::= a, x >>. *)
(* Proof. *)
(*   split;intros. *)

(*   do_star2starn H4. *)
(*   revert n x H3 s' H4. *)
(*   induction n;intros. *)
(*   inv H4. *)
(*   inv H4. *)
(*   destruct2 y H6. *)
(*   inv H5. *)
(*   do_starn2star H7. *)
(*   apply star_skip_means_R_star in H6. *)
(*   pose proof stable_star _ _ H0. *)
(*   eapply H7. *)
(*   split. *)
(*   2:apply H6. *)
(*   apply H2. *)
(*   assumption. *)
(*   destruct H5. *)
(*   simpl in *. *)
(*   rewrite <- H5 in H7. *)
(*   assert(P s0). *)
(*   eapply H. *)
(*   split;eauto. *)
(*   pose proof IHn s0 H8 s' H7. *)
(*   assumption. *)
 
(*   red;intros. *)
(*   do_star2starn H4. *)
(*   revert n x H3 y c' c'' z H5 H4. *)
(*   induction n;intros. *)
(*   inv H4. *)
(*   inv H5. *)
(*   apply H1. *)
(*   inv H4. *)
(*   destruct2 y0 H7. *)
(*   inv H6. *)
(*   apply starn_skip_skip in H8. *)
(*   subst. *)
(*   inv H5. *)
(*   destruct H6. *)
(*   simpl in *. *)
(*   rewrite <- H6 in H8. *)
(*   assert(P s0). *)
(*   eapply H. *)
(*   split;eauto. *)
(*   pose proof IHn _ H9 _ _ _ _ H5 H8. *)
(*   assumption. *)
(* Qed. *)

(* Lemma soundness_rg_atom : *)
(*   forall (R : Env)(G : Env)(P : assrt)(Q : assrt)(c : stmt)(H : Reflexive G), *)
(*     forall (H0 : ∀x y : st, star st G x y → G x y)(H1 : stable R P)(H2 : stable R Q), *)
(*       forall (H3 : G_val P c G Q)(x : st)(H4 : P x), *)
(*    (∀s' : st, star (stmt * st) (prog_red R) (atomic(c), x) (skip, s') → Q s') *)
(*    ∧ << R, G, atomic(c), x >>. *)
(* Proof. *)
(*   split; *)
(*   intros. *)
(*   apply star_does_atomic_inv in H5. *)
(*   destruct H5 as [s1 [s2 [H6 [H7 H8]]]]. *)
(*   pose proof stable_star _ _ H2. *)
(*   eapply H5. *)
(*   split. *)
(*   2:apply H8. *)
(*   assert(P s1).  *)
(*   pose proof stable_star _ _ H1. *)
(*   eapply H9;eauto. *)
(*   pose proof H3 _ H9 s2 H7. *)
(*   destruct H10. *)
(*   assumption. *)

(*   red;intros. *)
(*   pose proof H5. *)
(*   apply atomic_implies_skip in H5. *)
(*   destruct H5. *)
(*   subst. *)
(*   pose proof red_atomic_imp_skip _ _ _ _ H6. *)
(*   subst. *)
(*   apply red_atomic_implies_cstep in H6. *)
(*   pose proof star_does_atomic R c z y H6. *)
(*   pose proof atomic_atomic_implies_Rstar _ _ _ _ H7. *)
(*   clear H5. *)
(*   assert(P y). *)
(*   pose proof stable_star _ _ H1. *)
(*   eapply H5. *)
(*   split;eauto. *)
(*   pose proof H3 _ H5 _ H6. *)
(*   destruct H9. *)
(*   apply H0 in H10. *)
(*   assumption. *)
(*   subst. *)
(*   inv H6. *)
(* Qed. *)

(* Lemma soundness_rg_if : *)
(*   forall (R : Env)(G : Env)(P : assrt)(c1 : stmt)(c2 : stmt)(Q : assrt)(b : bexp), *)
(*     forall (H : Reflexive G)(H0 : stable R ([T]b))(H1 : stable R ([F]b))(H2 : stable R P), *)
(*       forall (H3 : [| R , G |] |- [| ([T]b)[/\]P |] c1 [| Q |]), *)
(*         forall (H4 : [| R , G |] |- [| ([F]b)[/\]P |] c2 [| Q |]), *)
(*           forall (IHtriple_rg1 : [| R , G |] |= [| ([T]b)[/\]P |] c1 [| Q |]), *)
(*             forall (IHtriple_rg2 : [| R , G |] |= [| ([F]b)[/\]P |] c2 [| Q |])(x : st)(H5 : P x), *)
(*    (∀s' : st, *)
(*     star (stmt * st) (prog_red R) (ifb b then c1 else c2 fi, x) (skip, s') *)
(*     → Q s') ∧ << R, G, ifb b then c1 else c2 fi, x >>. *)
(* Proof. *)
(*   split;intros. *)
(*   dependent induction H6. *)
(*   destruct2 y H7. *)
(*   inv H7. *)
(*   assert((([F]b)[/\]P) s0). *)
(*   split;auto. *)
(*   pose proof IHtriple_rg2 s0 H8. *)
(*   destruct H10. *)
(*   pose proof H10 _ H6. *)
(*   assumption. *)

(*   assert((([T]b)[/\]P) s0). *)
(*   split;auto. *)
(*   pose proof IHtriple_rg1 s0 H8. *)
(*   destruct H10. *)
(*   apply H10;auto. *)
(*   destruct H7;simpl in *. *)
(*   symmetry in H7;subst. *)
(*   assert(P s0). *)
(*   eapply H2;split;eauto. *)
(*   pose proof IHstar c1 c2 b H H0 H1 H2 H3 H4  *)
(*              IHtriple_rg1 IHtriple_rg2 s0 H7 s' refl_equal refl_equal. *)
(*   assumption. *)
 
(*   destruct(b2assrt_dec b x) as [Bt | Bf]; *)
(*              [ assert((assrtT b[/\]P) x) by (split;auto) |  *)
(*                assert((assrtF b[/\]P) x) by (split;auto)]; *)
(*              [ pose proof (IHtriple_rg1 _ H6) as H7 |  *)
(*                pose proof (IHtriple_rg2 _ H6) as H7 ];destruct H7. *)
(*   eapply within_if_true;auto. *)
(*   eapply within_if_false;auto. *)
(* Qed. *)

(* Lemma soundness_rg_seq : *)
(*   forall (R : Env)(G : Env)(c1 : stmt)(c2 : stmt)(P : assrt)(K : assrt)(Q : assrt), *)
(*     forall (H : Reflexive G)(H0 : [| R , G |] |- [| P |] c1 [| K |]), *)
(*       forall (H1 : [| R , G |] |- [| K |] c2 [| Q |]), *)
(*         forall (IHtriple_rg1 : [| R , G |] |= [| P |] c1 [| K |]), *)
(*           forall (IHtriple_rg2 : [| R , G |] |= [| K |] c2 [| Q |])(x : st)(H2 : P x), *)
(*    (∀s' : st, star (stmt * st) (prog_red R) (c1; c2, x) (skip, s') → Q s') *)
(*    ∧ << R, G, c1; c2, x >>. *)
(* Proof. *)
(*   split;intros. *)

(*   apply sequence_reduces_in_parts_3 in H3. *)
(*   destruct H3 as [s [H4 H5]]. *)
(*   pose proof IHtriple_rg1 _ H2. *)
(*   destruct H3. *)
(*   apply H3 in H4. *)
(*   pose proof IHtriple_rg2 _ H4. *)
(*   destruct H7. *)
(*   apply H7;auto. *)

(*   eapply within_seq. *)
(*   apply H. *)
(*   pose proof IHtriple_rg1 _ H2. *)
(*   destruct H3. *)
(*   assumption. *)
(*   pose proof IHtriple_rg1 _ H2. *)
(*   destruct H3. *)
(*   intros. *)
(*   do_starn2star H5. *)
(*   apply H3 in H6. *)
(*   pose proof IHtriple_rg2 _ H6. *)
(*   destruct H5. *)
(*   assumption. *)
(* Qed. *)

(* Lemma soundness_rg_conseq : *)
(*   forall (R : Env)(R' : Env)(G : Env)(G' : Env)(P : assrt)(P' : assrt)(Q : assrt)(Q' : assrt), *)
(*     forall (c : stmt)(H : [| R' , G' |] |- [| P' |] c [| Q' |])(H0 : P[->]P')(H1 : Q'[->]Q), *)
(*       forall (H2 : rstImp R R')(H3 : rstImp G' G), *)
(*       forall (IHtriple_rg : [| R' , G' |] |= [| P' |] c [| Q' |])(x : st)(H4 : P x), *)
(*    (∀s' : st, star (stmt * st) (prog_red R) (c, x) (skip, s') → Q s') *)
(*    ∧ << R, G, c, x >>. *)
(* Proof. *)
(*   split; *)
(*   pose proof stengthening R R' G G' P P' Q Q' c H0 H1 H2 H3 IHtriple_rg. *)
(*   apply H5 in H4. *)
(*   destruct H4. *)
(*   assumption. *)

(*   pose proof stengthening R R' G G' P P' Q Q' c H0 H1 H2 H3 IHtriple_rg. *)
(*   apply H5 in H4. *)
(*   destruct H4. *)
(*   assumption. *)
(* Qed. *)

(* Lemma soundness_rg_while : *)
(*   forall (R : Env)(G : Env)(P : assrt)(b : bexp)(c : stmt), *)
(*     forall (H : Reflexive G)(H0 : stable R ([T]b))(H1 : stable R ([F]b))(H2 : stable R P), *)
(*       forall (H3 : [| R , G |] |- [| ([T]b)[/\]P |] c [| P |]), *)
(*         forall (IHtriple_rg : [| R , G |] |= [| ([T]b)[/\]P |] c [| P |])(x : st)(H4 : P x), *)
(*    (∀s' : st, *)
(*     star (stmt * st) (prog_red R) (while b do c end, x) (skip, s') *)
(*     → (([F]b)[/\]P) s') ∧ << R, G, while b do c end, x >>. *)
(* Proof. *)
(*   split. eapply hoare_while;eauto.  admit. *)
(* Qed. *)

(* Lemma soundness_rg_par : *)
(*   forall (R : Env)(Rl : Env)(Rr : Env)(Gl : Env)(Gr : Env)(G : Env)(P : assrt)(Q1 : assrt), *)
(*     forall (Q2 : assrt)(cr : stmt)(cl : stmt)(H : Reflexive Gl)(H0 : Reflexive Gr), *)
(*       forall (H1 : rstImp (rstOr Gl Gr) G)(H2 : rstImp (rstOr Rl Gl) Rr), *)
(*       forall (H3 : rstImp (rstOr Rr Gr) Rl)(H4 : stable (rstOr Rr Gr) Q1), *)
(*         forall (H5 : stable (rstOr Rl Gl) Q2)(H6 : stable (rstOr Rr Gr) P), *)
(*           forall (H7 : stable (rstOr Rl Gl) P)(H8 : [| Rl , Gl |] |- [| P |] cl [| Q1 |]), *)
(*             forall (H9 : [| Rr , Gr |] |- [| P |] cr [| Q2 |]), *)
(*               forall (IHtriple_rg1 : [| Rl , Gl |] |= [| P |] cl [| Q1 |]), *)
(*                 forall (IHtriple_rg2 : [| Rr , Gr |] |= [| P |] cr [| Q2 |]), *)
(*                   forall (x : st)(H10 : P x), *)
(*    (∀s' : st, *)
(*     star (stmt * st) (prog_red (rstAnd Rl Rr)) (par cl with cr end, x) *)
(*       (skip, s') → (Q1[/\]Q2) s') *)
(*    ∧ << rstAnd Rl Rr, G, par cl with cr end, x >>. *)
(* Proof. *)
(* split. *)
(*   intros. *)
(*   pose proof IHtriple_rg1 _ H10. *)
(*   pose proof IHtriple_rg2 _ H10. *)
(*   destruct H12. *)
(*   destruct H13. *)
(*   pose proof par_reduces_to_skip_left Rl Rr Gl Gr cl cr x s' H2 H3 H14 H15 H11. *)
(*   destruct H16. *)
(*   destruct H16. *)
(*   destruct H16. *)
(*   destruct H17. *)
(*   assert(<<Rr,Gr,x0,x1>>). *)
(*   eapply within_prog_red_star. *)
(*   apply H18. *)
(*   assumption. *)
(*   pose proof within_par_skip_left _ _ _ _ H0 H19. *)
(*   pose proof rstAnd_split _ _ _ _ H17. *)
(*   destruct H21. *)
(*   split. *)

(*   pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H16 H14. *)
(*   clear H21. *)
(*   pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H22 H20. *)
(*   pose proof stable_star _ _ H4. *)
(*   eapply H24. *)
(*   split;eauto. *)

(*   pose proof par_reduces_to_skip_right Rl Rr Gl Gr cl cr x s' H2 H3 H14 H15 H11. *)
(*   destruct H23. *)
(*   destruct H23. *)
(*   destruct H23. *)
(*   destruct H24. *)
(*   assert(<<Rl,Gl,x2,x3>>). *)
(*   eapply within_prog_red_star. *)
(*   apply H25. *)
(*   assumption. *)
(*   pose proof within_par_skip_right _ _ _ _ H H26. *)
(*   pose proof rstAnd_split _ _ _ _ H24. *)
(*   destruct H28. *)

(*   pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H23 H15. *)
(*   clear H21. *)
(*   pose proof correct_reduction_wrt_rely_and_guarante _ _ _ _ _ _ H28 H27. *)
(*   pose proof stable_star _ _ H5. *)
(*   eapply H31. *)
(*   split;eauto. *)
  
(*   (** Guarantee parallel. *) *)
(*   eapply within_par_both. *)
(*   eapply(rstOr_refl Gl Gr);eauto. *)
(*   3:apply H1. *)
(*   pose proof IHtriple_rg1 _ H10. *)
(*   destruct H11. *)
(*   clear H11. *)
(*   eapply guarantee_impl with Rl. *)
(*   red;intros. *)
(*   destruct H11. *)
(*   destruct H11. *)
(*   apply H11. *)
(*   assert((rstOr Rr Gr) s s'). *)
(*   right. *)
(*   assumption. *)
(*   apply H3 in H13. *)
(*   assumption. *)
(*   assumption. *)
(*   pose proof IHtriple_rg2 _ H10. *)
(*   destruct H11. *)
(*   clear H11. *)
(*   eapply guarantee_impl with Rr. *)
(*   red;intros. *)
(*   destruct H11. *)
(*   destruct H11. *)
(*   apply H13. *)
(*   assert((rstOr Rl Gl) s s'). *)
(*   right. *)
(*   assumption. *)
(*   apply H2 in H13. *)
(*   assumption. *)
(*   assumption. *)
(* Qed. *)

Theorem soundness_rg :
  forall R G P Q c,
    [|  R  , G  |]  |- [|  P  |]  c [|  Q  |] ->
    HG_val' R G  |= [|  P  |]  c [|  Q  |].
Proof.
  induction 1;red;intros(*;split*).

  (* SKIP *)
  apply soundness_rg_skip;auto.

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
  pose proof soundness_rg_par R Rl Rr Gl Gr G P.
  apply H11;auto.
Qed.

End Sequential_Hoare_soundness.