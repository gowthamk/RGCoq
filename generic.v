(** * Generic definitions. *)
(** This script provides generic definition of relations that are used along the overall formalization. Most of the definitions and lemmas implemented here are quite trivial. *)

Require Export Arith Relations Program Omega Utf8.

(** Some usefull tactics *)
Ltac inv H := inversion H;try subst;try congruence.

Ltac fomega := elimtype False;omega.

Ltac do_stable H P x0 :=
  try assert(P x0) by (eapply H;esplit;eauto).

Ltac destruct2 v H :=
  destruct v;destruct H.

(** Reflexive and transitive closure of a relation [R] *)

Inductive star (A:Type)(R:relation A) : A -> A -> Prop :=
| star_refl : 
  forall x:A, star A R x x
| star_tran : 
  forall x y:A, 
    R x y -> forall z:A, star A R y z -> star A R x z.

(** Indexed reflexive and transitive closure over a relation [R] *)

Inductive starn (A:Type)(R:relation A) : nat -> A -> A -> Prop :=
| starn_refl : 
  forall x:A, 
    starn A R 0 x x
| starn_tran : 
  forall x y:A, 
    R x y -> forall (n:nat)(z:A), starn A R n y z -> starn A R (S n) x z.

Hint Constructors star starn.

(** Lemmas about the reflexive and transitive closure of a relation *)

Lemma star2starn:
  forall A R x y,
    star A R x y -> exists n, starn A R n x y.
Proof.
  induction 1.
  exists 0;auto.
  destruct IHstar.
  exists (S x0);econstructor 2;eauto.
Qed.

Lemma starn2star:
  forall A R n x y,
    starn A R n x y -> star A R x y.
Proof.
  induction n;intros.
  inversion H;auto.
  inversion_clear H.
  econstructor 2;eauto.
Qed.

(** Two simple tactics to exchange [nat]-indexed closure with the non-indexed one. *)

Ltac do_star2starn H :=
  let t := fresh "H" in 
    pose proof (star2starn _ _ _ _ H) as t;clear H;    
    let n := fresh "n" with m := fresh "H" in destruct t as [n m].

Ltac do_starn2star H :=
  let t := fresh "H" in 
    pose proof (starn2star _ _ _ _ _ H);clear H.

(** Transitivity of closures (indexed or not). *)

Lemma star_starn_trans :
  forall n A R x y,
    starn A R n x y -> 
    forall z, 
      star A R y z ->  star A R x z.
Proof.
  induction n;intros.
  inversion_clear H.
  assumption.
  inversion_clear H.
  constructor 2 with y0.
  assumption.
  eapply IHn.
  apply H2.
  assumption.
Qed.

Lemma star_trans :
  forall A R x y,
    star A R x y ->
    forall z, star A R y z -> star A R x z.
Proof.
  intros.
  do_star2starn H.
  eapply star_starn_trans;eauto.
Qed.

Lemma starn_trans :
  forall n A R x y,
    starn A R n x y ->
    forall m z,
      starn A R m y z ->
      starn A R (n+m) x z.
Proof.
  induction n;intros.
  inv H.
  simpl.
  assumption.
  inv H.
  constructor 2 with y0;eauto.
Qed.

Lemma starn_ex :
  forall n A R x y,
    starn A R n x y ->
    exists m x', m <= n /\ starn A R m x x' /\ starn A R (n-m) x' y.
Proof.
  induction n;intros.
  inv H.
  simpl.
  exists 0 y.
  split;auto with arith.
  inv H.
  pose proof IHn _ _ _ _ H2.
  destruct H0 as [m [x' [H4 [H5 H6]]]].
  exists (S m) x'.
  split;auto with arith.
  split.
  constructor 2 with y0;auto.
  simpl.
  assumption.
Qed.


Lemma star_R_star :
  forall A (R:relation A) x y,
    R x y ->
    star A R x y.
Proof.
  intros.
  constructor 2 with y.
  assumption.
  constructor.
Qed.

(** Closure for sub-relation. *)

Lemma star_R_star_incl :
  forall A (R1 R2:relation A) x y,
    (forall a b, R1 a b -> R2 a b) ->
    star A R1 x y ->
    star A R2 x y.
Proof.
  intros until y;intro H.
  induction 1;auto.
  constructor 2 with y.
  apply H.
  assumption.
  apply IHstar.
Qed.

(** Closure of a reflexive and transitive relation. *)

Lemma star_R_trans_imply_own :
  forall A (R:relation A) x y,
    (forall a, R a a) ->
    (forall a b c, R a b -> R b c -> R a c) ->
    star _ R x y -> R x y.
Proof.
  induction 3;intros.
  apply H.
  inv H2.
  apply H0 with y;assumption.
Qed.
   

(** Alternative inductive principle for dealing with the reflexive and
transitive closures. This one is used, in particular, in the soundness
proof of the while rule. 

This lemma indeed states that if we reach a state [s'] such that [P
s'] is statisfied in all the intermediate states [s''], then the
property [P] models the overall computation. This implies that the
reflexive and transitive closure [star] must be decomposed in the nth
transitions in the middle. One can look at this particular inductive
principle as a more detailed notion of well-founded induction over the
natural numbers, where each natural number refers to the nth-step of
execution of a program.
*)

Lemma RT_ind_gen : 
    forall (X:Type) (R P : X -> X -> Prop),
      (forall x : X, P x x) ->
      (forall (x y z: X) n, R x y -> starn _ R n y z -> 
      (forall y1 k, k <= n -> starn _ R k y1 z -> P y1 z) -> P x z) ->
      forall x y : X, star _ R x y -> P x y.
Proof.
  intros.
  case (star2starn _ _ _ _ H1).
  intros.
  assert (forall k z, k <= x0 -> starn _ R k z y -> P z y).
  induction H2.
  intros.
  replace k with 0 in *;try omega.
  inv H3;auto.
  intros.
  assert(k <= n \/ k = S n) by omega.
  destruct H6.
  eapply IHstarn with k.
  eapply starn2star with n.
  assumption.
  assumption.
  assumption.
  subst k.
  inv H5.
  pose proof H8.
  do_starn2star H3.
  eapply H0;eauto.
  eapply H3;eauto.
Qed.

