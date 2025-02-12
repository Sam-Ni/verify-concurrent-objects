Set Implicit Arguments.
Require Import 
  Arith
  Equivalence
  List
  LibVar
  LibTactic.
Import ListNotations.

Definition env (A : Type) := list (var * A)%type.

Open Scope vars_scope.
Declare Scope env_scope.

Section Definitions.
  Variable A : Type.

Definition key (e : nat * A) := fst e.
Definition val (e : nat * A) := snd e.

Definition dom (m : env A) : vars :=
  fold_right (fun e vars => \{key e} \u vars) 
    \{} (m).

Definition concat (E F : env A) : env A := F ++ E.
Definition empty : env A := [].

Definition single (x : nat) (T : A) :=
  [(x,T)].

End Definitions.

Arguments empty {A}.

Notation "\[]" := (empty) : env_scope.

Open Scope env_scope.

Notation "x ~ T" := (single x T) 
  (at level 49, left associativity): env_scope.

Notation "x # E" := (x \notin (dom E))
  (at level 67) : env_scope.

Notation "E ; F" := (concat E F)
  (at level 66, left associativity) : env_scope.


Section MoreDefinitions.

Variables A : Type.

Inductive ok : env A -> Prop :=
  | ok_empty : ok \[]
  | ok_push : forall E x T,
      ok E -> x # E -> ok (E ; x ~ T).

Fixpoint get (k : var) (E : env A) {struct E} : option A :=
  match E with
  | nil => None
  | (x,v) :: E' => if k =? x then Some v else get k E'
  end.

Definition binds x v E :=
  get x E = Some v.

Lemma env_ind : forall (P : env A -> Prop),
  (P empty) ->
  (forall E x v, P E -> P (E ; x ~ v)) ->
  (forall E, P E).
Proof.
  induction E.
  auto. destruct a. apply H0. assumption.
Qed.

End MoreDefinitions.

Ltac binds_ind :=
  intros;
  match goal with
  | [ H : binds _ _ ?E |- _ ] =>
    unfold binds in *; induction E using env_ind
  end;
  simpl; try discriminate.

Section StrutureProperties.

Variable A : Type.
Implicit Types E F : env A.

Lemma concat_empty_r : forall E,
  E ; empty = E.
Proof.
  simpl. reflexivity.
Qed.


End StrutureProperties.

Section Properties.

Variable A B : Type.
Implicit Types k x : var.
Implicit Types v : A.
Implicit Types E F G : env A.
Implicit Types f : A -> B.
Implicit Types r : var -> var.


Lemma binds_concat_inv : forall x v E1 E2,
  binds x v (E1 ; E2) ->
     (binds x v E2)
  \/ (x # E2 /\ binds x v E1).
Proof.
  induction E2 using env_ind; simpl; intros.
  - right. split. set_op. intuition.
  - unfold binds in *. simpl in *.
    eq_contra.
    right. split. apply notin_union. intuition.
    apply Nat.eqb_neq in Exx. intro. simpl in H1.
    intuition. eq_contra. assumption.
Qed.

Lemma binds_concat_right : forall x v E1 E2,
  binds x v E2 ->
  binds x v (E1 ; E2).
Proof.
  unfold binds. intros.
  induction E2 using env_ind; simpl in *.
  - discriminate.
  - destruct (x =? x0) eqn:Exx.
    -- auto.
    -- intuition.
Qed.

Lemma concat_assoc : forall E F G,
  E ; (F ; G) = (E ; F) ; G.
Proof.
  intros. unfold concat.
  rewrite app_assoc. reflexivity.
Qed.

Lemma binds_push_neq: forall x1 x2 v1 v2 E,
  binds x1 v1 E -> x1 <> x2 -> binds x1 v1 (E ; x2 ~ v2).
Proof.
  unfold binds. simpl; intros.
  destruct (x1 =? x2) eqn: Exx.
  - eq_contra.
  - assumption.
Qed.


Lemma binds_push_neq_inv : forall x1 x2 v1 v2 E,
  binds x1 v1 (E ; x2 ~ v2) -> x1 <> x2 -> binds x1 v1 E.
Proof.
  unfold binds. intros. simpl in H.
  simpl in H. destruct (x1 =? x2) eqn:Exx.
  - eq_contra.
  - assumption.
Qed. 

Lemma notin_dom_push: forall x x0 v0 E,
x # E; x0 ~ v0 -> x \notin \{x0} /\ x # E.
Proof.
  unfold "#". simpl; split.
  - intro. destruct H0; try intuition.
    subst. apply H. apply in_union.
    left. simpl. left; reflexivity.
  - apply notin_union in H. intuition.
Qed.


Lemma notin_dom_concat: forall x E1 E2,
x # E1 ; E2 -> x # E1 /\ x # E2.
Proof.
  induction E2 using env_ind; simpl; intros.
  - split. assumption. apply notin_empty.
  - apply notin_union in H. split. intuition.
    apply notin_union. intuition.
Qed.

Lemma binds_concat_left : forall x v E1 E2,
  binds x v E1 ->
  x # E2 ->
  binds x v (E1 ; E2).
Proof.
  intros.
  induction E2 using env_ind.
  - assumption.
  - rewrite concat_assoc.
    apply binds_push_neq.
    apply notin_dom_push in H0. intuition.
    simpl in H0. apply notin_union in H0.
    destruct H0. intro. apply H0. simpl.
    intuition.
Qed.

Lemma ok_push_inv : forall E x v,
  ok (E ; x ~ v) -> ok E /\ x # E.
Proof.
  intros. inversion H; subst. intuition.
Qed.

Lemma binds_in : forall x v E,
binds x v E -> x \in dom E.
Proof.
  binds_ind.
  apply in_union. simpl in H.
  eq_contra.
  left. simpl; intuition.
Qed.

Lemma binds_fresh_inv : forall x v E,
  binds x v E -> x # E -> False.
Proof.
  intros. apply H0. apply binds_in in H; assumption.
Qed.

Lemma binds_concat_left_ok : forall x v E1 E2,
  ok (E1 ; E2) ->
  binds x v E1 ->
  binds x v (E1 ; E2).
Proof.
  intros. induction E2 using env_ind.
  - simpl. assumption.
  - rewrite concat_assoc.
    rewrite concat_assoc in H.
    apply ok_push_inv in H.
    apply binds_push_neq. intuition.
    intro. subst.
    apply binds_fresh_inv in H0.
    intuition. destruct H.
    apply notin_dom_concat in H1. intuition.
Qed.

Lemma binds_weaken: forall x a E F G,
  binds x a (E ; G) ->
  ok (E ; F ; G) ->
  binds x a (E ; F ; G).
Proof.
  intros. apply binds_concat_inv in H.
  destruct H.
  - apply binds_concat_right. assumption.
  - rewrite <-concat_assoc in *.
    apply binds_concat_left_ok; intuition.
Qed.

Lemma ok_concat_inv : forall E F,
  ok (E ; F) -> ok E /\ ok F.
Proof.
  induction F using env_ind; simpl; intros.
  - intuition. constructor.
  - destruct (ok_push_inv H).
    intuition. apply notin_dom_concat in H1. 
    apply ok_push; intuition.
Qed.

Lemma ok_middle_inv : forall E F x v,
  ok (E ; x ~ v ; F) -> x # E /\ x # F.
Proof.
  induction F using env_ind; intros.
  - destruct (ok_push_inv H).
    split; [assumption|apply notin_empty].
  - simpl in H.
    destruct (ok_push_inv H).
    simpl in IHF.
    apply IHF in H0. intuition.
    apply notin_dom_concat in H1. intuition.
    simpl. apply notin_union. intuition.
    apply notin_dom_push in H0. intuition.
    intro. apply H1. simpl. simpl in H0. intuition.
Qed.

Lemma binds_remove : forall E2 E1 E3 x v,
  binds x v (E1 ; E2 ; E3) ->
  x # E2 ->
  binds x v (E1 ; E3).
Proof.
  intros. apply binds_concat_inv in H.
  destruct H.
  - apply binds_concat_right. intuition.
  - apply binds_concat_left.
    destruct H. apply binds_concat_inv in H1.
    destruct H1.
    -- apply binds_fresh_inv in H1. destruct H1.
      assumption.
    -- intuition.
    -- intuition.
Qed.

Lemma binds_subst : forall x2 v2 x1 v1 E1 E2,
  binds x1 v1 (E1 ; x2 ~ v2 ; E2) ->
  x1 <> x2 ->
  binds x1 v1 (E1 ; E2).
Proof.
  intros. apply binds_remove in H. assumption.
  simpl. apply notin_neq. assumption.
Qed.

Lemma binds_concat_left_inv : forall x v E1 E2,
  binds x v (E1 ; E2) ->
  x # E2 ->
  binds x v E1.
Proof.
  intros. apply binds_concat_inv in H.
  destruct H.
  - apply binds_fresh_inv in H. intuition.
    assumption.
  - intuition.
Qed.

Lemma get_push : forall k x v E,
  get k (E ; x ~ v) =
    if k =? x
      then Some v
      else get k E.
Proof.
  intros. eq_contra.
  - subst. simpl. rewrite (Nat.eqb_refl x).
    reflexivity.
  - simpl. apply Nat.eqb_neq in Exx; rewrite Exx.
    reflexivity.
Qed.

Lemma binds_push_inv : forall x1 v1 x2 v2 E,
  binds x1 v1 (E ; x2 ~ v2) ->
     (x1 = x2 /\ v1 = v2)
  \/ (x1 <> x2 /\ binds x1 v1 E).
Proof.
  unfold binds. intros. rewrite get_push in H.
  eq_contra. subst. inversion H; intuition.
Qed.

Lemma binds_push_eq : forall x T E,
  binds x T (E ; x ~ T).
Proof.
  intros. unfold binds. simpl.
  rewrite (Nat.eqb_refl x). reflexivity.
Qed.

Lemma binds_push_eq_inv : forall x v1 v2 E,
  binds x v1 (E ; x ~ v2) -> v1 = v2.
Proof.
  intros. apply binds_push_inv in H.
  destruct H.
  - intuition.
  - exfalso. intuition.
Qed.

Lemma binds_middle_eq_inv : forall x E1 E2 v1 v2,
  binds x v1 (E1 ; x ~ v2 ; E2) ->
  ok (E1 ; x ~ v2 ; E2) ->
  v1 = v2.
Proof.
  intros. apply ok_middle_inv in H0.
  apply binds_concat_left_inv in H.
  - apply binds_push_eq_inv in H. assumption.
  - intuition.
Qed.

Lemma ok_x1_neq_x2 : forall E x1 T1 x2 T2,
  ok (E ; (x1 ~ T1) ; (x2 ~ T2)) ->
  x1 <> x2.
Proof.
  intros. inversion H; subst.
  simpl in H4. div_notin. apply notin_neq in H0.
  intuition.
Qed.

Lemma binds_comm : forall x T E x1 T1 x2 T2,
  ok (E; x1 ~ T1; x2 ~ T2) ->
  binds x T (E; x1 ~ T1; x2 ~ T2) ->
  binds x T (E; x2 ~ T2; x1 ~ T1).
Proof.
  intros.
  generalize (ok_x1_neq_x2 H); intro.
  unfold binds in *. rewrite <-H0. simpl.
  destruct (x =? x1) eqn: Exx1;
  destruct (x =? x2) eqn: Exx2; auto.
  apply Nat.eqb_eq in Exx1, Exx2. subst.
  intuition.
Qed.

Lemma notin_concat: forall x E F,
x # E /\ x # F <-> x # E; F.
Proof.
  induction F using env_ind; simpl; split; intros.
  - intuition.
  - intuition. apply notin_empty.
  - apply notin_union.
    destruct H.
    apply notin_union in H0. intuition.
  - apply notin_union in H.
    split. intuition.
    apply notin_union. intuition.
Qed.

End Properties.

Ltac div_notin_dom :=
  repeat match goal with
  | [H : _ # _ ; _ |- _ ] => 
    apply notin_dom_concat in H; destruct H
  end.

Ltac notin_dom_solve :=
  div_notin_dom;
  repeat (match goal with
  | [ |-  _ # _ ; _] => 
    apply notin_concat
  end;
  intuition).

Ltac env_rw :=
  repeat (rewrite concat_empty_r in * || rewrite concat_assoc in *).

Ltac simpl_ok :=
  repeat match goal with
  | [ H : ok (?E ; ?x ~ ?v) |- _ ]
      => apply ok_push_inv in H; destruct H
  end
  ;
  repeat match goal with
  | [ |- ok (_ ; ?x ~ ?T)]
      => apply ok_push
  end.

Ltac env_solve :=
  subst; env_rw; intros;
  notin_dom_solve; simpl_ok;
  intuition; notin_solve; eauto.

Section MoreProperties.

Variable A : Type.
Implicit Types E F : env A.

Lemma ok_remove : forall F E G,
  ok (E ; F ; G) -> ok (E ; G).
Proof.
  induction G using env_ind; simpl; intros.
  - apply ok_concat_inv in H. intuition.
  - inversion H; subst. constructor. intuition.
    notin_dom_solve.
Qed.

Lemma ok_comm : forall E x1 T1 x2 T2,
  ok (E ; (x1 ~ T1) ; (x2 ~ T2)) ->
  ok (E ; (x2 ~ T2) ; (x1 ~ T1)).
Proof.
  intros. constructor. constructor;
  inversion H; subst; inversion H2; subst.
  assumption. simpl in H4. apply notin_union in H4.
  intuition. simpl. apply notin_union.
  apply ok_middle_inv in H; intuition.
Qed.

Lemma ok_concat_comm: forall E F,
  ok (E; F) ->
  ok (F; E).
Proof.
  induction E using env_ind; intros.
  - simpl. unfold ";" in H. rewrite app_nil_r in H. 
    assumption.
  - rewrite concat_assoc. constructor.
    apply IHE. generalize (ok_remove _ _ _ H); intro.
    assumption.
    apply ok_middle_inv in H. notin_dom_solve.
Qed.


Lemma binds_notin_neq : forall E x T y,
  binds x T E ->
  y # E ->
  x <> y.
Proof.
  intros. apply binds_in in H.
  unfold "#" in H0. intro. subst. intuition.
Qed.

Lemma notin_dom_push_get: forall x E x' T,
  x # E ->
  x \notin \{ x' } ->
  x # E; x' ~ T.
Proof.
  intros. env_solve.
Qed.


End MoreProperties.

Section SubsetDef.

Context {A : Type}.
  
Reserved Notation "E \subset F" (at level 70).
Inductive subset : env A -> env A -> Prop :=
  | subset_refl : forall E,
      ok E ->
      E \subset E
  | subset_push_r : forall E F x T,
      E \subset F ->
      ok (F ; x ~ T) ->
      E \subset F ; x ~ T
  | subset_push_l : forall E F x T,
      E \subset F ->
      binds x T F ->
      ok (E ; x ~ T) ->
      E ; x ~ T \subset F
where "E \subset F" := (subset E F).

Definition sameset E F := subset E F /\ subset F E.
Notation "E [=] F" := (sameset E F) (at level 69).


Hint Constructors ok : core.
Hint Constructors subset : core.

Lemma subset_empty_core: forall E F,
 ok (E ; F) ->
 E \subset (E ; F).
Proof.
  induction F using env_ind; env_solve.
Qed.

Hint Resolve subset_empty_core : core.

Lemma subset_empty : forall E,
  ok E ->
  \[] \subset E.
Proof.
  intros. remember \[] as F.
  induction H; subst; env_solve.
Qed.

Hint Resolve subset_empty : core.

Lemma subset_empty_inv : forall E,
  E \subset \[] -> E = \[].
Proof.
  intros. inversion H; reflexivity || discriminate.
Qed.

Hint Resolve subset_empty_inv : core.

Lemma subset_weaken: forall E E' x T,
  (E ; x ~ T) \subset E' -> E \subset E'.
Proof.
  intros. remember (E; x ~ T) as D.
  induction H; intros.
  - subst. env_solve.
  - env_solve.
  - inversion HeqD; subst. assumption.
Qed.

Hint Resolve subset_weaken : core.

Lemma subset_ok_inv : forall E F,
  E \subset F ->
  ok E /\ ok F.
Proof.
  intros. induction H; split; intuition.
Qed.

Lemma subset_ok_inv_l: forall E F,
  E \subset F ->
  ok E.
Proof.
  intros. apply subset_ok_inv in H; intuition.
Qed.

Lemma subset_ok_inv_r: forall E F,
  E \subset F ->
  ok F.
Proof.
  intros; apply subset_ok_inv in H; intuition.
Qed.

Hint Resolve subset_ok_inv_l : core.
Hint Resolve subset_ok_inv_r : core.

Lemma subset_ok : forall E F,
  E \subset F ->
  ok F ->
  ok E.
Proof.
  intros. induction H; env_solve.
Qed.

Hint Resolve subset_ok : core.

Lemma notin_dom_subset : forall E F x,
  x # F ->
  E \subset F ->
  x # E.
Proof.
  intros. induction H0; env_solve. simpl.
  apply notin_neq. generalize (binds_notin_neq H1 H).
  intuition.
Qed.

Hint Resolve binds_notin_neq : core.
Hint Resolve binds_push_neq : core.
Hint Resolve binds_push_neq_inv : core.
Hint Unfold binds : core.

Lemma subset_binds : forall E F x T,
  E \subset F ->
  binds x T E ->
  binds x T F.
Proof.
  intros. induction H; env_solve.
  - destruct (eq_nat_dec x x0); env_solve.
    -- subst. unfold binds in H0; simpl in H0.
      rewrite (Nat.eqb_refl x0) in H0.
      inversion H0. subst. assumption.
Qed.

Hint Resolve subset_binds : core.
Hint Resolve ok_comm : core.
Hint Resolve binds_push_eq : core.
Hint Resolve ok_concat_inv : core.

Lemma subset_comm : forall E x1 T1 x2 T2,
  ok (E; x1 ~ T1; x2 ~ T2) ->
  E; x1 ~ T1; x2 ~ T2 \subset E; x2 ~ T2; x1 ~ T1.
Proof.
  intros. generalize (ok_comm H); intro.
  apply subset_push_l; env_solve.
Qed.

Hint Resolve subset_comm : core.

Lemma subset_notin : forall E E' x,
  E' \subset E ->
  x # E ->
  x # E'.
Proof.
  intros. induction H; env_solve.
  - apply notin_neq.
    generalize (binds_notin_neq H1 H0); intuition.
Qed.

Hint Resolve subset_notin : core.
Hint Resolve subset_ok_inv : core.
Hint Resolve subset_binds : core.

Lemma sameset_ok_inv : forall E F,
  E [=] F -> ok E /\ ok F.
Proof.
  unfold "[=]". env_solve.
Qed.

Lemma sameset_inv : forall E F,
  E [=] F -> E \subset F /\ F \subset E.
Proof.
  unfold "[=]". intros. intuition.
Qed.

Lemma sameset_inv_l: forall E F,
  E [=] F -> E \subset F.
Proof.
  intros. apply sameset_inv in H; intuition.
Qed.

Lemma sameset_inv_r : forall E F,
  E [=] F -> F \subset E.
Proof.
  intros. apply sameset_inv in H; intuition.
Qed.

Hint Resolve sameset_inv_l : core.
Hint Resolve sameset_inv_r : core.

Instance trans_subset : Transitive subset.
Proof.
  red. intros. induction H; env_solve.
Qed.

Hint Resolve trans_subset : core.

Lemma sym_sameset : forall E F,
  E [=] F -> F [=] E.
Proof.
  unfold sameset; env_solve.
Qed.

Hint Resolve sym_sameset : core.

Lemma trans_sameset : forall E F G,
  E [=] F ->
  F [=] G ->
  E [=] G.
Proof.
  unfold sameset. env_solve.
Qed.

Hint Resolve trans_sameset : core.

Lemma sameset_subset_r : forall E F F',
  E \subset F ->
  F [=] F' ->
  E \subset F'.
Proof.
  env_solve.
Qed.

Hint Resolve sameset_subset_r : core.

Lemma sameset_comm : forall E x1 T1 x2 T2,
  ok (E ; x1 ~ T1 ; x2 ~ T2) ->
  E ; x1 ~ T1 ; x2 ~ T2 [=] E ; x2 ~ T2 ; x1 ~ T1.
Proof.
  intros. generalize (ok_comm H); intro.
  apply subset_comm in H, H0;
  unfold sameset; intuition.
Qed.

Hint Resolve sameset_comm : core.

Lemma subset_concat_r : forall E F G,
  E \subset F ->
  ok (F ; G) ->
  E \subset F ; G.
Proof.
  intros. induction G using env_ind; env_solve.
Qed.

Hint Resolve subset_concat_r : core.

Lemma subset_push : forall E E' x T,
  E \subset E' ->
  ok (E' ; x ~ T) ->
  E ; x ~ T \subset E' ; x ~ T.
Proof.
  intros.
  induction H.
  - env_solve.
  - apply subset_push_l; env_solve. env_solve.
  - apply subset_push_l; env_solve.
Qed.

Hint Resolve subset_push : core.

Lemma subset_concat : forall E E' F,
  E \subset E' ->
  ok (E' ; F) ->
  E ; F \subset E' ; F.
Proof.
  intros. induction F using env_ind; env_solve.
Qed.

Hint Resolve subset_concat : core.

Lemma sameset_ok : forall E F,
  E [=] F ->
  ok E ->
  ok F.
Proof.
  intros. unfold sameset in H; env_solve.
Qed.

Hint Resolve sameset_ok : core.

Lemma notin_sameset : forall x E F,
  x # E ->
  E [=] F ->
  x # F.
Proof.
  intros. unfold sameset in H0; env_solve.
Qed.

Hint Resolve notin_sameset : core.


Lemma notin_sameset_concat : forall x E E' F,
  x # (E ; F) ->
  E [=] E' ->
  x # (E' ; F).
Proof.
  induction F using env_ind; env_solve.
Qed.

Hint Resolve notin_sameset_concat : core.

Lemma sameset_ok_concat_l : forall E E' F,
  E [=] E' ->
  ok (E; F) ->
  ok (E'; F).
Proof.
  induction F using env_ind; env_solve.
Qed.

Hint Resolve sameset_ok_concat_l : core.

Lemma sameset_ok_concat_r : forall E F F',
  F [=] F' ->
  ok (E; F) ->
  ok (E; F').
Proof.
  intros. apply ok_concat_comm.
  apply ok_concat_comm in H0. env_solve.
Qed.

Hint Resolve sameset_ok_concat_r : core.

Hint Unfold sameset : core.

Lemma sameset_concat : forall E E' F,
  E [=] E' ->
  ok (E ; F) ->
  E ; F [=] E' ; F.
Proof.
  unfold sameset; env_solve.
Qed.

Lemma subset_congruence: forall E F F',
  F \subset F' ->
  ok (E; F) ->
  ok (E; F') ->
  E; F \subset E; F'.
Proof.
  induction 1; env_solve.
  - constructor. assumption. apply binds_concat_right.
    assumption. env_solve. notin_dom_solve.
Qed.

Hint Resolve subset_congruence : core.

Lemma sameset_concat_r: forall E F F',
  F [=] F' ->
  ok (E ; F) ->
  E ; F [=] E ; F'.
Proof.
  intros. assert (ok (E ; F')). env_solve.
  unfold sameset; env_solve.
Qed.

Hint Resolve sameset_concat_r : core.

Hint Resolve sameset_concat : core.

Lemma sameset_refl: forall E,
  ok E ->
  E [=] E.
Proof.
  intros. induction H; env_solve.
Qed.

Hint Resolve sameset_refl : core.

Lemma sameset_push_comm : forall E x T,
  ok (E; x ~ T) ->
  E; x ~ T [=] x ~ T; E.
Proof.
  induction E using env_ind; env_solve.
  assert (E; x ~ v; x0 ~ T [=] E; x0 ~ T; x ~ v).
  apply sameset_comm. env_solve. notin_dom_solve.
  assert (E; x0 ~ T; x ~ v [=] x0 ~ T; (E; x ~ v)).
  rewrite concat_assoc.
  apply sameset_concat; env_solve. notin_dom_solve.
  apply notin_neq in H3. apply notin_neq. intuition.
  env_solve.
Qed.

Hint Resolve sameset_push_comm : core.

Hint Resolve ok_remove : core.
Hint Resolve ok_concat_comm : core.

Lemma sameset_concat_comm: forall E F,
  ok (E; F) ->
  E; F [=] F; E.
Proof.
  induction E using env_ind; env_solve.
  - simpl. unfold ";" in *. rewrite app_nil_r.
    rewrite app_nil_r in H.
    env_solve.
  - generalize (IHE (x ~ v; F)); intro.
    rewrite concat_assoc in H0. intuition.
    assert (x ~ v; F; E [=] F; (E; x ~ v)).
    rewrite concat_assoc.
    rewrite <-concat_assoc.
    apply sym_sameset.
    apply sameset_push_comm. env_solve.
    apply ok_middle_inv in H. notin_dom_solve.
    env_solve.
Qed.

Lemma sameset_congruence: forall E E1 E1' F,
  E1 [=] E1' ->
  E [=] E1; F ->
  E [=] E1' ; F.
Proof.
  env_solve.
Qed.

Hint Resolve sameset_congruence : core.

End SubsetDef.