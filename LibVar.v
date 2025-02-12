Set Implicit Arguments.

Require Import List.
Require Import Lia.
Require Import Arith.
Import ListNotations.

Definition var := nat.
Definition vars := list var.

Definition notin (x : var) E := ~ In x E.
Definition union (E : vars) F := F ++ E.

Declare Scope vars_scope.

Notation "\{}" := [] : vars_scope.
Notation "\{ x }" := ([x]) : vars_scope.
Notation "x \notin E" := (notin x E) (at level 39) : vars_scope.
Notation "E \u F" := (union E F) 
  (at level 37, right associativity) : vars_scope.
Notation "x \in E" := (In x E) (at level 39) : vars_scope.

Open Scope vars_scope.

Lemma notin_empty: forall x,
x \notin \{}.
Proof.
  intros. intro. destruct H.
Qed.

Ltac set_op := try apply notin_empty.

Section Properties.

Implicit Type E F : vars.


Lemma notin_add_E : forall x a E,
x \notin (a::E) -> x \notin E.
Proof.
  unfold "\notin". intros. intro. apply H.
  simpl. right. assumption.
Qed.

Lemma notin_neq: forall x1 x2,
x1 <> x2 <-> x1 \notin \{x2}.
Proof.
  split; intros.
  - intro. simpl in H0. destruct H0; intuition.
  - intro. apply H. subst. simpl; left; reflexivity.
Qed.

Lemma notin_add_a : forall x a E,
x \notin (a::E) -> x \notin \{a}.
Proof.
  intros. intro. apply H. simpl.
  simpl in H0. intuition.
Qed.

Lemma in_union : forall x E F,
x \in E \u F <-> x \in E \/ x \in F.
Proof.
  unfold "\u". induction F; simpl; intros; split; intros.
  - left. assumption.
  - destruct H. assumption. destruct H.
  - destruct H.
    -- subst. right; left; reflexivity.
    -- apply IHF in H. destruct H.
      --- auto.
      --- auto.
  - destruct H.
    -- right. apply IHF. left. assumption.
    -- destruct H.
      --- left. assumption.
      --- right. apply IHF. right. assumption.
Qed.

Lemma in_add : forall x a E,
x \in (a::E) -> x \in \{a} \/ x \in E.
Proof.
  simpl; intros. destruct H; intuition.
Qed.


Lemma notin_add : forall x a E,
x \notin (a::E) <-> x \notin \{a} /\ x \notin E.
Proof.
  intros. split. split;
  [apply notin_add_a with (E:=E)|apply notin_add_E with (a:=a)];
  assumption.
  intros. intro. destruct H. apply in_add in H0; intuition.
Qed.

Lemma notin_union_aux: forall x E F,
x \notin E \u F -> x \notin E.
Proof.
  induction E; simpl; intros.
  - intro. destruct H0.
  - intro. simpl in H0. destruct H0.
    -- subst. apply H. apply in_union.
      left. simpl. left. reflexivity.
    -- apply H. apply in_union. left.
      simpl. right. assumption.
Qed.

Lemma notin_union: forall x E F,
x \notin (E \u F) <-> x \notin E /\ x \notin F.
Proof.
  unfold "\u". induction F; simpl; split; intros.
  - constructor.
    -- auto.
    -- intro. destruct H0.
  - intuition.
  - constructor.
    -- intro. apply H. simpl. right.
      apply in_union. left. assumption.
    -- intro. apply H. simpl. simpl in H0.
      destruct H0.
      --- intuition.
      --- right. apply in_union. intuition.
  - intro. destruct H. apply in_add in H0.
    apply notin_add in H1. intuition. 
Qed.


Definition var_gen (l : vars) :=
  1 + fold_right plus O l.

Lemma var_gen_spec_aux: forall n E,
  n \in E -> n < var_gen E.
Proof.
  unfold var_gen; induction E; simpl; intro.
  - destruct H.
  - destruct H.
    -- rewrite H. lia.
    -- apply IHE in H. lia.
Qed.

Lemma var_gen_spec : forall E, (var_gen E) \notin E.
Proof.
  intros. induction E; simpl; intro.
  - simpl in H. destruct H.
  - simpl in H. destruct H.
    -- unfold var_gen in H. simpl in H. lia.
    -- apply var_gen_spec_aux in H.
      unfold var_gen in H. simpl in H. lia.
Qed.

Lemma var_fresh: forall (E : vars), { x : var | x \notin E}.
Proof.
  intros. exists (var_gen E). apply var_gen_spec.
Qed.

End Properties.

Fixpoint removeAll a A :=
  match A with
  | nil => nil
  | cons h t => if h =? a then removeAll a t
              else cons h (removeAll a t)
  end.

Fixpoint diff E F :=
  match F with
  | nil => E
  | cons h t => diff (removeAll h E) t
  end.

Notation "E \d F" := (diff E F) (at level 61).

Ltac if_solve :=
  repeat (match goal with
  | [H : ?a =? ?b = true |- context[if ?a =? ?b then _ else _]]
    => rewrite H
  | [H : ?a =? ?b = false |- context[if ?a =? ?b then _ else _]] 
    => rewrite H
  | [H : ?a <> ?b |- context[if ?a =? ?b then _ else _]] 
    => apply Nat.eqb_neq in H
  | [H : ?a = ?b |- context[if ?a =? ?b then _ else _]]
    => subst
  | [|- context[if ?a =? ?a then _ else _]]
    => rewrite (Nat.eqb_refl a)
  | [|- context[if ?a =? ?b then _ else _]]
    => destruct (eq_nat_dec a b)
  end; simpl); try reflexivity.

Lemma notin_removeAll : forall E a,
  a \notin E ->
  removeAll a E = E.
Proof.
  induction E; simpl; intros; auto.
  unfold notin in H. simpl in H.
  intuition. if_solve. intuition.
  apply IHE in H1. rewrite H1; reflexivity.
Qed.

Lemma notin_removeAll_1 : forall E a b,
  b \notin (removeAll a E) ->
  a \notin E ->
  b \notin E.
Proof.
  intros. apply notin_removeAll in H0.
  rewrite <-H0. assumption.
Qed.

Lemma in_dec : forall E (a : var),
  a \in E \/ ~ a \in E.
Proof.
  induction E; simpl; intros; auto.
  destruct (eq_nat_dec a a0).
  - subst. intuition.
  - generalize (IHE a0); intro.
    intuition.
Qed.

Lemma notin_removeAll_2 : forall E a b,
  b \notin (removeAll a E) ->
  a \in E ->
  b = a \/ b \notin E.
Proof.
  induction E; simpl; intros; auto.
  intuition.
  - subst. rewrite (Nat.eqb_refl a0) in H.
    destruct (eq_nat_dec b a0).
    -- intuition.
    -- right. generalize (in_dec E a0); intro.
      intuition.
      --- apply IHE in H; auto. intuition.
        unfold notin. simpl. intuition.
      --- generalize (notin_removeAll_1 H H1); intro.
        unfold notin. simpl. intuition.
  - destruct (a =? a0) eqn:Eaa.
    -- rewrite Nat.eqb_eq in Eaa. subst.
      destruct (eq_nat_dec b a0).
      --- intuition.
      --- apply IHE in H; auto. intuition.
        right. unfold notin. simpl. intuition.
    -- unfold notin in H. simpl in H. intuition.
      apply IHE in H2; auto. intuition.
      right. unfold notin. simpl. intuition.
Qed.

Lemma notin_removeAll_inv : forall E a b,
  b \notin (removeAll a E) ->
  b = a \/ b \notin E.
Proof.
  intros. destruct (in_dec E a).
  - apply notin_removeAll_2; auto.
  - right. eapply notin_removeAll_1; eauto.
Qed.