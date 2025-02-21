Require Import 
  List
  Nat
  LTS
  Counter
  Register
  LibVar
  RegisterCounterImpl
.
Require 
  LibEnv.
Import ListNotations.
Section Properties.

Import LibEnv.
  
Definition RegCntImplStateWF st :=
  ok st.(pc).

Lemma regcntimpl_initial_preserves_ok: forall st st' pid qb,
  initial_state register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF; simpl; intuition;
  econstructor; eauto.
Qed.

Lemma regcntimpl_final_preserves_ok: forall st st' pid qb,
  final_state register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
    apply ok_remove in H7; intuition.
Qed.

Lemma regcntimpl_at_external_preserves_ok: forall st st' pid qb,
  at_external register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  simpl in H7;
  eapply ok_middle; eauto.
Qed.

Lemma regcntimpl_after_external_preserves_ok: forall st st' pid qb,
  after_external register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  simpl in H7;
  eapply ok_middle; eauto.
Qed.

Lemma regcntimpl_step_preserves_ok: forall st st' pid qb,
  step register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  simpl in H7;
  eapply ok_middle; eauto.
Qed.

Lemma regcntimpl_ok_inv: invariant_ind register_counter_impl RegCntImplStateWF.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold RegCntImplStateWF.
    unfold new_register_counter.
    simpl. constructor.
  - eapply regcntimpl_step_preserves_ok; eauto.
  - eapply regcntimpl_initial_preserves_ok; eauto.
  - eapply regcntimpl_at_external_preserves_ok; eauto.
  - eapply regcntimpl_after_external_preserves_ok; eauto.
  - eapply regcntimpl_final_preserves_ok; eauto.
Qed.

Lemma regcntimpl_valid_execution_preserves_ok: forall st st' acts in_acts,
  valid_execution_fragment register_counter_impl st st' acts in_acts ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  induction 1; simpl; intros.
  - subst; auto.
  - eapply regcntimpl_step_preserves_ok in H; eauto.
  - eapply regcntimpl_at_external_preserves_ok in H; eauto.
  - eapply regcntimpl_after_external_preserves_ok in H; eauto.
  - eapply regcntimpl_initial_preserves_ok in H; eauto.
  - eapply regcntimpl_final_preserves_ok in H; eauto.
Qed.

Lemma regcntimpl_reachable_inv: forall st,
  reachable register_counter_impl st ->
  RegCntImplStateWF st.
Proof.
  intros. unfold reachable in H.
  destruct H as [init [acts [in_acts [Hnew Hexe]]]].
  eapply regcntimpl_valid_execution_preserves_ok; eauto.
  inversion Hnew; subst.
  unfold new_register_counter.
  unfold RegCntImplStateWF. simpl. intuition; econstructor.
Qed.

End Properties.
