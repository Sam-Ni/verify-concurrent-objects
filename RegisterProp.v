Require Import
  List
  Arith
  LibVar
  LTS
  Register.
From VCO Require LibEnv.
Import ListNotations.

Section Properties.

Import LibEnv.

Definition RegStateWF st :=
  ok st.(requests) /\ ok st.(responses) /\
  (forall pid v, binds pid v st.(requests) -> pid # st.(responses)) /\
  (forall pid v, binds pid v st.(responses) -> pid # st.(requests))
  .

Definition _RegStateWF st :=
  ok st.(requests) /\ ok st.(responses)
  .

Lemma reg_initial_preserves_ok: forall st st' pid qb,
  RegStateWF st ->
  initial_state Register st pid qb st' ->
  RegStateWF st'.
Proof.
  - intros. unfold RegStateWF. inversion H0; subst; clear H0; simpl.
    -- unfold RegStateWF in H; simpl in H.
      intuition.
      --- econstructor; eauto.
      --- unfold binds in H6; simpl in H6.
        destruct (pid0 =? pid)eqn:Heq.
        + apply Nat.eqb_eq in Heq; subst.
          assumption.
        + eapply H5; eassumption.
      --- eapply notin_union; eauto.
        assert (pid0 <> pid).
        intro. subst.
        eapply binds_fresh_inv in H6. intuition. assumption.
        apply H7 in H6. intuition.
        apply notin_neq; intuition.
    -- unfold RegStateWF in H; simpl in H.
      intuition.
      --- econstructor; eauto.
      --- unfold binds in H6; simpl in H6.
        destruct (pid0 =? pid)eqn:Heq.
        + apply Nat.eqb_eq in Heq; subst.
          assumption.
        + eapply H5; eassumption.
      --- eapply notin_union; eauto.
        assert (pid0 <> pid).
        intro. subst.
        eapply binds_fresh_inv in H6. intuition. assumption.
        apply H7 in H6. intuition.
        apply notin_neq; intuition.
Qed.
        
Lemma _reg_initial_preserves_ok: forall st st' pid qb,
  initial_state Register st pid qb st' ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold _RegStateWF; simpl; intuition;
  econstructor; eauto.
Qed.

Lemma reg_final_preserves_ok: forall st st' pid rb,
  RegStateWF st ->
  final_state Register st pid rb st' ->
  RegStateWF st'.
Proof.
  - intros. unfold RegStateWF. inversion H0; subst; clear H0; simpl.
    -- unfold RegStateWF in H; simpl in H.
      intuition.
      --- apply ok_remove in H3; eauto.
      --- apply H1 in H4.
        apply notin_concat.
        apply notin_concat in H4. intuition.
        apply notin_dom_push in H6. intuition.
      --- destruct (Nat.eq_dec pid0 pid).
        + subst. apply ok_middle_inv in H3.
          apply notin_concat in H3.
          apply binds_fresh_inv in H4. inversion H4.
          assumption.
        + eapply H5.
          unfold binds. rewrite get_notin_eq; intuition.
          unfold binds; eassumption.
    -- unfold RegStateWF in H; simpl in H.
      intuition.
      --- apply ok_remove in H3; eauto.
      --- apply H1 in H4.
        apply notin_concat.
        apply notin_concat in H4. intuition.
        apply notin_dom_push in H6. intuition.
      --- destruct (Nat.eq_dec pid0 pid).
        + subst. apply ok_middle_inv in H3.
          apply notin_concat in H3.
          apply binds_fresh_inv in H4. inversion H4.
          assumption.
        + eapply H5.
          unfold binds. rewrite get_notin_eq; intuition.
          unfold binds; eassumption.
Qed.

Lemma _reg_final_preserves_ok: forall st st' pid rb,
  final_state Register st pid rb st' ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold _RegStateWF; simpl; intuition;
  apply ok_remove in H2; intuition.
Qed.

Lemma reg_at_external_preserves_ok: forall st st' pid qa,
  RegStateWF st ->
  at_external Register st pid qa st' ->
  RegStateWF st'.
Proof.
  - intros. unfold RegStateWF. inversion H0; subst; clear H0; simpl.
Qed.

Lemma _reg_at_external_preserves_ok: forall st st' pid qa,
  at_external Register st pid qa st' ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold _RegStateWF; simpl; intuition;
  apply ok_remove in H2; intuition.
Qed.

Lemma reg_after_external_preserves_ok: forall st st' pid ra,
  RegStateWF st ->
  after_external Register st pid ra st' ->
  RegStateWF st'.
Proof.
  - intros. unfold RegStateWF. inversion H0; subst; clear H0; simpl.
Qed.

Lemma _reg_after_external_preserves_ok: forall st st' pid ra,
  after_external Register st pid ra st' ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegStateWF; simpl; intuition;
  apply ok_remove in H2; intuition.
Qed.

Lemma reg_step_preserves_ok: forall st st' pid int,
  RegStateWF st ->
  step Register st pid int st' ->
  RegStateWF st'.
Proof.
  - intros. unfold RegStateWF. inversion H0; subst; clear H0; simpl.
    -- unfold RegStateWF in H; simpl in H.
      intuition.
      --- apply ok_remove in H2; eauto.
      --- econstructor; eauto.
      --- eapply notin_union; eauto.
        assert (pid0 <> pid).
        intro. subst.
        eapply binds_fresh_inv in H5. intuition.
        apply notin_concat.
        eapply ok_middle_inv in H2; eauto.
        assert (binds pid0 v0 (inv' ++ (pid, RegCAS old new) :: inv'')).
        unfold binds.
        rewrite get_notin_eq. assumption.
        assumption.
        apply H1 in H8. intuition.
        apply notin_neq; auto.
      --- unfold binds in H5. simpl in H5.
        destruct (pid0 =? pid)eqn:Heq.
        + apply Nat.eqb_eq in Heq. subst.
          apply notin_concat.
          eapply ok_middle_inv in H2; eauto.
        + apply H6 in H5.
          apply notin_concat.
          apply notin_concat in H5. intuition.
          apply notin_dom_push in H7. intuition.
    -- unfold RegStateWF in H; simpl in H.
      intuition.
      --- apply ok_remove in H2; eauto.
      --- econstructor; eauto.
      --- eapply notin_union; eauto.
        assert (pid0 <> pid).
        intro. subst.
        eapply binds_fresh_inv in H5. intuition.
        apply notin_concat.
        eapply ok_middle_inv in H2; eauto.
        assert (binds pid0 v0 (inv' ++ (pid, RegRead) :: inv'')).
        unfold binds.
        rewrite get_notin_eq. assumption.
        assumption.
        apply H1 in H8. intuition.
        apply notin_neq; auto.
      --- unfold binds in H5. simpl in H5.
        destruct (pid0 =? pid)eqn:Heq.
        + apply Nat.eqb_eq in Heq. subst.
          apply notin_concat.
          eapply ok_middle_inv in H2; eauto.
        + apply H6 in H5.
          apply notin_concat.
          apply notin_concat in H5. intuition.
          apply notin_dom_push in H7. intuition.
Qed.

Lemma _reg_step_preserves_ok: forall st st' pid int,
  step Register st pid int st' ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  inversion 1; intros; subst; simpl;
  unfold _RegStateWF; simpl; intuition;
  apply ok_remove in H1; intuition;
  econstructor; eauto.
Qed.

Lemma reg_ok_inv: invariant_ind Register RegStateWF.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold RegStateWF.
    unfold new_register.
    simpl. intuition.
    constructor.
    constructor.
    apply notin_empty.
    apply notin_empty.
  - eapply reg_step_preserves_ok; eauto.
  - eapply reg_initial_preserves_ok; eauto.
  - eapply reg_at_external_preserves_ok; eauto.
  - eapply reg_after_external_preserves_ok; eauto.
  - eapply reg_final_preserves_ok; eauto.
Qed.

Lemma astep_preserves_ok: forall st st',
  automaton_step Register st st' ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  intros. unfold automaton_step in H.
  destruct H as [pid Htmp]. intuition.
  - destruct H as [a Ha].
    eapply _reg_initial_preserves_ok; eauto.
  - destruct H1 as [a Ha].
    eapply _reg_final_preserves_ok; eauto.
  - destruct H as [a Ha].
    eapply _reg_at_external_preserves_ok; eauto.
  - destruct H1 as [a Ha].
    eapply _reg_after_external_preserves_ok; eauto.
  - destruct H1 as [a Ha].
    eapply _reg_step_preserves_ok; eauto.
Qed.

Lemma valid_execution_preserves_ok: forall st st' acts in_acts,
  valid_execution_fragment Register st st' acts in_acts ->
  _RegStateWF st ->
  _RegStateWF st'.
Proof.
  induction 1; simpl; intros.
  - subst; auto.
  - eapply _reg_step_preserves_ok in H; eauto.
  - eapply _reg_at_external_preserves_ok in H; eauto.
  - eapply _reg_after_external_preserves_ok in H; eauto.
  - eapply _reg_initial_preserves_ok in H; eauto.
  - eapply _reg_final_preserves_ok in H; eauto.
Qed.
  
Lemma reachable_inv: forall st,
  reachable Register st ->
  _RegStateWF st.
Proof.
  intros. unfold reachable in H.
  destruct H as [init [acts [in_acts [Hnew Hexe]]]].
  eapply valid_execution_preserves_ok; eauto.
  inversion Hnew; subst.
  unfold new_register.
  unfold _RegStateWF. simpl. intuition; econstructor.
Qed.

Lemma _reg_ok_inv: invariant_ind Register _RegStateWF.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold RegStateWF.
    unfold new_register.
    simpl. constructor; constructor.
  - eapply _reg_step_preserves_ok; eauto.
  - eapply _reg_initial_preserves_ok; eauto.
  - eapply _reg_at_external_preserves_ok; eauto.
  - eapply _reg_after_external_preserves_ok; eauto.
  - eapply _reg_final_preserves_ok; eauto.
Qed.

Lemma binds_same: forall (req: env Register_query) pid qb qb',
  ok req ->
  binds pid qb req ->
  binds pid qb' req ->
  qb = qb'.
Proof.
  induction 1; simpl; intros.
  - inversion H.
  - unfold binds in H1, H2. simpl in H1, H2.
    destruct (pid =? x)eqn:Heq.
    -- inversion H1; inversion H2; subst; auto.
    -- apply IHok; eauto.
Qed.

Lemma internal_preserves_notin: forall acts in_acts pid st st',
  gather_pid_external_events acts pid = [] ->
  pid # st.(requests) ->
  valid_execution_fragment Register st st' acts in_acts ->
  pid # st'.(requests).
Proof.
  intros.
  induction H1.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    eapply notin_dom_subset; eauto.
    simpl in H1. inversion H1; subst.
    -- simpl requests.
      eapply subset_concat.
      apply ok_concat_inv in H4.
      destruct H4.
      econstructor; eauto.
      econstructor; eauto.
      apply ok_concat_inv in H3. intuition.
      intuition.
    -- simpl requests.
      eapply subset_concat.
      apply ok_concat_inv in H4.
      destruct H4.
      econstructor; eauto.
      econstructor; eauto.
      apply ok_concat_inv in H3. intuition.
      intuition.
  - inversion H1.
  - inversion H1.
  - simpl in H.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H.
    -- apply IHvalid_execution_fragment; auto.
      simpl in H1.
      inversion H1; subst.
      + simpl requests.
        simpl.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply Nat.eqb_neq. assumption.
      + simpl requests.
        simpl.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply Nat.eqb_neq. assumption.
  - simpl in H.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H.
    -- apply IHvalid_execution_fragment; auto.
      simpl in H1.
      inversion H1; subst; simpl; assumption.
Qed.

Lemma initial_preserves_binds: forall st st' pid qb pid' qb',
  binds pid qb st.(requests) ->
  initial_state Register st pid' qb' st' ->
  pid <> pid' ->
  binds pid qb st'.(requests).
Proof.
  inversion 2; subst; simpl; intros;
  apply binds_push_neq; auto.
Qed.

Lemma final_preserves_binds: forall st st' pid rb pid' rb',
  binds pid rb st.(requests) ->
  final_state Register st pid' rb' st' ->
  pid <> pid' ->
  binds pid rb st'.(requests).
Proof.
  inversion 2; subst; simpl; intros;
  auto.
Qed.

Lemma internal_preserves_request: forall acts in_acts pid st st' qb qb',
  gather_pid_external_events acts pid = [] ->
  binds pid qb st.(requests) ->
  _RegStateWF st ->
  binds pid qb' st'.(requests) ->
  valid_execution_fragment Register st st' acts in_acts ->
  qb = qb'.
Proof.
  intros. induction H3.
  - subst. eapply binds_same; eauto.
    unfold _RegStateWF in H1; intuition.
  - eapply IHvalid_execution_fragment; eauto.
    destruct (pid =? pid0)eqn:Heq.
    -- assert (pid # st'.(requests)).
      eapply internal_preserves_notin; eauto.
      simpl in H3.
      apply Nat.eqb_eq in Heq. subst.
      inversion H3; subst.
      + simpl requests.
        apply ok_middle_inv in H6.
        apply notin_concat; eauto.
      + simpl requests.
        apply ok_middle_inv in H6.
        apply notin_concat; eauto.
      + apply binds_fresh_inv in H2; intuition.
    -- simpl in H3. inversion H3; subst; simpl.
      + simpl in H0.
        eapply binds_remove with (E2:=[(pid0, RegCAS old new)]); simpl; eauto.
        apply notin_neq. apply Nat.eqb_neq. assumption.
      + simpl in H0.
        eapply binds_remove with (E2:=[(pid0, RegRead)]); simpl; eauto.
        apply notin_neq. apply Nat.eqb_neq. assumption.
    -- eapply _reg_step_preserves_ok; eauto.
  - inversion H3.
  - inversion H3.
  - simpl in H.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H.
    -- apply IHvalid_execution_fragment; auto.
      eapply initial_preserves_binds; eauto.
      apply Nat.eqb_neq; auto.
      eapply _reg_initial_preserves_ok; eauto.
  - simpl in H.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H.
    -- apply IHvalid_execution_fragment; auto.
      eapply final_preserves_binds; eauto.
      apply Nat.eqb_neq; auto.
      eapply _reg_final_preserves_ok; eauto.
Qed.

End Properties.
