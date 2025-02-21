Require Import
  List
  LTS
  Arith
  LibVar
  LibEnv
  Refinement
  Register
  RegisterProp
  RegisterCounterImpl
  RegisterCounterImplProp
  Counter.
Import ListNotations.

(* 
  Prove that the composition of register_counter_impl (RegisterCounterImpl.v) and register (Register.v)
  refines the atomic counter (Counter.v).
*)
Section RegisterCounter.

Definition register_counter : lts li_null li_counter := linked_lts Register register_counter_impl.

Lemma step_preserves_binds_DInc5: forall st st' pid pid' int,
  binds pid DInc5 st.(pc) ->
  step register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DInc5 st'.(pc).
Proof.
  inversion 2; intros; subst;
  eapply binds_neq_middle; eauto.
Qed.

Lemma at_external_preserves_binds_DInc5: forall st st' pid pid' int,
  binds pid DInc5 st.(pc) ->
  at_external register_counter_impl st pid' int st' ->
  binds pid DInc5 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
  - inversion H0; intros; subst;
    eapply binds_neq_middle; eauto.
Qed.

Lemma after_external_preserves_binds_DInc5: forall st st' pid pid' int,
  binds pid DInc5 st.(pc) ->
  after_external register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DInc5 st'.(pc).
Proof.
  inversion 2; intros; subst;
  eapply binds_neq_middle; eauto.
Qed.

Lemma initial_preserves_binds_DInc5: forall st st' pid pid' int,
  binds pid DInc5 st.(pc) ->
  initial_state register_counter_impl st pid' int st' ->
  binds pid DInc5 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *;
    apply binds_in in H; unfold "#" in H2; intuition.
  - inversion H0; subst; simpl in *;
    eapply binds_push_neq; eauto.
Qed.

Lemma final_preserves_binds_DInc5: forall st st' pid pid' int,
  binds pid DInc5 st.(pc) ->
  final_state register_counter_impl st pid' int st' ->
  binds pid DInc5 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
  - inversion H0; intros; subst;
    eapply binds_remove; eauto;
    apply notin_neq; eauto.
Qed.

Lemma no_action_preserves_DInc5 : forall st st' pid acts in_acts,
  binds pid DInc5 st.(pc) ->
  gather_pid_internal_events in_acts pid = [] ->
  gather_pid_external_events acts pid = [] ->
  valid_execution_fragment register_counter_impl st st' acts in_acts ->
  binds pid DInc5 st'.(pc).
Proof.
  intros. induction H2.
  - subst. assumption.
  - simpl in H0.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H0.
    -- apply IHvalid_execution_fragment; auto.
      eapply step_preserves_binds_DInc5; eauto.
      eapply Nat.eqb_neq; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply at_external_preserves_binds_DInc5; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply after_external_preserves_binds_DInc5; eauto.
      eapply Nat.eqb_neq; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply initial_preserves_binds_DInc5; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply final_preserves_binds_DInc5; eauto.
Qed.

Lemma step_preserves_binds_DInc2: forall st st' pid pid' int,
  binds pid DInc2 st.(pc) ->
  step register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DInc2 st'.(pc).
Proof.
  inversion 2; intros; subst;
  eapply binds_neq_middle; eauto.
Qed.

Lemma at_external_preserves_binds_DInc2: forall st st' pid pid' int,
  binds pid DInc2 st.(pc) ->
  at_external register_counter_impl st pid' int st' ->
  binds pid DInc2 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
  - inversion H0; intros; subst;
    eapply binds_neq_middle; eauto.
Qed.

Lemma after_external_preserves_binds_DInc2: forall st st' pid pid' int,
  binds pid DInc2 st.(pc) ->
  after_external register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DInc2 st'.(pc).
Proof.
  inversion 2; intros; subst;
  eapply binds_neq_middle; eauto.
Qed.

Lemma initial_preserves_binds_DInc2: forall st st' pid pid' int,
  binds pid DInc2 st.(pc) ->
  initial_state register_counter_impl st pid' int st' ->
  binds pid DInc2 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *;
    apply binds_in in H; unfold "#" in H2; intuition.
  - inversion H0; subst; simpl in *;
    eapply binds_push_neq; eauto.
Qed.

Lemma final_preserves_binds_DInc2: forall st st' pid pid' int,
  binds pid DInc2 st.(pc) ->
  final_state register_counter_impl st pid' int st' ->
  binds pid DInc2 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
  - inversion H0; intros; subst;
    eapply binds_remove; eauto;
    apply notin_neq; eauto.
Qed.

Lemma no_action_preserves_DInc2 : forall st st' pid acts in_acts,
  binds pid DInc2 st.(pc) ->
  gather_pid_internal_events in_acts pid = [] ->
  gather_pid_external_events acts pid = [] ->
  valid_execution_fragment register_counter_impl st st' acts in_acts ->
  binds pid DInc2 st'.(pc).
Proof.
  intros. induction H2.
  - subst. assumption.
  - simpl in H0.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H0.
    -- apply IHvalid_execution_fragment; auto.
      eapply step_preserves_binds_DInc2; eauto.
      eapply Nat.eqb_neq; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply at_external_preserves_binds_DInc2; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply after_external_preserves_binds_DInc2; eauto.
      eapply Nat.eqb_neq; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply initial_preserves_binds_DInc2; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply final_preserves_binds_DInc2; eauto.
Qed.

Lemma step_preserves_binds_DRead2: forall st st' pid pid' int,
  binds pid DRead2 st.(pc) ->
  step register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DRead2 st'.(pc).
Proof.
  inversion 2; intros; subst;
  eapply binds_neq_middle; eauto.
Qed.

Lemma at_external_preserves_binds_DRead2: forall st st' pid pid' int,
  binds pid DRead2 st.(pc) ->
  at_external register_counter_impl st pid' int st' ->
  binds pid DRead2 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
  - inversion H0; intros; subst;
    eapply binds_neq_middle; eauto.
Qed.

Lemma after_external_preserves_binds_DRead2: forall st st' pid pid' int,
  binds pid DRead2 st.(pc) ->
  after_external register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DRead2 st'.(pc).
Proof.
  inversion 2; intros; subst;
  eapply binds_neq_middle; eauto.
Qed.

Lemma initial_preserves_binds_DRead2: forall st st' pid pid' int,
  binds pid DRead2 st.(pc) ->
  initial_state register_counter_impl st pid' int st' ->
  binds pid DRead2 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *;
    apply binds_in in H; unfold "#" in H2; intuition.
  - inversion H0; subst; simpl in *;
    eapply binds_push_neq; eauto.
Qed.

Lemma final_preserves_binds_DRead2: forall st st' pid pid' int,
  binds pid DRead2 st.(pc) ->
  final_state register_counter_impl st pid' int st' ->
  binds pid DRead2 st'.(pc).
Proof.
  intros.
  destruct (Nat.eq_dec pid pid').
  - subst. inversion H0; subst; simpl in *.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
    -- apply binds_concat_inv in H. intuition.
      --- eapply binds_concat_right; eauto.
      --- unfold binds in H2. simpl in H2.
        rewrite Nat.eqb_refl in H2. inversion H2.
  - inversion H0; intros; subst;
    eapply binds_remove; eauto;
    apply notin_neq; eauto.
Qed.

Lemma no_action_preserves_DRead2 : forall st st' pid acts in_acts,
  binds pid DRead2 st.(pc) ->
  gather_pid_internal_events in_acts pid = [] ->
  gather_pid_external_events acts pid = [] ->
  valid_execution_fragment register_counter_impl st st' acts in_acts ->
  binds pid DRead2 st'.(pc).
Proof.
  intros. induction H2.
  - subst. assumption.
  - simpl in H0.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H0.
    -- apply IHvalid_execution_fragment; auto.
      eapply step_preserves_binds_DRead2; eauto.
      eapply Nat.eqb_neq; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply at_external_preserves_binds_DRead2; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply after_external_preserves_binds_DRead2; eauto.
      eapply Nat.eqb_neq; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply initial_preserves_binds_DRead2; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H1.
    -- apply IHvalid_execution_fragment; auto.
      eapply final_preserves_binds_DRead2; eauto.
Qed.

End RegisterCounter.