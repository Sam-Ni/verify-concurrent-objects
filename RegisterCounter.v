Require Import
  List
  LTS
  Arith
  LibVar
  LibEnv
  Refinement
  Register
  RegisterCounterImpl
  Counter.
Import ListNotations.

(* 
  Prove that the composition of register_counter_impl (RegisterCounterImpl.v) and register (Register.v)
  refines the atomic counter (Counter.v).
*)
Section RegisterCounter.

Definition register_counter : lts li_null li_counter := linked_lts Register register_counter_impl.

Definition no_inv_from_return (st' : register_counter.(state)) :=
  forall (st : register_counter.(state)) pid ra,
  linked_after_external st pid ra st' ->
  pid # st'.(L1State).(Register.requests).

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

Fixpoint gather_requests' (pc : LibEnv.env RCounter_pc) (regst : state Register) : LibEnv.env Counter_query :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let requests' := gather_requests' pc' regst in
      let (pid, inst) := ins in
        (match inst with
        | DInc1 => (pid, CntInc)::requests'
        | DInc2 => (pid, CntInc)::requests'
        | DInc3 _ => (pid, CntInc)::requests'
        | DInc4 => (pid, CntInc)::requests'
        | DInc5 => match get pid regst.(Register.requests) with
                  | None => match get pid regst.(Register.responses) with
                            | None => (pid, CntInc)::requests'
                            | Some res => match res with
                                          | RegCASOk b => if b then requests' else (pid, CntInc)::requests'
                                          | RegReadOk _ => (pid, CntInc)::requests'
                                          end
                            end
                  | Some _ => (pid, CntInc)::requests'
                  end
        | DInc6 ret => match ret with
                      | true => requests'
                      | false => (pid, CntInc)::requests'
                      end
        | DInc7 => requests'
        | DRead1 => (pid, CntRead)::requests'
        | DRead2 => match get pid regst.(Register.requests) with
                  | None => match get pid regst.(Register.responses) with
                            | None => (pid, CntRead)::requests'
                            | Some res => match res with
                                          | RegCASOk _ => (pid, CntRead)::requests'
                                          | RegReadOk _ => requests'
                                          end
                            end
                  | Some _ => (pid, CntRead)::requests'
                  end
        | DRead3 _ => requests'
        end)
  end.

Fixpoint gather_responses' (pc : LibEnv.env RCounter_pc) (regst : state Register) : LibEnv.env Counter_reply :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let responses' := gather_responses' pc' regst in
      let (pid, inst) := ins in
        (match inst with
        | DInc1 => responses' 
        | DInc2 => responses' 
        | DInc3 _ => responses' 
        | DInc4 => responses'
        | DInc5 => match get pid regst.(Register.requests) with
                  | None => match get pid regst.(Register.responses) with
                            | None => responses'
                            | Some res => match res with
                                          | RegCASOk b => if b then (pid, CntIncOk)::responses' else responses'
                                          | RegReadOk _ => responses'
                                          end
                            end
                  | Some _ => responses'
                  end
        | DInc6 ret => match ret with
                      | true => (pid, CntIncOk)::responses'
                      | false => responses'
                      end
        | DInc7 => (pid, CntIncOk)::responses'
        | DRead1 => responses' 
        | DRead2 => match get pid regst.(Register.requests) with
                  | None => match get pid regst.(Register.responses) with
                            | None => responses'
                            | Some res => match res with
                                          | RegCASOk _ => responses'
                                          | RegReadOk ret => (pid, CntReadOk ret)::responses'
                                          end
                            end
                  | Some _ => responses'
                  end
        | DRead3 ret => (pid, CntReadOk ret)::responses'
        end)
  end.

Lemma gather_requests_preserves_pid_notin': forall pc pid regst,
  pid # pc ->
  pid # gather_requests' pc regst.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    eapply IHpc in H1.
    destruct r; simpl; try apply notin_union; eauto.
    -- destruct (get v (Register.requests regst)).
      + simpl. apply notin_union; eauto.
      + destruct (get v (Register.responses regst)).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
          +++ simpl. apply notin_union; auto.
        ++ simpl. apply notin_union; auto.
    -- destruct ret; eauto. simpl. apply notin_union; eauto.
    -- destruct (get v (Register.requests regst)).
      + simpl. apply notin_union; eauto.
      + destruct (get v (Register.responses regst)).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
            apply notin_union; auto.
          +++ assumption.
        ++ simpl. apply notin_union; auto.
Qed.

Lemma gather_responses_preserves_pid_notin': forall pc pid regst,
  pid # pc ->
  pid # gather_responses' pc regst.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    eapply IHpc in H1.
    destruct r; simpl; try apply notin_union; eauto.
    -- destruct (get v (Register.requests regst)).
      + assumption.
      + destruct (get v (Register.responses regst)).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
          +++ assumption.
        ++ assumption.
    -- destruct ret; eauto. simpl. apply notin_union; eauto.
    -- destruct (get v (Register.requests regst)).
      + assumption.
      + destruct (get v (Register.responses regst)).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
          +++ apply notin_union; auto.
        ++ assumption.
Qed.

Lemma gather_requests_dist': forall pc pc' regst,
  gather_requests' (pc ++ pc') regst =
  gather_requests' pc regst ++ gather_requests' pc' regst.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct r; simpl; rewrite IHpc; try reflexivity.
    -- destruct (get v (Register.requests regst)); simpl.
      + reflexivity.
      + destruct (get v (Register.responses regst)); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct ret; reflexivity.
    -- destruct (get v (Register.requests regst)); simpl.
      + reflexivity.
      + destruct (get v (Register.responses regst)); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
Qed.

Lemma gather_responses_dist': forall pc pc' regst,
  gather_responses' (pc ++ pc') regst =
  gather_responses' pc regst ++ gather_responses' pc' regst.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct r; simpl; rewrite IHpc; try reflexivity.
    -- destruct (get v (Register.requests regst)); simpl.
      + reflexivity.
      + destruct (get v (Register.responses regst)); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct ret; reflexivity.
    -- destruct (get v (Register.requests regst)); simpl.
      + reflexivity.
      + destruct (get v (Register.responses regst)); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
Qed.

Lemma gather_requests_notin_req: forall pc pid inv res v pid_inv,
  pid # pc ->
  gather_requests' pc (mkRegState ((pid, pid_inv) :: inv) res v) =
  gather_requests' pc (mkRegState inv res v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- f_equal; eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success.
          +++ eapply IHpc; eauto.
          +++ f_equal; eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- f_equal; eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
Qed.

Lemma gather_responses_notin_req: forall pc pid inv res v pid_inv,
  pid # pc ->
  gather_responses' pc (mkRegState ((pid, pid_inv) :: inv) res v) =
  gather_responses' pc (mkRegState inv res v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
          +++ eapply IHpc; eauto.
          +++ eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        eapply IHpc; eauto.
Qed.

Lemma gather_requests_notin_res: forall pc pid inv res v pid_res,
  pid # pc ->
  gather_requests' pc (mkRegState inv ((pid, pid_res) :: res) v) =
  gather_requests' pc (mkRegState inv res v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- f_equal; eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success.
          +++ eapply IHpc; eauto.
          +++ f_equal; eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- f_equal; eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
Qed.

Lemma gather_responses_notin_res: forall pc pid inv res v pid_res,
  pid # pc ->
  gather_responses' pc (mkRegState inv ((pid, pid_res) :: res) v) =
  gather_responses' pc (mkRegState inv res v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
          +++ eapply IHpc; eauto.
          +++ eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      destruct (get x inv); simpl.
      --- eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        eapply IHpc; eauto.
Qed.

Lemma gather_requests_notin_env: forall pc pid inv inv' res v pid_inv,
  pid # pc ->
  gather_requests' pc (mkRegState (inv ++ (pid, pid_inv) :: inv') res v) =
  gather_requests' pc (mkRegState (inv ++ inv') res v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- rewrite get_notin_eq.
      (* assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition . *)
      destruct (get x (inv ++ inv'));simpl; try (f_equal; eapply IHpc; eauto).
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
      --- apply notin_neq in H0; intuition.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      rewrite get_notin_eq; intuition.
      destruct (get x (inv ++ inv')); simpl; try (f_equal; eapply IHpc; eauto).
      destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto).
        (* destruct success; simpl; try (f_equal; eapply IHpc; eauto). *)
        eapply IHpc; eauto.
Qed.

Lemma gather_requests_notin_env': forall pc pid inv res res' v pid_res,
  pid # pc ->
  gather_requests' pc (mkRegState inv (res ++ (pid, pid_res):: res') v) =
  gather_requests' pc (mkRegState inv (res ++ res') v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- rewrite get_notin_eq.
      (* assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition . *)
      destruct (get x inv);simpl; try (f_equal; eapply IHpc; eauto).
      --- destruct (get x (res ++ res')); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
      --- apply notin_neq in H0; intuition.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      rewrite get_notin_eq; intuition.
      destruct (get x inv); simpl; try (f_equal; eapply IHpc; eauto).
      destruct (get x (res ++ res')); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto).
        (* destruct success; simpl; try (f_equal; eapply IHpc; eauto). *)
        eapply IHpc; eauto.
Qed.

Lemma gather_responses_notin_env: forall pc pid inv inv' res v pid_inv,
  pid # pc ->
  gather_responses' pc (mkRegState (inv ++ (pid, pid_inv) :: inv') res v) =
  gather_responses' pc (mkRegState (inv ++ inv') res v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- rewrite get_notin_eq.
      destruct (get x (inv ++ inv'));simpl; try (f_equal; eapply IHpc; eauto).
      --- eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
        eapply IHpc; eauto.
      --- apply notin_neq in H0; intuition.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      rewrite get_notin_eq; intuition.
      destruct (get x (inv ++ inv'));simpl; try (f_equal; eapply IHpc; eauto).
      --- eapply IHpc; eauto.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        (* destruct success; simpl; try (f_equal; eapply IHpc; eauto). *)
        eapply IHpc; eauto.
Qed.

Lemma gather_responses_notin_env': forall pc pid inv res res' v pid_res,
  pid # pc ->
  gather_responses' pc (mkRegState inv (res ++ (pid, pid_res):: res') v) =
  gather_responses' pc (mkRegState inv (res ++ res') v).
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- rewrite get_notin_eq.
      destruct (get x inv);simpl; try (f_equal; eapply IHpc; eauto).
      --- eapply IHpc; eauto.
      --- destruct (get x (res ++ res')); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
        eapply IHpc; eauto.
      --- apply notin_neq in H0; intuition.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      rewrite get_notin_eq; intuition.
      destruct (get x inv);simpl; try (f_equal; eapply IHpc; eauto).
      --- eapply IHpc; eauto.
      --- destruct (get x (res ++ res')); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        (* destruct success; simpl; try (f_equal; eapply IHpc; eauto). *)
        eapply IHpc; eauto.
Qed.

Lemma gather_requests_any_v_reg: forall pc inv res v v',
  gather_requests' pc (mkRegState inv res v) =
  gather_requests' pc (mkRegState inv res v').
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - destruct v; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
    -- destruct (get x inv); simpl; try (f_equal; eapply IHpc; eauto).
      destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
      destruct r; simpl; try (f_equal; eapply IHpc; eauto).
      destruct success; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- destruct (get x inv); simpl; try (f_equal; eapply IHpc; eauto).
      destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
      destruct r; simpl; try (f_equal; eapply IHpc; eauto).
      (* destruct success; simpl; try (f_equal; eapply IHpc; eauto). *)
      eapply IHpc; eauto.
Qed.

Lemma gather_responses_any_v_reg: forall pc inv res v v',
  gather_responses' pc (mkRegState inv res v) =
  gather_responses' pc (mkRegState inv res v').
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - destruct v; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
    -- destruct (get x inv); simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
      destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
      destruct r; simpl; try (f_equal; eapply IHpc; eauto).
      destruct success; simpl; try (f_equal; eapply IHpc; eauto).
      all : eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- destruct (get x inv); simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
      destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
      destruct r; simpl; try (f_equal; eapply IHpc; eauto).
      destruct success; simpl; try (f_equal; eapply IHpc; eauto).
      all : eapply IHpc; eauto.
Qed.

Lemma gather_requests_preserves_ok: forall pc regst,
  ok pc ->
  ok (gather_requests' pc regst).
Proof.
  induction pc using env_ind; simpl; intros.
  - constructor.
  - inversion H; subst. destruct v; simpl.
    all : try (econstructor; eauto).
    all : try (eapply gather_requests_preserves_pid_notin'; eauto).
    -- destruct (get x (Register.requests regst)); simpl.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
      destruct (get x (Register.responses regst)).
      destruct r; simpl. destruct success; simpl.
      eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
    -- destruct ret; simpl.
      eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
    -- eauto.
    -- destruct (get x (Register.requests regst)); simpl.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
      destruct (get x (Register.responses regst)).
      destruct r; simpl. destruct success; simpl.
      eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
      eapply IHpc; eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin'; eauto.
    -- eauto.
Qed.

Lemma gather_responses_preserves_ok: forall pc regst,
  ok pc ->
  ok (gather_responses' pc regst).
Proof.
  induction pc using env_ind; simpl; intros.
  - constructor.
  - inversion H; subst. destruct v; simpl.
    all : try (econstructor; eauto).
    all : try (eapply gather_responses_preserves_pid_notin'; eauto).
    all : eauto.
    -- destruct (get x (Register.requests regst)); simpl.
      eauto.
      destruct (get x (Register.responses regst)).
      destruct r; simpl. destruct success; simpl.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin'; eauto.
      eauto.
      eauto.
      eauto.
    -- destruct ret; simpl.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin'; eauto.
      eauto.
    -- destruct (get x (Register.requests regst)); simpl.
      eauto.
      destruct (get x (Register.responses regst)).
      destruct r; simpl. destruct success; simpl.
      eapply IHpc; eauto.
      eapply IHpc; eauto.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin'; eauto.
      eapply IHpc; eauto.
Qed.

(* 
  Potential problem: the mapping relation missed some details
*)
Definition f (s1 : register_counter.(state)) (s2 : counter.(state)) :=
  sameset (gather_requests' s1.(L2State).(RegisterCounterImpl.pc) s1.(L1State)) s2.(requests) /\
  sameset (gather_responses' s1.(L2State).(RegisterCounterImpl.pc) s1.(L1State)) s2.(responses) /\
  s1.(L1State).(Register.value) = s2.(value).

(* 
  The proof stuck in the case of fsim_simulation (to be more specific, when the action is int_cas in Register).
  Problem: the rule linked_step_L1_internal is too general 
            and additional information may be added in linked_state (see LINK).
*)
Theorem register_counter_correct: refines register_counter counter.
Proof.
  eapply forward_simulation_inv_ind with (f:=f) (inv:= fun (st : register_counter.(state)) => RegStateWF st.(L1State) /\ RegCntImplStateWF st.(L2State)).
  unfold fsim_properties_inv_ind. intuition.
  - simpl.
    unfold invariant_ind. intuition.
    apply reg_ok_inv.
      inversion H; intuition.
    apply regcntimpl_ok_inv.
      inversion H; intuition.
    all : 
      simpl in H0; inversion H0; subst; simpl in *; try assumption.
      + eapply reg_initial_preserves_ok; eauto.
      + eapply reg_step_preserves_ok; eauto.
      + eapply reg_final_preserves_ok; eauto.
      + eapply regcntimpl_step_preserves_ok; eauto.
      + eapply regcntimpl_at_external_preserves_ok; eauto.
      + eapply regcntimpl_after_external_preserves_ok; eauto.
      + eapply regcntimpl_initial_preserves_ok; eauto.
      + eapply reg_at_external_preserves_ok; eauto.
      + eapply reg_after_external_preserves_ok; eauto.
      + eapply regcntimpl_final_preserves_ok; eauto.
  - exists new_counter. intuition.
    reflexivity. unfold f.
    simpl in H.
    unfold linked_new_state in H.
    simpl in H. inversion H.
    unfold register_new_state in H0.
    rewrite H0.
    unfold register_counter_new_state in H1.
    destruct H1.
    rewrite H1. simpl. intuition.
    repeat econstructor.
    repeat econstructor.
  - intros. inversion H1; subst.
    inversion H; subst.
    -- simpl. unfold f in H0. simpl in H0.
      intuition. subst.
      exists (mkCntState ((pid, CntInc):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        eapply sameset_concat with (F:= [(pid, CntInc)]) in H4.
        eauto. econstructor.
        unfold RegCntImplStateWF in H3. simpl in H3.
        eapply gather_requests_preserves_ok; eauto.
        eapply gather_requests_preserves_pid_notin'; eauto.
      }
      econstructor; eauto.
      eapply notin_sameset.
      2: { eauto. }
        eapply gather_requests_preserves_pid_notin'; eauto.
      eapply notin_sameset.
      2: { eauto. }
        eapply gather_responses_preserves_pid_notin'; eauto.
      (* rewrite <-H4. apply gather_requests_preserves_pid_notin'; auto.
      rewrite <-H0. apply gather_responses_preserves_pid_notin'; auto. *)
      destruct s2.
      reflexivity.
    -- simpl. unfold f in H0. simpl in H0.
      intuition. subst.
      exists (mkCntState ((pid, CntRead):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        eapply sameset_concat with (F:= [(pid, CntRead)]) in H4.
        eauto. econstructor.
        unfold RegCntImplStateWF in H3. simpl in H3.
        eapply gather_requests_preserves_ok; eauto.
        eapply gather_requests_preserves_pid_notin'; eauto.
      }
      econstructor; eauto.
      eapply notin_sameset.
      2: { eauto. }
        eapply gather_requests_preserves_pid_notin'; eauto.
      eapply notin_sameset.
      2: { eauto. }
        eapply gather_responses_preserves_pid_notin'; eauto.
      destruct s2.
      reflexivity.
  - intros. inversion H1; subst.
    inversion H; subst.
    -- simpl. unfold f in H0. simpl in H0.
      intuition.
      rewrite gather_requests_dist' in H4. simpl in H4.
      rewrite gather_responses_dist' in H0. simpl in H0.
      exists (mkCntState (requests s2) (gather_responses' (pc' ++ pc'') st1) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite gather_requests_dist'. assumption.
        eapply sameset_refl.
        eapply gather_responses_preserves_ok; eauto.
        unfold RegCntImplStateWF in H3. simpl in H3.
        assert (Hlok : ok (pc' ++ [(pid, DInc7)] ++ pc'')).
        simpl; assumption.
        apply ok_remove in Hlok. assumption.
      }
      eapply counter_final_state_inc with (inv:=requests s2) (res:=responses s2); eauto.
      eapply sym_sameset. simpl. eauto.
      destruct s2; eauto.
      rewrite gather_responses_dist'; eauto.
    -- simpl. unfold f in H0. simpl in H0.
      intuition.
      rewrite gather_requests_dist' in H4. simpl in H4.
      rewrite gather_responses_dist' in H0. simpl in H0.
      exists (mkCntState (requests s2) (gather_responses' (pc' ++ pc'') st1) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite gather_requests_dist'. assumption.
        eapply sameset_refl.
        eapply gather_responses_preserves_ok; eauto.
        unfold RegCntImplStateWF in H3. simpl in H3.
        assert (Hlok : ok (pc' ++ [(pid, DRead3 ret)] ++ pc'')).
        simpl; assumption.
        apply ok_remove in Hlok. assumption.
      }
      eapply counter_final_state_read with (inv:=requests s2) (res:=responses s2); eauto.
      eapply sym_sameset. simpl. eauto.
      destruct s2; eauto.
      rewrite gather_responses_dist'; eauto.
  - intros. inversion H1; subst.
    -- clear H1. simpl in H2.
        simpl in H4. exists s2, nil.
        intuition.
        econstructor; eauto.
        unfold f. simpl.
        unfold f in H0. simpl in H0.
        inversion H4; subst; simpl in H0; simpl;
        rewrite gather_requests_dist' in H0;
        rewrite gather_responses_dist' in H0;
        rewrite gather_requests_dist';
        rewrite gather_responses_dist';
        simpl in H0; simpl; intuition.
    -- exists s2, nil. intuition.
      econstructor; eauto.
      unfold f. simpl.
      unfold f in H0. simpl in H0.
      intuition.
      --- eapply trans_sameset; eauto.
        inversion H; subst; inversion H5; subst; simpl in *.
        + repeat rewrite gather_requests_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3.
          generalize ok_middle_inv; intro.
          specialize (H11 _ _ _ _ _ H3).
          intuition.
          rewrite gather_requests_notin_req; auto.
          simpl.
          rewrite gather_requests_notin_req; auto.
          apply sameset_refl.
          eapply gather_requests_preserves_ok in H3.
          rewrite gather_requests_dist' in H3.
          simpl in H3. eauto.
        + repeat rewrite gather_requests_dist'.

          unfold RegCntImplStateWF in H3.
          simpl in H3.
          generalize ok_middle_inv; intro.
          specialize (H6 _ _ _ _ _ H3).
          intuition.
          rewrite gather_requests_notin_req; auto.
          simpl. rewrite Nat.eqb_refl.
          rewrite gather_requests_notin_req; auto.
          apply sameset_refl.
          eapply gather_requests_preserves_ok in H3.
          rewrite gather_requests_dist' in H3.
          simpl in H3. eauto.
        + repeat rewrite gather_requests_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3.
          
          generalize ok_middle_inv; intro.
          specialize (H11 _ _ _ _ _ H3).
          intuition.
          rewrite gather_requests_notin_req; auto.
          simpl.
          rewrite gather_requests_notin_req; auto.
          rewrite Nat.eqb_refl.
          apply sameset_refl.
          eapply gather_requests_preserves_ok in H3.
          rewrite gather_requests_dist' in H3.
          simpl in H3. eauto.
      --- eapply trans_sameset; eauto.
        inversion H; subst; inversion H5; subst; simpl in *.
        + repeat rewrite gather_responses_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3.
          generalize ok_middle_inv; intro.
          specialize (H11 _ _ _ _ _ H3).
          intuition.
          rewrite gather_responses_notin_req; auto.
          simpl.
          rewrite gather_responses_notin_req; auto.
          apply sameset_refl.
          eapply gather_responses_preserves_ok in H3.
          rewrite gather_responses_dist' in H3.
          simpl in H3. eauto.
        + repeat rewrite gather_responses_dist'.

          unfold RegCntImplStateWF in H3.
          simpl in H3.
          generalize ok_middle_inv; intro.
          specialize (H6 _ _ _ _ _ H3).
          intuition.
          rewrite gather_responses_notin_req; auto.
          simpl. rewrite Nat.eqb_refl.
          rewrite gather_responses_notin_req; auto.
          apply sameset_refl.
          eapply gather_responses_preserves_ok in H3.
          rewrite gather_responses_dist' in H3.
          simpl in H3. eauto.
        + repeat rewrite gather_responses_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3.
          
          generalize ok_middle_inv; intro.
          specialize (H11 _ _ _ _ _ H3).
          intuition.
          rewrite gather_responses_notin_req; auto.
          simpl.
          rewrite gather_responses_notin_req; auto.
          rewrite Nat.eqb_refl.
          apply sameset_refl.
          eapply gather_responses_preserves_ok in H3.
          rewrite gather_responses_dist' in H3.
          simpl in H3. eauto.
      --- inversion H5; subst; simpl; intuition.
    -- destruct act.
      --- simpl in *.
        destruct qb; intuition.
        inversion H; subst.
        simpl in *.
        unfold f in H0. simpl in H0. intuition.
        subst. simpl in *.

        destruct H7 as [lst1 [lst2 [lst2st1 [lst2st2 [st1acts [st2acts [cs3 Htmp]]]]]]].
        destruct Htmp as [st2in_acts [st1in_acts [Hbefore Hremain]]].
        inversion Hbefore; subst.
        inversion H10; subst.
        simpl in Hremain, Hbefore. intuition.
        inversion H7; subst. clear H7.
        inversion H12; subst.
        assert (RegCAS (r pid) (S (r pid)) = RegCAS old0 new0).
        eapply internal_preserves_request
        with (st:= mkRegState ((pid, RegCAS (r pid) (S (r pid))) :: inv)
                              res0 v)
        (st':= mkRegState (inv' ++ (pid, RegCAS old0 new0) :: inv'')
                                res (value s2)); simpl; eauto.
        unfold binds. simpl. rewrite Nat.eqb_refl. reflexivity.
        unfold _RegStateWF. simpl. intuition.
        econstructor; eauto.
        simpl. eapply binds_concat_left.
        unfold binds. simpl. rewrite Nat.eqb_refl. reflexivity.
        apply ok_middle_inv in H6; intuition.
        inversion H7; subst. clear H7. simpl in *.
        assert (Hst2: binds pid DInc5 st2.(pc)).
        eapply no_action_preserves_DInc5; eauto.
        apply regcntimpl_reachable_inv in H18.
        unfold RegCntImplStateWF in H18.
        simpl in H18.
        eapply binds_concat_left; eauto.
        unfold binds. simpl. rewrite Nat.eqb_refl.
        reflexivity.
        apply ok_middle_inv in H18.
        intuition.
        apply binds_reconstruct in Hst2.
        destruct Hst2 as [pc2' [pc2'' Hpc]].
        rewrite Hpc in H5. simpl in H5.
        rewrite gather_requests_dist' in H5.
        simpl in H5.
        rewrite gather_requests_notin_env in H5.
        rewrite get_notin_env in H5. simpl in H5.
        rewrite Nat.eqb_refl in H5.
        rewrite gather_requests_notin_env in H5.

        destruct (value s2 =? r pid)eqn:Hbool.
        +
          exists (mkCntState 
                    (gather_requests' pc2'
                    (mkRegState (inv'++inv'') res ((value s2)))
                      ++ gather_requests' pc2'' (mkRegState (inv'++inv'') res (value s2))) 
                    ((pid, CntIncOk)::responses s2) (S (value s2))).
          exists [(pid, int_cnt_inc)]. intuition.
          ++ econstructor; eauto.
            2 : {
              econstructor; eauto.
            }
            destruct s2. simpl in *.
            econstructor; eauto.
            eapply sym_sameset; eauto.
          ++ unfold f. simpl.
            intuition.
            +++ rewrite Hpc.
              rewrite gather_requests_dist'.
              apply regcntimpl_reachable_inv in H18.
              assert (RegCntImplStateWF st2).
              eapply regcntimpl_valid_execution_preserves_ok; eauto.
              unfold RegCntImplStateWF in H7.
              rewrite Hpc in H7.
              rewrite gather_requests_notin_res.
              simpl.
              rewrite get_notin_env.
              assert (Hl : inv'' = inv'' ++ []).
              rewrite app_nil_r. reflexivity.
              rewrite Hl.
              rewrite get_notin_env. simpl.
              rewrite Nat.eqb_refl.
              rewrite gather_requests_notin_res.
              rewrite gather_requests_any_v_reg with (v':=value s2).
              rewrite gather_requests_any_v_reg with (v:=S (r pid)) (v':=value s2).
              eapply sameset_refl; eauto.
              eapply ok_remove in H7.
              eapply gather_requests_preserves_ok in H7.
              unfold ";" in H7.
              rewrite gather_requests_dist' in H7.
              eauto.
              eapply ok_middle_inv in H7. intuition.
              unfold RegStateWF in H2. simpl in H2.
              intuition.
              apply ok_middle_inv in H17. intuition.
              unfold RegStateWF in H2. simpl in H2.
              intuition.
              apply ok_middle_inv in H17. intuition.
              eapply ok_middle_inv in H7. intuition.
            +++ rewrite Hpc.
              rewrite gather_responses_dist'.
              apply regcntimpl_reachable_inv in H18.
              assert (RegCntImplStateWF st2).
              eapply regcntimpl_valid_execution_preserves_ok; eauto.
              unfold RegCntImplStateWF in H7.
              rewrite Hpc in H7.
              generalize ok_middle_inv; intro Hokremove.
              specialize (Hokremove _ _ _ _ _ H7).
              unfold RegStateWF in H2.
              simpl in H2. intuition.
              apply ok_middle_inv with (x:=pid) in H17.

              rewrite gather_responses_notin_res; intuition.
              simpl.
              rewrite get_notin_env; intuition.
              assert (Hl : inv'' = inv'' ++ []).
              rewrite app_nil_r. reflexivity.
              rewrite Hl.
              rewrite get_notin_env; intuition. simpl.
              rewrite Nat.eqb_refl; intuition.
              rewrite gather_responses_notin_res; intuition.
              rewrite gather_responses_any_v_reg with (v':=value s2); intuition.
              rewrite gather_responses_any_v_reg with (v:=S (r pid)) (v':=value s2); intuition.
              (* generalize sameset_ExF_xEF; intro. *)
              eapply sameset_congruence with (F:= [(pid, CntIncOk)]) in H0; intuition.
              simpl in H0.
              eapply trans_sameset.
              eapply sameset_ExF_xEF; eauto.
              rewrite <-Hl.
              eapply ok_ExF_xEF.

              rewrite <-gather_responses_dist'.
              econstructor; eauto.
              eapply gather_responses_preserves_ok; eauto.
              eapply ok_remove in H7; eauto.
              eapply gather_responses_preserves_pid_notin'; eauto.
              eapply ok_middle_inv in H7; eauto.
              apply notin_concat in H7. assumption.
              eauto. simpl.
              rewrite Hpc. simpl.
              rewrite gather_responses_dist'.
              simpl. rewrite get_notin_env; intuition. simpl.
              rewrite Nat.eqb_refl.
              rewrite gather_responses_notin_env; intuition.
              rewrite gather_responses_notin_env; intuition.
              rewrite app_nil_r.
              eapply sameset_refl.

              rewrite <-gather_responses_dist'.
              econstructor; eauto.
              eapply gather_responses_preserves_ok; eauto.
              eapply ok_remove in H7; eauto.
              eapply gather_responses_preserves_pid_notin'; eauto.
              eapply ok_middle_inv in H7; eauto.
              apply notin_concat in H7. assumption.
            +++ f_equal. apply Nat.eqb_eq in Hbool; intuition.
        + exists s2. exists nil. intuition.
          econstructor; eauto.
          unfold f. simpl. intuition.
          ++ rewrite Hpc.
            rewrite gather_requests_dist'. simpl.
            unfold RegStateWF in H2.
            simpl in H2. intuition.
            apply ok_middle_inv with (x:=pid) in H7.
          
              assert (RegCntImplStateWF st2).
              eapply regcntimpl_valid_execution_preserves_ok; eauto.
              eapply regcntimpl_reachable_inv; eauto.
              unfold RegCntImplStateWF in H23.
              rewrite Hpc in H23.
              generalize ok_middle_inv; intro Hokremove.
              specialize (Hokremove _ _ _ _ _ H23).

            rewrite get_notin_env; intuition.
            assert (Hl : inv'' = inv'' ++ []) by (rewrite app_nil_r; reflexivity).
            rewrite Hl.
            rewrite get_notin_env; intuition. simpl.
            rewrite Nat.eqb_refl.
            rewrite <-Hl.
            rewrite gather_requests_notin_res; intuition.
            rewrite gather_requests_notin_res; intuition.
          ++ rewrite Hpc.
            rewrite gather_responses_dist'. simpl.
            unfold RegStateWF in H2.
            simpl in H2. intuition.
            apply ok_middle_inv with (x:=pid) in H7.
          
              assert (RegCntImplStateWF st2).
              eapply regcntimpl_valid_execution_preserves_ok; eauto.
              eapply regcntimpl_reachable_inv; eauto.
              unfold RegCntImplStateWF in H23.
              rewrite Hpc in H23.
              generalize ok_middle_inv; intro Hokremove.
              specialize (Hokremove _ _ _ _ _ H23).

            rewrite get_notin_env; intuition.
            assert (Hl : inv'' = inv'' ++ []) by (rewrite app_nil_r; reflexivity).
            rewrite Hl.
            rewrite get_notin_env; intuition. simpl.
            rewrite Nat.eqb_refl.
            rewrite <-Hl.
            rewrite gather_responses_notin_res; intuition.
            rewrite gather_responses_notin_res; intuition.
            erewrite gather_responses_any_v_reg.
            erewrite gather_responses_any_v_reg with (pc:=pc2'').
            rewrite Hpc in H0.
            rewrite gather_responses_dist' in H0. simpl in H0.
            rewrite get_notin_env in H0; intuition. simpl in H0.
            rewrite Nat.eqb_refl in H0.
            rewrite gather_responses_notin_env in H0; intuition.
            rewrite gather_responses_notin_env in H0; intuition.
            eassumption.
        + assert (RegCntImplStateWF st2).
          eapply regcntimpl_valid_execution_preserves_ok; eauto.
          eapply regcntimpl_reachable_inv; eauto.
          unfold RegCntImplStateWF in H7.
          rewrite Hpc in H7.
          generalize ok_middle_inv; intro Hokremove.
          specialize (Hokremove _ _ _ _ _ H7).
          intuition.
        + unfold RegStateWF in H2.
          simpl in H2. intuition.
          apply ok_middle_inv with (x:=pid) in H7. intuition.
        + assert (RegCntImplStateWF st2).
          eapply regcntimpl_valid_execution_preserves_ok; eauto.
          eapply regcntimpl_reachable_inv; eauto.
          unfold RegCntImplStateWF in H7.
          rewrite Hpc in H7.
          generalize ok_middle_inv; intro Hokremove.
          specialize (Hokremove _ _ _ _ _ H7).
          intuition.
      ---
      simpl in *.
        destruct qb; intuition.
        inversion H; subst.
        simpl in *.
        unfold f in H0. simpl in H0. intuition.
        subst. simpl in *.

        destruct H7 as [lst1 [lst2 [lst2st1 [lst2st2 [st1acts [st2acts [cs3 Htmp]]]]]]].
        destruct Htmp as [st2in_acts [st1in_acts [Hbefore Hremain]]].
        inversion Hbefore; subst.
        inversion H10; subst.
        (* RegRead in Inc, not a linearization point *)
        * 

        simpl in Hremain, Hbefore. intuition.
        inversion H7; subst. clear H7.
        inversion H12; subst. simpl in *.
        assert (Hst2: binds pid DInc2 st2.(pc)).
        eapply no_action_preserves_DInc2; eauto.
        apply regcntimpl_reachable_inv in H18.
        unfold RegCntImplStateWF in H18.
        simpl in H18.
        eapply binds_concat_left; eauto.
        unfold binds. simpl. rewrite Nat.eqb_refl.
        reflexivity.
        apply ok_middle_inv in H18.
        intuition.
        apply binds_reconstruct in Hst2.
        destruct Hst2 as [pc2' [pc2'' Hpc]].
        rewrite Hpc in H5. simpl in H5.
        rewrite gather_requests_dist' in H5.
        simpl in H5.

        assert (RegCntImplStateWF st2).
          eapply regcntimpl_valid_execution_preserves_ok; eauto.
          eapply regcntimpl_reachable_inv; eauto.
          unfold RegCntImplStateWF in H21.
          rewrite Hpc in H21.
          generalize ok_middle_inv; intro Hokremove.
          specialize (Hokremove _ _ _ _ _ H21).
          intuition.

        unfold RegStateWF in H2.
        simpl in H2. intuition.
        apply ok_middle_inv with (x:=pid) in H24. intuition.

        rewrite gather_requests_notin_env in H5; intuition.
        rewrite gather_requests_notin_env in H5; intuition.
        exists s2. exists nil.
        econstructor; eauto.
        econstructor; eauto.
        unfold f. simpl. intuition.

        rewrite Hpc.
        rewrite gather_requests_dist'.
        simpl.
        rewrite gather_requests_notin_res; intuition.
        rewrite gather_requests_notin_res; intuition.

        rewrite Hpc.
        rewrite gather_responses_dist'.
        simpl.
        rewrite gather_responses_notin_res; intuition.
        rewrite gather_responses_notin_res; intuition.

        rewrite Hpc in H0.
        rewrite gather_responses_dist' in H0.
        simpl in H0.
        rewrite gather_responses_notin_env in H0; intuition.
        rewrite gather_responses_notin_env in H0; intuition.
        (* RegRead in Read, a linearization point *)
        *
        simpl in Hremain, Hbefore. intuition.
        inversion H7; subst. clear H7.
        inversion H12; subst. simpl in *.
        assert (Hst2: binds pid DRead2 st2.(pc)).
        eapply no_action_preserves_DRead2; eauto.
        apply regcntimpl_reachable_inv in H18.
        unfold RegCntImplStateWF in H18.
        simpl in H18.
        eapply binds_concat_left; eauto.
        unfold binds. simpl. rewrite Nat.eqb_refl.
        reflexivity.
        apply ok_middle_inv in H18.
        intuition.
        apply binds_reconstruct in Hst2.
        destruct Hst2 as [pc2' [pc2'' Hpc]].
        rewrite Hpc in H5. simpl in H5.
        rewrite gather_requests_dist' in H5.
        simpl in H5.

        assert (RegCntImplStateWF st2).
          eapply regcntimpl_valid_execution_preserves_ok; eauto.
          eapply regcntimpl_reachable_inv; eauto.
          unfold RegCntImplStateWF in H21.
          rewrite Hpc in H21.
          generalize ok_middle_inv; intro Hokremove.
          specialize (Hokremove _ _ _ _ _ H21).
          intuition.

        unfold RegStateWF in H2.
        simpl in H2. intuition.
        apply ok_middle_inv with (x:=pid) in H24 .

        rewrite gather_requests_notin_env in H5; intuition.
        rewrite gather_requests_notin_env in H5; intuition.
        rewrite get_notin_env in H5; intuition.
        simpl in H5.
        rewrite Nat.eqb_refl in H5.

        exists (mkCntState 
                  (gather_requests' pc2'
                  (mkRegState (inv'++inv'') res ((value s2)))
                    ++ gather_requests' pc2'' (mkRegState (inv'++inv'') res (value s2)))
                  ((pid, CntReadOk (value s2))::responses s2) ((value s2))).
        exists [(pid, int_cnt_read)]. intuition.

          ++ econstructor; eauto.
            2 : {
              econstructor; eauto.
            }
            destruct s2. simpl in *.
            econstructor; eauto.
            eapply sym_sameset; eauto.
          ++ unfold f. simpl.
            intuition.
            +++ 
            rewrite Hpc.
              rewrite gather_requests_dist'.
              (* apply regcntimpl_reachable_inv in H18.
              assert (RegCntImplStateWF st2).
              eapply regcntimpl_valid_execution_preserves_ok; eauto.
              unfold RegCntImplStateWF in H7.
              rewrite Hpc in H7. *)
              rewrite gather_requests_notin_res.
              simpl.
              rewrite get_notin_env.
              assert (Hl : inv'' = inv'' ++ []).
              rewrite app_nil_r. reflexivity.
              rewrite Hl.
              rewrite get_notin_env. simpl.
              rewrite Nat.eqb_refl.
              rewrite gather_requests_notin_res.
              (* rewrite gather_requests_any_v_reg with (v':=value s2).
              rewrite gather_requests_any_v_reg with (v:=S (r pid)) (v':=value s2). *)
              eapply sameset_refl; eauto.
              eapply ok_remove in H21.
              eapply gather_requests_preserves_ok in H21.
              unfold ";" in H21.
              rewrite gather_requests_dist' in H21.
              eauto.
              eapply ok_middle_inv in H21. intuition.
              intuition. intuition. intuition.
            +++ rewrite Hpc.
              rewrite gather_responses_dist'.
              (* apply regcntimpl_reachable_inv in H18.
              assert (RegCntImplStateWF st2).
              eapply regcntimpl_valid_execution_preserves_ok; eauto.
              unfold RegCntImplStateWF in H7.
              rewrite Hpc in H7.
              generalize ok_middle_inv; intro Hokremove.
              specialize (Hokremove _ _ _ _ _ H7).
              unfold RegStateWF in H2.
              simpl in H2. intuition.
              apply ok_middle_inv with (x:=pid) in H17. *)

              rewrite gather_responses_notin_res; intuition.
              simpl.
              rewrite get_notin_env; intuition.
              assert (Hl : inv'' = inv'' ++ []).
              rewrite app_nil_r. reflexivity.
              rewrite Hl.
              rewrite get_notin_env; intuition. simpl.
              rewrite Nat.eqb_refl; intuition.
              rewrite gather_responses_notin_res; intuition.
              (* rewrite gather_responses_any_v_reg with (v':=value s2); intuition.
              rewrite gather_responses_any_v_reg with (v:=S (r pid)) (v':=value s2); intuition. *)
              (* generalize sameset_ExF_xEF; intro. *)
              eapply sameset_congruence with (F:= [(pid, CntReadOk (value s2))]) in H0; intuition.
              simpl in H0.
              eapply trans_sameset.
              eapply sameset_ExF_xEF; eauto.
              rewrite <-Hl.
              eapply ok_ExF_xEF.

              rewrite <-gather_responses_dist'.
              econstructor; eauto.
              eapply gather_responses_preserves_ok; eauto.
              eapply ok_remove in H21; eauto.
              eapply gather_responses_preserves_pid_notin'; eauto.
              eapply ok_middle_inv in H21; eauto.
              apply notin_concat in H21. assumption.
              eauto. simpl.
              rewrite Hpc. simpl.
              rewrite gather_responses_dist'.
              simpl. rewrite get_notin_env; intuition. simpl.
              rewrite Nat.eqb_refl.
              rewrite gather_responses_notin_env; intuition.
              rewrite gather_responses_notin_env; intuition.
              rewrite app_nil_r.
              eapply sameset_refl.

              rewrite <-gather_responses_dist'.
              econstructor; eauto.
              eapply gather_responses_preserves_ok; eauto.
              eapply ok_remove in H21; eauto.
              eapply gather_responses_preserves_pid_notin'; eauto.
              eapply ok_middle_inv in H21; eauto.
              apply notin_concat in H21. assumption.
    -- exists s2. exists nil.
      econstructor; eauto.
      econstructor; eauto.
      unfold f. simpl.
      unfold f in H0. simpl in H0.
      intuition.
      --- eapply trans_sameset; eauto.
        inversion H; subst; inversion H4; subst; simpl in *.
        + repeat rewrite gather_requests_dist'.


          unfold RegStateWF in H2. simpl in H2.
          inversion H2 as [Hokinv [Hokres [Hbindsinv Hbindsres]]].
          apply ok_middle_inv in Hokres.
          unfold RegCntImplStateWF in H3. simpl in H3.
          generalize ok_middle_inv; intro Hok_pc_concat.
          specialize (Hok_pc_concat _ _ _ _ _ H3).

          assert (Hinv : get pid inv = None).
          {
            assert (Hinv': pid # inv).
            eapply Hbindsres with (v:=RegCASOk b); eauto.
            apply binds_concat_left; eauto.
            unfold binds. simpl. rewrite Nat.eqb_refl.
            reflexivity. apply ok_middle_inv in H10; intuition.
            apply notin_get_none; auto.
          }

          simpl. rewrite Hinv. destruct b.
          (* prove by contradiction *)
          ++
            rewrite get_notin_env; intuition.
            simpl. rewrite Nat.eqb_refl.
            rewrite gather_requests_notin_env'; intuition.
            rewrite gather_requests_notin_env'; intuition.
            apply sameset_refl.
            rewrite <-gather_requests_dist'; intuition.
            apply gather_requests_preserves_ok; eauto.
            apply ok_remove with (F:=[(pid, DInc5)]) in H3. intuition.
          ++ 
            rewrite get_notin_env; intuition.
            simpl. rewrite Nat.eqb_refl.
            rewrite gather_requests_notin_env'; intuition.
            rewrite gather_requests_notin_env'; intuition.
            apply sameset_refl.
            eapply gather_requests_preserves_ok 
            with (regst:= mkRegState inv (res'++res'') v)
            in H3.
            rewrite gather_requests_dist' in H3.
            simpl in H3. rewrite Hinv in H3.
            rewrite get_notin_env in H3; intuition.
            assert (Hl : res'' = res'' ++ []).
            rewrite app_nil_r.
            reflexivity.
            rewrite Hl in H3.
            rewrite get_notin_env in H3; intuition.
            simpl in H3. rewrite <-Hl in H3. assumption.
        + repeat rewrite gather_requests_dist'.


          unfold RegStateWF in H2. simpl in H2.
          inversion H2 as [Hokinv [Hokres [Hbindsinv Hbindsres]]].
          apply ok_middle_inv in Hokres.
          unfold RegCntImplStateWF in H3. simpl in H3.
          generalize ok_middle_inv; intro Hok_pc_concat.
          specialize (Hok_pc_concat _ _ _ _ _ H3).

          assert (Hinv : get pid inv = None).
          {
            assert (Hinv': pid # inv).
            eapply Hbindsres with (v:=RegReadOk ret); eauto.
            apply binds_concat_left; eauto.
            unfold binds. simpl. rewrite Nat.eqb_refl.
            reflexivity. apply ok_middle_inv in H10; intuition.
            apply notin_get_none; auto.
          }

          simpl.
          rewrite gather_requests_notin_env'; intuition.
          rewrite gather_requests_notin_env'; intuition.
          apply sameset_refl.
          eapply gather_requests_preserves_ok 
          with (regst:= mkRegState inv (res'++res'') v)
          in H3.
          rewrite gather_requests_dist' in H3.
          simpl in H3. assumption.
        + repeat rewrite gather_requests_dist'.

          unfold RegStateWF in H2. simpl in H2.
          inversion H2 as [Hokinv [Hokres [Hbindsinv Hbindsres]]].
          apply ok_middle_inv in Hokres.
          unfold RegCntImplStateWF in H3. simpl in H3.
          generalize ok_middle_inv; intro Hok_pc_concat.
          specialize (Hok_pc_concat _ _ _ _ _ H3).

          assert (Hinv : get pid inv = None).
          {
            assert (Hinv': pid # inv).
            eapply Hbindsres with (v:=RegReadOk ret); eauto.
            apply binds_concat_left; eauto.
            unfold binds. simpl. rewrite Nat.eqb_refl.
            reflexivity. apply ok_middle_inv in H10; intuition.
            apply notin_get_none; auto.
          }

          simpl. rewrite Hinv.
          (* prove by contradiction *)
            rewrite get_notin_env; intuition.
            simpl. rewrite Nat.eqb_refl.
            rewrite gather_requests_notin_env'; intuition.
            rewrite gather_requests_notin_env'; intuition.
            apply sameset_refl.
            rewrite <-gather_requests_dist'; intuition.
            apply gather_requests_preserves_ok; eauto.
            apply ok_remove with (F:=[(pid, DRead2)]) in H3. intuition.
      --- eapply trans_sameset; eauto.
        inversion H; subst; inversion H4; subst; simpl in *.
        + repeat rewrite gather_responses_dist'.


          unfold RegStateWF in H2. simpl in H2.
          inversion H2 as [Hokinv [Hokres [Hbindsinv Hbindsres]]].
          apply ok_middle_inv in Hokres.
          unfold RegCntImplStateWF in H3. simpl in H3.
          generalize ok_middle_inv; intro Hok_pc_concat.
          specialize (Hok_pc_concat _ _ _ _ _ H3).

          assert (Hinv : get pid inv = None).
          {
            assert (Hinv': pid # inv).
            eapply Hbindsres with (v:=RegCASOk b); eauto.
            apply binds_concat_left; eauto.
            unfold binds. simpl. rewrite Nat.eqb_refl.
            reflexivity. apply ok_middle_inv in H10; intuition.
            apply notin_get_none; auto.
          }

          simpl. rewrite Hinv. destruct b.
          (* prove by contradiction *)
          ++
            rewrite get_notin_env; intuition.
            simpl. rewrite Nat.eqb_refl.
            rewrite gather_responses_notin_env'; intuition.
            rewrite gather_responses_notin_env'; intuition.
            apply sameset_refl.

            eapply gather_responses_preserves_ok 
            with (regst:= mkRegState inv (res'++[(pid, RegCASOk true)]++res'') v)
            in H3.
            rewrite gather_responses_dist' in H3.
            simpl in H3. rewrite Hinv in H3.
            rewrite get_notin_env in H3; intuition.
            assert (Hl : res'' = res'' ++ []).
            rewrite app_nil_r.
            reflexivity.
            rewrite Hl in H3. simpl in H3.
            rewrite Nat.eqb_refl in H3.
            simpl in H3. rewrite <-Hl in H3.
            rewrite gather_responses_notin_env' in H3; intuition.
            rewrite gather_responses_notin_env' in H3; intuition.
          ++ 
            rewrite get_notin_env; intuition.
            simpl. rewrite Nat.eqb_refl.
            rewrite gather_responses_notin_env'; intuition.
            rewrite gather_responses_notin_env'; intuition.
            apply sameset_refl.
            rewrite <-gather_responses_dist'.
            apply gather_responses_preserves_ok; auto.
            apply ok_remove with (F:=[(pid, DInc5)]) in H3. intuition.
        + repeat rewrite gather_responses_dist'.

          unfold RegStateWF in H2. simpl in H2.
          inversion H2 as [Hokinv [Hokres [Hbindsinv Hbindsres]]].
          apply ok_middle_inv in Hokres.
          unfold RegCntImplStateWF in H3. simpl in H3.
          generalize ok_middle_inv; intro Hok_pc_concat.
          specialize (Hok_pc_concat _ _ _ _ _ H3).

          assert (Hinv : get pid inv = None).
          {
            assert (Hinv': pid # inv).
            eapply Hbindsres with (v:=RegReadOk ret); eauto.
            apply binds_concat_left; eauto.
            unfold binds. simpl. rewrite Nat.eqb_refl.
            reflexivity. apply ok_middle_inv in H10; intuition.
            apply notin_get_none; auto.
          }

          simpl.
          rewrite gather_responses_notin_env'; intuition.
          rewrite gather_responses_notin_env'; intuition.
          apply sameset_refl.
            rewrite <-gather_responses_dist'.
            apply gather_responses_preserves_ok; auto.
            apply ok_remove with (F:=[(pid, DInc2)]) in H3. intuition.
        + repeat rewrite gather_responses_dist'.

          unfold RegStateWF in H2. simpl in H2.
          inversion H2 as [Hokinv [Hokres [Hbindsinv Hbindsres]]].
          apply ok_middle_inv in Hokres.
          unfold RegCntImplStateWF in H3. simpl in H3.
          generalize ok_middle_inv; intro Hok_pc_concat.
          specialize (Hok_pc_concat _ _ _ _ _ H3).

          assert (Hinv : get pid inv = None).
          {
            assert (Hinv': pid # inv).
            eapply Hbindsres with (v:=RegReadOk ret); eauto.
            apply binds_concat_left; eauto.
            unfold binds. simpl. rewrite Nat.eqb_refl.
            reflexivity. apply ok_middle_inv in H10; intuition.
            apply notin_get_none; auto.
          }

          simpl. rewrite Hinv.
          (* prove by contradiction *)
            rewrite get_notin_env; intuition.
            simpl. rewrite Nat.eqb_refl.

            eapply gather_responses_preserves_ok 
            with (regst:= mkRegState inv (res'++[(pid, RegReadOk ret)]++res'') v)
            in H3.
            rewrite gather_responses_dist' in H3.
            simpl in H3. rewrite Hinv in H3.
            rewrite get_notin_env in H3; intuition.
            assert (Hl : res'' = res'' ++ []).
            rewrite app_nil_r.
            reflexivity.
            rewrite Hl in H3. simpl in H3.
            rewrite Nat.eqb_refl in H3.
            simpl in H3. rewrite <-Hl in H3.
            rewrite gather_responses_notin_env'; intuition.
            rewrite gather_responses_notin_env'; intuition.
            eapply sameset_refl.
            rewrite gather_responses_notin_env' in H3; intuition.
            rewrite gather_responses_notin_env' in H3; intuition.
      ---
        inversion H; subst; inversion H4; subst; simpl in *; intuition.
Qed.
  
End RegisterCounter.