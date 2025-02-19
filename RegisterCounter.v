Require Import
  List
  LTS
  Arith
  LibVar
  LibEnv
  Refinement
  Register
  DCounter
  Counter.
Import ListNotations.

(* 
  Prove that the composition of register_counter_impl (DCounter.v) and register (Register.v)
  refines the atomic counter (Counter.v).
*)
Section RegisterCounter.

Definition register_counter : lts li_null li_counter := linked_lts Register register_counter_impl.

Fixpoint gather_requests (pc : LibEnv.env DCounter_pc) : LibEnv.env Counter_query :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let requests' := gather_requests pc' in
      let (pid, inst) := ins in
        (match inst with
        | DInc1 => (pid, CntInc)::requests'
        | DInc2 => (pid, CntInc)::requests'
        | DInc3 _ => (pid, CntInc)::requests'
        | DInc4 => (pid, CntInc)::requests'
        | DInc5 => (pid, CntInc)::requests'
        | DInc6 ret => match ret with
                      | true => requests'
                      | false => (pid, CntInc)::requests'
                      end
        | DInc7 => requests'
        | DRead1 => (pid, CntRead)::requests'
        | DRead2 => (pid, CntRead)::requests'
        | DRead3 _ => requests'
        end)
  end.

Fixpoint gather_responses (pc : LibEnv.env DCounter_pc) : LibEnv.env Counter_reply :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let responses' := gather_responses pc' in
      let (pid, inst) := ins in
        (match inst with
        | DInc1 => responses' 
        | DInc2 => responses' 
        | DInc3 _ => responses' 
        | DInc4 => responses'
        | DInc5 => responses'
        | DInc6 ret => match ret with
                      | true => (pid, CntIncOk)::responses'
                      | false => responses'
                      end
        | DInc7 => (pid, CntIncOk)::responses'
        | DRead1 => responses' 
        | DRead2 => responses'
        | DRead3 ret => (pid, CntReadOk ret)::responses'
        end)
  end.

Lemma gather_requests_dist: forall pc pc',
  gather_requests (pc ++ pc') =
  gather_requests pc ++ gather_requests pc'.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct d; simpl; rewrite IHpc; try reflexivity.
    destruct ret; reflexivity.
Qed.

Lemma gather_responses_dist: forall pc pc',
  gather_responses (pc ++ pc') =
  gather_responses pc ++ gather_responses pc'.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct d; simpl; rewrite IHpc; try reflexivity.
    destruct ret; reflexivity.
Qed.

Lemma gather_requests_preserves_pid_notin: forall pc pid,
  pid # pc ->
  pid # gather_requests pc.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    apply IHpc in H1.
    destruct d; simpl; try apply notin_union; eauto.
    destruct ret; eauto. simpl. apply notin_union; eauto.
Qed.

Lemma gather_responses_preserves_pid_notin: forall pc pid,
  pid # pc ->
  pid # gather_responses pc.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    apply IHpc in H1.
    destruct d; simpl; try apply notin_union; eauto.
    destruct ret; eauto. simpl. apply notin_union; eauto.
Qed.

(* Lemma final_preserves_binds_DInc5: forall st st' pid pid' int,
  binds pid DInc5 st.(pc) ->
  final_state register_counter_impl st pid' int st' ->
  pid <> pid' ->
  binds pid DInc5 st'.(pc).
Proof.
  inversion 2; intros; subst;
  apply binds_remove in H;
  simpl in *; try assumption;
  apply notin_neq; auto.
Qed. *)

Section StrutureProperties.

Variable A : Type.
Implicit Types E F : env A.

Lemma binds_neq_middle: forall F E x x1 v v1 v1',
  binds x v (E ++ [(x1, v1)] ++ F) ->
  x <> x1 ->
  binds x v (E ++ [(x1, v1')] ++ F).
Proof.
  intros.
  apply binds_concat_inv in H. intuition.
  - eapply binds_concat_right; eauto.
  - apply binds_concat_inv in H2. intuition.
    -- unfold binds in H1. simpl in H1.
      apply Nat.eqb_neq in H0.
      rewrite H0 in H1. inversion H1.
    -- eapply binds_concat_left; eauto.
      eapply binds_push_neq; eauto.
Qed.

End StrutureProperties.


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
  (* pid <> pid' -> *)
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
  (* pid <> pid' -> *)
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


Section MoreDefinitions.

Variables A : Type.

Lemma binds_reconstruct: forall x v (l : env A),
  binds x v l ->
  exists l1 l2, l = l1 ++ [(x, v)] ++ l2.
Proof.
  induction l using env_ind; simpl; intros.
  - inversion H.
  - unfold binds in H. simpl in H.
    destruct (x =? x0)eqn:Heq.
    -- inversion H; subst.
      exists []. exists l.
      eapply Nat.eqb_eq in Heq.
      subst; intuition.
    -- apply IHl in H.
      destruct H as [l1 [l2 Htmp]].
      subst.
      exists ((x0, v0)::l1).
      exists l2. reflexivity.
Qed.

End MoreDefinitions.

Fixpoint gather_requests' (pc : LibEnv.env DCounter_pc) (regst : state Register) : LibEnv.env Counter_query :=
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
        | DRead2 => (pid, CntRead)::requests'
        | DRead3 _ => requests'
        end)
  end.

Fixpoint gather_responses' (pc : LibEnv.env DCounter_pc) (regst : state Register) : LibEnv.env Counter_reply :=
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
        | DRead2 => responses'
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
    destruct d; simpl; try apply notin_union; eauto.
    -- destruct (get v (Register.requests regst)).
      + simpl. apply notin_union; eauto.
      + destruct (get v (Register.responses regst)).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
          +++ simpl. apply notin_union; auto.
        ++ simpl. apply notin_union; auto.
    -- destruct ret; eauto. simpl. apply notin_union; eauto.
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
    destruct d; simpl; try apply notin_union; eauto.
    -- destruct (get v (Register.requests regst)).
      + assumption.
      + destruct (get v (Register.responses regst)).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
          +++ assumption.
        ++ assumption.
    -- destruct ret; eauto. simpl. apply notin_union; eauto.
Qed.

Lemma gather_requests_dist': forall pc pc' regst,
  gather_requests' (pc ++ pc') regst =
  gather_requests' pc regst ++ gather_requests' pc' regst.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct d; simpl; rewrite IHpc; try reflexivity.
    -- destruct (get v (Register.requests regst)); simpl.
      + reflexivity.
      + destruct (get v (Register.responses regst)); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct ret; reflexivity.
Qed.

Lemma gather_responses_dist': forall pc pc' regst,
  gather_responses' (pc ++ pc') regst =
  gather_responses' pc regst ++ gather_responses' pc' regst.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct d; simpl; rewrite IHpc; try reflexivity.
    -- destruct (get v (Register.requests regst)); simpl.
      + reflexivity.
      + destruct (get v (Register.responses regst)); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct ret; reflexivity.
Qed.

Lemma gather_requests_notin: forall pc pid inv res v pid_inv,
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
Qed.

Lemma gather_responses_notin: forall pc pid inv res v pid_inv,
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
Qed.

(* 
  Potential problem: the mapping relation missed some details
*)
Definition f (s1 : register_counter.(state)) (s2 : counter.(state)) :=
  gather_requests' s1.(L2State).(DCounter.pc) s1.(L1State) = s2.(requests) /\
  gather_responses' s1.(L2State).(DCounter.pc) s1.(L1State) = s2.(responses) /\
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
    rewrite H1. intuition.
  - intros. inversion H1; subst.
    inversion H; subst.
    -- simpl. unfold f in H0. simpl in H0.
      intuition. subst.
      exists (mkCntState ((pid, CntInc):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite H4. reflexivity.
      }
      econstructor; eauto.
      rewrite <-H4. apply gather_requests_preserves_pid_notin'; auto.
      rewrite <-H0. apply gather_responses_preserves_pid_notin'; auto.
      destruct s2.
      reflexivity.
    -- simpl. unfold f in H0. simpl in H0.
      intuition. subst.
      exists (mkCntState ((pid, CntRead):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite H4. reflexivity.
      }
      econstructor; eauto.
      rewrite <-H4. apply gather_requests_preserves_pid_notin'; auto.
      rewrite <-H0. apply gather_responses_preserves_pid_notin'; auto.
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
        rewrite <-H4. apply gather_requests_dist'.
      }
      eapply counter_final_state_inc with (inv:=requests s2) (res:=responses s2); eauto.
      rewrite <-H0. simpl. eauto. destruct s2. eauto.
      rewrite gather_responses_dist'. rewrite H6. reflexivity.
    -- simpl. unfold f in H0. simpl in H0.
      intuition.
      rewrite gather_requests_dist' in H4. simpl in H4.
      rewrite gather_responses_dist' in H0. simpl in H0.
      exists (mkCntState (requests s2) (gather_responses' (pc' ++ pc'') st1) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite <-H4. apply gather_requests_dist'.
      }
      eapply counter_final_state_read with (inv:=requests s2) (res:=responses s2); eauto.
      rewrite <-H0. simpl. eauto. destruct s2. eauto.
      rewrite gather_responses_dist'. rewrite H6. reflexivity.
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
      --- rewrite <-H4.
        inversion H; subst; inversion H5; subst; simpl in *.
        + repeat rewrite gather_requests_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3. apply ok_middle_inv in H3. intuition.
          rewrite gather_requests_notin; auto.
          simpl.
          rewrite gather_requests_notin; auto.
        + repeat rewrite gather_requests_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3. apply ok_middle_inv in H3. intuition.
          rewrite gather_requests_notin; auto.
          simpl. rewrite Nat.eqb_refl.
          rewrite gather_requests_notin; auto.
        + repeat rewrite gather_requests_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3. apply ok_middle_inv in H3. intuition.
          rewrite gather_requests_notin; auto.
          simpl.
          rewrite gather_requests_notin; auto.
      --- rewrite <-H0.
        inversion H; subst; inversion H5; subst; simpl in *.
        + repeat rewrite gather_responses_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3. apply ok_middle_inv in H3. intuition.
          rewrite gather_responses_notin; auto.
          simpl.
          rewrite gather_responses_notin; auto.
        + repeat rewrite gather_responses_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3. apply ok_middle_inv in H3. intuition.
          rewrite gather_responses_notin; auto.
          simpl. rewrite Nat.eqb_refl.
          rewrite gather_responses_notin; auto.
        + repeat rewrite gather_responses_dist'.
          unfold RegCntImplStateWF in H3.
          simpl in H3. apply ok_middle_inv in H3. intuition.
          rewrite gather_responses_notin; auto.
          simpl.
          rewrite gather_responses_notin; auto.
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
        unfold RegStateWF. simpl. intuition.
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

        destruct (value s2 =? r pid)eqn:Hbool.
        +
          exists (mkCntState (gather_requests pc2' ++ gather_requests pc2'') ((pid, CntIncOk)::responses s2) (S (value s2))).
          exists [(pid, int_cnt_inc)]. intuition.
          ++ econstructor; eauto.
            2 : {
              econstructor; eauto.
            }
            destruct s2. simpl in *.
            econstructor; eauto.
            f_equal; auto.
          ++ unfold f. simpl.
            intuition.




        destruct (value s2 =? old) eqn:Heq.
        + exists (mkCntState (requests s2) ((pid, CntIncOk)::responses s2) (S (value s2))).
          simpl. intuition.
          ++ eapply Step_Internal with (int:=int_cnt_inc); eauto.
            2: { econstructor; eauto. }
            simpl.
Admitted.
  
End RegisterCounter.