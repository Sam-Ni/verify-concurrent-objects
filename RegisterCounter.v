Require Import
  List
  LTS
  Nat
  LibVar
  LibEnv
  Refinement
  Register
  DCounter
  Counter.

(* 
  Prove that the composition of register_counter_impl (DCounter.v) and register (Register.v)
  refines the atomic counter (Counter.v).
*)
Section RegisterCounter.

Definition register_counter : lts li_null li_counter := linked_lts Register register_counter_impl.

Fixpoint gather_requests (pc : LibEnv.env DCounter_pc) : LibEnv.env Counter.Invocation :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let requests' := gather_requests pc' in
      let (pid, inst) := ins in
        (match inst with
        | DInc1 => (pid, Inv_Inc)::requests'
        | DInc2 => (pid, Inv_Inc)::requests'
        | DInc3 _ => (pid, Inv_Inc)::requests'
        | DInc4 => (pid, Inv_Inc)::requests'
        | DInc5 => (pid, Inv_Inc)::requests'
        | DInc6 ret => match ret with
                      | true => requests'
                      | false => (pid, Inv_Inc)::requests'
                      end
        | DInc7 => requests'
        | DRead1 => (pid, Inv_Read)::requests'
        | DRead2 => (pid, Inv_Read)::requests'
        | DRead3 _ => requests'
        end)
  end.

Fixpoint gather_responses (pc : LibEnv.env DCounter_pc) : LibEnv.env Counter.Response :=
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
                      | true => (pid, Res_Inc)::responses'
                      | false => responses'
                      end
        | DInc7 => (pid, Res_Inc)::responses'
        | DRead1 => responses' 
        | DRead2 => responses'
        | DRead3 ret => (pid, Res_Read ret)::responses'
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

(* 
  Potential problem: the mapping relation missed some details
*)
Definition f (s1 : register_counter.(state)) (s2 : counter.(state)) :=
  gather_requests s1.(L2State).(DCounter.pc) = s2.(requests) /\
  gather_responses s1.(L2State).(DCounter.pc) = s2.(responses) /\
  s1.(L1State).(Register.value) = s2.(value).

(* 
  The proof stuck in the case of fsim_simulation (to be more specific, when the action is int_cas in Register).
  Problem: the rule linked_step_L1_internal is too general 
            and additional information may be added in linked_state (see LINK).
*)
Theorem register_counter_correct: refines register_counter counter.
Proof.
  eapply forward_simulation with (f:=f).
  constructor.
  - intros. exists new_counter. intuition.
    reflexivity. unfold f.
    simpl in H.
    unfold linked_new_state in H.
    simpl in H. inversion H.
    unfold register_new_state in H0.
    rewrite H0.
    unfold register_counter_new_state in H1.
    rewrite H1. intuition.
  - intros. inversion H0; subst.
    inversion H1; subst.
    -- simpl. unfold f in H. simpl in H.
      intuition. subst.
      exists (mkCntState ((pid, Inv_Inc):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite H2. reflexivity.
      }
      econstructor; eauto.
      rewrite <-H2. apply gather_requests_preserves_pid_notin; auto.
      rewrite <-H. apply gather_responses_preserves_pid_notin; auto.
      destruct s2.
      reflexivity.
    -- simpl. unfold f in H. simpl in H.
      intuition. subst.
      exists (mkCntState ((pid, Inv_Read):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite H2. reflexivity.
      }
      econstructor; eauto.
      rewrite <-H2. apply gather_requests_preserves_pid_notin; auto.
      rewrite <-H. apply gather_responses_preserves_pid_notin; auto.
      destruct s2.
      reflexivity.
  - intros. inversion H0; subst.
    inversion H1; subst.
    -- simpl. unfold f in H. simpl in H.
      intuition.
      rewrite gather_requests_dist in H2. simpl in H2.
      rewrite gather_responses_dist in H. simpl in H.
      exists (mkCntState (requests s2) (gather_responses (pc' ++ pc'')) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite <-H2. apply gather_requests_dist.
      }
      eapply counter_final_state_inc with (inv:=requests s2) (res:=responses s2); eauto.
      rewrite <-H. simpl. eauto. destruct s2. eauto.
      rewrite gather_responses_dist. rewrite H4. reflexivity.
    -- simpl. unfold f in H. simpl in H.
      intuition.
      rewrite gather_requests_dist in H2. simpl in H2.
      rewrite gather_responses_dist in H. simpl in H.
      exists (mkCntState (requests s2) (gather_responses (pc' ++ pc'')) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite <-H2. apply gather_requests_dist.
      }
      eapply counter_final_state_read with (inv:=requests s2) (res:=responses s2); eauto.
      rewrite <-H. simpl. eauto. destruct s2. eauto.
      rewrite gather_responses_dist. rewrite H4. reflexivity.
  - intros. inversion H0; subst.
    -- clear H0.
        simpl in H1.
        simpl in H. exists s2.
        intuition.
        econstructor; eauto.
        unfold f. simpl.
        unfold f in H. simpl in H.
        inversion H1; subst; simpl in H; simpl;
        rewrite gather_requests_dist in H;
        rewrite gather_responses_dist in H;
        rewrite gather_requests_dist;
        rewrite gather_responses_dist;
        simpl in H; simpl; intuition.
    -- exists s2. intuition.
      econstructor; eauto.
      unfold f. simpl.
      unfold f in H. simpl in H. intuition.
      simpl in H3. rewrite <-H5.
      inversion H3; subst.
      --- reflexivity.
      --- reflexivity.
    -- destruct act.
      --- simpl in H1.
        inversion H1; subst.
        simpl. simpl in H0.
        unfold f in H. simpl in H. intuition.
        subst. simpl in H1.
        destruct (value s2 =? old) eqn:Heq.
        + exists (mkCntState (requests s2) ((pid, Res_Inc)::responses s2) (S (value s2))).
          simpl. intuition.
          ++ eapply Step_Internal with (int:=int_cnt_inc); eauto.
            2: { econstructor; eauto. }
            simpl.
Admitted.
  
End RegisterCounter.