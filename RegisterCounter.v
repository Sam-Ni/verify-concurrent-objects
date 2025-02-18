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
  eapply forward_simulation_inv_ind with (f:=f) (inv:= fun (st : register_counter.(state)) => RegStateWF st.(L1State)).
  unfold fsim_properties_inv_ind. intuition.
  - simpl. unfold invariant_ind. simpl. intuition; destruct st; simpl.
    -- unfold linked_new_state in H. simpl in H.
      intuition. unfold RegStateWF.
      unfold register_new_state in H0.
      inversion H0; subst. unfold new_register.
      simpl. intuition; econstructor.
    -- simpl in H.
      inversion H0; subst.
      + inversion H2; subst. simpl. assumption.
      + simpl. inversion H2; subst.
        eapply reg_initial_preserves_ok; eauto.
      + simpl. inversion H4; subst.
        eapply reg_step_preserves_ok; eauto.
      + simpl. inversion H5; subst.
        eapply reg_final_state_preserves_ok; eauto.
    -- simpl in H.
      inversion H0; subst.
      simpl. inversion H2; subst; assumption.
    -- simpl in H.
      inversion H0; subst.
      simpl. inversion H2; subst; assumption.
  - intros. exists new_counter. intuition.
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
    inversion H2; subst.
    -- simpl. unfold f in H0. simpl in H0.
      intuition. subst.
      exists (mkCntState ((pid, CntInc):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite H3. reflexivity.
      }
      econstructor; eauto.
      rewrite <-H3. apply gather_requests_preserves_pid_notin; auto.
      rewrite <-H0. apply gather_responses_preserves_pid_notin; auto.
      destruct s2.
      reflexivity.
    -- simpl. unfold f in H0. simpl in H0.
      intuition. subst.
      exists (mkCntState ((pid, CntRead):: requests s2) (responses s2) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite H3. reflexivity.
      }
      econstructor; eauto.
      rewrite <-H3. apply gather_requests_preserves_pid_notin; auto.
      rewrite <-H0. apply gather_responses_preserves_pid_notin; auto.
      destruct s2.
      reflexivity.
  - intros. inversion H1; subst.
    inversion H2; subst.
    -- simpl. unfold f in H0. simpl in H0.
      intuition.
      rewrite gather_requests_dist in H3. simpl in H3.
      rewrite gather_responses_dist in H0. simpl in H0.
      exists (mkCntState (requests s2) (gather_responses (pc' ++ pc'')) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite <-H3. apply gather_requests_dist.
      }
      eapply counter_final_state_inc with (inv:=requests s2) (res:=responses s2); eauto.
      rewrite <-H0. simpl. eauto. destruct s2. eauto.
      rewrite gather_responses_dist. rewrite H5. reflexivity.
    -- simpl. unfold f in H0. simpl in H0.
      intuition.
      rewrite gather_requests_dist in H3. simpl in H3.
      rewrite gather_responses_dist in H0. simpl in H0.
      exists (mkCntState (requests s2) (gather_responses (pc' ++ pc'')) (value s2)).
      intuition.
      2: {
        unfold f. simpl. intuition.
        rewrite <-H3. apply gather_requests_dist.
      }
      eapply counter_final_state_read with (inv:=requests s2) (res:=responses s2); eauto.
      rewrite <-H0. simpl. eauto. destruct s2. eauto.
      rewrite gather_responses_dist. rewrite H5. reflexivity.
  - intros. inversion H1; subst.
    -- clear H1.
        simpl in H2.
        simpl in H0. exists s2.
        intuition.
        econstructor; eauto.
        unfold f. simpl.
        unfold f in H0. simpl in H0.
        inversion H2; subst; simpl in H0; simpl;
        rewrite gather_requests_dist in H0;
        rewrite gather_responses_dist in H0;
        rewrite gather_requests_dist;
        rewrite gather_responses_dist;
        simpl in H0; simpl; intuition.
    -- exists s2. intuition.
      econstructor; eauto.
      unfold f. simpl.
      unfold f in H0. simpl in H0.
      inversion H2; subst; simpl in *;
      rewrite gather_requests_dist in H0;
        rewrite gather_responses_dist in H0;
        simpl in H0;
        rewrite gather_requests_dist;
        rewrite gather_responses_dist;
        simpl; inversion H4; subst; simpl in *;
        intuition.
    -- destruct act.
      --- simpl in *.
        destruct qb; intuition.
        inversion H2; subst.
        simpl in *.
        unfold f in H0. simpl in H0. intuition.
        subst. simpl in *.

        destruct H6 as [lst1 [lst2 [lst2st1 [lst2st2 [st1acts [st2acts [cs3 Htmp]]]]]]].
        destruct Htmp as [Hbefore Hremain].
        inversion Hbefore; subst.
        inversion H11; subst.
        simpl in Hremain, Hbefore. intuition.
        inversion H6; subst. clear H6.
        inversion H9; subst.
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
        apply ok_middle_inv in H5; intuition.
        inversion H6; subst. clear H6. simpl in *.
        exists (mkCntState (requests s2) (responses s2) (S (value s2))).

        simpl.
        f_equal.

        clear H9.  



        destruct (value s2 =? old) eqn:Heq.
        + exists (mkCntState (requests s2) ((pid, CntIncOk)::responses s2) (S (value s2))).
          simpl. intuition.
          ++ eapply Step_Internal with (int:=int_cnt_inc); eauto.
            2: { econstructor; eauto. }
            simpl.
Admitted.
  
End RegisterCounter.