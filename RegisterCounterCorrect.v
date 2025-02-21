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
  Counter
  RegisterCounter
  RegisterCounterMapping.
Import ListNotations.

Section Correctness.

(* 
  forward simulation between RegisterCounter and CounterSpec.
  It indicates that requests, responses and value of Counter can be computed by observing the state of RegisterCounter.
*)
Definition f (s1 : register_counter.(state)) (s2 : counter.(state)) :=
  sameset (gather_requests' s1.(L2State).(RegisterCounterImpl.pc) s1.(L1State)) s2.(requests) /\
  sameset (gather_responses' s1.(L2State).(RegisterCounterImpl.pc) s1.(L1State)) s2.(responses) /\
  s1.(L1State).(Register.value) = s2.(value).

(* 
  Prove that RegisterCounter refines Counter by applying forward simulation f with invariant of Register and RegisterCounterImpl.
  From the proof it can be seen that
  Inc takes effects only in the case where int_cas succeeds
  and that Read takes effects only in the case where int_read (of Register) performs,
  which indicates that our RegisterCounter is linearizable.
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

End Correctness.