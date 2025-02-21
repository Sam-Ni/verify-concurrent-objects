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
  RegisterCounter.
Import ListNotations.

Section Mapping.

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

End Mapping.