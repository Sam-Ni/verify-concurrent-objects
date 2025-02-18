Require Import
  List
  Nat
  Arith
  LTS
  LibVar.
From VCO Require LibEnv.
Import ListNotations.

(* 
  Linearizability is a special kind of refinement which additionally requires that
  there is only one internal action for each function in
  the specification.

  Our goal is to build up objects from smaller objects and
  verify them with the specification (simpler than implementation) of these smaller ones.

  The specification of an atomic register (lts li_null li_register)
  equipped with functions CAS and Read is defined below.
  It is the smallest object in our example.
*)
Section Register.

  (* 
    Queries and replies provided by Register.
    The first parameter of each constructor is the process 'pid'
    who calls to or returns from Register.
  *)
  Inductive Register_query :=
  | RegCAS (old : nat) (new : nat)
  | RegRead
  .

  Inductive Register_reply :=
  | RegCASOk (success : bool)
  | RegReadOk (value : nat)
  .

  Definition li_register_valid_query_reply :=
    fun q r => match q, r with
    | RegCAS _ _, RegCASOk _ => True
    | RegRead, RegReadOk _ => True
    | _, _ => False
    end.

  Definition li_register :=
    {|
      query := Register_query;
      reply := Register_reply;
      valid_query_reply := li_register_valid_query_reply;
    |}.

  Inductive Internal := 
  | int_cas
  | int_read.

  (* Inductive Invocation :=
  | Inv_CAS (old : nat) (new : nat)
  | Inv_Read.

  Inductive Response :=
  | Res_CAS (success : bool)
  | Res_Read (value : nat). *)

  (* 
    A register state comprises of
    requests - set of pending invocations (by process pid)
    responses - set of functions which has taken effect but yet returned (to pid)
    value - the value of the register.

    LibEnv.env T := list (nat*T)
  *)
  Record Register_state := mkRegState {
    requests : LibEnv.env Register_query; 
    responses : LibEnv.env Register_reply;
    value : nat
  }.

  Definition new_register := mkRegState nil nil O.

  Definition register_new_state reg_st := reg_st = new_register.

  Import LibEnv.

  (* 
    Called by environment
  *)
  Inductive register_initial_state : Register_state -> Pid -> query li_register -> Register_state -> Prop :=
  | register_initial_state_cas : forall pid old new st st' inv res v,
    pid # inv -> pid # res ->
    ok inv -> ok res ->
    st = mkRegState inv res v ->
    st' = mkRegState ((pid, RegCAS old new)::inv) res v ->
    register_initial_state st pid (RegCAS old new) st'
  | register_initial_state_read : forall pid st st' inv res v,
    pid # inv -> pid # res ->
    ok inv -> ok res ->
    st = mkRegState inv res v ->
    st' = mkRegState ((pid, RegRead)::inv) res v ->
    register_initial_state st pid (RegRead) st'
  .

  (* 
    Return to environment
  *)
  Inductive register_final_state : Register_state -> Pid -> reply li_register -> Register_state -> Prop :=
  | register_final_state_cas : forall pid inv res res' res'' b v st st',
    res = res' ++ [(pid, RegCASOk b)] ++ res'' ->
    ok inv -> ok res ->
    st = mkRegState inv res v ->
    st' = mkRegState inv (res' ++ res'') v ->
    register_final_state st pid (RegCASOk b) st'
  | register_final_state_read : forall pid inv res res' res'' v st st' ret,
    res = res' ++ [(pid, RegReadOk ret)] ++ res'' ->
    ok inv -> ok res ->
    st = mkRegState inv res v ->
    st' = mkRegState inv (res' ++ res'') v ->
    register_final_state st pid (RegReadOk ret) st'
  .

  (* 
    Internal execution
  *)
  Inductive register_step : Register_state -> Pid -> Internal -> Register_state -> Prop :=
  | register_step_cas : forall pid st st' inv inv' inv'' res v old new,
    inv = inv' ++ [(pid, RegCAS old new)] ++ inv'' ->
    ok inv -> ok res ->
    pid # res ->
    st = mkRegState inv res v ->
    st' = mkRegState (inv' ++ inv'') ((pid, RegCASOk (st.(value) =? old))::res) (if value st =? old then new else old) ->
    register_step st pid int_cas st'
  | register_step_read : forall pid st st' inv inv' inv'' res v,
    inv = inv' ++ [(pid, RegRead)] ++ inv'' ->
    ok inv -> ok res ->
    pid # res ->
    st = mkRegState inv res v ->
    st' = mkRegState (inv' ++ inv'') ((pid, RegReadOk v)::res) v ->
    register_step st pid int_read st' 
  .

  (* 
    No external calls since Register does not rely on other objects
  *)
  Inductive register_at_external : Register_state -> Pid -> query li_null -> Register_state -> Prop :=.

  Inductive register_after_external : Register_state -> Pid -> reply li_null -> Register_state -> Prop :=.

  Definition register_valid_int_query int q :=
    match int, q with
    | int_cas, RegCAS _ _ => True
    | int_read, RegRead => True
    | _, _ => False
    end.

  Definition register_valid_query_query (qa : query li_null) (qb : query li_register) : Prop :=
    match qa with end.

  Definition Register : lts li_null li_register  := mkLTS li_null li_register
    Register_state
    Internal
    register_step
    register_new_state
    register_initial_state
    register_at_external
    register_after_external
    register_final_state
    register_valid_int_query
    register_valid_query_query
  .
  
End Register.

Section Properties.

Import LibEnv.

Definition RegStateWF st :=
  ok st.(requests) /\ ok st.(responses).

Lemma reg_initial_preserves_ok: forall st st' pid qb,
  initial_state Register st pid qb st' ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegStateWF; simpl; intuition;
  econstructor; eauto.
Qed.

Lemma reg_final_state_preserves_ok: forall st st' pid rb,
  final_state Register st pid rb st' ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegStateWF; simpl; intuition;
  apply ok_remove in H2; intuition.
Qed.

Lemma reg_at_external_preserves_ok: forall st st' pid qa,
  at_external Register st pid qa st' ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegStateWF; simpl; intuition;
  apply ok_remove in H2; intuition.
Qed.

Lemma reg_after_external_preserves_ok: forall st st' pid ra,
  after_external Register st pid ra st' ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegStateWF; simpl; intuition;
  apply ok_remove in H2; intuition.
Qed.

Lemma reg_step_preserves_ok: forall st st' pid int,
  step Register st pid int st' ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  inversion 1; intros; subst; simpl;
  unfold RegStateWF; simpl; intuition;
  apply ok_remove in H1; intuition;
  econstructor; eauto.
Qed.

Lemma astep_preserves_ok: forall st st',
  automaton_step Register st st' ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  intros. unfold automaton_step in H.
  destruct H as [pid Htmp]. intuition.
  - destruct H as [a Ha].
    eapply reg_initial_preserves_ok; eauto.
  - destruct H1 as [a Ha].
    eapply reg_final_state_preserves_ok; eauto.
  - destruct H as [a Ha].
    eapply reg_at_external_preserves_ok; eauto.
  - destruct H1 as [a Ha].
    eapply reg_after_external_preserves_ok; eauto.
  - destruct H1 as [a Ha].
    eapply reg_step_preserves_ok; eauto.
Qed.

Lemma valid_execution_preserves_ok: forall st st' acts in_acts,
  valid_execution_fragment Register st st' acts in_acts ->
  RegStateWF st ->
  RegStateWF st'.
Proof.
  induction 1; simpl; intros.
  - subst; auto.
  - eapply reg_step_preserves_ok in H; eauto.
  - eapply reg_at_external_preserves_ok in H; eauto.
  - eapply reg_after_external_preserves_ok in H; eauto.
  - eapply reg_initial_preserves_ok in H; eauto.
  - eapply reg_final_state_preserves_ok in H; eauto.
Qed.
  
Lemma reachable_inv: forall st,
  reachable Register st ->
  RegStateWF st.
Proof.
  intros. unfold reachable in H.
  destruct H as [init [acts [in_acts [Hnew Hexe]]]].
  eapply valid_execution_preserves_ok; eauto.
  inversion Hnew; subst.
  unfold new_register.
  unfold RegStateWF. simpl. intuition; econstructor.
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
  RegStateWF st ->
  binds pid qb' st'.(requests) ->
  valid_execution_fragment Register st st' acts in_acts ->
  qb = qb'.
Proof.
  intros. induction H3.
  - subst. eapply binds_same; eauto.
    unfold RegStateWF in H1; intuition.
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
    -- eapply reg_step_preserves_ok; eauto.
  - inversion H3.
  - inversion H3.
  - simpl in H.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H.
    -- apply IHvalid_execution_fragment; auto.
      eapply initial_preserves_binds; eauto.
      apply Nat.eqb_neq; auto.
      eapply reg_initial_preserves_ok; eauto.
  - simpl in H.
    destruct (pid =? pid0)eqn:Heq.
    -- inversion H.
    -- apply IHvalid_execution_fragment; auto.
      eapply final_preserves_binds; eauto.
      apply Nat.eqb_neq; auto.
      eapply reg_final_state_preserves_ok; eauto.
Qed.

End Properties.
