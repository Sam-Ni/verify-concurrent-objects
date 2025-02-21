Require Import 
  List
  Nat
  LTS
  Counter
  Register
  LibVar
.
Require 
  LibEnv.
Import ListNotations.

(* 
  An implementation (lts li_register li_counter) of atomic counter is defined.

  The pseudocode of function Increment and Read is shown as follows.
  The line numbers correspond to RCounter_pc, the program counter.

  void Increment ()
  1. call Register.Read()
  2. get result from Register.Read()
  3. assign the result to local variable 'r'
  4. call Register.CAS(r, r + 1)
  5. get result from Register.CAS(r, r + 1)
  6. if result is false goto 1
  7. return

  nat Read ()
  1. call Register.Read()
  2. get result from Register.Read()
  3. return result
*)
Section RegisterCounterImpl.

  Inductive RCounter_pc :=
  | DInc1
  | DInc2
  | DInc3 (ret : nat)
  | DInc4
	| DInc5 
	| DInc6 (ret : bool)
	| DInc7
	| DRead1
	| DRead2
	| DRead3 (ret : nat)
  .

  Inductive Internal :=
  | Assign
  | Goto.

  (* pc - program counter for each process
     r - local variable used in inc for each process *)
  Record RCounter_state := mkDCntState {
    pc : LibEnv.env RCounter_pc;
    r : nat -> nat
  }.

  Definition new_register_counter := mkDCntState nil (fun _ => O).

  Definition register_counter_new_state reg_cnt_st := reg_cnt_st = new_register_counter.

  Import LibEnv.

  Inductive register_counter_initial_state : RCounter_state -> Pid -> query li_counter -> RCounter_state -> Prop :=
  | register_counter_initial_state_inc : forall pc st st' pid r,
      st = mkDCntState pc r ->
      pid # pc ->
      st' = mkDCntState ((pid, DInc1)::pc) r ->
      register_counter_initial_state st pid CntInc st'
  | register_counter_initial_state_read : forall pc st st' pid r,
      st = mkDCntState pc r ->
      pid # pc ->
      st' = mkDCntState ((pid, DRead1)::pc) r ->
      register_counter_initial_state st pid CntRead st'
  .

  Inductive register_counter_final_state : RCounter_state -> Pid -> reply li_counter -> RCounter_state -> Prop :=
  | register_counter_final_state_inc : forall pc st st' pid pc' pc'' r,
      pc = pc' ++ [(pid, DInc7)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ pc'') r ->
      register_counter_final_state st pid CntIncOk st'
  | register_counter_final_state_read : forall pc st st' pid pc' pc'' r ret,
      pc = pc' ++ [(pid, DRead3 ret)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ pc'') r ->
      register_counter_final_state st pid (CntReadOk ret) st'
  .

  Inductive register_counter_step : RCounter_state -> Pid -> Internal -> RCounter_state -> Prop :=
  | register_counter_step_inc_assign : forall pc st st' pid pc' pc'' ret r,
      pc = pc' ++ [(pid, DInc3 ret)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc4)] ++ pc'') (fun x => if x =? pid then ret else r x) ->
      register_counter_step st pid Assign st'
  | register_counter_step_inc_goto_t : forall pc st st' pid pc' pc'' r,
      pc = pc' ++ [(pid, DInc6 true)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc7)] ++ pc'') r ->
      register_counter_step st pid Goto st'
  | register_counter_step_inc_goto_f : forall pc st st' pid pc' pc'' r,
      pc = pc' ++ [(pid, DInc6 false)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc1)] ++ pc'') r ->
      register_counter_step st pid Goto st'
  .

  Inductive register_counter_at_external : RCounter_state -> Pid -> query li_register -> RCounter_state -> Prop :=
  | register_counter_at_external_inc_read : forall pc st pid pc' pc'' r st',
      pc = pc' ++ [(pid, DInc1)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc2)] ++ pc'') r ->
      register_counter_at_external st pid RegRead st'
  | register_counter_at_external_inc_cas : forall pc st pid pc' pc'' r st',
      pc = pc' ++ [(pid, DInc4)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc5)] ++ pc'') r ->
      register_counter_at_external st pid (RegCAS (r pid) (S (r pid))) st'
  | register_counter_at_external_read_read : forall pc st pid pc' pc'' r st',
      pc = pc' ++ [(pid, DRead1)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DRead2)] ++ pc'') r ->
      register_counter_at_external st pid RegRead st'
  .

  Inductive register_counter_after_external : RCounter_state -> Pid -> reply li_register -> RCounter_state -> Prop :=
  | register_counter_after_external_inc_read_ok : forall pc st st' pid pc' pc'' ret r,
      pc = pc' ++ [(pid, DInc2)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc3 ret)] ++ pc'') r ->
      register_counter_after_external st pid (RegReadOk ret) st'
  | register_counter_after_external_inc_cas : forall pc st st' pid pc' pc'' r ret,
      pc = pc' ++ [(pid, DInc5)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DInc6 ret)] ++ pc'') r ->
      register_counter_after_external st pid (RegCASOk ret) st'
  | register_counter_after_external_read_read_ok : forall pc st st' pid pc' pc'' ret r,
      pc = pc' ++ [(pid, DRead2)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DRead3 ret)] ++ pc'') r ->
      register_counter_after_external st pid (RegReadOk ret) st'
  .

  Definition register_counter_valid_int_query :=
    fun int qb =>
    match int, qb with
    | Assign, CntInc => True
    | Goto, CntInc => True
    | _, _ => False
    end.

  Definition register_counter_valid_query_query :=
    fun qa qb =>
    match qa, qb with
    | RegCAS _ _, CntInc => True
    | RegRead, CntInc => True
    | RegRead, CntRead => True
    | _, _ => False
    end.

  Definition register_counter_impl : lts Register.li_register Counter.li_counter := mkLTS Register.li_register Counter.li_counter
    RCounter_state
    Internal
    register_counter_step
    register_counter_new_state
    register_counter_initial_state
    register_counter_at_external
    register_counter_after_external
    register_counter_final_state
    register_counter_valid_int_query
    register_counter_valid_query_query
  .
  
End RegisterCounterImpl.

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
