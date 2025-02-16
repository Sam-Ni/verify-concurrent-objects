Require Import 
  List
  Nat
  LTS
  Counter
  Register
.
Require 
  LibEnv.
Import ListNotations.

(* 
  An implementation (lts li_register li_counter) of atomic counter is defined.

  The pseudocode of function Increment and Read is shown as follows.
  The line numbers correspond to DCounter_pc, the program counter.

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
Section DCounter.

  Inductive DCounter_pc :=
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
  Record DCounter_state := mkDCntState {
    pc : LibEnv.env DCounter_pc;
    r : nat -> nat
  }.

  Definition new_register_counter := mkDCntState nil (fun _ => O).

  Definition register_counter_new_state reg_cnt_st := reg_cnt_st = new_register_counter.

  Import LibEnv.

  Inductive register_counter_initial_state : DCounter_state -> Pid -> query li_counter -> DCounter_state -> Prop :=
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

  Inductive register_counter_final_state : DCounter_state -> Pid -> reply li_counter -> DCounter_state -> Prop :=
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

  Inductive register_counter_step : DCounter_state -> Pid -> DCounter.Internal -> DCounter_state -> Prop :=
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

  Inductive register_counter_at_external : DCounter_state -> Pid -> query li_register -> DCounter_state -> Prop :=
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

  Inductive register_counter_after_external : DCounter_state -> Pid -> reply li_register -> DCounter_state -> Prop :=
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
      pc = pc' ++ [(pid, DRead1)] ++ pc'' ->
      st = mkDCntState pc r ->
      st' = mkDCntState (pc' ++ [(pid, DRead3 ret)] ++ pc'') r ->
      register_counter_after_external st pid (RegReadOk ret) st'
  .

  Definition register_counter_impl : lts Register.li_register Counter.li_counter := mkLTS Register.li_register Counter.li_counter
    DCounter_state
    DCounter.Internal
    register_counter_step
    register_counter_new_state
    register_counter_initial_state
    register_counter_at_external
    register_counter_after_external
    register_counter_final_state
  .
  
End DCounter.