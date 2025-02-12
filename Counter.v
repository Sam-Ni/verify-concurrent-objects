Require Import 
  List
  LTS.
Require LibEnv.
Import ListNotations.

(* 
  Specification of an atomic counter (lts li_null li_counter) is defined.
  The structure of the definitions are similar to the one of Register.
*)
Section Counter.

  Inductive Counter_query :=
  | CntInc (pid : nat)
  | CntRead (pid : nat)
  .

  Inductive Counter_reply :=
  | CntIncOk (pid : nat)
  | CntReadOk (pid : nat) (value : nat)
  .

  Definition li_counter :=
    {|
      query := Counter_query;
      reply := Counter_reply;
    |}.

  Inductive Internal := 
  | int_cnt_inc
  | int_cnt_read.

  Inductive Invocation :=
  | Inv_Inc
  | Inv_Read.

  Inductive Response :=
  | Res_Inc
  | Res_Read (value : nat).

  Record Counter_state := mkCntState {
    requests : LibEnv.env Invocation; 
    responses : LibEnv.env Response;
    value : nat
  }.

  Definition new_counter := mkCntState nil nil O.

  Definition counter_new_state cnt_st := cnt_st = new_counter.

  Import LibEnv.

  Inductive counter_initial_state : Counter_state -> query li_counter -> Counter_state -> Prop :=
  | counter_initial_state_inc : forall pid st st' inv res v,
    pid # inv -> pid # res ->
    st = mkCntState inv res v ->
    st' = mkCntState ((pid, Inv_Inc)::inv) res v ->
    counter_initial_state st (CntInc pid) st'
  | counter_initial_state_read : forall pid st st' inv res v,
    pid # inv -> pid # res ->
    st = mkCntState inv res v ->
    st' = mkCntState ((pid, Inv_Read)::inv) res v ->
    counter_initial_state st (CntRead pid) st'
  .

  Inductive counter_final_state : Counter_state -> reply li_counter -> Counter_state -> Prop :=
  | counter_final_state_inc : forall pid inv res res' res'' v st st',
    res = res' ++ [(pid, Res_Inc)] ++ res'' ->
    st = mkCntState inv res v ->
    st' = mkCntState inv (res' ++ res'') v ->
    counter_final_state st (CntIncOk pid) st'
  | counter_final_state_read : forall pid inv res res' res'' v st st' ret,
    res = res' ++ [(pid, Res_Read ret)] ++ res'' ->
    st = mkCntState inv res v ->
    st' = mkCntState inv (res' ++ res'') v ->
    counter_final_state st (CntReadOk pid ret) st'
  .

  Inductive counter_step : Counter_state -> Internal -> Counter_state -> Prop :=
  | counter_step_inc : forall pid st st' inv inv' inv'' res v,
    inv = inv' ++ [(pid, Inv_Inc)] ++ inv'' ->
    st = mkCntState inv res v ->
    st' = mkCntState (inv' ++ inv'') ((pid, Res_Inc)::res) (S v) ->
    counter_step st int_cnt_inc st'
  | counter_step_read : forall pid st st' inv inv' inv'' res v,
    inv = inv' ++ [(pid, Inv_Read)] ++ inv'' ->
    st = mkCntState inv res v ->
    st' = mkCntState (inv' ++ inv'') ((pid, Res_Read v)::res) v ->
    counter_step st int_cnt_read st' 
  .

  Inductive counter_at_external : Counter_state -> query li_null -> Counter_state -> Prop :=.

  Inductive counter_after_external : Counter_state -> reply li_null -> Counter_state -> Prop :=.

  Definition counter : lts li_null li_counter := mkLTS li_null li_counter
    Counter_state
    Internal
    counter_step
    counter_new_state
    counter_initial_state
    counter_at_external
    counter_after_external
    counter_final_state
  .
  
End Counter.
