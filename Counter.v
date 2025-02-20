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
  | CntInc
  | CntRead
  .

  Inductive Counter_reply :=
  | CntIncOk
  | CntReadOk (value : nat)
  .

  Definition li_counter_valid_query_reply : Counter_query -> Counter_reply -> Prop :=
    fun q r => match q, r with
    | CntInc, CntIncOk => True
    | CntRead, CntReadOk _ => True
    | _, _ => False
    end.

  Definition li_counter :=
    {|
      query := Counter_query;
      reply := Counter_reply;
      valid_query_reply := li_counter_valid_query_reply;
    |}.

  Inductive Internal := 
  | int_cnt_inc
  | int_cnt_read.

  (* Inductive Invocation :=
  | Inv_Inc
  | Inv_Read.

  Inductive Response :=
  | Res_Inc
  | Res_Read (value : nat). *)

  Record Counter_state := mkCntState {
    requests : LibEnv.env Counter_query; 
    responses : LibEnv.env Counter_reply;
    value : nat
  }.

  Definition new_counter := mkCntState nil nil O.

  Definition counter_new_state cnt_st := cnt_st = new_counter.

  Import LibEnv.

  Inductive counter_initial_state : Counter_state -> Pid -> query li_counter -> Counter_state -> Prop :=
  | counter_initial_state_inc : forall pid st st' inv res v,
    pid # inv -> pid # res ->
    st = mkCntState inv res v ->
    st' = mkCntState ((pid, CntInc)::inv) res v ->
    counter_initial_state st pid CntInc st'
  | counter_initial_state_read : forall pid st st' inv res v,
    pid # inv -> pid # res ->
    st = mkCntState inv res v ->
    st' = mkCntState ((pid, CntRead)::inv) res v ->
    counter_initial_state st pid CntRead st'
  .

  Inductive counter_final_state : Counter_state -> Pid -> reply li_counter -> Counter_state -> Prop :=
  | counter_final_state_inc : forall pid inv res res1 res2 v st st' res',
    sameset res (res1 ++ [(pid, CntIncOk)] ++ res2) ->
    st = mkCntState inv res v ->
    res' = (res1 ++ res2) ->
    st' = mkCntState inv res' v ->
    counter_final_state st pid CntIncOk st'
  | counter_final_state_read : forall pid inv res res1 res2 v st st' ret res',
    sameset res (res1 ++ [(pid, CntReadOk ret)] ++ res2) ->
    st = mkCntState inv res v ->
    res' = (res1 ++ res2) ->
    st' = mkCntState inv res' v ->
    counter_final_state st pid (CntReadOk ret) st'
  .

  Inductive counter_step : Counter_state -> Pid -> Internal -> Counter_state -> Prop :=
  | counter_step_inc : forall pid st st' inv inv1 inv2 res v inv',
    sameset inv (inv1 ++ [(pid, CntInc)] ++ inv2) ->
    st = mkCntState inv res v ->
    inv' = (inv1 ++ inv2) ->
    st' = mkCntState inv' ((pid, CntIncOk)::res) (S v) ->
    counter_step st pid int_cnt_inc st'
  | counter_step_read : forall pid st st' inv inv1 inv2 res v inv',
    sameset inv (inv1 ++ [(pid, CntRead)] ++ inv2) ->
    st = mkCntState inv res v ->
    inv' = (inv1 ++ inv2) ->
    st' = mkCntState inv' ((pid, CntReadOk v)::res) v ->
    counter_step st pid int_cnt_read st' 
  .

  Inductive counter_at_external : Counter_state -> Pid -> query li_null -> Counter_state -> Prop :=.

  Inductive counter_after_external : Counter_state -> Pid -> reply li_null -> Counter_state -> Prop :=.

  Definition counter_valid_int_query int q :=
    match int, q with
    | int_cnt_inc, CntInc => True
    | int_cnt_read, CntRead => True
    | _, _ => False
    end.

  Definition counter_valid_query_query (qa : query li_null) (qb : query li_counter) : Prop :=
    match qa with end.

  Definition counter : lts li_null li_counter := mkLTS li_null li_counter
    Counter_state
    Internal
    counter_step
    counter_new_state
    counter_initial_state
    counter_at_external
    counter_after_external
    counter_final_state
    counter_valid_int_query
    counter_valid_query_query
  .
  
End Counter.
