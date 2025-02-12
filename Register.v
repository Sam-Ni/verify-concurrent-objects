Require Import 
  List
  Nat
  LTS.
Require LibEnv.
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
  | RegCAS (pid : nat) (old : nat) (new : nat)
  | RegRead (pid : nat)
  .

  Inductive Register_reply :=
  | RegCASOk (pid : nat) (success : bool)
  | RegReadOk (pid : nat) (value : nat)
  .

  Definition li_register :=
    {|
      query := Register_query;
      reply := Register_reply;
    |}.

  Inductive Internal := 
  | int_cas
  | int_read.

  Inductive Invocation :=
  | Inv_CAS (old : nat) (new : nat)
  | Inv_Read.

  Inductive Response :=
  | Res_CAS (success : bool)
  | Res_Read (value : nat).

  (* 
    A register state comprises of
    requests - set of pending invocations (by process pid)
    responses - set of functions which has taken effect but yet returned (to pid)
    value - the value of the register.

    LibEnv.env T := list (nat*T)
  *)
  Record Register_state := mkRegState {
    requests : LibEnv.env Invocation; 
    responses : LibEnv.env Response;
    value : nat
  }.

  Definition new_register := mkRegState nil nil O.

  Definition register_new_state reg_st := reg_st = new_register.

  Import LibEnv.

  (* 
    Called by environment
  *)
  Inductive register_initial_state : Register_state -> query li_register -> Register_state -> Prop :=
  | register_initial_state_cas : forall pid old new st st' inv res v,
    pid # inv -> pid # res ->
    st = mkRegState inv res v ->
    st' = mkRegState ((pid, Inv_CAS old new)::inv) res v ->
    register_initial_state st (RegCAS pid old new) st'
  | register_initial_state_read : forall pid st st' inv res v,
    pid # inv -> pid # res ->
    st = mkRegState inv res v ->
    st' = mkRegState ((pid, Inv_Read)::inv) res v ->
    register_initial_state st (RegRead pid) st'
  .

  (* 
    Return to environment
  *)
  Inductive register_final_state : Register_state -> reply li_register -> Register_state -> Prop :=
  | register_final_state_cas : forall pid inv res res' res'' b v st st',
    res = res' ++ [(pid, Res_CAS b)] ++ res'' ->
    st = mkRegState inv res v ->
    st' = mkRegState inv (res' ++ res'') v ->
    register_final_state st (RegCASOk pid b) st'
  | register_final_state_read : forall pid inv res res' res'' v st st' ret,
    res = res' ++ [(pid, Res_Read ret)] ++ res'' ->
    st = mkRegState inv res v ->
    st' = mkRegState inv (res' ++ res'') v ->
    register_final_state st (RegReadOk pid ret) st'
  .

  (* 
    Internal execution
  *)
  Inductive register_step : Register_state -> Internal -> Register_state -> Prop :=
  | register_step_cas : forall pid st st' inv inv' inv'' res v old new,
    inv = inv' ++ [(pid, Inv_CAS old new)] ++ inv'' ->
    st = mkRegState inv res v ->
    st' = mkRegState (inv' ++ inv'') ((pid, Res_CAS (st.(value) =? old))::res) (if value st =? old then new else old) ->
    register_step st int_cas st'
  | register_step_read : forall pid st st' inv inv' inv'' res v,
    inv = inv' ++ [(pid, Inv_Read)] ++ inv'' ->
    st = mkRegState inv res v ->
    st' = mkRegState (inv' ++ inv'') ((pid, Res_Read v)::res) v ->
    register_step st int_read st' 
  .

  (* 
    No external calls since Register does not rely on other objects
  *)
  Inductive register_at_external : Register_state -> query li_null -> Register_state -> Prop :=.

  Inductive register_after_external : Register_state -> reply li_null -> Register_state -> Prop :=.

  Definition Register : lts li_null li_register  := mkLTS li_null li_register
    Register_state
    Internal
    register_step
    register_new_state
    register_initial_state
    register_at_external
    register_after_external
    register_final_state
  .
  
End Register.