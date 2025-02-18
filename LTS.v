Require Import
  List
  Nat.
From VCO Require LibEnv.
Import ListNotations.

(*
  Concurrent objects are formalized as (restricted) labeled transition systems (lts).
*)

Notation Pid := nat.

Section LTS.

(* 
  A general lts is parameterized with language interfaces liA and liB
  (the name'language interface' is adopted from CompCert.
  The name 'object interface' or 'type interface' is more appropriate in this context).

  The functions called by the lts are specified in liA and
  the functions provided by the lts are specified in liB.
  A function is specified with its invocations (query) and responses (reply).
*)
Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    valid_query_reply: query -> reply -> Prop;
  }.

(* 
  A lts comprises of 
  state - set of possible values of variables in the lts (e.g., value in a register object)
  internal - set of internal actions which are not observable by environment (e.g., assignment)
  step - transition enabled by internal actions
  new_state - set of states when the lts is created (e.g., constructors in c++)
  initial_state - transition enabled by query in liB
  at_external - transition enabled by query in liA
  after_external - transition enabled by reply in liB
  final_state - transition enable by reply in liB.

  A lts is created in the new_state,
  waiting for queries from the environment.

  When it gets query 'q' from process 'pid',
  its state get updated through initial_state, which marks that q from pid started.
  Then the lts can do one of the following things (if enabled):
  1. get another query q' in liB
  2. progress in the query q through step
  3. call external functions in liA through at_external
  4. get a reply from external functions in liA through after_external
  5. reply the query q in liB through final_state
*)
Record lts liA liB: Type := mkLTS {
  state : Type;
  internal : Type;
  step : state -> Pid -> internal -> state -> Prop;
  (* valid_query: query liB -> bool; *)
  new_state : state -> Prop;
  initial_state: state -> Pid -> query liB -> state -> Prop;
  at_external: state -> Pid -> query liA -> state -> Prop;
  after_external: state -> Pid -> reply liA -> state -> Prop;
  final_state: state -> Pid -> reply liB -> state -> Prop;
  valid_int_query : internal -> query liB -> Prop;
  valid_query_query : query liA -> query liB -> Prop;
}.

(* 
  Special language interface with no queries and replies.
  A concurrent object can be formalized as lts li_null liB.
  We can get such an object by composing its implementation of type lts liA liB
  with lower objects of type lts li_null liA (see Section LINK).
*)
Definition li_null :=
  {|
    query := Empty_set;
    reply := Empty_set;
    valid_query_reply := fun q r => match q, r with end
  |}.

End LTS.

Arguments state {liA} {liB}.
Arguments internal {liA} {liB}.
Arguments step {liA} {liB}.
Arguments new_state {liA} {liB}.
Arguments initial_state {liA} {liB}.
Arguments at_external {liA} {liB}.
Arguments after_external {liA} {liB}.
Arguments final_state {liA} {liB}.
Arguments valid_int_query {liA} {liB}.
Arguments valid_query_query {liA} {liB}.


(* 
  An object (of type lts li_null liB) can be specified by its observable executions from new_state.
  A possible execution can be described by a list of events.
*)
Section Trace.

Context {liA liB : language_interface}.
Variable L: lts liA liB.

Definition automaton_step st st' : Prop :=
  exists pid,
  ((exists qb, initial_state L st pid qb st') \/
  (exists rb, final_state L st pid rb st') \/
  (exists qa, at_external L st pid qa st') \/
  (exists ra, after_external L st pid ra st') \/
  (exists int, step L st pid int st')
  ).

Inductive _event :=
| event_invB : query liB -> _event
| event_resB : reply liB -> _event
| event_invA : query liA -> _event
| event_resA : reply liA -> _event
.

Definition event := (nat * _event)%type.

Definition int_event := (nat * internal L)%type.

(* 
  valid_execution_fragment records the list of events from state st to st'.
*)
Inductive valid_execution_fragment (st st' : L.(state)) : list event -> list int_event -> Prop :=
| Step_None :
    st = st' ->
    valid_execution_fragment st st' nil nil
| Step_Internal : forall st'' acts in_acts (int : L.(internal)) pid,
    step L st pid int st'' ->
    valid_execution_fragment st'' st' acts in_acts ->
    valid_execution_fragment st st' acts ((pid, int) :: in_acts)
| Step_At_External : forall st'' acts in_acts qa pid,
    at_external L st pid qa st'' ->
    valid_execution_fragment st'' st' acts in_acts ->
    valid_execution_fragment st st' ((pid, event_invA qa) :: acts) in_acts
| Step_After_External : forall st'' acts in_acts ra pid,
    after_external L st pid ra st'' ->
    valid_execution_fragment st'' st' acts in_acts ->
    valid_execution_fragment st st' ((pid, event_resA ra) :: acts) in_acts
| Step_Initial_Call : forall st'' acts in_acts qb pid,
    initial_state L st pid qb st'' ->
    valid_execution_fragment st'' st' acts in_acts ->
    valid_execution_fragment st st' ((pid, event_invB qb) :: acts) in_acts
| Step_Final_Return : forall st'' acts in_acts rb pid,
    final_state L st pid rb st'' ->
    valid_execution_fragment st'' st' acts in_acts ->
    valid_execution_fragment st st' ((pid, event_resB rb) :: acts) in_acts
.

Hint Constructors valid_execution_fragment : core.

Lemma valid_execution_fragment_join : forall (s s' s'' : L.(state)) a a' i i',
    valid_execution_fragment s s' a i ->
    valid_execution_fragment s' s'' a' i' ->
    valid_execution_fragment s s'' (a ++ a') (i ++ i').
Proof.
  intros.
  induction H; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_join' : forall (s s' s'' : L.(state)) a a' a'' i i' i'',
    valid_execution_fragment s s' a i ->
    valid_execution_fragment s' s'' a' i' ->
    a'' = a ++ a' ->
    i'' = i ++ i' ->
    valid_execution_fragment s s'' a'' i''.
Proof.
  intros; subst; eauto using valid_execution_fragment_join.
Qed.

Fixpoint gather_pid_external_events events pid : list event :=
  match events with
  | nil => nil
  | (pid', act) :: events' =>
      let remaining_events := gather_pid_external_events events' pid in
      if pid =? pid' then (pid', act) :: remaining_events
                      else remaining_events
  end.

(* 
  A list of events 'acts' is a trace of the object
  if 'acts' is an execution from new_state to some state.
*)
Definition in_traces acts :=
  exists init final in_acts, L.(new_state) init /\ valid_execution_fragment init final acts in_acts.

Definition reachable st :=
  exists init acts in_acts, L.(new_state) init /\ valid_execution_fragment init st acts in_acts.


(* 
  General invariant property of an object.
*)
Definition invariant (P : state L -> Prop) :=
  forall st, reachable st -> P st.

(* 
  Induction principle used to derive refinement below.
  at_external and after_external is redundant here since 
*)
Definition invariant_ind (P : state L -> Prop) :=
  (forall st, L.(new_state) st -> P st) /\
  (forall st st' act pid,
    P st ->
    step L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    initial_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    at_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    after_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    final_state L st pid act st' ->
    P st').

End Trace.

(*
  Compose two lts with the common interface liB.
  Potential problems (when proving simulation) lie in
  the definition of linked_state and linked_step.
*)
Section LINK.
  Context {liA liB liC: language_interface}.
  Variable L1: lts liA liB.
  Variable L2: lts liB liC.

  Inductive call_return : Type :=
  | Call : query liB -> call_return
  | Return : reply liB -> call_return.

  (* 
    (Currently,) linked_state is the product of state L1 and state L2.
    potential problem:
      the information seem not enough in the simulation proof;
      additional structure (maybe the call_stack from L2 to L1) is needed.
  *)
  Record linked_state : Type := mkLinkedState {
    L1State : L1.(state);
    L2State : L2.(state);
    call_stack : LibEnv.env (call_return)
  }.

  Inductive linked_internal : Type :=
  | intL1 (act : L1.(internal))
  | intL2 (act : L2.(internal))
  | intQuery (act : query liB)
  | intReply (act : reply liB).

  Definition linked_new_state lst : Prop := 
    L1.(new_state) lst.(L1State) /\ 
    L2.(new_state) lst.(L2State) /\
    lst.(call_stack) = nil.

  Inductive linked_initial_state : linked_state -> Pid -> query liC -> linked_state -> Prop :=
  | linked_initial_state_L2 : forall lst lst' st2 st2' qc st1 cs pid,
      initial_state L2 st2 pid qc st2' ->
      lst = mkLinkedState st1 st2 cs ->
      lst' = mkLinkedState st1 st2' cs ->
      linked_initial_state lst pid qc lst'
  .

  Import LibEnv.

  (* 
    Problem: the rule linked_step_L1_internal is too general!
    We must add additional constraints:
    1. there is a correspondence between act and state st2
       (i.e., st2 is waiting for st1 to execute act);
    2. st1 still 'remembers' the arguments passed by st2.
  *)
  Inductive linked_step : linked_state -> Pid -> linked_internal -> linked_state -> Prop :=
  | linked_step_L2_internal : forall st1 st2 st2' act lst lst' cs pid,
      pid # cs -> (* L2 is enabled by pid only if pid is not blocking for calling L1 *)
      step L2 st2 pid act st2' ->
      lst = mkLinkedState st1 st2 cs ->
      lst' = mkLinkedState st1 st2' cs ->
      linked_step lst pid (intL2 act) lst'
  | linked_step_L2_push : forall st1 st2 st1' qb lst lst' st2' cs cs' pid,
      at_external L2 st2 pid qb st2' ->
      lst = mkLinkedState st1 st2 cs ->
      initial_state L1 st1 pid qb st1' ->
      cs' = (pid, Call qb):: cs ->
      lst' = mkLinkedState st1' st2' cs' ->
      linked_step lst pid (intQuery qb) lst'
  | linked_step_L1_internal : forall st1 st2 st1' act lst lst' cs pid cs1 cs2 qb,
      step L1 st1 pid act st1' ->
      valid_int_query L1 act qb ->
      cs = cs1 ++ [(pid, Call qb)] ++ cs2 ->
      lst = mkLinkedState st1 st2 cs ->
      (exists lst1 lst2 lst2st1 lst2st2 st1acts st2acts cs' st2in_acts st1in_acts,
        linked_step lst1 pid (intQuery qb) lst2 /\
        lst2 = mkLinkedState lst2st1 lst2st2 cs' /\
        valid_execution_fragment L2 lst2st2 lst.(L2State) st2acts st2in_acts /\
        valid_execution_fragment L1 lst2st1 lst.(L1State) st1acts st1in_acts /\
        gather_pid_external_events st1acts pid = []) ->
      lst' = mkLinkedState st1' st2 cs ->
      linked_step lst pid (intL1 act) lst'
  | linked_step_L1_pop : forall st1 st1' rb st2 st2' lst lst' cs pid qb cs1 cs2 cs',
      final_state L1 st1 pid rb st1' ->
      after_external L2 st2 pid rb st2' ->
      valid_query_reply liB qb rb ->
      cs = cs1 ++ [(pid, Call qb)] ++ cs2 ->
      lst = mkLinkedState st1 st2 cs ->
      cs' = cs1 ++ [(pid, Return rb)] ++ cs2 ->
      lst' = mkLinkedState st1' st2' cs' ->
      linked_step lst pid (intReply rb) lst'
  .

  Inductive linked_at_external : linked_state -> Pid -> query liA -> linked_state -> Prop :=
  | linked_at_external_L1 : forall st1 qa st2 lst st1' lst' cs pid,
      at_external L1 st1 pid qa st1' ->
      (* at_external L2 st2 qb -> *)
      (* reachable st1 qa qb -> *)
      lst = mkLinkedState st1 st2 cs ->
      lst' = mkLinkedState st1' st2 cs ->
      linked_at_external lst pid qa lst'
  .

  Inductive linked_after_external : linked_state -> Pid -> reply liA -> linked_state -> Prop :=
  | linked_after_external_L1 : forall st1 ra st1' lst lst' st2 pid cs,
      after_external L1 st1 pid ra st1' ->
      lst = mkLinkedState st1 st2 cs ->
      lst' = mkLinkedState st1' st2 cs ->
      linked_after_external lst pid ra lst'
  .

  Inductive linked_final_state : linked_state -> Pid -> reply liC -> linked_state -> Prop :=
  | linked_final_state_L2 : forall st1 st2 rc st2' lst lst' pid cs,
      final_state L2 st2 pid rc st2' ->
      lst = mkLinkedState st1 st2 cs ->
      lst' = mkLinkedState st1 st2' cs ->
      linked_final_state lst pid rc lst'
  .

  Definition linked_valid_int_query :=
    fun int qc => match int with
    | intL1 act => exists qb, valid_int_query L1 act qb /\ valid_query_query L2 qb qc
    | intL2 act => valid_int_query L2 act qc
    | intQuery qb => valid_query_query L2 qb qc
    | intReply rb => exists qb, valid_query_reply liB qb rb /\ valid_query_query L2 qb qc
    end.

  Definition linked_query_query :=
    fun qa qc => 
      exists qb, valid_query_query L1 qa qb /\
                  valid_query_query L2 qb qc.

  Definition linked_lts : lts liA liC :=
    mkLTS liA liC linked_state
      linked_internal
      linked_step
      linked_new_state
      linked_initial_state
      linked_at_external
      linked_after_external
      linked_final_state
      linked_valid_int_query
      linked_query_query.

End LINK.

Arguments L1State {liA liB liC L1 L2}.
Arguments L2State {liA liB liC L1 L2}.