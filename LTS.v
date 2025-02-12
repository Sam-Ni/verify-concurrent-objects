
(*
  Concurrent objects are formalized as (restricted) labeled transition systems (lts).
*)

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
  step : state -> internal -> state -> Prop;
  (* valid_query: query liB -> bool; *)
  new_state : state -> Prop;
  initial_state: state -> query liB -> state -> Prop;
  at_external: state -> query liA -> state -> Prop;
  after_external: state -> reply liA -> state -> Prop;
  final_state: state -> reply liB -> state -> Prop;
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

(*
  Compose two lts with the common interface liB.
  Potential problems (when proving simulation) lie in
  the definition of linked_state and linked_step.
*)
Section LINK.
  Context {liA liB liC: language_interface}.
  Variable L1: lts liA liB.
  Variable L2: lts liB liC.

  (* 
    (Currently,) linked_state is the product of state L1 and state L2.
    potential problem:
      the information seem not enough in the simulation proof;
      additional structure (maybe the call_stack from L2 to L1) is needed.
  *)
  Record linked_state : Type := mkLinkedState {
    L1State : L1.(state);
    L2State : L2.(state);
    (* call_stack : LibEnv.env ...  *)
  }.

  Inductive linked_internal : Type :=
  | intL1 (act : L1.(internal))
  | intL2 (act : L2.(internal))
  | intQuery (act : query liB)
  | intReply (act : reply liB).

  Definition linked_new_state lst : Prop := 
    L1.(new_state) lst.(L1State) /\ 
    L2.(new_state) lst.(L2State).
    (* lst.(call_stack) = nil. *)

  Inductive linked_initial_state : linked_state -> query liC -> linked_state -> Prop :=
  | linked_initial_state_L2 : forall lst lst' st2 st2' qc st1,
      initial_state L2 st2 qc st2' ->
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1 st2' ->
      linked_initial_state lst qc lst'
  .

  (* 
    Problem: the rule linked_step_L1_internal is too general!
    We must add additional constraints:
    1. there is a correspondence between act and state st2
       (i.e., st2 is waiting for st1 to execute act);
    2. st1 still 'remembers' the arguments passed by st2.
  *)
  Inductive linked_step : linked_state -> linked_internal -> linked_state -> Prop :=
  | linked_step_L2_internal : forall st1 st2 st2' act lst lst',
      step L2 st2 act st2' ->
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1 st2' ->
      linked_step lst (intL2 act) lst'
  | linked_step_L2_push : forall st1 st2 st1' qb lst lst' st2',
      at_external L2 st2 qb st2' ->
      lst = mkLinkedState st1 st2 ->
      initial_state L1 st1 qb st1' ->
      lst' = mkLinkedState st1' st2 ->
      linked_step lst (intQuery qb) lst'
  | linked_step_L1_internal : forall st1 st2 st1' act lst lst',
      step L1 st1 act st1' ->
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1' st2 ->
      linked_step lst (intL1 act) lst'
  | linked_step_L1_pop : forall st1 st1' rb st2 st2' lst lst',
      final_state L1 st1 rb st1' ->
      after_external L2 st2 rb st2' ->
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1' st2' ->
      linked_step lst (intReply rb) lst'
  .

  Inductive linked_at_external : linked_state -> query liA -> linked_state -> Prop :=
  | linked_at_external_L1 : forall st1 qa st2 lst st1' lst',
      at_external L1 st1 qa st1' ->
      (* at_external L2 st2 qb -> *)
      (* reachable st1 qa qb -> *)
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1' st2 ->
      linked_at_external lst qa lst'
  .

  Inductive linked_after_external : linked_state -> reply liA -> linked_state -> Prop :=
  | linked_after_external_L1 : forall st1 ra st1' lst lst' st2,
      after_external L1 st1 ra st1' ->
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1' st2 ->
      linked_after_external lst ra lst'
  .

  Inductive linked_final_state : linked_state -> reply liC -> linked_state -> Prop :=
  | linked_final_state_L2 : forall st1 st2 rc st2' lst lst',
      final_state L2 st2 rc st2' ->
      lst = mkLinkedState st1 st2 ->
      lst' = mkLinkedState st1 st2' ->
      linked_final_state lst rc lst'
  .

  Definition linked_lts : lts liA liC :=
    mkLTS liA liC linked_state
      linked_internal
      linked_step
      linked_new_state
      linked_initial_state
      linked_at_external
      linked_after_external
      linked_final_state.

End LINK.

Arguments L1State {liA liB liC L1 L2}.
Arguments L2State {liA liB liC L1 L2}.