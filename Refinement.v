Require Import 
  List
  LTS.
Import ListNotations.

(* (* 
  An object (of type lts li_null liB) can be specified by its observable executions from new_state.
  A possible execution can be described by a list of events.
*)
Section Trace.

Context {liB : language_interface}.
Variable L: lts li_null liB.

Inductive event :=
| event_inv : query liB -> event
| event_res : reply liB -> event
.

(* 
  valid_execution_fragment records the list of events from state st to st'.
*)
Inductive valid_execution_fragment (st st' : L.(state)) : list event -> Prop :=
| Step_None :
    st = st' ->
    valid_execution_fragment st st' nil
| Step_Internal : forall st'' acts (int : L.(internal)) pid,
    step L st pid int st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' acts
(* | Step_At_External : forall st'' acts qa,
    at_external L st qa st'' ->
    (* automaton_step _ st (inr ext) st'' -> *)
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' (event_invA qa :: acts)
| Step_After_External : forall st'' acts ra,
    after_external L st ra st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' (event_resA ra :: acts) *)
| Step_Initial_Call : forall st'' acts qb pid,
    initial_state L st pid qb st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' (event_inv qb :: acts)
| Step_Final_Return : forall st'' acts rb pid,
    final_state L st pid rb st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' (event_res rb :: acts)
.

Hint Constructors valid_execution_fragment : core.

Lemma valid_execution_fragment_join : forall (s s' s'' : L.(state)) a a',
    valid_execution_fragment s s' a ->
    valid_execution_fragment s' s'' a' ->
    valid_execution_fragment s s'' (a ++ a').
Proof.
  intros.
  induction H; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_join' : forall (s s' s'' : L.(state)) a a' a'',
    valid_execution_fragment s s' a ->
    valid_execution_fragment s' s'' a' ->
    a'' = a ++ a' ->
    valid_execution_fragment s s'' a''.
Proof.
  intros; subst; eauto using valid_execution_fragment_join.
Qed.

(* 
  A list of events 'acts' is a trace of the object
  if 'acts' is an execution from new_state to some state.
*)
Definition in_traces acts :=
  exists init final, L.(new_state) init /\ valid_execution_fragment init final acts.

Definition reachable st :=
  exists init acts, L.(new_state) init /\ valid_execution_fragment init st acts.

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

End Trace. *)

(* 
  The correctness of an object is described by refinement.
  We say that an object refines a given specification
  if its traces are included in the traces of the specification.


  The refinement can be derived from simulation (Theorem forward_simulation).
*)
Section Refinement.

Context {liB : language_interface}.

Definition refines (L1 L2 : lts li_null liB) : Prop :=
  forall acts, in_traces L1 acts -> in_traces L2 acts.

Record fsim_properties (L1 L2 : lts li_null liB) 
                       (match_states: state L1 -> state L2 -> Prop) : Prop := {
    (* fsim_match_valid_query:
      forall q1 q2, match_query ccB wB q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1; *)
    fsim_match_new_states:
      forall s1, new_state L1 s1 -> 
      exists s2, new_state L2 s2 /\ match_states s1 s2;
    fsim_match_initial_states:
      forall s1 s1' s2 qb pid, match_states s1 s2 -> initial_state L1 s1 pid qb s1' ->
      exists s2', initial_state L2 s2 pid qb s2' /\ match_states s1' s2';
    fsim_match_final_states:
      forall s1 s1' s2 rb pid, match_states s1 s2 -> final_state L1 s1 pid rb s1' ->
      exists s2', final_state L2 s2 pid rb s2' /\ match_states s1' s2';
    fsim_simulation:
      forall s1 s1' s2 int pid, match_states s1 s2 -> step L1 s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2'
  }.

Definition fsim_properties_inv_ind (L1 L2 : lts li_null liB)
                       (match_states: state L1 -> state L2 -> Prop)
                       (inv : L1.(state) -> Prop) : Prop :=
  (invariant_ind _ inv) /\
      (forall s1, new_state L1 s1 -> 
      exists s2, new_state L2 s2 /\ match_states s1 s2) /\
      (forall s1 s1' s2 qb pid, inv s1 -> match_states s1 s2 -> initial_state L1 s1 pid qb s1' ->
      exists s2', initial_state L2 s2 pid qb s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 rb pid, inv s1 -> match_states s1 s2 -> final_state L1 s1 pid rb s1' ->
      exists s2', final_state L2 s2 pid rb s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 int pid, inv s1 -> match_states s1 s2 -> step L1 s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2')
  .

Lemma forward_simulation_inv_ind_reconstruct: 
  forall (L1 L2 : lts li_null liB) f inv s1' s1 acts s2',
  fsim_properties_inv_ind _ _ f inv ->
  valid_execution_fragment L1 s1' s1 acts ->
  inv s1' ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2' s2 acts.
Proof.
  intros L1 L2 f inv s1' s1 acts s2'.
  intros Hforward Htrace1 Hrelinit.
  inversion Hforward as [Hinv [_ Hrel_trace]].
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel.
  - exists s2'. intuition.
    econstructor; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final Hrel_trace_step]].
    specialize (Hrel_trace_step st st'' s2' int pid Hinvst Hrel H).
    inversion Hrel_trace_step as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 Hs2].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final Hrel_trace_step]].
    specialize (Hrel_trace_init st st'' s2' qb pid Hinvst Hrel H).
    inversion Hrel_trace_init as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 Hs2].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final Hrel_trace_step]].
    specialize (Hrel_trace_final st st'' s2' rb pid Hinvst Hrel H).
    inversion Hrel_trace_final as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 Hs2].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
Qed.

Theorem forward_simulation_inv_ind :
  forall (L1 L2 : lts li_null liB),
  forall (f : L1.(state) -> L2.(state) -> Prop)
         (inv : L1.(state) -> Prop),
    fsim_properties_inv_ind _ _ f inv ->
    refines L1 L2.
Proof.
  intros L1 L2 f inv Hforward.
  unfold refines.
  intros acts Htrace1.
  unfold in_traces in *.
  destruct Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  inversion Hforward as [[Hrel_inv_start _] [Hrel_start Hrel_trace]].
  specialize (Hrel_start s1init Hstart1).
  inversion Hrel_start as [s2init [Hs2start Hs2rel]].
  assert (inv s1init) as Hinvs1init by eauto.
  pose proof (forward_simulation_inv_ind_reconstruct _ _
                f
                inv
                s1init
                s1final
                acts
                s2init
                Hforward
                Hfrag1
                Hinvs1init
                Hs2rel) as [s2final Hs2final].
  repeat eexists; intuition; eauto.
Qed.

Theorem forward_simulation :
  forall (L1 L2 : lts li_null liB)
         (f : L1.(state) -> L2.(state) -> Prop),
    fsim_properties _ _ f ->
    refines L1 L2.
Proof.
  intros.
  eapply (forward_simulation_inv_ind _ _ _ (fun _ => True)).
  inversion H. unfold fsim_properties_inv_ind.
  unfold invariant_ind. split; eauto. split; eauto.
  split; eauto. split; eauto.
Qed.
  
End Refinement.