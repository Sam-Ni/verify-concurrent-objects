Require Import
  List
  LTS
  Refinement.
Import ListNotations.

Section Transitivity.
  
Context {liA: language_interface}.
Variable L: lts li_null liA.
Variable L': lts li_null liA.
Variable L'': lts li_null liA.

Theorem trans_refinement:
  refines L L' ->
  refines L' L'' ->
  refines L L''.
Proof.
  unfold refines; intros.
  apply H in H1. intuition.
Qed.

End Transitivity.


Section test.

Context {liA liB liC: language_interface}.
Variable L1: lts liA liB.
Variable L2: lts liB liC.

Fixpoint gather_at_after_external_events 
  (in_acts : list (int_event (linked_lts L1 L2))) : list (@event liA liB) :=
  match in_acts with
  | nil => nil
  | in_act :: in_acts' =>
    let events' := gather_at_after_external_events in_acts' in
    let (pid, act) := in_act in
    match act with
    | intQuery qb => (pid, event_invB qb) :: events'
    | intReply rb => (pid, event_resB rb) :: events'
    | _ => events'
    end
  end.
  
End test.


Section ComposedRefinement.

Context {liA liB liC: language_interface}.
Variable L1: lts li_null liA.
Variable L1': lts li_null liA.
Variable L2: lts liA liB.


Theorem composed_refinement:
  refines L1 L1' ->
  refines (linked_lts L1 L2) (linked_lts L1' L2).
Proof.
  unfold refines; intros.
  unfold in_traces.
  unfold in_traces in H0.
  destruct H0 as [init [final [in_acts [Hnew Htrace]]]].
  inversion Hnew; subst. intuition. clear Hnew.
  destruct init. simpl in *.
  assert (in_traces L1 nil).
  unfold in_traces.
  exists L1State. exists L1State. exists nil.
  intuition. econstructor; eauto.
  apply H in H1. unfold in_traces in H1.
  destruct H1 as [L1State' [L1State1' [L1in_acts' [HL1new' HL1trace']]]].
  exists (mkLinkedState L1State' L2State call_stack).
  specialize (H (gather_at_after_external_events L1 L2 in_acts)).
  unfold in_traces in H.
  exists (mkLinkedState L1State' L2State call_stack).
  exists nil. intuition.

Admitted.
  
End ComposedRefinement.
