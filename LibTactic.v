Require Import Arith.
Require Import LibVar.

Ltac gather_vars_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | \{} => gather FH
      | context [FH] => fail 1
      | _ => gather (FH \u V)
      end
    | _ => V
    end in
  let L := gather (\{}:vars) in eval simpl in L.

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | ?E1 \u ?E2 => let Acc1 := go Acc E1 in
                     go Acc1 E2
     | \{}  => Acc
     | ?E1 => match Acc with
              | \{} => E1
              | _ => constr:(Acc \u E1)
              end
     end
  in go (\{}:vars) V.

Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (var_fresh L) as [Y Fr]).

Ltac div_notin :=
  repeat match goal with
  | [H : _ \notin _ \u _ |- _ ] => 
    apply notin_union in H; destruct H
  end.

Ltac notin_solve :=
  div_notin;
  repeat match goal with
  | [ |- _ \notin _ \u _] => 
    apply notin_union
  end;
  intuition.

Tactic Notation "sets" ident(X) ":" constr(E) :=
  set (X := E) in *.

Ltac eq_contra :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X eqn:Exx
  | _ => idtac
  end;
  match goal with
  | [ H : context[if ?X then _ else _] |- _ ] => destruct X eqn:Exx
  | _ => idtac
  end;
  match goal with
  | [H : (_ =? _) = true |- _] => apply Nat.eqb_eq in H
  | [H : (_ =? _) = false |- _] => apply Nat.eqb_neq in H
  end;
  try intuition
.