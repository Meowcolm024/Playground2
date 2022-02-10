Require Import List.
Require Import Nat.

Import ListNotations.

Inductive Term :=
| true
| false
| zero
| succ (t : Term)
| pred (t : Term)
| iszero (t : Term)
| cond : Term -> Term -> Term -> Term.

Compute (succ (succ zero)).

Fixpoint eval (t: Term) : Term :=
    match t with
    | succ t' => succ (eval t')
    | iszero zero => true
    (* FIX LATER *)
    | iszero (succ _) => false
    | pred t' => match eval t' with
        | zero => zero
        | succ t'' => t''
        | t'' => pred t''
        end
    | cond p t e => match eval p with
        | true => eval t
        | false => eval e
        | _ => t
        end
    | _ => t
    end.

Compute (eval (cond (iszero (pred zero)) true (succ zero))).
