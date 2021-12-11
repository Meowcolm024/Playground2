Inductive parens : Type :=
| empty
| inner (p : parens) (r : parens).

Inductive token : Type :=
| open
| close.

Require Import List.
Import ListNotations.

Compute [open].

Fixpoint check_bal_help (l: list token) (acc : nat) : bool :=
    match (l, acc) with
    | (nil, O) => true
    | (nil, S _) => false 
    | (open :: rest, n) => check_bal_help rest (S n)
    | (close :: _, O) => false
    | (close :: rest, S n) => check_bal_help rest n
    end.

Definition check_bal (l: list token) : bool := 
    check_bal_help l O.

(* Compute check_bal [open; open; close; close].
Compute check_bal [open; open; close; open].
Compute check_bal [open; close; close; open].
Compute check_bal [open; close; open; close]. *)

Fixpoint constr (p: parens) : list token :=
    match p with
    | empty => nil
    | inner x y => [open] ++ constr x ++ [close] ++ constr y
    end.

Lemma con_bal: forall x y: list token,
    check_bal (x ++ y) = andb (check_bal x) (check_bal y).
Proof.
    intros x y.
    induction x as [| n lx IHx].
Abort. 

Theorem l_is_balances : forall p : parens,
    check_bal ( constr p ) = true.
Proof.
    intro p.
    induction p as [| n m IH].
    + auto.
    + simpl.
      unfold check_bal.
      simpl.
    
Abort.
(* Qed. *)
