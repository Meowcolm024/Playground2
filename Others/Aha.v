Require Import Init.Datatypes.
From Coq Require Recdef.
Require Import Init.Nat.
From Coq Require Import Lia.

Inductive Term :=
| t
| f
| zero
| succ (t : Term)
| pred (t : Term)
| iszero (t : Term)
| cond (p : Term) (t1 : Term) (t2 : Term).

Fixpoint isnv (t: Term) : bool :=
    match t with
    | zero => true
    | succ t' => isnv t'
    | _ => false
    end.

Fixpoint reduce (t : Term) : option Term :=
    match t with
    | cond t t1 _       => Some t1
    | cond f _ t2       => Some t2
    | cond k t1 t2      => option_map (fun z => cond z t1 t2) (reduce k)
    | succ n            => option_map succ (reduce n)
    | pred zero         => Some zero
    | pred (succ n)     => if isnv n then Some f else None
    | pred n            => option_map pred (reduce n)
    | iszero zero       => Some t
    | iszero (succ n)   => if isnv n then Some f else None
    | iszero n          => option_map iszero (reduce n)
    | _                 => None
    end.

Fixpoint depth (t : Term) : nat :=
    match t with
    | zero | t | f  => 1
    | succ n        => 1 + depth n
    | iszero n      => 1 + depth n
    | pred n        => 1 + depth n
    | cond p t1 t2  => 1 + (max (depth p) (max (depth t1) (depth t2)))
    end.

(* too obvious *)
Lemma le_S : forall (a b : nat), a < b -> S a < S b. Proof. intros. lia. Qed.
Lemma le_O : forall (a : nat), 0 < S a. Proof. intros. lia. Qed.

(* the measufe might be wrong *)
Function eval (t : Term) {measure depth t} : Term :=
    match reduce t with
    | None      => t
    | Some t'   => eval t'
    end.
Proof.
    intro tm. induction tm; 
    intros tm' teq; inversion teq.
    - destruct (reduce tm) eqn: T.
      + simpl in H0. inversion H0.
        simpl. apply le_S.
        apply IHtm. reflexivity.
      + inversion H0.
    - 
      
Abort.
