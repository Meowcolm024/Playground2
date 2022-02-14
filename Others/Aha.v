Require Import Init.Datatypes.
From Coq Require Recdef.
Require Import Init.Nat.
From Coq Require Import Lia.

Inductive Term :=
| t
| f
| zero
| succ      (t : Term)
| pred      (t : Term)
| iszero    (t : Term)
| cond      (p : Term) (t1 : Term) (t2 : Term).

Fixpoint isnv (tm: Term) : bool :=
    match tm with
    | zero      => true
    | succ tm'  => isnv tm'
    | _         => false
    end.

Fixpoint reduce (tm : Term) : option Term :=
    match tm with
    | cond t t1 _       => Some t1
    | cond f _  t2      => Some t2
    | cond k t1 t2      => option_map (fun z => cond z t1 t2) (reduce k)
    | succ n            => option_map succ (reduce n)
    | pred zero         => Some zero
    | pred (succ n)     => if isnv n then Some n else None
    | pred n            => option_map pred (reduce n)
    | iszero zero       => Some t
    | iszero (succ n)   => if isnv n then Some f else None
    | iszero n          => option_map iszero (reduce n)
    | _                 => None
    end.

(* size *)
Fixpoint depth (tm : Term) : nat :=
    match tm with
    | zero | t | f  => 1
    | succ n        => 1 + depth n
    | iszero n      => 1 + depth n
    | pred n        => 1 + depth n
    | cond p t1 t2  => 1 + (depth p) + (depth t1) + (depth t2)
    end.

(* too obvious *)
Lemma le_S : forall (a b : nat), a < b -> S a < S b. Proof. intros. lia. Qed.
Lemma le_O : forall (a : nat), 0 < S a. Proof. intros. lia. Qed.

Function eval (tm : Term) {measure depth tm} : Term :=
    match reduce tm with
    | None      => tm
    | Some tm'  => eval tm'
    end.
Proof.
    intro tm. induction tm; 
    intros tm' teq; inversion teq.
    - destruct (reduce tm) eqn: T.
      + simpl in H0. inversion H0.
        simpl. apply le_S.
        apply IHtm. reflexivity.
      + inversion H0.
    - destruct (reduce tm) eqn: T.
      + destruct tm; inversion T.
        {
            simpl in teq. destruct (isnv tm).
            inversion H0. rewrite <- H2. simpl. 
            lia. inversion H0.
        }
        {
            simpl in H0. inversion H0. simpl.
            assert (S (depth t0) < S(depth(pred tm))).
            apply le_S. apply IHtm. reflexivity.
            simpl in H. apply H.
        }
        {
            simpl in H0. inversion H0. 
            assert (S (depth t0) < S(depth(iszero tm))).
            apply le_S. apply IHtm. reflexivity.
            simpl in H. apply H.
        }
        {
            simpl in H0. inversion H0.
            assert (S (depth t0) < S(depth(cond tm1 tm2 tm3))).
            apply le_S. apply IHtm. reflexivity.
            simpl in H. apply H.
        } 
     + destruct tm; inversion H0.
       { auto. }
       { 
            destruct (isnv tm); inversion H1.
            simpl. lia.
       }
    - destruct (reduce tm) eqn: T.
      + destruct tm; inversion T.
        {
            simpl in teq. destruct (isnv tm); inversion H0.
            simpl. lia.
        }
        {
            simpl in teq. destruct (isnv tm);
            simpl in H0; inversion H0;
            assert (S (depth t0) < S(depth (pred tm)));
            simpl; apply le_S; apply IHtm; reflexivity;
            apply H.
        }
        {
            simpl in H0. inversion H0.
            assert (S (depth t0) < S (depth (iszero tm))).
            apply le_S. apply IHtm. reflexivity. apply H.
        }
        {
            simpl in H0. inversion H0.
            assert (S (depth t0) < S(depth(cond tm1 tm2 tm3))).
            apply le_S. apply IHtm. reflexivity.
            simpl in H. apply H.
        }
      + destruct tm; inversion H0.
        { simpl. lia. }
        { 
            destruct (isnv tm); inversion H0.
            simpl. lia.
        }
    - destruct (reduce tm1) eqn: T.
      + destruct tm1.
        * simpl. inversion H0. lia.
        * simpl. inversion H0. lia.
        * inversion teq.
        * simpl in H0. inversion H0.
          simpl. apply le_S.
          assert (depth t0 < depth (succ tm1)).
          apply IHtm1. reflexivity.
        simpl in H. lia.
        * simpl in H0. inversion H0.
          simpl. apply le_S.
          assert (depth t0 < depth (pred tm1)).
          apply IHtm1. reflexivity.
          simpl in H. lia.
        * simpl in H0. inversion H0.
          simpl. apply le_S.
          assert (depth t0 < depth (iszero tm1)).
          apply IHtm1. reflexivity.
          simpl in H. lia.
        * simpl in H0. inversion H0. simpl. apply le_S.
          assert (depth t0 < depth (cond tm1_1 tm1_2 tm1_3)).
          apply IHtm1. reflexivity. 
          simpl in H. lia.
      + destruct tm1; inversion H0.
        * simpl. lia.
        * simpl. lia.
Defined.

Compute (reduce (iszero zero)).

Definition t1 := cond (cond (iszero zero) f t) (succ zero) (succ (succ zero)).
Compute (eval t1).
