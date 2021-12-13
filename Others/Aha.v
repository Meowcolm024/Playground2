Require Import List.
Require Import Nat.

Import ListNotations.


Fixpoint f (ms: nat) (i: nat) : nat :=
    match ms with
    | 0 => i
    | S n => i * f n (S i)
    end.

Fixpoint g (ms: nat) (xs ys: list nat) : list nat :=
    match ms, xs, ys with
    | 0, _, _ => nil
    | _, nil, _ => ys
    | _, _, nil => xs
    | S n, x::xss, y::yss => 
        if leb x y 
            then x :: g n xss ys
            else y :: g n xs yss
    end.

Definition merge (xs ys: list nat): list nat :=
    g (length xs + length ys) xs ys.

Compute (f 5 1).
Compute (merge [1;3;5;7;9] [2;4;6;8]).