Require Import ZArith.

(** Exercice 1 **)

Inductive earith :=
  | Const : Z -> earith
  | Var : nat -> earith
  | Plus : earith -> earith -> earith
  | Mult : earith -> earith -> earith
  | Moins : earith -> earith.

Fixpoint interp_earith (e : earith) (vars : nat -> Z) : Z := match e with
  | Const n => n
  | Var n => vars n
  | Plus e1 e2 => (interp_earith e1 vars) + (interp_earith e2 vars)
  | Mult e1 e2 => (interp_earith e1 vars) * (interp_earith e2 vars)
  | Moins e1 => - (interp_earith e1 vars)
end.

Lemma deterermin : forall (e:earith) (vars : nat -> Z) (a b : Z), (interp_earith e vars) = a -> (interp_earith e vars) = b -> a=b.
Proof.
intros. rewrite H in H0. exact H0.
Qed.

(** Exercice 2 **)

Inductive e_bool :=
  | Constb : Z -> e_bool
  | Varb : nat -> e_bool
  | Eqb : e_bool -> e_bool -> e_bool
  | Notb : e_bool -> e_bool
  | Andb : e_bool -> e_bool -> e_bool.

Search (Z -> Z -> bool).

Fixpoint interp_ebool (e : e_bool) (vars : nat -> Z) : Z := match e with
  | Constb n => n
  | Varb n => vars n
  | Eqb e1 e2 => if Z.eqb (interp_ebool e1 vars) (interp_ebool e2 vars) then (interp_ebool e1 vars) else 0
  | Notb e => if Z.eqb (interp_ebool e vars) 0 then 0 else (interp_ebool e vars)
  | Andb e1 e2 => if Z.eqb (interp_ebool e1 vars) 0 then 0 else (interp_ebool e2 vars)
end.