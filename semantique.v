Require Import ZArith.

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

