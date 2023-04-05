Require Import ZArith.

(* Search (Z -> Z -> bool). *)

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

Lemma determin_arith : forall (e:earith) (vars : nat -> Z) (a b : Z), (interp_earith e vars) = a -> (interp_earith e vars) = b -> a=b.
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

Lemma determin_bool : forall (e:e_bool) (vars : nat -> Z) (a b : Z), (interp_ebool e vars) = a ->(interp_ebool e vars) = b -> a=b.
Proof.
intros. rewrite H in H0. exact H0.
Qed.

(** Exercice 3 **)

Inductive IMP :=
  | Skip : IMP
  | Affect : nat -> earith -> IMP
  | Cons : IMP -> IMP -> IMP
  | IfThenElse : e_bool -> IMP -> IMP -> IMP
  | While : e_bool -> IMP -> IMP
  | Until : e_bool -> IMP -> IMP
  | DoubleAffect : nat -> nat -> earith -> earith -> IMP.

Fixpoint interp_imp (e : IMP) (vars : nat -> Z) (i : nat): (nat -> Z) := 
  match i with 
    | 0=> vars
    | S l => match e with
                  | Skip => vars
                  | Affect n e => fun (k : nat) => if k=?n then (interp_earith e vars) else (vars k)
                  | Cons e1 e2 => interp_imp e2 (interp_imp e1 vars l) l
                  | IfThenElse bl e1 e2 => if Z.eqb (interp_ebool bl vars) 0 then (interp_imp e2 vars l) else (interp_imp e1 vars l)
                  | While bl e1 => if Z.eqb (interp_ebool bl vars) 0 then vars else (interp_imp (While bl e1) (interp_imp e1 vars l) l)
                  | Until bl e1 => if Z.eqb (interp_ebool bl vars) 0 then (interp_imp (While bl e1) (interp_imp e1 vars l) l) else vars
                  | DoubleAffect n1 n2 e1 e2 => fun (k : nat) => if k=?n2 then (interp_earith e2 vars) else (if k=?n1 then (interp_earith e1 vars) else (vars k))
                end
end.

Lemma determin_imp : forall (e:IMP) (vars : nat -> Z) (i : nat) (a b : nat -> Z), (interp_imp e vars i) = a -> (interp_imp e vars i) = b -> a=b.
Proof.
intros. rewrite H in H0. exact H0.
Qed.

Definition equivalent_com (e1 e2 : IMP ) : Prop := exists i, forall (vars : nat -> Z), (interp_imp e1 vars (S i)) = (interp_imp e2 vars (S i)).


Goal forall (b : e_bool) (c : IMP), equivalent_com (While b c) (IfThenElse b (Cons c (While b c)) Skip).
Proof.
intros.
unfold equivalent_com. eexists. intros. unfold interp_imp. induction (interp_ebool b vars).
    + simpl. instantiate (1 := 0). simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Axiom fun_eq : forall (f g : nat -> Z), (forall x : nat, f x = g x) -> f = g.

Lemma fun_eq_inv : forall (x :nat) (f g : nat -> Z), f = g -> f x = g x.
Proof.
intros. rewrite H. reflexivity.
Qed.

Goal forall (x y :nat) (e1 e2 : earith),
(forall (vars : nat-> Z), (interp_earith e2 vars) = (interp_earith e2 (fun k : nat => if k =? x then interp_earith e1 vars else vars k)))
<->
(equivalent_com (DoubleAffect x y e1 e2) (Cons (Affect x e1) (Affect y e2))).
Proof. intros. split.
    + exists 1. intros. apply (fun_eq (interp_imp (DoubleAffect x y e1 e2) vars 2) (interp_imp (Cons (Affect x e1) (Affect y e2)) vars 2)). intros. simpl. destruct (x0 =? y).
      ++ apply (H vars).
      ++ reflexivity.
    + unfold equivalent_com. intros. destruct H as [i H']. pose proof (H' vars). apply (fun_eq_inv y) in H. repeat simpl in H. destruct (y =? y).
      ++ unfold interp_imp in H. destruct i.
        (* i=0 *) +++ pose proof (H' (fun (k:nat) => if k=?x then (Z.of_nat 1) else (if k=?y then (Z.of_nat 2) else (Z.of_nat 0)))). simpl in H0. pose proof (fun_eq H0 x).






