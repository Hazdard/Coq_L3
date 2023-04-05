Require Import ZArith.


(** Exercice 1 **)


  (** Question 1**) 

  Inductive env :=
    | Bot : env
    | Env : (nat -> Z) -> env.

  Inductive earith :=
    | Const : Z -> earith
    | Var : nat -> earith
    | Plus : earith -> earith -> earith
    | Mult : earith -> earith -> earith
    | Moins : earith -> earith.

  Inductive sem_earith : earith -> env -> Z -> Prop :=
    | SemConst : forall (n : Z) (vars : nat -> Z), sem_earith (Const n) (Env vars) n
    | SemVars : forall (x : nat) (vars : nat -> Z), sem_earith (Var x) (Env vars) (vars x)
    | SemPlus : forall (e1 e2 : earith) (vars : nat-> Z) (n1 n2 : Z), sem_earith e1 (Env vars) n1 -> sem_earith e2 (Env vars) n2 -> sem_earith (Plus e1 e2) (Env vars) (n1 + n2)
    | SemMult : forall (e1 e2 : earith) (vars : nat-> Z) (n1 n2 : Z), sem_earith e1 (Env vars) n1 -> sem_earith e2 (Env vars) n2 -> sem_earith (Mult e1 e2) (Env vars) (n1 * n2)
    | SemMoins : forall (e1 : earith) (vars : nat-> Z) (n1 n2 : Z), sem_earith e1 (Env vars) n1 -> sem_earith (Moins e1) (Env vars) (- n1).

  (** Question 2 **)

  Fixpoint interp_earith (e : earith) (vars : env) : Z := match vars with
  | Bot => 667
  | Env env1 => match e with
                | Const n => n
                | Var n => env1 n
                | Plus e1 e2 => (interp_earith e1 vars) + (interp_earith e2 vars)
                | Mult e1 e2 => (interp_earith e1 vars) * (interp_earith e2 vars)
                | Moins e1 => - (interp_earith e1 vars)
                end
end.

  (** Question 3 **)

  Theorem determin_earith : forall (e:earith) (vars : env) (a b : Z), sem_earith e vars a -> sem_earith e vars b -> a=b.
  Proof.
  induction e.
    + intros. inversion H. inversion H0. subst. reflexivity.
    + intros. inversion H. inversion H0. subst. inversion H4. reflexivity.
    + intros. inversion H. inversion H0. subst. inversion H10. rewrite H2 in H9. pose proof (IHe1 (Env vars0) n1 n0 H3 H9). rewrite H2 in H12. pose proof (IHe2 (Env vars0) n2 n3 H6 H12). rewrite H1. rewrite H4. reflexivity.
    + intros. inversion H. inversion H0. subst. inversion H10. rewrite H2 in H9. pose proof (IHe1 (Env vars0) n1 n0 H3 H9). rewrite H2 in H12. pose proof (IHe2 (Env vars0) n2 n3 H6 H12). rewrite H1. rewrite H4. reflexivity.
    + intros. inversion H. inversion H0. subst. inversion H7.  rewrite H3 in H6. pose proof (IHe (Env vars0) (n1) (n0) H2 H6). rewrite H1. reflexivity.
Qed.


(** Exercice 2 **) 

  (** Question 1 **)

  Inductive e_bool :=
    | Constb : Z -> e_bool
    | Varb : nat -> e_bool
    | Equalb : earith -> earith -> e_bool
    | Notb : e_bool -> e_bool
    | Andb : e_bool -> e_bool -> e_bool.

  Inductive sem_e_bool : e_bool -> env -> Z -> Prop :=
    | SemConstb : forall (n : Z) (vars : nat -> Z), sem_e_bool (Constb n) (Env vars) n
    | SemVarb : forall (x : nat) (vars : nat -> Z), sem_e_bool (Varb x) (Env vars) (vars x)
    | SemEqualb : forall (e1 e2 : earith) (vars : nat-> Z) (n1 n2 : Z),
        sem_earith e1 (Env vars) n1 -> sem_earith e2 (Env vars) n2 -> sem_e_bool (Equalb e1 e2) (Env vars) (if Z.eqb n1 n2 then 1 else 0) 
    | SemNotb : forall (e : e_bool) (vars : nat -> Z) (n : Z),
        sem_e_bool e (Env vars) n -> sem_e_bool (Notb e) (Env vars) (if Z.eqb n 0 then 42 else 0)
    | SemAndb : forall (e1 e2 : e_bool) (vars : nat-> Z) (n1 n2 : Z),
        sem_e_bool e1 (Env vars) n1 -> sem_e_bool e2 (Env vars) n2 -> sem_e_bool (Andb e1 e2) (Env vars) (if Z.eqb (n1*n2) 0 then 0 else 42).

  (** Question 2 **)

  Fixpoint interp_e_bool (e : e_bool) (vars : env) : Z := match vars with
    | Bot => 0
    | Env env1 => match e with
                  | Constb n => n
                  | Varb n => env1 n
                  | Equalb e1 e2 => if Z.eqb (interp_earith e1 vars) (interp_earith e2 vars) then 1 else 0
                  | Notb e => if Z.eqb(interp_e_bool e vars) (Z.of_nat 0) then 1 else 0
                  | Andb e1 e2 => if orb (Z.eqb (interp_e_bool e1 vars) 0) (Z.eqb (interp_e_bool e2 vars) 0) then 0 else 1
                end
  end.

  (** Question 3 **)

  Theorem determin_e_bool : forall (e : e_bool) (vars : env) (a b : Z), sem_e_bool e vars a -> sem_e_bool e vars b -> a = b.
  Proof.
    induction e.
    + intros. inversion H. inversion H0. subst. reflexivity.
    + intros. inversion H. inversion H0. subst. inversion H4. reflexivity.
    + intros. inversion H. inversion H0. subst. rewrite H10 in H9. rewrite H10 in H12.
      pose proof (determin_earith e (Env vars0) n1 n0 H3 H9).
      pose proof (determin_earith e0 (Env vars0) n2 n3 H6 H12).
      rewrite H1. rewrite H2. reflexivity.
    + intros. inversion H. inversion H0. subst. rewrite H7 in H6.
      pose proof (IHe (Env vars0) n n0 H2 H6).
      rewrite H1. reflexivity.
    + intros. inversion H. inversion H0. subst. rewrite H10 in H9. rewrite H10 in H12.
      pose proof (IHe1 (Env vars0) n1 n0 H3 H9).
      pose proof (IHe2 (Env vars0) n2 n3 H6 H12).
      rewrite H1. rewrite H2. reflexivity.
  Qed.


(** Exercice 3 **)

  (** Question 1 **)

  Inductive IMP :=
    | Skip : IMP
    | Affect : nat -> earith -> IMP
    | Cons : IMP -> IMP -> IMP
    | IfThenElse : e_bool -> IMP -> IMP -> IMP
    | While : e_bool -> IMP -> IMP
    | Until : e_bool -> IMP -> IMP
    | DoubleAffect : nat -> nat -> earith -> earith -> IMP.

Definition update_env (vars : env) (x : nat) (n : Z) : env := match vars with
  |Bot => Bot 
  |Env env1 => Env (fun (k:nat) => if k=?x then n else (env1 k))
end.

  Inductive sem_imp : IMP -> env -> env -> nat -> Prop :=
    | SemSkip : forall (vars : env), sem_imp Skip vars vars 0
    | SemAffect : forall (x : nat) (e : earith) (n : Z) (vars : env), sem_earith e vars n -> sem_imp (Affect x e) vars (update_env vars x n) 0
    | SemCons : forall (vars1 vars2 vars3 : env) (e1 e2 : IMP), sem_imp e1 vars1 vars2 0 -> sem_imp e2 vars2 vars3 0 -> sem_imp (Cons e1 e2) vars1 vars3 0
    | SemIfThen : forall (vars1 vars2 : env) (e1 e2 : IMP) (b : e_bool) (n : Z) (k : nat), sem_e_bool b vars1 n -> n <> 0%Z -> sem_imp e1 vars1 vars2 k -> sem_imp (IfThenElse b e1 e2) vars1 vars2 k
    | SemifElse : forall (vars1 vars2 : env) (e1 e2 : IMP) (b : e_bool) (n : Z) (k : nat), sem_e_bool b vars1 n -> n = 0%Z -> sem_imp e2 vars1 vars2 k -> sem_imp (IfThenElse b e1 e2) vars1 vars2 k
    | SemWhileIn : forall (vars1 vars2 vars3 : env) (e : IMP) (b : e_bool) (n : Z) (k p : nat), sem_e_bool b vars1 n -> n <> 0%Z -> sem_imp e vars1 vars2 k -> sem_imp (While b e) vars2 vars3 p -> sem_imp (While b e) vars1 vars3 (S p)
    | SemWhileOut : forall (vars1 vars2 : env) (e : IMP) (b : e_bool) (n : Z) (k : nat), sem_e_bool b vars1 n -> n = 0%Z -> sem_imp (While b e) vars1 vars1 0
   (** Question 6 **)
    | SemUntilIn : forall (vars1 vars2 vars3 : env) (e : IMP) (b : e_bool) (n : Z) (k p : nat), sem_e_bool b vars1 n -> n = 0%Z -> sem_imp e vars1 vars2 k -> sem_imp (Until b e) vars2 vars3 p -> sem_imp (Until b e) vars1 vars3 (S p)
    | SemUntilOut : forall (vars1 vars2 : env) (e: IMP) (b : e_bool) (n : Z), sem_e_bool b vars1 n -> n <> 0%Z -> sem_imp (Until b e) vars1 vars1 0
    (** Question 7 **)
    | SemDoubleAffect : forall (x y : nat) (e1 e2 : earith) (n1 n2 : Z) (vars : env), sem_earith e1 vars n1 -> sem_earith e2 vars n2  -> sem_imp (DoubleAffect x y e1 e2) vars (update_env (update_env vars x n1) y n2) 0.

  (** Question 2 **)

  Fixpoint interp_imp (e : IMP) (vars : env) (i : nat): env := match vars with 
    | Bot => Bot
    | Env env1 => match i with 
                        | 0=> Bot
                        | S l => match e with
                                      | Skip => vars
                                      | Affect x e => (update_env vars x (interp_earith e vars))
                                      | Cons e1 e2 => interp_imp e2 (interp_imp e1 vars l) l
                                      | IfThenElse bl e1 e2 => if Z.eqb (interp_e_bool bl vars) 0 then (interp_imp e2 vars l) else (interp_imp e1 vars l)
                                      | While bl e1 => if Z.eqb (interp_e_bool bl vars) 0 then vars else (interp_imp (While bl e1) (interp_imp e1 vars l) l)
                                      | Until bl e1 => if Z.eqb (interp_e_bool bl vars) 0 then (interp_imp (While bl e1) (interp_imp e1 vars l) l) else vars
                                      | DoubleAffect x y e1 e2 => (update_env (update_env vars x (interp_earith e1 vars)) y (interp_earith e2 vars))
                                end
                  end
end.

  (** Question 3 **)

  Theorem determin_imp : forall (e : IMP) (k1 k2 : nat) (vars : env) (env1 env2 : env), sem_imp e vars env1 k1 -> sem_imp e vars env2 k2 -> env1 = env2.
  Proof.
  induction e.
  + intros. inversion H. inversion H0. subst. reflexivity.
  + intros. inversion H. inversion H0. subst. pose proof (determin_earith e vars n0 n1 H6 H12). rewrite H1. reflexivity.
  + intros. inversion H. inversion H0. subst. pose proof (IHe1 0 0 vars vars2 vars4 H3 H10). rewrite H1 in H7. pose proof (IHe2 0 0  vars4 env1 env2 H7 H14). assumption.
  + intros. inversion H ; inversion H0 ; subst.
      ++ apply (IHe1 k1 k2 vars env1 env2  H9 H18).
      ++ subst. pose proof (determin_e_bool e1 vars n 0 H4 H13). contradiction.
      ++ pose proof (determin_e_bool e1 vars n0 0 H13 H4). contradiction.
      ++ apply (IHe2 k1 k2 vars env1 env2 H9 H18).
  + induction k1 ; induction k2 ; intros ; inversion H ; inversion H0 ; subst.
      ++ reflexivity.
      ++ inversion H. inversion H0. subst. pose proof (determin_e_bool e env1 0 n0 H3 H10). symmetry in H1. contradiction.
      ++ inversion H. inversion H0. subst. pose proof (determin_e_bool e env2 n 0 H4 H12). contradiction.
      ++ pose proof (IHe k k0 vars vars2 vars4 H8 H17). subst. apply (IHk1 k2 vars4 env1 env2 H9 H18).
 + induction k1 ; induction k2 ; intros ; inversion H ; inversion H0 ; subst.
      ++ reflexivity.
      ++ inversion H. inversion H0. subst. pose proof (determin_e_bool e env1 0 n0 H13 H4). symmetry in H1. contradiction.
      ++ inversion H. inversion H0. subst. pose proof (determin_e_bool e env2 n0 0 H12 H5). contradiction.
      ++ pose proof (IHe k k0 vars vars2 vars4 H8 H17). subst. apply (IHk1 k2 vars4 env1 env2 H9 H18).
 + intros. inversion H. inversion H0. subst. (pose proof determin_earith e vars n1 n3 H8 H17). (pose proof determin_earith e0 vars n2 n4 H9 H18). rewrite H1. rewrite H2. reflexivity.
Qed.


  (** Question 4 **)

  Definition equivalent_com e1 e2 := forall (vars env1 env2 : env) (n m : nat), (sem_imp e1 vars env1 n) -> (sem_imp e2 vars env2 m) -> (env1 = env2).

  (** Question 5 **)
  
  Goal forall (b : e_bool) (c : IMP), equivalent_com (While b c) (IfThenElse b (Cons c (While b c)) Skip).
  Proof. unfold equivalent_com. intros. inversion H ; inversion H0 ; subst.
      + inversion H18. subst. pose proof (determin_imp c k 0 vars vars2 vars0 H5 H6). rewrite H1 in H9. apply (determin_imp (While b c) p 0 vars0 env1 env2 H9 H11).
      + pose proof (determin_e_bool b vars n0 0 H3 H13). contradiction.
      + pose proof (determin_e_bool b env1 0 n1 H3 H11). symmetry in H1. contradiction.
      + inversion H16. reflexivity.
Qed.















  