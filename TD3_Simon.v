Require Import List.

Axiom TODO : forall x:Type, x.

Axiom ltle : forall (x y : nat), x < y -> x <= y.

Hypothesis le_lt_dec : forall (n m : nat), {n <= m}+{m < n}.

Lemma or_eq : forall (n m : nat), n < m -> n <= m.
Proof.
Admitted.
  

Fixpoint insert (n : nat) (l : list nat) :=
  match l with
  | nil => n :: nil
  | m :: l' =>
    match le_lt_dec n m with
    | left _ => n :: l
    | right _ => m :: (insert n l')
    end
  end.


Fixpoint sort (l : list nat) : list nat :=
  match l with
  | nil => nil
  | n :: l' => insert n (sort l')
  end.

Inductive Sorted : list nat -> Prop :=
  | SortedNil : Sorted nil
  | SortedSingle n : Sorted (n :: nil)
  | SortedCons n m l : Sorted (m :: l) -> n <= m -> Sorted (n :: m :: l).

Lemma SimpleSorted : forall (n : nat), forall (l : list nat), Sorted (n ::l) -> Sorted l.
Proof.
Admitted.

Lemma SortedFirst : forall (l : list nat) (a b : nat), Sorted (a :: b :: l) -> a <= b.
Proof.
Admitted.

Lemma InsertNew: forall (l : list nat) (a b: nat), exists (q : list nat) (h : nat),
                     (insert a (b::l)) = h::q /\ (h=a \/ h=b).
Proof.
Admitted.

Lemma WellInserted : forall (l : list nat) (n : nat), Sorted l -> Sorted (insert n l).
Proof.
  intros l.
  induction l as [| m l'].
    + intros n _.
      simpl.
      exact (SortedSingle n).
    + intros n l_sorted.
      simpl.
      destruct (le_lt_dec n m) as [le | lt].
        - apply ((SortedCons n m l') l_sorted le).
        - apply SimpleSorted with (n:=m) (l:=l') in l_sorted as l'_sorted.
          apply IHl' with (n := n) in l'_sorted as ins_n_l'_sorted.
          destruct l' as [| n0 l0].
          ++ simpl.
             apply ((SortedCons m n nil) (SortedSingle n) (or_eq m n lt)).
          ++ apply (SortedFirst l0 m n0) in l_sorted as m_leq_n0.
             assert (exists (q : list nat) (h : nat),
                     (insert n (n0::l0)) = h::q /\ (h=n \/ h=n0)).
             -- apply (InsertNew l0 n n0).
             -- destruct H as [l1]. destruct H as [n1].
                destruct H as [relat H].
                rewrite -> relat.
                apply (SortedCons m n1 l1).
                 +++ rewrite <- relat. exact ins_n_l'_sorted.
                 +++ destruct H as [case1 | case2].
                     --- rewrite case1. exact (ltle m n lt).
                     --- rewrite case2. exact m_leq_n0.

Fixpoint WellInserted (n : nat) (l : list nat) : Sorted (insert n l) :=
  match l with
  | nil => TODO _
  | m :: l' =>
    match le_lt_dec n m with
    | left _ as H => TODO _
    | right_ => TODO _
    end
  end.

Check (SortedCons 0 1 nil) (SortedSingle 1).

