Require Import List.

Axiom ltle : forall (x y : nat), x < y -> x <= y.
Hypothesis le_lt_dec : forall (n m :nat), {n <=m} + {m < n}.

Fixpoint inser (a:nat) (l:list nat) : list nat := 
match l with
  |x::r => match le_lt_dec a x with 
                                      | left _ => a::l 
                                      | right _ =>  x::(inser a r)
                  end
  | nil => a::nil
end.

Fixpoint sort (l:list nat) : list nat := match l with
  |a::r => (inser a (sort r))
  | nil => nil
end.

(** Preuve que le tri renvoie une liste triée **)

Inductive Sorted : list nat -> Prop :=
  | SortedNil : Sorted nil
  | SortedSingle n : Sorted (n :: nil)
  | SortedCons n m l : Sorted (m :: l) -> n <= m -> Sorted (n :: m :: l).

Lemma sorted_subpart : forall (a:nat) (l:list nat), Sorted(a::l)-> Sorted(l).
Proof.
intros a l Hyp. inversion Hyp. apply SortedNil. exact H1.
Qed.

Lemma SortedFirst : forall (l : list nat) (a b : nat), Sorted (a :: b :: l) -> a <= b.
Proof.
intros a b l Hyp. inversion Hyp. exact H3. 
Qed.

Lemma InsertNew: forall (l : list nat) (a b: nat), 
exists (q : list nat) (h : nat), (inser a (b::l)) = h::q /\ (h=a \/ h=b).
Proof.
intros l a b. simpl. destruct (le_lt_dec a b).
  + exists (b::l). exists a. split.
    -- reflexivity.
    -- left. reflexivity.
  + exists (inser a l). exists b. split.
    -- reflexivity.
    -- right. reflexivity.
Qed.

Lemma inser_is_ok : forall (l:list nat) (n:nat), Sorted(l)-> Sorted(inser n l).
Proof.
intros l n l_sorted. induction l. 
  + apply SortedSingle.
  + simpl. destruct (le_lt_dec n a) as [le | lt].
    - apply SortedCons. exact l_sorted. exact le.
    - apply sorted_subpart in l_sorted as lbis_sorted. 
      apply IHl in lbis_sorted as r_sorted. destruct l. apply ltle in lt as lt_larg. 
      ++ simpl. apply ((SortedCons a n nil) (SortedSingle n) (lt_larg)).
      ++ apply (SortedFirst l a n0) in l_sorted as a_leq_n0.
         assert (exists (q : list nat) (h : nat), (inser n (n0::l)) = h::q /\ (h=n \/ h=n0)).
        -- apply (InsertNew l n n0).
        -- destruct H as [l1]. destruct H as [n1]. 
           destruct H as [relat H].
           rewrite relat.
                apply (SortedCons a n1 l1).
                 +++ rewrite <- relat. exact r_sorted.
                 +++ destruct H as [case1 | case2].
                     --- rewrite case1. exact (ltle a n lt).
                     --- rewrite case2. exact a_leq_n0.
Qed.

Goal forall (l:list nat), Sorted(sort l).
Proof.
intro l. induction l.
  + simpl. apply SortedNil.
  + simpl. apply (inser_is_ok (sort l) a IHl).
Qed.

(** Preuve que le tri renvoie une permutation de la liste initiale **)

Fixpoint ins_ind (i:nat) (a:nat) (l:list nat) : list nat := match i with
  |0 => a::l
  |S j => match l with
                    |nil => a::nil
                    |b::r => b::(ins_ind j a r)
          end
end.

Inductive permuted : (list nat) -> (list nat) -> Type := 
  |N : permuted nil nil
  |Succ : forall (x : nat) (l1 l2 :list nat), (permuted l1 l2) -> forall (i : nat),
permuted (x::l1) (ins_ind i x l2).

Lemma ins_equiv : forall (l : list nat) (a:nat), exists (i:nat), (inser a l)=(ins_ind i a l).
Proof.
intros l a. induction l as [|m l'].
  + exists 0. simpl. reflexivity.
  + simpl. destruct (le_lt_dec a m).
    -- exists 0. simpl. reflexivity.
    -- destruct IHl' as [i0]. rewrite H. exists (S i0). simpl. reflexivity.
Qed.

Goal forall (l:list nat), permuted l (sort l).
Proof.
intro l. induction l as [|a l'].
  + simpl. apply N.
  + simpl. assert (exists (i:nat), (inser a l')=(ins_ind i a l')).
    -- apply ins_equiv.
    -- apply H !!!!!!!!!!!!!!!


































