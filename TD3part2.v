Require Import List.

Require Import Bool.

Variable T : Type.

Hypothesis T_eq_dec : forall (x y :T), {x=y} + {~x=y}.


(** Definition **)

Definition multiset := list (T*nat).

Definition empty:multiset := nil.

Fixpoint member (x : T) (ms : multiset) : bool :=
  match ms with
  |nil => false
  |(a,b)::r => match T_eq_dec a x with
                    |left _ => true
                    |right _ => (member x r)
               end
  end.

Definition singleton (x : T) := (x,1)::empty .

Fixpoint add (x : T) (n : nat) (ms : multiset) : multiset :=
 match ms with 
  |nil => match n with 
                  |0 => nil
                  |_ => (x,n)::nil
          end
  |(a,b)::r =>  match T_eq_dec a x with
                    |left _ => (a,n+b)::r
                    |right _ => (a,b)::(add x n r)
               end
end.

Fixpoint union (ms1 : multiset) (ms2 : multiset) : multiset :=
match ms1 with
  |nil => ms2
  |(a,b)::r => union r (add a b ms2)
end.

Fixpoint multiplicity (x : T) (ms : multiset) : nat := 
match ms with
  |nil =>0
  |(a,b)::r => match T_eq_dec a x with
                    |left _ => b
                    |right _ => multiplicity x r
              end
end.

Fixpoint removeOne (x : T) (ms : multiset) : multiset :=
match ms with
  |nil => nil
  |(a,b)::r => match T_eq_dec a x with
                     |right _ => (a,b)::(removeOne x r)
                     |left _ => match b with 
                                              |0 | S(0) => r
                                              | S(m) => (a,m)::r
                                end
              end
end.

Fixpoint removeAll (x : T) (ms : multiset) : multiset :=
match ms with
  |nil => nil
  |(a,b)::r => match T_eq_dec a x with
                     |right _ => (a,b)::(removeAll x r)
                     |left _ => removeAll x r
              end
end.

(** Rq : Cette definition est redondante car elle laisse croire que l'on peut trouver plusieurs couples pour un même élément x, cependant cela facilite les preuves de correction **)

Inductive InMultiset : T -> multiset -> Prop :=
  | TL : forall h x ms, InMultiset x ms -> InMultiset x (cons h ms)
  | HD : forall x n ms, InMultiset x (cons (x,S(n)) ms).

Inductive wf : multiset -> Prop :=
 | Empt : wf empty
 | Cons : forall x n t,(wf t)/\~(InMultiset x t) -> wf (cons (x,S(n)) t).

Goal wf empty.
Proof.
apply Empt.
Qed.

Goal forall x, wf (singleton x).
Proof.
intro x. apply (Cons x 0 empty).
split. apply Empt. intro H. inversion H.
Qed.


Lemma Add0 : forall x ms, (add x 0 ms)=ms.
Proof.
induction ms as [|hd tl]. 
  + simpl. reflexivity.
  + simpl. destruct hd as [a n]. destruct (T_eq_dec a x).
    ++ reflexivity.
    ++ rewrite IHtl. reflexivity.
Qed.

Goal forall x n ms, wf ms -> wf (add x n ms).
destruct n.
  +intros ms H. rewrite (Add0 x ms). exact H.
  + induction ms as [ |hd tl].
    ++ intro H. apply (Cons x n nil). split. exact H. intro Hneg. inversion Hneg.
    ++ intro H. simpl. destruct hd as [a m]. destruct (T_eq_dec a x).
        +++ apply (Cons a (n+m) tl). inversion H. destruct H1. split. exact H1. exact H4.
        +++ destruct m. inversion H. apply (Cons a m (add x (S n) tl)). inversion H. destruct H1. split.
            ++++ apply IHtl in H1. exact H1.
            ++++ intro Hneg. destruct Hneg.






































