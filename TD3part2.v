Require Import List.

Require Import Bool.

Require Import Lia.

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

Lemma AddDistinct : forall (a x : T) (n : nat) (ms : multiset), ~(InMultiset a ms) -> ~(a=x) -> ~(InMultiset a (add x (S n) ms)).
Proof.
intros a x n ms. intros Happ Hdist. induction ms.
  + simpl. intro Hneg. inversion Hneg. inversion H1. contradiction.
  + intro Hneg. Admitted.


Goal forall x n ms, wf ms -> wf (add x n ms).
destruct n.
  +intros ms H. rewrite (Add0 x ms). exact H.
  + induction ms as [ |hd tl].
    ++ intro H. apply (Cons x n nil). split. exact H. intro Hneg. inversion Hneg.
    ++ intro H. simpl. destruct hd as [a m]. destruct (T_eq_dec a x).
        +++ apply (Cons a (n+m) tl). inversion H. destruct H1. split. exact H1. exact H4.
        +++ destruct m. inversion H. apply (Cons a m (add x (S n) tl)). inversion H. destruct H1. split.
            ++++ apply IHtl in H1. exact H1.
            ++++ intro Hneg. destruct Hneg. Admitted.





(** Question 3 **)

Goal forall x, ~InMultiset x empty.
Proof.
intro x. intro Hneg. inversion Hneg.
Qed.

Goal forall x y, InMultiset y (singleton x) -> x=y.
Proof.
intros x y. intro Hyp. inversion Hyp. inversion H1. reflexivity.
Qed.

Goal forall x y, x=y -> InMultiset y (singleton x).
Proof.
intros x y. intro Hyp. rewrite Hyp. apply (HD y 0 empty).
Qed.

Goal forall x, multiplicity x (singleton x) = 1.
Proof.
intro x. simpl. destruct (T_eq_dec x x). reflexivity. contradiction.
Qed.


Lemma WfSub : forall a ms, wf(a::ms)-> wf ms.
Proof.
intros a ms. intro Hform. inversion Hform. destruct H0. exact H0.
Qed.

Goal forall x s, wf s -> (member x s = true <-> InMultiset x s).
intros x s. intro Hform. split.
  + intro Hmem. induction s.
    ++ inversion Hmem.
    ++ pose proof (WfSub a s Hform) as Hform2. destruct a as [a1 n]. destruct (T_eq_dec a1 x). 
      +++ destruct n. inversion Hform. rewrite e. apply (HD x n s).
      +++ apply IHs in Hform2. apply (TL (a1,n) x s Hform2). inversion Hmem. destruct (T_eq_dec a1 x). contradiction. reflexivity.
  + intro Hyp. induction Hyp.
    ++ pose proof (WfSub h ms Hform) as Hform2. apply IHHyp in Hform2. destruct h as [a n]. simpl. destruct (T_eq_dec a x). reflexivity. exact Hform2.
    ++ simpl. destruct (T_eq_dec x x). reflexivity. contradiction.
Qed.


Goal forall x n s, n>0 -> InMultiset x (add x n s).
intros x n s Hstr. destruct n. lia. induction s.
  + simpl. apply (HD x n empty).
  + destruct a as [a1 m]. simpl. destruct (T_eq_dec a1 x).
    ++ rewrite e. apply (HD x (n+m) s).
    ++ apply (TL (a1,m) x (add x (S n) s)). exact IHs.
Qed.

Lemma CoqEstPerdu : forall (a : T) (k : nat) (h : T*nat) (ms tl : multiset), h::ms = (a,k)::tl -> tl=ms.
Proof.
intros a k h ms tl. Admitted.


Goal forall x y n s, x<>y ->(InMultiset y (add x n s) <-> InMultiset y s).
Proof.
intros x y n s. intro Hdiff. split.
  + intro Happ. induction s as [|hd tl].
    ++ destruct n. 
      +++ inversion Happ.
      +++ inversion Happ. inversion H1. admit. (** on a x<>y et x=y mais Coq ne voit pas la contradiction ... **)
   ++ destruct hd as [a m]. destruct (T_eq_dec a x).
      +++ rewrite e. apply (TL (x,m) y tl). rewrite -> e in Happ. inversion Happ. destruct (T_eq_dec x x). pose proof (CoqEstPerdu x (n+m) h ms tl H). rewrite <- H2 in H1. exact H1. contradiction. 





inversion Happ. destruct (T_eq_dec a x). apply (TL (a,m) y tl). pose proof (CoqEstPerdu a (n+m) h ms tl H). rewrite H2. exact H1.




























