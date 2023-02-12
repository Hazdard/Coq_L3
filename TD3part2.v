Require Import List.

Require Import Bool.

Variable T : Type.

Hypothesis T_eq_dec : forall (x y :T), {x=y} + {~x=y}.

Definition multiset := list (T*nat).

Definition empty:multiset := nil.

Definition singleton (x : T) := (x,1)::empty .

Fixpoint member (x : T) (ms : multiset) : bool :=
  match ms with
  |nil => false
  |(a,b)::r => match T_eq_dec a x with
                    |left _ => true
                    |right _ => (member x r)
               end
  end.

Fixpoint add (x : T) (n : nat) (ms : multiset) : multiset :=
 match ms with 
  |nil => (x,n)::nil
  |(a,b)::r =>  match T_eq_dec a x with
                    |left _ => (a,b+n)::r
                    |right _ => (a,b)::(add x n r)
               end
end.

Fixpoint union (ms1 : multiset) (ms2 : multiset) : mutliset :=
match ms1 with
  |



