(** * Tutoriel 5 - Notions avancées sur l'induction *)

Require Export ZArith.

(** Ce tutoriel regroupe différentes notions avancées autour de 
    l'induction. *)

(** ** I. Induction sur un prédicat inductif *)

(** On rappelle la définition de [even] sous forme d'un prédicat inductif. *)
Inductive even : nat -> Prop :=
 | even_0 : even 0
 | even_SS : forall n, even n -> even (S (S n)).

(** Dans le tutoriel 3, vous avez fait beaucoup d'inductions !
    Vous avez peut-être eu des difficultés avec le lemme suivant : *)
Lemma ev_even : forall n,
  even n -> exists k, n = 2 * k.
Proof.
  intros n H.
  (* Comme [even] est un prédicat inductif, il a une structure inductive.
     Il est donc tout à fait possible de faire une induction sur une
     hypothèse énonçant un fait avec [even], comme c'est le cas pour H.
     Ici, il y a donc 2 choix possibles pour faire une induction :
       - [induction n.]
       - [induction H.]
     La preuve est donc faisable en effectuant une induction sur H. *)
     induction H.
      + exists 0. reflexivity.
      + destruct IHeven as [x].
        exists (S x). rewrite H0. simpl.
        symmetry. rewrite plus_n_Sm with (n:=x) (m:=x + 0). reflexivity.
Qed.

(** *** Exercice 1 - Le prédicat inductif le *)

(** On rappelle la définition de [le] sous forme d'un prédicat inductif. *)
Inductive le : nat -> nat -> Prop :=
 | le_n (n : nat) : le n n
 | le_S (n m : nat) (H : le n m) : le n (S m).

(** On introduit une notion pour [le]. *)
Notation "n <= m" := (le n m).

(** Les théorèmes suivants sont assez similaires à ceux que vous avez
    pu faire au tutorial 1. *)
Theorem test_le1 :
  3 <= 3.
Proof. apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. intros H. inversion H. inversion H2. Qed.

(** La relation "strictement inférieur à", notée n < m, peut maintenant être 
    définie en termes de [le]. *)
Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Voici un certain nombre de faits concernant les relations <= et <.
    A vous de jouer ! *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
Admitted.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
Admitted.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
Admitted.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
Admitted.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
Admitted.

(* Conseil : Le prochain point peut être plus facile à prouver par 
             induction sur n. *)
Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
Admitted.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
Admitted.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
Admitted.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
Admitted.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
Admitted.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
Admitted.

(* Conseil : Le prochain point peut être plus facile à prouver par 
             induction sur m. *)
Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
Admitted.

(* Conseil : La suivante peut facilement être prouvée sans utiliser 
             l'induction. *)
Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
Admitted.


(** ** II. Généralisation *)

(** On rappelle la définition de [double]. *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** La stratégie qui consiste à faire [intros] avant une [induction] pour
    pour obtenir une IH plus générale ne fonctionne pas toujours 
    d'elle-même ; parfois un certain réarrangement des variables 
    quantifiées est nécessaire.  
    Supposons, par exemple, que nous voulions prouver [double_injectif] 
    par induction sur induction sur [m] au lieu de [n]. *)
Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Ici, nous sommes bloqués... *)
Abort.

(** Le problème est que, pour faire une induction sur [m], nous devons
    d'abord introduire [n]. (Et si nous disons simplement [induction m] 
    sans rien introduire d'abord, Coq introduira automatiquement [n] 
    pour nous !)  *)

(** Que pouvons-nous faire à ce sujet ? Une possibilité est de réécrire
    l'énoncé du lemme de sorte que [m] soit quantifié avant [n].
    Cela fonctionne, mais ce n'est pas agréable : Nous ne voulons pas avoir
    à tordre l'énoncé des lemmes pour répondre aux besoins d'une stratégie
    particulière pour les prouver !
    Nous voulons plutôt les énoncer de la manière la plus claire et
    la plus naturelle. *)

(** Ce que nous pouvons faire à la place, c'est d'abord introduire toutes
    les variables quantifiées, puis généraliser une ou plusieurs d'entre
    elles, en retirant des variables du contexte et en les remettant
    au début du but.
    La tactique [generalize dependent] permet de faire cela. *)

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* [n] et [m] sont tous les 2 dans le contexte. *)
  generalize dependent n.
  (* Maintenant [n] est de nouveau dans le but et nous pouvons faire une
     induction sur [m] et obtenir un IH suffisamment général. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal.
Qed.

(** *** Exercice 2 - Mise en pratique de la tactique [generalize] *)

Require Export List.

(** La fonction [nth_error] fonctionne avec n'importe quel type de liste. *)
Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
   | nil => None
   | a :: l' => match n with
                 | O => Some a
                 | S n' => nth_error l' n'
               end
  end.

(** Prouvez le théorème suivant par induction sur [l]. *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
Admitted.

(** ** III. Equivalence entre les principes d'induction *)

(** Dans le tutoriel 3, vous avez déjà réfléchi aux relations entre
    les différents principes d'induction.
    Nous allons ici creuser ces équivalences entre différents principes
    d'induction sur les entiers naturels. *)

(** Nous utiliserons comme axiome le principe d'induction généré avec la
    définition du type inductif des entiers naturels qui, souvenons-nous,
    est le suivant : *)
Check nat_ind.
(* nat_ind
     : forall P : nat -> Prop,
       P 0 -> 
       (forall n : nat, P n -> P (S n)) -> 
       forall n : nat, P n *)

(** Ce principe d'induction est dit structurelle, et se note également
       ∀P, P (0) ⇒ (∀n, P (n) ⇒ P (n + 1)) ⇒ ∀n, P (n)
    Dans le cas des entiers naturels, on parle aussi de récurrence faible.

    Une vision plus ensembliste de ce principe d'induction peut s'écrire
    ainsi : ∀E ⊆ N, (0 ∈ E) ⇒ (∀n, (n ∈ E) ⇒ (n + 1 ∈ E)) ⇒ E = N. *)
Theorem weak_induction : forall (P:nat -> Prop),
P O ->
(forall m, P m -> P (S m)) -> 
forall n, P n.
Proof. apply nat_ind. Qed.

(** *** Exercice 3 - Une première équivalence *)

(** L'équivalence avec le principe d'induction avec un k fixé arbitrairement,
    à savoir ∀P, P (k) ⇒ (∀k ≤ n, P (n) ⇒ P (n + 1)) ⇒ ∀k ≤ n, P (n), 
    est facile à démontrer : *)
Theorem arbitrary_k_induction : forall (k:nat) (P:nat -> Prop),
P k -> (forall n, k <= n -> P n -> P (S n)) -> forall n, k <= n -> P n.
Proof.
Admitted.

(** *** Exercice 4 - Equivalence avec la récurrence à 2 pas 
                     et ses variantes *)

(** Démontrer les théorèmes suivants en utilisant seulement des
    inductions sur les entiers naturels. *)

Theorem two_steps_induction : forall (P:nat -> Prop),
  P 0 -> P 1 ->
  (forall n, (P n /\ P (S n)) -> P (S (S n))) ->
  forall n, P n.
Proof.
Admitted.

Theorem variant_two_steps_induction : forall (P:nat -> Prop), 
  P 0 -> P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n /\ P (S n).
Proof.
Admitted.

Theorem weak_variant_two_steps_induction : forall (P:nat -> Prop),
   P 0 -> P 1 ->
  (forall n, P n -> P (S (S n))) ->
  forall n, P n.
Proof.
Admitted.

(** *** Exercice 5 - Equivalence avec la récurrence forte *)

(** Le principe de récurrence forte ou d'induction bien fondée ou encore
    de récurrence cumulative (= généralisation récurrence à n pas) est le
    suivant :
         ∀P, P (0) ⇒ (∀n, [∀k ≤ n, P (k)] ⇒ P (n + 1)) ⇒ ∀n, P (n)

    Pour rappel, le principe d'induction avec un k fixé arbitrairement est
         ∀P, P (k) ⇒ (∀k ≤ n, P (n) ⇒ P (n + 1)) ⇒ ∀k ≤ n, P (n) *)

(** Bien sûr, ce principe implique le principe de récurrence faible : *)
Theorem le_strong_induction_impl_weak_induction : 
  ( forall (P:nat -> Prop),
    P 0 ->
    (forall n, (forall k, k <= n -> P k) -> P (S n)) ->
    forall n, P n
  ) -> forall (P:nat -> Prop),
       P O ->
       (forall m, P m -> P (S m)) -> 
       forall n, P n.
Proof.
Admitted.

(** Mais ce qui est plus intéressant, c'est que l'on peut également 
    démontrer le principe de récurrence forte à l'aide du principe de
    récurrence faible : *)
Theorem le_strong_induction : forall (P:nat -> Prop),
  P 0 ->
  (forall n, (forall k, k <= n -> P k) -> P (S n)) ->
  forall n, P n.
Proof.
Admitted.

(** Cette récurrence peut également se décaler à partir d'un certain rang, 
    exactement comme la récurrence simple. *)

(** Une autre version plus synthétique de ce principe d'induction existe :
       ∀P, (∀n, [∀k < n, P (k)]) ⇒ ∀n, P (n) *)
Theorem lt_strong_induction : forall (P:nat -> Prop),
(forall n, (forall k, k < n -> P k)) -> forall n, P n.
Proof.
Admitted.

(** Pour finir, démontrer le théorème suivant : *)
Theorem lt_strong_induction_impl_weak_induction :
  ( forall (P:nat -> Prop),
    (forall n, (forall k, k < n -> P k)) ->
    forall n, P n
  ) -> forall (P:nat -> Prop),
       P O ->
       (forall m, P m -> P (S m)) -> 
       forall n, P n.
Proof.
Admitted.

(** Merci à François Thiré et Catherine Dubois *)