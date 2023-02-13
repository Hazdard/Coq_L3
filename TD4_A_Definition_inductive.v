(** * Tutoriel 3 - Retour sur les types et prédicats inductifs *)

(** Cette feuille d'exercices regroupe différents exercices 
    courants sur les types et prédicats inductifs. *)



(** ** Exercice 1 - Addition et multiplication sur les entiers *)

(** Les nombres naturels sont prédéfinis dans Coq, comme le montre la 
    requête suivante.
    Du sucre syntaxique est également disponible pour écrire, par exemple, 
    [2] au lieu de [S (S O)]. *)

Print nat.

Goal 2 = S (S O).
Proof.
  reflexivity.
Qed.

(** La définition inductive de [nat] est en dehors des possibilités de la
    logique du premier ordre : elle a un certain nombre de conséquences 
    implicites montrées ci-dessous.

    Notez ici l'utilisation de la tactique [inversion] sur les égalités 
    entre les constructeurs du type inductif [nat]. *)

Goal forall x:nat, O <> S x.
Proof.
  intros x H.
  inversion H.
Qed.

Goal forall x y : nat, S x = S y -> x = y.
Proof.
  intros x y H.
  inversion H.
  reflexivity.
Qed.

(** Nous pouvons utiliser [destruct] pour effectuer une analyse de cas sur 
    un nombre naturel. *)

Goal forall x:nat, x = O \/ exists y:nat, x = S y.
Proof.
  intro x. destruct x.
  + left. reflexivity.
  + right. exists x. reflexivity.
Qed.

(** Un principe d'induction est également dérivé de la définition inductive,
    qui est implicitement utilisée par la tactique [induction].
    Notez que le principe d'induction est une formule d'ordre supérieur,
    quantifiant sur [Prop]. *)

Check nat_ind.

Lemma Sx_x : forall x:nat, S x <> x.
Proof.
  intros x H.
  induction x.
  + inversion H.
  + inversion H. apply IHx. exact H1.
Qed.

(** [x+y] est une notation pour [plus x y]. Contrairement à la logique du
    premier ordre, [plus] n'est pas un symbole de fonction abstraite dont
    l'interprétation est contrainte par des axiomes.

    Il est plutôt défini comme une fonction récursive sur les nombres naturels.
    Dans Coq, toutes les fonctions sont totales : la terminaison est garantie 
    et il n'y a pas d'erreurs. *)

Print plus.

(** Dans la preuve suivante, nous utilisons [simpl] pour calculer [1+1].
    Notez que le script de preuve fonctionne sans cette
    étape de simplification explicite. *)

Goal 2 = 1+1.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma succ_simpl : forall x y : nat, S x + y = S (x+y).
Proof.
  intros. reflexivity.
Qed.

(** Les preuves suivantes ne sont pas des calculs évidents pour Coq :
    l'induction sera nécessaire à la place. Afin d'utiliser
    une hypothèse d'égalité, vous aurez besoin de la tactique [rewrite]. *)

Goal forall x y z : nat, x = y -> x + z = y + z.
Proof.
  intros x y z Heq.
  rewrite Heq.
  reflexivity.
Qed.

(** Prouver les lemmes suivants sur l'addition des entiers naturels : *)
Lemma plus_0_n : forall n, 0 + n = n.
Proof.
intro n. simpl. reflexivity.
Qed.

Lemma plus_n_0 : forall n, n + 0 = n.
Proof.
intro n. induction n.
  + reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

(** Ecrire la multiplication pour les entiers *)

(** Prouver les lemmes suivants. *)

Lemma mult_0_n : forall n : nat, 0 * n = 0.
Proof.
intro n. simpl. reflexivity.
Qed.

Lemma mult_n_0 : forall n, n * 0 = 0.
Proof.
intro n. induction n.
  + reflexivity.
  + simpl. exact IHn.
Qed.

Lemma plus_assoc : forall n m p,
  n+(m+p) = n+m+p.
Proof.
intros n m p. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m,
  n + S m = S (n + m).
Proof.
intros n m. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_comm : forall n m, n + m = m + n.
Proof.
intros n m. induction n.
  + simpl. rewrite plus_n_0. reflexivity.
  + simpl. rewrite plus_n_Sm. rewrite IHn. reflexivity.
Qed.

Lemma mult_n_Sm : forall n m, n*S m = n + n*m.
Proof.
intros n m. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. rewrite plus_assoc. rewrite plus_assoc. rewrite plus_comm with (n:=m) (m:=n). reflexivity.
Qed.

Lemma mult_comm : forall n m, n *m=m*n.
Proof.
intros n m. induction n.
  + simpl. rewrite mult_n_0. reflexivity.
  + simpl. rewrite mult_n_Sm. rewrite IHn. reflexivity.
Qed.

Lemma mult_plus_distr_r : forall n m p,
  (n+m)*p = n*p+m*p.
Proof.
intros n m p. induction p.
  + rewrite mult_n_0. rewrite mult_n_0. rewrite mult_n_0. simpl. reflexivity.
  + rewrite mult_n_Sm. rewrite mult_n_Sm. rewrite mult_n_Sm. rewrite IHp. rewrite plus_assoc. 
    symmetry. rewrite plus_assoc. rewrite plus_comm with (n:=n+n*p) (m:=m). rewrite plus_assoc. rewrite plus_comm with (n:=m) (m:=n). reflexivity.
Qed.

Lemma mult_assoc : forall n m p, n*(m*p) = (n*m)*p.
Proof.
intros n m p. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. rewrite mult_plus_distr_r. reflexivity.
Qed.

(** Prouver directement par induction sur n *)
Lemma mult_plus_distr_l : forall n m p,
  n*(m+p)=n*m+n*p.
Proof.
intros n m p. induction n.
  + simpl. reflexivity.
  + 
 
(** Prouver en utilisant les lemmes précédents, mais bien sûr pas    
   [mult_plus_distr_l]) *)
Lemma mult_plus_distr_l_bis : forall n m p,
  n*(m+p)=n*m+n*p.
Proof.
Admitted.

(** ** Exercice 2 - L'appartenance à une liste *)

(** Après avoir compris la signification de [mem],
    prouver les lemmes qui suivant. *)

Variable A : Type.

Inductive mem : A -> list A -> Prop :=
  mem_head : forall x l, mem x (cons x l)
| mem_tail : forall x y l, 
   mem x l -> mem x (cons y l).

Check app.
Print app.

Lemma app_left : forall l1 l2 x,
mem x l1 -> mem x (app l1 l2).
Proof.
Admitted.


Lemma app_or : forall l1 l2 x, 
mem x (app l1 l2) -> mem x l1 \/ mem x l2.
Proof.
Admitted.

(** ** Exercice 3 - Retour un ancien exercice *)

(** Souvenez-vous d'un exercice de la première feuille ! 
    Peut-être que, dans un premier temps, vous aviez défini
    la fonction double ainsi : *)
Definition double_math (m:nat) : nat := plus m m.

(** Mais pour des raisons calculatoires, il était préférable d'écrire : *)
Fixpoint double (m:nat) : nat := 
  match m with
  | 0 => 0
  | S p => S (S (double p))
  end.

(** A présent, vous avez toutes les clefs en main pour démontrer leur
    équivalence : *)

Lemma equiv_double_math_double :
forall n, double_math n = double n.
Proof.
Admitted.

(** ** Exercice 4 - Une vision plus calculatoire *)

(** De même que pour [double], il est possible d'écrire une version plus 
    calculatoire de [even] : *)
Definition is_even n := exists p, n = 2 * p.

(** Prouver les lemmes suivants : *)

Lemma zero_is_even : is_even 0.
Proof.
Admitted.

Lemma is_even_plus : forall n p, 
   is_even n -> is_even p -> is_even (n + p).
Proof.
Admitted.

(** ** Exercice 5 - Retour sur le prédicat de parité *)

(** On rappelle la définition de [even] sous forme d'un prédicat inductif . *)

Inductive even : nat -> Prop :=
 | even_0 : even 0
 | even_SS : forall n, even n -> even (S (S n)).

(** Prouver les lemmes suivants : *)

Lemma even_4 : even 4.
Proof.
Admitted.

Lemma even_succ_lemma : forall n, even n -> even (S (S (S (S n)))).
Proof.
Admitted.

Theorem even_plus4 : forall n, even n -> even (4 + n).
Proof.
Admitted.
 
Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
Admitted.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
Admitted.

Lemma ev_even : forall n,
  even n -> exists k, n = 2 * k.
Proof.
Admitted.
 
Lemma even_n_or_Sn : forall n, even n \/ even (S n).
Proof.
Admitted.

Lemma even_n_not_Sn : forall n, even n -> ~ even (S n).
Proof.
Admitted.

(** Induction de 2 en 2. *)
Lemma two_steps_induction : forall P : nat -> Prop, 
   P 0 -> 
   P 1 ->
  (forall n, P n -> P (S (S n))) ->
     forall n, P n.
Proof.
Admitted.

Lemma even_dec : forall n, even n \/ ~ even n.
Proof.
Admitted.


(** Définir [evenb : nat -> bool] qui teste si un entier est pair. *)


(** Prouver les lemmes suivants. Si vous avez besoin de résultats sur les
    booléens, vous pouvez les trouver dans [Bool]
    (utiliser [Require Import Bool.]). *)

Lemma evenb_correct : forall n, evenb n = true -> even n.
Proof.
Admitted.



Lemma evenb_complete : forall n, even n -> evenb n = true.
Proof.
Admitted.


Lemma evenb_spec : forall n, evenb n = true <-> even n.
Proof.
Admitted.


(** Prouver [even_dec_bis : forall n, even n \/ ~ even n]
    en utilisant [evenb_spec]. *)

Lemma even_dec_bis : forall n, even n \/ ~ even n.
Proof.
Admitted.


(** ** Exercice 6 - Ordre *)

(** [x <= y] est une notation pour [le x y],
    où [le] est défini de manière inductive comme le montre la 
    requête sui