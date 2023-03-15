(** * Tutoriel 6 - Ltac *)

(** Dans ce tutoriel plus avancé, nous allons voir comment
    écrire nos propres tactiques, à l'aide de Ltac. *)


(** ** I. Un premier exemple *)

(** Un premier cas d'utilisation de Ltac  *)

Module Ltac_example.
  Require Import ZArith Lia.
  Open Scope Z_scope.

 (* Définition du type des listes de couples. *)
 Inductive elt_list :=
  | Nil : elt_list
  | Cons : Z -> Z -> elt_list -> elt_list.

 (* Un invariant exprimant que les couples sont rangés 
    par ordre croissant, ne se chevauchent pas, et sont
    séparés d'au moins deux entiers. *)
 Inductive Inv_elt_list : Z -> elt_list -> Prop :=
  | invNil  : forall b, Inv_elt_list b Nil
  | invCons : forall (a b j : Z) (q : elt_list),
     j <= a -> a <= b ->  Inv_elt_list (b+2) q ->
     Inv_elt_list j (Cons a b q).

 (* Un théorème exprimant que si y est plus petit que
    tous les éléments de l, et que z est plus petit que y,
    alors z est plus petit que tous les éléments de l. *)
 Theorem inv_elt_list_monoton : forall l y z, 
 Inv_elt_list y l -> z <= y -> Inv_elt_list z l.
 Proof.
 intros l y z Hinv Hle.
 induction Hinv.
  - constructor.
  - constructor;(lia||assumption).
 Qed.

 (* La tactique [Inv_monotony z] prend en argument une valeur [z] pour
    la variable nommée [y] dans le théorème précédent, valeur difficile 
    à inférer pour Coq.
    Deux buts seront alors générés :
       - un de la forme [Inv_elt_list y l], noté B1
       - et l'autre de la forme [z <= y],   noté B2.
    La tactique [Inv_monotony] permet de finir la preuve si B1 est dans
    les hypothèses et si B2 peut être déduit grâce à la tactique [lia]. *)
 Ltac Inv_monotony z := 
   apply inv_elt_list_monoton with (y:=z);
    [assumption|lia].

End Ltac_example.

(** ** II. Quelques cas d'usage de Ltac *)

  (** Avec Ltac, il est possible de faire bien plus que d'enchainer des 
      tactiques les unes à la suite des autres, comme nous l'avons vu dans 
      l'exemple précédent.
      Une fonctionnalité très puissante de Ltac est de pouvoir faire du 
      pattern-matching sur le but courant. *)

(** *** A. Un premier pattern-matching très simple *)

  (** Voici un premier exemple pour vous montrer la syntaxe d'un
      pattern-matching dans le langage de Ltac :  *)
  Ltac my_trivial_tactic :=
   match goal with
      | [ |- _ ] => intro
      | [ |- True ] => constructor
    end.

  (** Avec la tactique précédente, nous pouvons prouver : *)
  Theorem m1 : True.
  Proof. my_trivial_tactic. Qed.

  (** Notez que [True] matche le 1er cas du pattern-matching de
      [my_trival_tactic] et pourtant ce n'est pas ce cas de figure qui est
      utilisé pour construire le terme de preuve, mais bien le 2ème.
      En effet, le 1er cas du pattern-matching renvoie une erreur car la
      tactique [intro] ne peut pas être utilisée sur le but [True]. *)

(** *** B. Ecrire un pattern-matching plus compliqué *)

  (** La tactique [find_if] vérifie si la conclusion est un if, puis,
      si c'est le cas, détruit l'expression de test. *)
  Ltac find_if :=
    match goal with
      | [ |- if ?X then _ else _ ] => destruct X
    end.

  (** Certaines classes de théorèmes sont triviales à prouver
      automatiquement avec une telle tactique, comme par exemple : *)
  Goal forall (a b c : bool),
    if a
      then if b
        then True
        else True
      else if c
        then True
        else True.
  Proof.
    intros.
    repeat find_if.
      + constructor.
      + constructor.
      + constructor.
      + constructor.
    (* ou encore : [intros; repeat find_if; constructor.] *)
  Qed.

  (** Malheureusement, la tactique [find_if] n'est pas capable de détecter
      qu'un if apparait dans un sous-terme du but, comme le montre l'exemple 
      suivant : *)
  Goal forall (a b : bool),
    (if a then 42 else 42) = (if b then 42 else 42).
  Proof.
    intros. 
    repeat find_if. (* Rien ne se passe. *)
  Abort.

  (** Le pattern [context] permet de résoudre ce problème. *)

  (** Le comportement de la tactique [find_if_inside] est de trouver tout
      sous-terme de la conclusion qui est un if, et ensuite de détruire
      l'expression de test. *)
  Ltac find_if_inside :=
    match goal with
      | [ |- context[if ?X then _ else _] ] => destruct X
    end.

  (** Cette version étend ce que pouvait résoudre la tactique [find_if],
      car nous pouvons toujours démontrer : *)
  Goal forall (a b c : bool),
    if a
      then if b
        then True
        else True
      else if c
        then True
        else True.
  Proof.
    intros; repeat find_if_inside; constructor.
  Qed.

  (** Mais nous pouvons également utiliser [find_if_inside] pour prouver
      les objectifs que [find_if] ne simplifie pas suffisamment : *)
  Goal forall (a b : bool),
    (if a then 42 else 42) = (if b then 42 else 42).
  Proof.
    intros; repeat find_if_inside; reflexivity.
  Qed.

(** *** C. Faire référence à une hypothèse dans un pattern-matching *)

  (** Lorsque nous avons écrit les tactiques [find_if] et [find_if_inside],
      nous avons vu la syntaxe [?X], permettant de faire référence à un 
      sous-terme. *)

  (** Notez ici comment faire référence à une hypothèse dans le
      pattern-matching : *)
  Ltac intro_exact := intros; match goal with
      | [ H : _ |- _ ] => exact H
    end.

  (** Avec la tactique [intro_exact], il est possible de prouver le but
      suivant : *)
  Goal forall P Q R : Prop, P -> Q -> R -> Q.
  Proof. intro_exact. Qed.

(** *** D. Pour le débuggage : [idtac] *)

(** Ltac n'est pas très simple à prendre en main.
    Pour vous aider à mieux comprendre pourquoi la tactique que vous
    avez écrit ne fait pas ce que vous voulez, vous pouvez utiliser la
    tactique [idtac]. *)

Ltac ex_idtac :=
  intros; match goal with
              | [ H : ?P |- _ ] => idtac H ; idtac P
          end.

Goal forall P, P -> P.
Proof. ex_idtac. apply X. Qed.


(** ** III. Quelques exercices *)

  (** *** Exercice 1 - Votre version de la tactique [tauto] *)

  (** Cet exercice vous propose d'utiliser le langage de Ltac pour écrire
      une version la plus proche possible de la tactique [tauto].
      Vous nommerez votre tactique [my_tauto]. *)

Ltac my_tauto := 
  intros; repeat match goal with
      | [ |- True ] => constructor ; idtac "1"
      | [ _ : ?X |- ?X ] => assumption ; idtac "2"
      | [ H : False |- _ ] => contradiction ; idtac "3"
      | [ H : _/\_ |- _ ] => destruct H ; idtac "4"
      | [ |- _/\_ ] => split ; idtac "5"
      | [ H : _\/_ |- _ ] => destruct H ; idtac "6"
      | [ H : ?P->?Q |- ?Q ] => apply H ; idtac "7"
      | [ H1 : ?P , H2 : ?P->_ |- _ ] => apply H2 in H1 ; idtac "8"
      | [ |- exists (_:?T), _ ] => eexists ; idtac "9"
      | [ H : exists (_ : ?T), _  |- _] => destruct H ; idtac "10"
      end.


  (** Voici quelques cas de tests pour vous aider à tester votre tactique : *)

  (* Niveau 1 : Une première version *)
  Goal forall P, P -> True.
  Proof. my_tauto. Qed.

  Goal forall P Q R : Prop, P -> Q -> R -> Q.
  Proof. my_tauto. Qed.

  Goal forall P Q R : Prop,
    P /\ R /\ Q -> Q /\ R /\ P.
  Proof. my_tauto. Qed.

  Goal forall P Q : Prop,
    Q /\ (P /\ False) /\ P -> P /\ Q.
  Proof. my_tauto. Qed.

  Goal forall P Q,
    False /\ P -> Q.
  Proof. my_tauto. Qed.


  (* Niveau 2 : Avec le modus ponens *)
  Goal forall P Q : Prop,
    (P -> Q) -> (P -> True /\ Q).
  Proof. my_tauto. Qed.

  Goal forall P Q R : Prop,
    (Q -> R) -> (P /\ Q -> P /\ R).
  Proof. my_tauto. Qed.

  Goal forall P Q R S,
    (S -> P /\ (Q /\ R)) -> (S -> (P /\ Q) /\ R).
  Proof. my_tauto. Qed.

  Goal forall P Q R S,
    (S -> Q /\ (P /\ R)) -> (S -> (P /\ Q) /\ R).
  Proof. my_tauto. Qed.

  Goal forall P Q R,
    (R -> P /\ Q) -> (R -> Q /\ P).
  Proof. my_tauto. Qed.

  Goal forall P Q,
    (P -> Q /\ True) -> (P -> Q).
  Proof. my_tauto. Qed.


  (* Niveau 3 : Quelques cas plus avancés *)
  Goal forall P Q R : Prop, 
    (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
  Proof. my_tauto. Qed.

  Goal forall P Q,
    (P /\ True -> Q) -> (P -> Q).
  Proof. my_tauto. Qed.

  Goal forall P Q R S,
    (P /\ (Q /\ R) -> S) -> ((P /\ Q) /\ R -> S).
  Proof. my_tauto. Qed.

  Goal forall P Q R S,
    (Q /\ (P /\ R) -> S) -> ((P /\ Q) /\ R -> S).
  Proof. my_tauto. Qed.

  Goal forall P Q R,
    (P /\ Q -> R) -> (Q /\ P -> R).
  Proof. my_tauto. Qed.

  (* Niveau 4 : Pour aller plus loin que la tactique [tauto] *)
  Goal forall (T : Type) (P : T -> Prop) (Q R : Prop),
    (forall x, P x /\ Q -> R) -> (exists y, P y /\ Q -> R).
  Proof. my_tauto. Abort. (* L'énoncé est faux en l'état, nous ne savons pas si il existe un élément de type  T*)

  Goal forall (T : Type) (P : T -> Prop) (Q R : Prop) x,
    (Q -> P x /\ R) -> (Q -> ex P /\ R).
  Proof. my_tauto. Admitted.

  Goal forall (P : nat -> Prop) Q, (exists x, P x /\ Q) -> Q /\ (exists x, P x).
  Proof. my_tauto. Qed.


  (** *** Exercice 2 - Passer de [bool] à [Prop] *)

  Require Import Arith Lia.

  (** Vous avez peut-être déjà remarqué que, parfois, Coq fait apparaitre des
      "notations" un peu étranges, comme [<=?]. *)

  (** En réalité, [<=] est une notation pour [le], qui lui-même est un 
      prédicat inductif. Son type de retour est donc [Prop]. *)

  Check le.
  Check 1 <= 2.

  (** Par contre, [<=?] a pour type de retour [bool], comme vous le montre 
  les commandes suivantes : *)
  Check  1 <=? 2.
  Check (1 <=? 2) = true.

  (** Il est tout à fait possible de passer d'une notation à l'autre : *)
  Lemma le_bool_imp_le : forall n m, (n <=? m) = true -> (n <= m).
  Proof.
  induction n.
   + destruct m.
      { intros. constructor.                     }
      { intros. constructor. apply Peano.le_0_n. }
   + destruct m.
      { simpl. intro H. discriminate H.                                 }
      { simpl. intro H. apply IHn in H. apply Peano.le_n_S. assumption. }
  Qed.

  (** Mais comme [lia] ne raisonne que sur [Prop], cette tactique est capable
      de prouver le but [lt_impl_le_prop], mais pas le but [lt_impl_le_bool]. *)
  Lemma lt_impl_le_prop : forall n m, n < m -> n <= m.
  Proof. intros. lia. Qed.

  Lemma lt_impl_le_bool : forall n m, (n <? m) = true -> (n <=? m) = true.
  Proof. intros. (* lia. *) Abort.


  (** Votre objectif est donc d'écrire une tactique qui réécrit des notations
      [bool] en des notations sur [Prop].
      L'utilisation de la bibliothèque standard de Coq est fortement 
      recommandée. *)

  (** Vous commencerez par écrire une tactique qui transforme uniquement les
      hypothèses.
      Ensuite, il sera plus simple d'écrire une tactique qui transforme le but
      courant, en adaptant la tactique écrite précédemment. *)



(** ** IV. Des références pour aller plus loin *)

(** Ltac :
      - http://adam.chlipala.net/cpdt/html/Match.html
      - http://www.lirmm.fr/~delahaye/papers/ltac%20(LPAR%2700).pdf

    Ltac2, une version typée de Ltac :
      - https://coq.inria.fr/refman/proof-engine/ltac2.html *)
