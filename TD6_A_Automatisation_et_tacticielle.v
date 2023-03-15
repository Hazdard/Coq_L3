(** * Tutoriel 6 - Un peu d'automatisation *)

(** Durant les différentes feuilles d'exercices que vous avez cherchées
    jusqu'ici, peut-être que vous avez eu parfois l'envie d'aller plus vite,
    ou plutôt de laisser Coq faire ou finir la preuve seule, car vous avez
    déjà effectué à plusieurs reprises des morceaux de preuve similiaires.

    Ce tutoriel est donc là pour vous donner quelques moyens pour écrire
    plus vite vos scripts de preuve, ou pour vous aider à poursuivre 
    l'élaboration d'un script de preuve. *)

(** ** I. Tactiques automatiques *)

(** *** A. Les tactiques [tauto], [auto] et [intuition] *)

Module T2_A.

  Variables P Q R : Prop.

  (** Pour commencer, sachez que la tactique [tauto] permet de résoudre un
      but de la logique propositionnelle.
      Si le but ne peut pas être prouvé avec [tauto], alors [tauto] échoue.

      Ainsi, la preuve suivante ... *)

  Goal P /\ Q -> Q /\ P.
  Proof.
    intro H.
    destruct H.
    split.
     + exact H0.
     + exact H.
  Qed.

  (** ... peut s'effectuer de manière automatique à l'aide de [tauto] : *)

  Goal P /\ Q -> Q /\ P.
  Proof. tauto. Qed.

  (** Vous noterez que la plupart des preuves que vous avez du effectuer dans
      la feuille d'exercices [T2_A_prouver.v], peuvent se faire uniquement
      avec [tauto] : *)

  Goal P \/ Q -> Q \/ P.
  Proof. tauto. Qed.

  Goal P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
  Proof. tauto. Qed.

  Goal (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).
  Proof. tauto. Qed.

  Goal (P -> Q -> R) -> (Q -> P -> R).
  Proof. tauto. Qed.

  Goal (P -> Q -> R) <-> (P /\ Q -> R).
  Proof. tauto. Qed.

  Goal P -> ~ ~ P.
  Proof. tauto. Qed.

  Goal (~P /\ ~Q) -> ~(P \/ Q).
  Proof. tauto. Qed.

  Goal ~(P \/ Q) -> (~P /\ ~Q).
  Proof. tauto. Qed.

  Goal (~P \/ ~Q) -> ~(P /\ Q).
  Proof. tauto. Qed.

  Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
  Proof. tauto. Qed.

  (** Ici, remarquez que [tauto] n'est pas gêné par les quantification 
      sur [Prop]. *)
  Lemma P_notP_contradiction : forall P : Prop, ~ (P /\ ~ P).
  Proof. tauto. Qed.

  Lemma not_and : forall P Q : Prop, P \/ Q -> ~(~ P /\ ~Q).
  Proof. tauto. Qed.

End T2_A.

(** La feuille d'exercices [T2_B_prouver.v] ne peut cependant pas être 
    effectuée avec [tauto]. *)

Module T2_B_exists.

  Variable T : Type.
  Variable P : T -> Prop.
  Variable Q : Prop.
  Variable R : T -> T -> Prop.

  (** Essayez de finir la preuve ci-dessous avec [tauto] et constatez
      que [tauto] échoue. *)

  Goal (exists x:T, forall y:T, R x y)
    -> (forall y:T, exists x:T, R x y).
  Proof.
    intros H y.
    destruct H.
    exists x.
    apply H.
  Qed.

  (** A l'inverse, la tactique [auto] n'échouera pas.
      Cette tactique peut tout de même prouver plus de buts que [tauto].

      Regardez attentivement le script suivant pour bien comprendre
      les différences entre [tauto] et [auto]. *)

  Goal (exists x:T, forall y:T, R x y)
    -> (forall y:T, exists x:T, R x y).
  Proof.
    auto.
    intros H y. auto.
    destruct H. auto.
    exists x.   auto. (* Alors que [tauto] échoue ici. *)
  Qed.

  (** Pour résoudre un but de la logique constructive du 1er ordre, il existe
      aussi la tactique [intuition] qui :
        - n'échoue jamais (comme [auto] donc)
        - a l'un des comportemens suivants :
           * Ne fait rien (et dans ce cas il est préférable de la supprimer)
           * Avance la preuve (contrairement à [auto])
           * Finit la preuve

      Regardez attentivement le script suivant pour bien comprendre
      les différences entre [tauto], [auto] et [intuition]. *)

  Goal (exists x:T, forall y:T, R x y)
    -> (forall y:T, exists x:T, R x y).
  Proof.
    intuition. (* Alors que [auto] ne fait rien, et que [tauto] échoue. *)
    destruct H. intuition.
    exists x.   intuition. (* Même résultat que [auto]. *)
  Qed.

  (** ATTENTION : Cette tactique peut vous aider à avancer une preuve, mais
                  elle peut aussi vous emmener dans une mauvaise direction !
                  Ce n'est pas parce que [intuition] fait quelque chose que
                  c'est ce qu'il fallait faire pour terminer la preuve.

                  De plus, comme [intuition] fait des [intros], vos scripts
                  sont moins robustes. Si les conventions de nommage de
                  [intuition] changent, vos scripts ne fonctionneront plus.
                  Il en est de même si [intuition] devient plus expressive.

      Je recommande donc d'utiliser [intuition] pour vous aider à trouver
      une preuve, mais de chercher à la supprimer de vos scripts finaux. *)


(** *** B. Le cas des existentielles *)

  (** Il n'est pas toujours aisé de manipuler des buts avec des existentielles.
      Voyons les outils que Coq propose pour nous aider dans ce cas de 
      figure. *)

  (** Les tactiques [econstructor], [eexists], [esplit], [eleft], [eright] se
      comportent comme [constructor], [exists], [split], [left] et [right]
      respectivement, mais elles introduisent des variables existentielles 
      au lieu d'échouer lorsqu'une variable ne peut pas être instanciée. *)

  (** La tactique [eapply] se comporte comme [apply] mais elle n'échoue pas
      lorsque aucune instanciation n'est déductible pour certaines variables 
      des prémisses. Au contraire, elle transforme ces variables en variables 
      existentielles qui sont des variables restant à instancier. 

      L'instanciation est destinée à être trouvée plus tard dans la preuve,
      potentiellement par une utilisation de [apply] qui pourra instancier
      toutes les variables existentielles. *)

  (** Ainsi, la preuve précédente peut également se faire ainsi : *)

  Goal (exists x:T, forall y:T, R x y)
    -> (forall y:T, exists x:T, R x y).
  Proof. 
  intros H y.
  destruct H.
  eexists.  (* ?x est une variable existentielle *)
  eapply H. (* ou [apply H] *)
  Qed.

  (** Il est possible d'instancier soi-même les variables existentielles à 
      l'aide de la tactique [instantiate].

      Le 1 dans le script ci-dessous identifie une variable existentielle
      apparaissant dans le but actuel. La convention de nommage est que la
      dernière variable existentielle apparaissant est attribuée au numéro 1,
      l'avant-dernière au numéro 2, et ainsi de suite.
      L'existentielle nommée est remplacée partout par le terme à droite 
      du :=. *)

  Goal (exists x:T, forall y:T, R x y)
    -> (forall y:T, exists x:T, R x y).
  Proof. 
  intros H y.
  destruct H.
  eexists.
  instantiate (1 := x). eapply (H y). (* ou [apply H] *)
  Qed.

  (** La tactique [instantiate] peut être pratique pour faire de l'exploration
      de preuve, mais elle conduit à des scripts de preuve très fragiles qui
      ont peu de chances de s'adapter à des énoncés de théorèmes changeants.
      Il est souvent plus utile d'avoir une tactique qui peut être utilisée
      pour attribuer une valeur à un terme connu pour être un existentiel. *)


  (** **** Exercice 1 - A vous de jouer ! *)

  Goal (exists x:T, P x \/ Q) -> ((exists x:T, P x) \/ Q).
  Proof.
    intro H. destruct H. destruct H.
     + left.  eexists. eapply H.
     + right. exact H.
Qed.

  Variable a : T.

  Goal ((exists x:T, P x) \/ Q) -> (exists x:T, P x \/ Q).
  Proof.
  intro Hor.
  destruct Hor as [Hex | HQ].
   + destruct Hex. eexists. left. instantiate (1 := x). apply H.
   + exists a. right. exact HQ. 
Qed.

  (* Finissez cette preuve à l'aide de la tactique [instantiate]. *)
  Goal exists p : nat * nat, fst p = 3.
  Proof.
  eexists. instantiate (1 := (3,42)). simpl. reflexivity.
Qed.

End T2_B_exists.

  (** De nombreuses autres tactiques possèdent également leur version
      n'échouant pas lorsque des variables ne peuvent pas être instanciées,
      comme [eassumpion], [eexact] ou encore [eauto]. *)


(** *** C. Les tactiques [congruence], [ring] et [lia] *)

(** Certaines tactiques existent pour résoudre des buts dans un domaine
    spécialisé des mathématiques :
      - [congruence] pour résoudre des égalités closes avec des symboles
                     non interprétés, en utilisant également les propriétés
                     des constructeurs de types inductifs.
      - [ring] pour résoudre des égalités avec des additions et
               multiplications (dans un anneau donc)
      - [lia] (anciennement [omega]) pour résoudre un but avec des équations
                                     et inéquations linéaires *)

(** Commençons avec des exemples utilisant la tactique [congruence].
    Elle permet de faire automatiquement des preuves de la feuille
    d'exercices [T2_B_prouver.v]. *)

Module T2_B_equality.

  Variable T : Type.
  Variable P : T -> Prop.

  Variable f : T -> T.

  Goal forall x y : T, x = y -> f x = f y.
  Proof. congruence. Qed.

  Goal forall x y : T, x = y -> P y -> P x.
  Proof. congruence. Qed.

  Goal forall x y : T, forall z:T,
    x = y -> f y = z -> P (f x) -> P z.
  Proof. congruence. Qed.

  Lemma symmetry : forall x y : T, x = y -> y = x.
  Proof. congruence. Qed.

  (** Rappel : La tactique [symmetry] permet d'échanger les deux membres d'une
      égalité. *)

  Lemma transitivity : forall x y z : T, x = y -> y = z -> x = z.
  Proof. congruence. Qed.

End T2_B_equality.

(** Continuons avec des exemples utilisant la tactique [ring]. *)

Require Import ZArith. (* inclut Require Import Ring. *)
Open Scope Z_scope.

Module Ex_ring.

  Goal forall a b c:Z,
      (a + b + c) ^ 2 =
       a * a + b ^ 2 + c * c + 2 * a * b + 2 * a * c + 2 * b * c.
  Proof. intros a b c. ring. Qed.

  Goal forall a b:Z,
       2 * a * b = 30 -> (a + b) ^ 2 = a ^ 2 + b ^ 2 + 30.
  Proof. intros a b H. ring [H]. Qed.

End Ex_ring.

(** Enfin, voici un exemple utilisant la tactique [lia]. *)

Require Import Recdef Lia.

Goal forall z z0 x, z <= x <= z0 <-> (z <= z0) /\ (z = x \/ z+1 <= x <= z0).
Proof.
intros z z0 x.
split.
 - intro Hyp. destruct (dec_eq z x).
   * split.
        + lia.
        + left. assumption.
   * split.
        + lia.
        + right. destruct Hyp. split.
          { lia. }
          { assumption. }
 - intro Hyp. destruct Hyp. destruct H0.
    * lia.
    * lia.
Qed.

(** Il existe d'autres moyens pour vous aider à l'élaboration d'une
    preuve : c'est ce que nous allons le voir par la suite. *)


(** ** II. Tacticielle *)

(** Une tacticielle permet de combiner plusieurs tactiques entre-elles. *)

(** Par exemple, la preuve suivante ... *)
Goal forall (P : bool -> Prop), P true /\ P false -> forall b, P b.
Proof.
intros P Hyp1 b.
destruct Hyp1.
destruct b.
 + assumption.
 + assumption.
Defined.

(** ... peut être simplifiée en : *)

Goal forall (P : bool -> Prop), P true /\ P false -> forall b, P b.
Proof.
intros P Hyp1 b.
destruct Hyp1.
destruct b ; assumption. (* Ici, les 2 buts générés par [destruct b]
                            sont prouvables de la même manière.
                            Nous pouvons donc utiliser la tacticielle [;]
                            pour utiliser [assumption] directement dans les
                            2 buts générés. *)
Defined.

(** Les tacticielles vous permettent de rendre vos scripts plus concis et 
    plus robustes.
    L'utilisation des tacticielles doit être guidée par l'amélioration de la
    lisibilité de vos scripts. *)


(** Voyons plusieurs façons d'utiliser des tacticielles sur le lemme suivant :
       Lemma andb_prop : forall b1 b2,
       andb b1 b2 = true -> b1 = true /\ b2 = true. *)

(** Mettre les tactiques les unes à la suite des autres rend le script 
    illisible : il est très difficile de comprendre après coup, pourquoi
    l'énoncé a pu être prouvé. *)
Goal forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H.
  split.
  destruct b1.
  reflexivity.
  simpl in H.
  discriminate H.
  destruct b2.
  reflexivity.
  destruct b1.
  simpl in H.
  discriminate H.
  simpl in H.
  discriminate H.
Qed.

(** Structurer son script aide à sa compréhension, mais un script sans
    tacticielle est souvent très verbeux. *)
Goal forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H.
  split.
   - destruct b1.
      + reflexivity.
      + simpl in H. discriminate H.
   - destruct b2.
      + reflexivity.
      + destruct b1.
         * simpl in H. discriminate H.
         * simpl in H. discriminate H.
Qed.

(** L'utilisation des tacticielles permet de mettre en évidence les étapes de
    la preuve qui sont importantes, et de cacher les autres qui le sont moins. 

    La preuve précédente cache uniquement les 2 dernières lignes du 
    script précédent. *)
Goal forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H.
  split.
   - destruct b1.
      + reflexivity.
      + simpl in H. discriminate H.
   - destruct b2.
      + reflexivity.
      + destruct b1;simpl in H;discriminate H.
Qed.

(** Mais nous pouvons aussi cacher les étapes utilisant la réflexivité,
    à l'aide de [try] : *)
Goal forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H.
  split.
   - destruct b1;try reflexivity.
     simpl in H. discriminate H.
   - destruct b2;try reflexivity.
     destruct b1.
       * simpl in H. discriminate H.
       * simpl in H. discriminate H.
Qed.
(** La tacticielle [try] essaye la ou les tactiques passées en paramètre
    sur chaque sous-buts générés, de manière non récursive.
    Si le sous-but n'est pas résolu, celui-ci n'est pas modifié par [try].
    La tacticielle [try] ne peut pas échouer. *)

(** Il est également possible d'utiliser la tacticielle t0;[t1|t2] qui
    si la tactique t0 génère 2 sous-buts, applique la tactique t1
    sur le 1er sous-but, et la tactique t2 sur le 2ème sous-but.  *)
Goal forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H. 
  split;[destruct b1 | destruct b2].
    - reflexivity.
    - simpl in H. discriminate H.
    - reflexivity.
    - destruct b1.
       * simpl in H. discriminate H.
       * simpl in H. discriminate H.
Qed.

(** Au final, nous pouvons écrire le script de la manière suivante,
    mettant en valeur que la preuve a nécessité une analyse par cas
    sur b1, puis sur b2, et que tous les sous-buts générés ont été
    résolus facilement, sauf un qui a néccessité une autre analyse
    par cas sur b1 : *)
Goal forall b1 b2, andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H. 
  split;[destruct b1 | destruct b2]; 
    try (reflexivity || simpl in H; discriminate H).
  destruct b1; simpl in H ; discriminate H.
Qed.
(** Notez l'utilisation de la tacticielle (t1 || t2) combinée avec [try].
    Cela permet d'appliquer t1, puis t2 si t1 n'a pas permis de résoudre
    le sous-but courant généré.
    Dans la preuve précédente, [try] est nécessaire car tous les sous-buts
    ne sont pas résolus grâce à (reflexivity || simpl in H; discriminate H). *)


(** Ainsi, vous avez découvert les tacticielles suivantes : 
      - ;
      - try
      - [ | ]
      - ( || )

    Avant de conclure cette première feuille d'exercices, voyons comment
    s'utilise la tacticielle [repeat]. *)

(** Rappelons la définition de [even] sous forme d'un predicat inductif. *)
Inductive even : nat -> Prop :=
 | even_0 : even 0
 | even_SS : forall n, even n -> even (S (S n)).

(** Vous avez également déjà effectué la preuve suivante : *)
Lemma even_4 : even 4.
Proof.
apply even_SS. apply even_SS. apply even_0.
Qed.

(** Vous sauriez faire la preuve suivante, mais cela serait très fastidieux : *)
Lemma even_120 : even 120.
Proof.
apply even_SS. apply even_SS. apply even_SS. (* ... apply even_0. *)
Abort.

(** En réalité, vous connaissez déjà la tactique [constructor], qui permet de 
    faire la preuve [even_4] un peu plus automatiquement : *)
Lemma even_4_bis : even 4.
Proof.
constructor. constructor. constructor.
Qed.

(** Si vous combinez la tactique [constructor] avec la tacticielle [repeat],
    qui applique la tactique donnée en paramètre tant qu'elle s'applique,
    vous êtes capable de faire la preuve nommée précédemment [even_120] : *)
Lemma even_120 : even 120.
Proof.
repeat constructor.
Qed.

(** ATTENTION : Il faut faire attention lorsque vous utilisez la tacticielle
                [repeat] car une mauvaise utilisation pourrait faire boucler
                à l'infini la recherche de la suite de la preuve ! *)


(** **** Exercice 2 - A vous de jouer ! *)

Require Import Recdef ZArith Lia.
Open Scope Z_scope.

(** Simplifiez la preuve suivante à l'aide des tacticielles. *)
Goal forall z z0 x, z <= x <= z0 <-> (z <= z0) /\ (z = x \/ z+1 <= x <= z0).
Proof.
 intros.
 split.
 intro Hyp.
 destruct (dec_eq z x).
 split.
 lia.
 left.
 assumption.
 split.
 lia.
 right.
 destruct Hyp. 
 split.
 lia.
 assumption.
 intro Hyp.
 destruct Hyp. 
 destruct H0.
 lia.
 lia.
Qed.

Goal forall z z0 x, z <= x <= z0 <-> (z <= z0) /\ (z = x \/ z+1 <= x <= z0).
Proof. 
lia.
Qed.


(** La feuille d'exercices suivante vous présente un langage permettant
    d'écrire vos propres tactiques. *)
