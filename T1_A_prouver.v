(** * Tutoriel 1 - Prouver avec Coq : Logique propositionnelle *)

Require Import Bool.

(** ** I. Un premier exemple *)

(** Souvenez-vous de cet exposé sur Coq (et sur K) !
    Je vous avais expliqué cette preuve : *)

Lemma andb_prop : forall b1 b2,
  andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2 H.
  (* introduit les hypothèses *)
  split. (* sépare le but en deux sous-buts *)
  - destruct b1. (* raisonnement par cas *)
    + reflexivity. (* true = true *)
    + simpl in H. exact H. (* ce que l'on veut montrer est une hypothèse *)
  - destruct b2. (* raisonnement par cas *)
    + reflexivity. (* true = true *)
    + destruct b1.  (* raisonnement par cas *)
      * simpl in H. exact H. (* ce que l'on veut montrer est une hypothèse *)
      * simpl in H. exact H. (* ce que l'on veut montrer est une hypothèse *)
Qed.

(** Cette preuve montre l'utilisation de plusieurs tactiques que nous
    allons expliquer plus précisément au fur et à mesure des feuilles
    d'exercices.

    Notez déjà l'utilisation massive des bullets [+] afin d'identifier
    les points de branchement dans une preuve.
    Les autres bullets possibles sont [*], [-], [**], [+++], etc.
    Si une bullet est utilisée pour un sous-but, cette même bullet doit être
    utilisée pour tous les autres sous-buts du même niveau.
    Il est également possible d'utiliser les accolades pour délimiter un but. *)

(** Dans cette feuille d'exercices, nous nous intéressons uniquement à des 
    énoncés exprimables dans la logique propositionnelle.
    Vous n'avez donc besoin que des tactiques suivantes :
     - intro / intros : introduction de l'implication ->
     - apply H : pour utiliser un énoncé, une hypothèse
     - exact H / assumption : la règle nommée "axiome"
     - left et right : pour l'introduction de la disjonction \/
     - split : pour l'introduction de la conjonction /\
     - destruct H : pour l'élimination de la conjonction /\, la disjonction \/,
                    de [False]
     - unfold d in H : pour dérouler une définition [d] dans une hypothèse [H].
*)

(** Dans Coq, le type des propositions est [Prop].
    Nous déclarons trois objets arbitraires de ce type. *)

Variable P : Prop.
Variable Q : Prop.
Variable R : Prop.

(** La requête [Check] peut être utilisée pour vérifier que les expressions ont
    un sens, mais aussi de voir leur type.
    Les requêtes suivantes montrent les notations Coq pour la disjonction (\/),
    la conjonction (/\) et l'implication (->). *)

Check True.
Check P \/ Q.
Check False /\ P.
Check P -> Q -> R.

(** ** II. Commutativité de la conjonction.

    Ici, nous déclarons un objectif sans nom, et nous le prouvons.
    Une preuve est une succession de tactiques, chaque tactique réduisant le
    premier sous-but à une nouvelle liste (éventuellement vide) de sous-buts. *)

Goal P /\ Q -> Q /\ P.
Proof.
  intro H.
  destruct H.
  split.
   + exact H0.
   + exact H.
Qed.

(** ** III. Commutativité de la disjonction. *)

Goal P \/ Q -> Q \/ P.
Proof.
  intro H.
  destruct H.
   + right. exact H.
   + left.  exact H.
Qed.

(** ** IV. Distributivité *)

(** *** Exercice 1 - A vous de jouer ! *)

Goal P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intro H.
  destruct H.
  destruct H0.
  +left. split. exact H. exact H0.
  +right. split. exact H. exact H0.
Qed.

Goal (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).
Proof.
 intro H. destruct H.
  +split. destruct H. exact H. destruct H. left. exact H0.
  +split. destruct H. exact H. destruct H. right. exact H0.
Qed.

(** ** V. Une forme de commutativité pour l'implication.

    A noter ici :
      - l'associativité de l'implication
      - la variante [intros] de [intro]. *)

Goal (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros H HQ HP.
  apply H.
   + exact HP.
   + exact HQ.
Qed.

(** ** VI. Hypothèses multiples

    Prouvez l'équivalence suivante, en gardant à l'esprit que
    [P <-> Q] est une notation pour [(P -> Q) /\ (Q -> P)].
    Vous pouvez le vérifier en utilisant la tactique [unfold iff]. *)

(** *** Exercice 2 - A vous de jouer ! *)

Goal (P -> Q -> R) <-> (P /\ Q -> R).
Proof.
  split. 
  +intros H HQ. apply H. destruct HQ. exact H0. destruct HQ. exact H1.
  +intros H HP HQ. apply H. split. exact HP. exact HQ.
Qed.

(** Note : En Coq, on écrit généralement [P -> Q -> R] plutôt que [P /\ Q -> R],
    puisque la première forme est plus facile à travailler en utilisant les
    tactiques fournies. *)

(** ** VII. Négation

    La négation [~ P] est une notation pour [P -> False]. *)

Goal P -> ~ ~ P.
Proof.
  intros H Hn.
  unfold not in Hn.
  apply Hn.
  exact H.
Qed.

(** *** Exercice 3 - A vous de jouer ! *)

Goal (~P /\ ~Q) -> ~(P \/ Q).
Proof.
intros H Hn. destruct H. unfold not in H. unfold not in H0. destruct Hn. 
  +apply H. exact H1.
  +apply H0. exact H1.
Qed.

Lemma not_or : forall (P Q : Prop), ~(P \/ Q) -> (~P /\ ~Q).
Proof.
  intros P Q H. split.
    + unfold not in H. intro Hn. destruct H. left. exact Hn.
    + unfold not in H. intro Hn. destruct H. right. exact Hn.
Qed.

Goal (~P \/ ~Q) -> ~(P /\ Q).
Proof.
intros H Hn. destruct H.
  + unfold not in H. destruct Hn. apply H. exact H0.
  + unfold not in H. destruct Hn. apply H. exact H1.
Qed.

(** *** Exercice 4 - Avec le modus ponens *)

(** Note : Les quantifications [forall P : Prop] sont
           des quantifications d'ordre supérieur.
           Nous quittons donc la logique propositionnelle. *)

Lemma modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
intros P Q H0 H1. apply H1. exact H0.
Qed.


(** Démontrer à nouveau l'énoncé suivant, mais cette fois en utilisant
    [modus_ponens]. *)
Lemma impl_not : forall P : Prop, P -> ~ ~ P.
Proof.
intro P. unfold not. apply modus_ponens.
Qed.

(** Démontrer l'énoncé suivant à partir de [impl_not]. *)
Lemma P_notP_contradiction : forall P : Prop, ~ (P /\ ~ P).
Proof.
intro P. unfold not. intro Hn. destruct Hn. apply H0. exact H.
Qed.

Lemma not_and : forall P Q : Prop, P \/ Q -> ~(~ P /\ ~Q).
Proof.
intros P Q. intro H. unfold not. intro Hn. destruct Hn. destruct H.
  + apply H0. exact H.
  + apply H1. exact H.
Qed.

(** ** VIII.  Raisonnement classique

    Coq implémente une logique constructive.
    Cela veut dire que la logique interne de Coq n'a pas l'axiome du tiers exclu,
    ou un équivalent. Il n'est également pas possible de prouver le tiers exclu.
    Nous verrons les conséquences de ce choix plus tard. *)

(** *** Exercice 5 - Tiers exclu avec Coq *)

(** Pour le raisonnement classique, il faut donc déclarer un axiome.
    Note : [RAA] signifie pour Reductio Ad Absurdum.

    Ces objectifs de preuve sont un peu plus difficiles. *)

Axiom RAA : forall A:Prop, ~~A -> A.

Goal ~(P /\ Q) -> (~P \/ ~Q).
Proof.
intro H. apply RAA. intro Hn. apply not_or in Hn. destruct Hn. apply RAA in H0. apply RAA in H1. 
apply H. split. exact H0. exact H1.
Qed.

(** [LEM] pour Law of Excluded Middle. *)
Lemma LEM : P \/ ~P.
Proof.
apply RAA. intro H. apply not_or in H. apply H. destruct H. exact H.
Qed.


Goal (P -> Q) \/ (Q -> P).
Proof.
apply RAA. intro H. apply not_or in H. destruct H. 
apply H. intro P. apply RAA. intro nQ. 
apply H0. intro Q. apply RAA. intro nP. apply nP. exact P.
Qed.

(** Merci à David Baelde et Catherine Dubois. *)
