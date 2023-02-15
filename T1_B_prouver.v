(** * Tutoriel 1 - Prouver avec Coq : Logique du premier ordre *)

(** Dans cette feuille, nous simulons la logique du premier ordre 
    dans le cadre plus riche de la logique de Coq.
    À cet effet, nous déclarons un type [T] pour les termes, un prédicat 
    unaire [P], une proposition [Q], et une relation [R]. *)

Variable T : Type.
Variable P : T -> Prop.
Variable Q : Prop.
Variable R : T -> T -> Prop.

(** ** I. Quantifications universelle et existentielle *)

(** Les tactiques [intro] et [apply] sont utilisées également pour raisonner
    sur les quantifications universelles, tandis que les tactiques [exists]
    et [destruct] sont utilisées pour les quantifications existentielles. *)

Goal (exists x:T, forall y:T, R x y)
  -> (forall y:T, exists x:T, R x y).
Proof.
  intros H y.
  destruct H.
  exists x.
  apply H.
Qed.

Goal (exists x:T, P x \/ Q) -> ((exists x:T, P x) \/ Q).
Proof.
  intro H. destruct H. destruct H.
   + left.  exists x. exact H.
   + right. exact H.
Qed.

(** *** Exercice 1 - A vous de jouer ! *)

Lemma exists_not_forall : forall P : nat -> Prop,
(exists n, P n) ->  ~(forall n,~ (P n)).
Proof.
intros P H. unfold not. intro Hn. destruct H. apply Hn with (n:=x). exact H.
Qed.

(** Note : Ici aussi, l'ordre supérieur a été utilisé. *)

(** *** Exercice 2 - A vous de jouer ! *)

(** Pour le résultat suivant, nous devons être capable d'introduire une
    existentielle avec un terme arbitraire. Ceci n'est pas autorisé dans Coq,
    où les types peuvent être vides. Nous postulons donc l'existence de
    au moins un élément dans [T]. *)

Variable a : T.

Goal ((exists x:T, P x) \/ Q) -> (exists x:T, P x \/ Q).
Proof.
intros H. destruct H. destruct H. exists x. left. exact H. exists a. right. exact H.
Qed.

(** ** II. Egalité *)

(** L'égalité étant réflexive, la tactique [reflexivity] permet de clore
    un but lorsque les 2 éléments à gauche et à droite d'une égalité sont
    égaux syntaxiquement.

    De plus, la tactique [rewrite] permet d'utiliser une égalité, 
    c'est-à-dire de réécrire x en y grâce à x = y.
    Pour réécrire y en x grâce à x = y, il faut utiliser la tactique 
    [rewrite <-]. *)

Variable f : T -> T.

Goal forall x y : T, x = y -> f x = f y.
Proof.
  intros x y Heq.
  rewrite Heq.
  reflexivity.
Qed.

Goal forall x y : T, x = y -> P y -> P x.
Proof.
  intros x y Heq H.
  rewrite Heq.
  exact H.
Qed.

Goal forall x y : T, forall z:T,
  x = y -> f y = z -> P (f x) -> P z.
Proof.
  intros x y z Hxy Hfyz H.
  rewrite <- Hxy in Hfyz.
  rewrite Hfyz in H.
  exact H.
Qed.

(** *** Exercice 3 - Symétrie et transitivité de l'égalité *)

(** La symétrie et la transitivité sont des conséquences du principe 
    de substitution incarné par la tactique de [rewrite] : prouvez-le ! *)

Lemma symmetry : forall x y : T, x = y -> y = x.
Proof.
Admitted.

Lemma transitivity : forall x y z : T, x = y -> y = z -> x = z.
Proof.
Admitted.

(** A présent, vous avez le droit d'utiliser la tactique [symmetry]
    pour échanger les 2 membres d'une égalité. *)

(** *** Exercice 4 - Fonctions *)

(** Ici, nous définissons une nouvelle sorte de termes, et diverses
    propriétés de fonctions sur ces termes.
    Démontrez le théorème en guise d'exercice. *)

Module Functions.

  Variable A : Type.

  Definition injective (f:A->A) :=
    forall x:A, forall y:A, f x = f y -> x = y.

  Definition surjective (f:A->A) :=
    forall x:A, exists y:A, x = f y.

  Definition bijective (f:A->A) := injective f /\ surjective f.

  Definition involutive (f:A->A) := forall x:A, f (f x) = x.

  Theorem inv_bij : forall (f:A->A), involutive f -> bijective f.
  Proof.
  Admitted.

End Functions.

(** ** III. Exercice avancé *)

(** *** Exercice 5 - Le paradoxe du buveur (Drinker's paradox) *)

(** Comme exercice avancé (probablement pour la prochaine fois), prouvez que
    la formule du buveur tient, en utilisant un raisonnement classique et en
    en supposant que l'univers des termes n'est pas vide. *)

Module Drinker.

  (** Supposons un bar non vide, et un prédicat indiquant
      quelles personnes dans le bar boivent. *)

  Variable Person : Type.
  Variable p : Person.
  Variable Drinks : Person -> Prop.

  (** Vous pouvez utiliser n'importe lequel des deux axiomes équivalents. *)

  Axiom RAA : forall P:Prop, ~~P -> P.
  Axiom LEM : forall P:Prop, P \/ ~P.

  (** Vous allez probablement vouloir utiliser [LEM] en premier,
      mais sachez que l'utilisation de seulement [RAA] amène à plus
      de difficulté. *)

  Goal exists x:Person, Drinks x -> forall y:Person, Drinks y.
  Proof.
  Admitted.

End Drinker.

(** Merci à David Baelde et Catherine Dubois. *)