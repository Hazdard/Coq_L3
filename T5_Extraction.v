(** * Tutoriel 4 - Extraction de programmes à partir de preuves *)

(** Dans ce tutoriel, nous allons extraire des programmes à partir de preuves
    simples sur les nombres naturels. *)

Require Extraction. (* Commentez cette ligne pour les anciennes 
                       versions de Coq. *)

(** ** Exercice 1 - Relation d'Ackermann *)

(** Nous définissons une relation [ack : nat -> nat -> nat -> Prop] qui est
    la spécification de la fonction d'Ackermann : [ack m n r] signifie que
    le résultat de la fonction sur [m] et [n] doit être [r]. *)

Inductive ack : nat -> nat -> nat -> Prop :=
  | ack_0_n : forall n, ack O n (S n)
  | ack_m_0 : forall m r, ack m (S O) r -> ack (S m) O r
  | ack_m_n : forall m n r r',
      ack (S m) n r -> ack m r r' -> ack (S m) (S n) r'.

(** Prouvons que la relation est totale.
    Faites attention à bien commencer votre preuve, ce n'est pas simple ! *)

Lemma ack_total : forall m n, exists r, ack m n r.
Proof.
  (** Dans cette preuve, vous pouvez trouver utile de choisir des noms lors de
      la destruction d'une existentielle, en utilisant [destruct ... as (x,H)].

      Vous pouvez aussi utiliser [assumption] au lieu d'utiliser explicitement
      [exact H] lorsque la conclusion du but est l'une de ses hypothèses. *)
  induction m.
  + intro n. exists (S n). apply (ack_0_n n).
  + induction n.
    ++ eexists. apply ack_m_0. apply IHm with (n:=1).
(** Demandez à Coq d'extraire un programme de la preuve [ack_total].
    Le résultat est décevant : c'est parce que le contenu calculatoire des 
    objets de [Prop] est effacé. *)

Extraction ack_total.

(** L'expression [exists x:A, P x] est une notation pour [ex A P].
    Le type [ex] est défini de manière inductive : ses habitants 
    (c'est-à-dire les preuves des énoncés existentiels) ne peuvent 
    être dérivés qu'à l'aide de [ex_intro], c'est-à-dire en 
    fournissant un témoin [x] et une preuve de [P x]. *)

Print ex.

(** Coq vient avec une variante de [ex] appelée [sig] qui définit
    la quantification existentielle sur [Type] plutôt que sur [Prop].
    L'expression [{x : A | P x}] est une notation pour [sig A P]. *)

Check { r : nat | ack 2 3 r }.
Print sig.

(** Prouvons la totalité en utilisant [sig]. *)

Lemma ack_total_sig : forall m n, { r | ack m n r }.
Proof.
  (** Les éléments suivants ne seront pas autorisés :

      intros. destruct (ack_total m n).

      En effet, nous ne pouvons pas utiliser [ack_total], qui n'a pas de
      sens du point de vue du calcul, pour définir [ack_total_sig].

      Cependant, copier le script de preuve de [ack_total] devrait fonctionner.
      En particulier, [destruct] fonctionne de manière similaire sur [ex] et 
      sur [sig].

      À la fin, utilisez [Defined] plutôt que [Qed] pour éviter les 
      avertissements : ceci informe Coq que nous nous intéressons au contenu 
      de la preuve, et pas seulement au fait que l'énoncé est prouvable. *)
Admitted.

(** Nous pouvons maintenant extraire quelque chose d'intéressant de la preuve
    de la totalité. *)

Extraction ack_total_sig.


(** ** Exercice 2 - Fonction d'Ackermann *)

(** Nous allons extraire la fonction d'Ackermann à partir d'une preuve de la
    totalité de la relation d'Ackermann. Il est également possible (et souvent
    pratique) de définir la fonction explicitement dans Coq.

    La fonction sera essentiellement définie par induction sur les nombres 
    naturels. Concrètement, nous formerons une définition [Fixpoint] : elle 
    permet de définir une fonction récursive tant qu'un argument décroît
    strictement dans ces appels, de sorte que la terminaison est assurée.
    Ici, "décroissant" signifie que le nouvel argument doit être un 
    sous-terme strict de l'argument (fini) initial.

    Par exemple, dans la (re)définition suivante de la fonction d'addition,
    l'argument décroissant est le premier : le seul appel récursif est un
    un sous-terme strict [m'] de [m]. *)

Fixpoint addition (m:nat) (n:nat) : nat :=
   match m with
    | O => n
    | S m' => S (addition m' n)
  end.

(** Définissons d'abord [fack'] de telle sorte que, si [fack_m] est la fonction
    d'Ackermann avec un premier argument fixé à [m], alors [fack' fack_m n] est
    le résultat de la fonction d'Ackermann pour [S m] et [n]. *)

Fixpoint fack' (fack_m : nat -> nat) (n:nat) : nat := match n with
  | O => 12 (* TODO *)
  | S n' => 3456 (* TODO *)
end.

(** Définissez maintenant [fack] comme étant la fonction d'Ackermann. *)

Fixpoint fack (m:nat) (n:nat) : nat.

(** Prouvez que [fack] implémente la spécification d'Ackermann. *)

Lemma fack_correct : forall m n, ack m n (fack m n).
Proof.
Admitted.

(** On obtient ainsi une nouvelle preuve de la totalité. *)

Lemma ack_total_fun : forall m n, { r | ack m n r }.
Proof.
  intros m n. exists (fack m n). apply fack_correct.
Defined.

Recursive Extraction ack_total_fun.

(** Calculons quelques valeurs de la fonction. *)

Lemma ack_3_3 : { x : nat | ack 3 3 x }.
Proof.
  apply ack_total_fun.
Defined.

(** L'extraction nous donne un programme que nous pourrions exécuter
    en OCaml. *)

Recursive Extraction ack_3_3.

(** Mais puisque nous avons une fonction Coq, nous pouvons aussi 
    l'évaluer directement. *)

Eval compute in fack 3 3.

(** Nous pouvons également dérouler ce résultat à partir du type [sig] de
    l'une de nos preuves d'existence. *)

Eval compute in ack_total_fun 3 3.
Eval compute in let (x,_) := ack_total_fun 3 3 in x.
Eval compute in let (x,_) := ack_total_sig 3 3 in x.

(** ** Exercice 3 - Induction sur une relation *)

(** Jusqu'à présent, nous n'avons pas utilisé le fait que [ack] est donné comme
    une définition [Inductive]. Nous l'utiliserons ensuite pour prouver
    l'unicité : parce que [ack] est inductive, vous avez un schéma 
    d'induction pour elle, que vous pouvez utiliser à travers la tactique
    d'induction : si [H : ack m n r], essayez d'utiliser [induction H]. *)

Check ack_ind.

Lemma ack_unicity : forall m n r1,
  ack m n r1 -> forall r2, ack m n r2 -> r1 = r2.
Proof.
  (** N'utilisez PAS les inductions sur [m] et [n] : faites une induction sur 
      [ack m n r] directement.
      Attention : le [forall r2] n'arrive pas tout de suite dans la formule 
      pour une bonne raison. *)
Admitted.

(** Merci à David Baelde. *)