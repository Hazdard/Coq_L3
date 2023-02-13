(** * Tutoriel 3 - Isomorphisme de Curry-Howard et ses conséquences *)

(** La correspondance de Curry-Howard identifie :
      - une formule A avec un type de données, et 
      - une preuve (dérivation formelle) avec un objet 
        (du lambda calcul) de type A. 

    Autrement dit, les types sont vus comme des propositions,
    et les programmes comme des preuves *)

(** Une preuve d'une implication par exemple est une fonction, 
    une preuve d'une conjonction est un couple, 
    appliquer la règle du modus-ponens se matérialise par 
    l'application d'une fonction à un argument. *)

(** Cet objet du lambda calcul est appelé terme de preuve. 
    Il représente un arbre de preuve.
    Lorsque l'on écrit un script de preuve (une suite de tactiques) 
    on construit peu à peu le terme de preuve. 
    Le Qed final vérifie que ce terme représente bien une preuve de 
    la formule de départ. Comment ? En vérifiant que son type est
    bien celui de la formule.
    Vous verrez cela de manière plus théorique plus tard. *)

(** L'objet de ce TP est de découvrir ce mécanisme.

    Si [toto] est un théorème ou n'importe quel objet de Coq, 
    la commande [Check toto] permet d'obtenir le type de toto.

    Pour afficher sa valeur on utilisera la commande [Print toto].

    Attention : La définition d’une constante à l’aide du système 
                de tactiques (invoqué par Theorem , etc.) est opaque 
                par défaut; il n’est donc pas possible de consulter sa
                valeur. Pour que la définition soit transparente, il
                suffit de remplacer [Qed] par [Defined] à la fin de 
                la preuve. *)

(** ** Exercice 1 - Première observation *)

(** Prouvez la proposition [forall A : Prop, A -> A] et 
    affichez sa preuve. *)

(** En Coq, la fonction qui a x de type T associe e 
   (en OCaml function x → e) se note fun (x : T) => e.
   Son type est un produit dépendant, noté en Coq,
   [forall (x : T), U(x)] où U(x)est le type de e. 

   Dans le cas où U(x) = U ne dépend pas de la variable x : T , 
   le produit (non) dépendant s’abrège en T -> U et on retrouve le 
   type d'une fonction à la Ocaml. *)

(** ** Exercice 2 - Premiers termes de preuve *)

Variables A B C : Prop. (* On introduit ainsi 3 propositions 
                           logiques. *)

(** A RETENIR : Une preuve de [A → B] est une fonction qui a toute
                preuve de A associe une preuve de B. *)

(** Prouver les propriétés suivantes et grâce à la commande
    [Print] regarder les termes de preuve.

      1. A -> A
      2. (A -> B) -> (B -> C) -> A -> C
      3. A -> B -> A
      4. (A -> B -> C) -> (A -> B) -> A -> C
      5. Essayer de construire directement le terme de preuve 
        (sans utiliser de tactique) de la formule [A -> B -> B]. 
        Pour vérifier que c'est bien la preuve, utiliser la tactique
        [exact] suivie de ce terme dans la preuve.

           Theorem ex2.5 : A -> B -> B.
           exact (le terme).
           Defined.
*)


(** ** Exercice 3 - Retour sur la négation *)

(** On rappelle que [~A] est une abréviation pour [A -> False]. *)

(** Prouver les formules suivantes (en utilisant des tactiques).
    A l'aide de Print, regardez les termes de preuve.
       1. A -> ~~A
       2. (A -> B) -> (~B -> ~A) *)

(** Indication :
      Pour éliminer la proposition [False], on pourra utiliser 
      la constante prédéfinie (ex falso quod libet) :
        false_ind : forall P : Prop, False -> P *)


(** ** Exercice 4 - Retour sur la conjonction *) 

(** À l’aide des constantes prédéfinies
    and : Prop -> Prop -> Prop (* Sucre : A /\ B := and A B *)
    conj : forall A B : Prop, A -> B -> A /\ B.
    proj1 : forall A B : Prop, A /\ B -> A.
    proj2 : forall A B : Prop, A /\ B -> B.
    donnez des termes de preuve des propositions suivantes :
      1. A /\ B -> B /\ A
      2. (A /\ B) /\ C -> A /\ (B /\ C)
      3. (A -> B) /\ (A -> C) -> (A -> B /\ C)
      4. (A -> B /\ C) → (A -> B) /\ (A -> C)

    Vous commencerez par faire les preuves à l'aide des tactiques. *)

(** ** Exercice 5 - Retour sur la disjonction *)

(** À l’aide des constantes prédéfinies
    or : Prop -> Prop -> Prop (* Sucre : A \/ B := or A B *)
    or_introl : forall A B : Prop, A -> A \/ B
    or_intror : forall A B : Prop, B -> A \/ B
    or_ind : forall A B P : Prop, (A -> P) -> (B -> P) -> A \/ B -> P,
    donnez des termes de preuve des propositions suivantes :
      1. A \/ B -> B \/ A
      2. (A \/ B) \/ C -> A \/ (B \/ C)
      3. (A \/ B -> C) <-> (A -> C) /\ (B -> C)
      4. ~~ (A \/ ~A)

    Vous commencerez par faire les preuves à l'aide des tactiques. *)


(** Merci à Catherine Dubois. *)
