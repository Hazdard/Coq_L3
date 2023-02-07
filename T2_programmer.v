(** * Tutoriel 1 - Programmer avec un OCaml pur *)

(** Ce premier tutoriel a pour objectif de vous faire découvrir
    le langage de programmation associé à Coq,
    c'est-à-dire le langage fonctionnel pur appelé Gallina.

    Plus précisément, dans ce fichier nous introduisons les définitions
    de types inductifs en Coq, ainsi que la programmation de fonctions 
    simples manipulant ces types. *)


(** Dans toute la feuille, nous utiliserons l'axiome suivant, analogue du
    [Obj.magic] d'OCaml, quand nous n'avons pas (encore) d'expression du bon
    type, par exemple dans les trous laissés en exercice.
    Votre mission est de supprimer toute utilisation de [TODO] dans la feuille.
*)

Axiom TODO : forall x:Type, x.


(** ** I. Définition inductive *)

(** Vous avez découvert la notion de définition inductive en cours de
    Logique, notion fondamentale en Coq.
    Vous pouvez faire le rapprochement entre cette notion et les 
    déclarations de typage de OCaml. *)

(** Q0. Comment écririez vous en OCaml le type suivant, qui déclare un type
        "route" comme étant soit une "departementale", soit une "nationale"
        ou soit une "autoroute" ? *)

Inductive route : Type :=
 | departementale : route
 | nationale : route
 | autoroute : route.

Check autoroute.

(** R0. Il s'agit du type :
           type route = Departementale | Nationale | Autoroute *)

(** Il est bien sûr possible d'écrire des fonctions en utilisant le type
    que nous venons de définir. De même qu'en OCaml, pour examiner un terme
    dont le type est inductif, on utilise le pattern-matching (filtrage).
    Voici un exemple de fonction non-récursive : *)

Definition agrandir (r : route) :=
  match r with
   | departementale => nationale
   | nationale => autoroute
   | autoroute => autoroute
  end.
(** Note : - En Gallina, un pattern-matching est FORCEMENT exhaustif et 
             non-redondant.
           - A la différence de OCaml, un filtrage se termine par "end" et
             nous notons "=>" au lieu de "->". *)

Check agrandir.

(** Voyons comment calculer avec notre fonction précédemment définie : *)
Eval compute in (agrandir (agrandir nationale)).

(** Voici une autre définition inductive, où l'un des constructeurs prend
    des arguments, ainsi qu'un autre exemple de fonction non-récursive. *)
Inductive terrain : Type :=
 | t_terre : terrain
 | t_route : route -> terrain
 | t_batiment : terrain.

Check (t_route nationale).

Definition agrandir_terrain (t : terrain) := match t with
| t_terre => t_batiment
| t_route r => t_route (agrandir r)
| t_batiment => t_batiment
end.
Check agrandir_terrain. (* : terrain -> terrain *)

(** De plus, voici quelques exemples classiques de type qui existent 
    déjà dans la bibliothèque standard de Coq.
    Nous ouvrons ici un module pour ne pas cacher leur définition. *)

Module definition_inductive.

 (** Cette déclaration est analogue à la déclaration OCaml
     [type bool = Vrai | Faux]. *)
  Inductive bool : Type :=
  | Vrai : bool
  | Faux : bool.

  (** Cette déclaration est analogue à la déclaration OCaml
      [type nat = Zero | Succ of nat]. *)
  Inductive nat : Type :=
  | Zero : nat
  | Succ : nat -> nat.

  (** Cette déclaration est analogue à la déclaration OCaml
      [type list_nat = Nil | Cons of nat * list_nat]. *)
  Inductive list_nat : Type :=
  | Nil  : list_nat
  | Cons : nat -> list_nat -> list_nat.

End definition_inductive.

(** Voici les types précédents tels qu'ils sont définis dans la bibliothèque
    standard de Coq : *)
Print bool.
Print nat.
(** Nous verrons plus loin comment est défini le type des listes en Coq. *)

(** *** Exercice 1 - Ecrire une définition inductive *)

  Inductive bin_tree_bool : Type :=
  | Feuille : bool -> bin_tree_bool
  | Noeud : bin_tree_bool -> bin_tree_bool -> bin_tree_bool.

(** Définir le type d'un arbre binaire sur les booléens, noté [bin_tree_bool]. *)

(** *** Exercice 2 - Prédicat de parité *)

(** Pour finir cette partie, prenons un exemple de définition inductive :
    l'ensemble des nombres pairs.
    Pour rappel : P = 2N est défini par 0 ∈ P et si n ∈ P alors n + 2 ∈ P
    ou encore par les règles :

                             ---
                              0

                              n
                            -----
                            n + 2

    Voici une manière de le modéliser en Coq, à l'aide d'un prédicat inductif.
    Vous noterez les similitudes avec la définition mathématique précédente. *)

(** On définit inductivement un prédicat sur [nat],
    c'est à dire un ensemble d'entiers. *)
Inductive even : nat -> Type :=
  | EZ : even 0
  | ES : forall n, even n -> even (S (S n))
    (** Le constructeur [ES] prend un entier [n] et une dérivation
        attestant que l'entier est pair (une expression de type [even n])
        et construit une dérivation indiquand que [2+n] est lui aussi pair.
        Le type du résultat dépend de la valeur [n]; ceci est noté via le
        mot clé [forall]. En Coq, le type flèche est un cas particulier
        particulier de cette construction : [A -> B] est [forall _:A, B]. *).

(** On vérifie ici que des termes sont bien typés.
    Prenez le temps de comprendre leurs types. *)

Check EZ.
Check (ES 0 EZ).
Check (ES _ EZ). (** L'expression laissée vide [_] est inférée par Coq. *)

(** Les type [forall] sont une généralisation des types flèches usuels,
    ils sont habités par des fonctions, notées avec [fun] comme pour les
    types flèches usuels. Attention à bien comprendre les deux applications
    faites sur [ES]. *)
Check (fun n e => ES n e).

(** On utilise ici [Definition] plutôt que [Fixpoint] car il n'y a pas
    besoin de récursion. *)
Definition even_4 : even (S (S (S (S 0)))) := ES 2 (ES 0 EZ).

(** On voit ci-dessous que Coq identifie [2+2] et [4]. *)
Definition deux := S (S 0).
Definition even_2_plus_2 : even (plus deux deux) := even_4.

(** Implémentez une fonction qui prouve que les entiers pairs sont
    stables par quadruple successeur. *)
Definition even_succ : forall n, even n -> even (S (S (S (S n)))) :=
 fun n e => ( ES (S(S n )) (ES n e) ).



(** *** Exercice facultatif 1 - Une autre définition inductive *)

(** Soit le langage E = {a, b}∗ et la définition inductive suivante :
                        ---
                         b

                         X
                       ------
                       a X a
*)

(** Modélisez-la en Coq. *)

Inductive E : Type :=
  | epsilon : E
  | a : E
  | b : E
  |concat : E->E->E.

Inductive Lang : E -> Type :=
  | Lb : Lang b
  | Laa : forall x, Lang x -> Lang (concat a (concat x a)).

(** Montrer que aabaa  est dans le language*)

Check Lb.
Check (Laa b Lb).
Check (Laa (concat a (concat b a)) (Laa b Lb))  .

(** ** II. Fonction récursive *)

(** Reprenons les entiers naturels de la bibliothèque standard : *)
Print nat.

(** On définit récursivement la fonction d'addition, de façon analogue à
    la définition OCaml [let rec plus m n = ...]. *)
Fixpoint plus (m:nat) (n:nat) : nat :=
  match m with
  | 0 => n
  | S p => S (plus p n)
  end.
(** Note : Une fonction doit TOUJOURS terminer !
           Cas détecté automatiquement par Coq : récurrence structurelle *)

(** On peut demander à Coq de réaliser quelques calculs pour vérifier.
    En Coq, une expression est identifiée avec le résultat de son évaluation. *)

Eval compute in 0.
Eval compute in (S 0).
Eval compute in (plus (S 0) 0).
Eval compute in (plus 0 (S 0)).

(** *** Exercice 3 - Définir la fonction [_*2]. *)
Fixpoint double (m:nat) : nat :=
  match m with
    | 0 => 0
    | S p => S (S (double p))
  end.

Eval compute in double (S 0).
Eval compute in double (S (S (S (S 0)))).

(** *** Exercice 4 - Retour sur l'exercice 1 *)

(** Définir l'opération booléenne "et" sur le type défini à l'exercice 1. *)

(** *** Exercice 5 - Retour sur l'exercice 2 *)

(** Implémentez la fonction suivante qui construit pour tout entier [n]
    une dérivation attestant que le double de [n] est pair. *)
Fixpoint even_double (n:nat) : even (double n) :=
  match n with
    |0 => EZ
    |S p => (ES (double p) (even_double p))
  end.



(** ** III. Polymorphisme *)

(** Le polymorphique est aussi une fonctionnalité de OCaml
    présente en Gallina. *)

(** *** Type polymorphique *)

(** Les types peuvent être paramétrés par d’autres types.
    Exemple le plus classique : les listes. *)
Print list.

Check list. (* list : Type → Type *)
Check nil.  (* nil : forall A : Type, list A *)
Check cons. (* cons : forall A : Type, A → list A → list A *)

(** *** Fonctions polymorphiques *)

(** Les fonctions peuvent aussi être paramétrées par des types.
    Un exemple un peu artificiel : *)
Definition id (A:Type) (x:A) := x.

Check id. (* id : forall A : Type, A → A *)

(** Un exemple sur les listes. *)
Fixpoint length (A:Type) (l : list A) := match l with
 | nil => 0
 | cons _ t => S (length A t)
end.

(** Un exemple sur les booléens. *)
Definition apply_neg_poly (A:Type) (f : _ -> _ -> A) b1 b2 :=
 f (negb b1) (negb b2).

Check apply_neg_poly.
(* apply_neg : forall A : Type, (bool -> bool -> A) -> bool -> bool -> A *)


(** *** Exercice 6 - Définition polymorphe *)

(** Définir la fonction de concaténation sur les listes polymorphes. *)


(** ** IV. Autres fonctionnalités  *)

(** Gallina, tout comme OCaml considère les fonctions comme des
    valeurs de première classe : *)

Definition apply_neg (f : _ -> _ -> bool) b1 b2 := f (negb b1) (negb b2).

Check apply_neg. (* apply_neg : (bool -> bool -> bool) -> bool -> bool -> bool *)

(** Il est également possible d'écrire des applications partielles... *)

Definition nor := apply_neg andb.
Check nor. (* nor : bool -> bool -> bool *)

(** ... ainsi que des fonctions anonymes *)

Definition idb (b:bool) := b.
Definition idb_bis : bool -> bool := fun b => b.
Definition my_first := apply_neg (fun b1 => fun b2 => b1).

(** A la différence de OCaml, nous pouvons améliorer la lisibilité 
    des termes manipulés : *)

(** Avec des paramètres implicites : 
      Si un argument peut toujours être inféré à partir d’un autre, 
      nous pouvons le rendre implicite : *)
Definition apply_neg_arg {A:Type} (f : _ -> _ -> A) b1 b2 :=
  f (negb b1) (negb b2).

Definition nor_bis := apply_neg andb.
  (* au lieu de apply_neg bool andb
     ou apply_neg _ andb *)

(** Avec des notations : 
       Notation "0" := O.
       Notation "1" := (S O).
    ou encore :
       Notation "x = y" := ...
       Notation "[ ]" := nil.
*)


(** ** V. Exercices *)

(** *** Exercice 7 - Entiers naturels en binaire

    On peut représenter les entiers positifs en binaire,
    en partant de zéro et avec les opérations [_*2] et [_*2+1]. *)

Inductive bin : Type :=
  | BZ : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.


(** L'intention derrière cette représentation
    est que [BZ] représente le zéro,
    [B0] est l'opération [_*2] et [B1] est [_*2+1].

    Implémentez la fonction de conversion vers [nat]
    correspondant à cette intention. *)
Fixpoint convert (b:bin) : nat := TODO _.

(** Définition du successeur sur [bin]. *)
Fixpoint bsucc (b:bin) : bin := TODO _.


(** *** Exercice 8 - Relation d'égalité entre [bin] et [nat] *)

(** On définit inductivement une relation entre des entiers
    [bin] et [nat]. *)
Inductive equal : bin -> nat -> Type :=
  | EQZ : equal BZ 0
  | EQ0 : forall b n, equal b n -> equal (B0 b) (double n)
  | EQ1 : forall b n, equal b n -> equal (B1 b) (S (double n)).

(** Quelques exemples. *)

Definition eq_0 : equal BZ 0 :=
  EQZ.

Definition eq_1 : equal (B1 BZ) (S 0) := TODO _.

(** TODO : définir eq_2, eq_3. *)

(** Preuve d'égalité entre un entier binaire et sa conversion. *)
Fixpoint equal_convert (b:bin) : equal b (convert b) := TODO _.

(** Implémentez les fonctions suivantes :
    deux préliminaires et un gros morceau... *)

Definition conv_succ_bz : equal (bsucc BZ) (S (convert BZ)) := TODO _.

Definition conv_succ_b0 :
  forall c, equal (bsucc (B0 c)) (S (convert (B0 c))) := TODO _.

Fixpoint conv_succ (b:bin) : equal (bsucc b) (S (convert b)) := match b with
  | BZ => TODO _
  | B0 c => TODO _
  | B1 c => TODO _
end.


(** ** VI. Pour conclure *)

(** Vous savez à présent programmer avec Coq, notamment
   car vous avez découvert les différences principales avec OCaml :
      - type algébrique / définition inductive
      - fonction récursive, qui doit toujours terminer !
      - pattern-matching, qui doit toujours être exhautif et non-redondant !
      - fonction partielle, anonyme, etc.
      - polymorphisme
      - pas d'exception

 Vous avez également pu constater plusieurs fonctionnalités de Coq,
    non existantes en OCaml :
      - arguments implicites
      - déclaration de notations
*)



(** Une fois ce fichier d'exercices terminé, réfléchissez à comment représenter
    en Coq, les définitions inductives suivantes :

                 A ∧ B
                -------
                   A

                 A ∧ B
                -------
                   B

             A => B      A
            ---------------
                   B

            --------------
             (P => Q) ∧ P

*)

(** Merci à David Baelde et Catherine Dubois. *)