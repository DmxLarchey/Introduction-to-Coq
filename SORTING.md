# Certification des algorithmes de tri en Coq

## But du projet

Le but du projet consiste à certifier trois algorithmes de tri
classiques, par extraction de code OCaml depuis des preuves en Coq.
* le tri par [_insertion_](https://fr.wikipedia.org/wiki/Tri_par_insertion) (le plus simple);
* le tri rapide, ou [_quick sort_](https://fr.wikipedia.org/wiki/Tri_rapide);
* le tri fusion, ou [_merge sort_](https://fr.wikipedia.org/wiki/Tri_fusion).

Les trois algorithmes sont représentés dans le type `sorting_function : (list X -> list X) -> Prop`
où `sorting_function s` est satisfaite quand pour toute liste `l : list X`, la liste
`s l` est triée et aussi permutable avec `l`.

## Le code source Coq à compléter pour le projet

Le code source Coq se trouve dans le fichier [`sorting_algorithms.v`](sorting_algorithms.v) 
et contient du code pré-rempli pour modéliser partiellement le problème. Votre
objectif est de combler les _trous_, c'est-à-dire, de pouvoir remplacer
les `admit` par de vraies preuves (combinaisons de tactiques). Une fois
ce travail accompli, vous pourrez conclure les preuves par `Qed` en
lieu et place de `Admitted`. 

Une partie des preuves sont déjà complètes. Je vous conseille toutefois 
de les étudier pour comprendre comment elles fonctionnent.

* Vous n'avez pas besoin d'inventez des inductions compliquées,
  elles sont déjà fournies dans le code;
* Vous n'avez pas besoin d'inventer de nouvelles notions, la
  modélisation est déjà faite aussi;
* Mais vous avez besoin de comprendre comment sont formalisées
  les notions de permutation et de listes triées, et le sens
  des résultats qui leur sont associés;
* Des _astuces/indications_ sous également fournies afin de
  vous orientez et vous évitez d'explorer trop de fausses
  pistes;
* Certains trous sont faciles, d'autres un peu plus compliqués,
  surtout vers la fin. Vous n'êtes pas obligés de procéder dans
  l'ordre du code pour boucher les trous;

## Objectifs et dates

Le projet commence le 28 mars 2023 et dure 5 semaines. C'est
un projet individuel. Chaque étudiant devra me rendre un fichier
de code complété, à m'envoyer par _e-mail_ à l'adresse
[Dominique Larchey-Wendling](mailto:larchey@loria.fr), et
ce avant le **9 mai, 2023**. Une soutenance sera programmée
à une date ultérieure, où vous aurez à présenter et commenter
votre travail.

N'hésitez pas à me contacter pour toute question ou difficulté
concernant le projet ou le cours.
