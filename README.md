# Travail encadré de recherche : localisation et morphisme

Dans le cadre pédagogique d'une licence de mathématiques au sein de l'[Université Jean-Monnet](https://www.univ-st-etienne.fr/fr/index.html) de Saint-Etienne, j'ai choisi de me concentrer sur un assistant de preuve, Lean, afin de faire un premier pas dans le milieu de la recherche.
Ce repository contient les fichiers qui ont permis la formalisation de deux théorèmes sur les morphimses de modules localisés dans Lean.
Ce projet a été effecuté sous la tutelle de [Filippo A. E. Nuccio](https://github.com/faenuccio) en tant qu'Enseignant-Chercheur de [l'institut Camille Jordan](http://math.univ-lyon1.fr/). Je le remercie chaleuresement : sans lui, rien de tout ça n'aurait été possible.

Pour plus de détails, je vous invite à consulter le [Mémoire de recherche](https://github.com/FRANCHI-Charles/TER/blob/f55e32aa91734687e79cef8c63889ea892f8b0f0/Memoire.pdf).

Le code des fonctions est également disponible dans le fichier [src/Resultats.lean](https://github.com/FRANCHI-Charles/TER/blob/f55e32aa91734687e79cef8c63889ea892f8b0f0/src/Resultats.lean).

## Résultats démontrés


L'objectif était de formaliser deux résultats, dont les détails des démonstrations sont accessibles dans la partie 3.3 du [Mémoire](https://github.com/FRANCHI-Charles/TER/blob/f55e32aa91734687e79cef8c63889ea892f8b0f0/Memoire.pdf) :


**Extension d'un Morphisme de modules vers son localisé :**

Si $f: M \rightarrow N$ est un morphisme de $R$-modules, avec $R$ un anneau unitaire commutatif, et $S^{-1}M, S^{-1}N$ sont les localisés des modules $M$ et $N$, alors on peut construire :

$$ S^{-1}f: S^{-1}M \rightarrow S^{-1}N $$

$$ \frac{m}{s} \mapsto \frac{f(m)}{s} $$

qui est un morphisme de $S^{-1}R$-Modules.

```lean
def extended (f : M →+[R] N) : (localized_module S M) →+[localization S] (localized_module S N) :=
```

**Composition de ces extensions :**

Si $f: N \rightarrow P$ et $g: M \rightarrow N$ sont des morphismes de $R$-modules, avec $R$ un anneau unitaire commutatif, alors :

$$S^{-1}(f \circ g) = S^{-1}f \circ S^{-1}g$$

```lean
lemma extended_comp (f : N →+[R] P) (g : M →+[R] N) : extended S (f.comp g) = (extended S f).comp (extended S g) :=
```

## Exercices pratiqués

Vous pouvez consulter les exercices effectués afin de s'approprier Lean et Mathlib dans le dossier [Exercices](https://github.com/FRANCHI-Charles/TER/tree/f55e32aa91734687e79cef8c63889ea892f8b0f0/src/Exercices).
