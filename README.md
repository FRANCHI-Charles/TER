# Travail encadré de recherche : localisation et morphisme

Ce projet a pour but d'expliquer et donner les fichiers qui ont permis la création du [morphimse d'anneau de la localisation](https://github.com/FRANCHI-Charles/TER/blob/main/src/Exercices/localisation.lean) dans Lean.

Il a été effecuté sous la tutelle de [Filippo A. E. Nuccio](https://github.com/faenuccio) en tant qu'Enseignant-Chercheur de [l'institut Camille Jordan](http://math.univ-lyon1.fr/).



## Présentation générale

Dans le cadre pédagogique d'une licence de mathématiques, j'ai choisit de me concentrer sur un assistant de preuve, Lean, afin de faire un premier pas dans le milieu de la recherche.
L'objectif était de formaliser deux résultats :


**Extension d'un Morphisme vers son localisé :**


$$ f:M \rightarrow N \text{ un morphisme de A-module, avec A un anneau unitaire commutatif, } S^{-1}M, S^{-1}N \text{ les localisés des modules M et N. Alors :}$$

$$ S^{-1}f: S^{-1}M \rightarrow S^{-1}N $$

$$ \frac{m}{s} \mapsto \frac{f(m)}{s} $$

$$ \text{est un morphisme des } S^{-1}A \text{-Modules } S^{-1}M\ S^{-1}N.$$
