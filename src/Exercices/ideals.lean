import ring_theory.ideal.basic

variables {R S : Type} [comm_ring R] [comm_ring S] (I : ideal R)


/- ### Intro
Voici une liste d'examples à faire une fois que vous aurez terminé le premier chapitre
de Atiyah-Macdonald -/


example (a b : R) : a ∈ I → b ∈ I → (a + b) ∈ I := sorry

example (a x : R) : a ∈ I → (a * x) ∈ I ∧ (x * a) ∈ I := sorry


/- Est-ce que vous pouvez expliquer pourquoi l'énoncé "la préimage d'un idéal par un morphisme
d'anneaux" est une `définition` et pas un `lemme`? -/
definition preimage (f : R →+* S) (J : ideal S) : (ideal R) :=
{ carrier := {x : R | f x ∈ J},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

example (f : R →+* S) (J : ideal S) (hJ: J.is_prime) : (preimage f J).is_prime := sorry

/- Est-ce que vous pouvez expliquer pourquoi l'énoncé "l'intersection de deux idéaux est un idéal" est
une `définition` et pas un `lemme`? -/
definition intersection (J : ideal R) : ideal R :=
{ carrier := I ∩ J,
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

-- Pourquoi l'exemple suivant ne compile pas, même avec la définition précédente?
example (J : ideal R) (x y : R) : x ∈ I → x ∈ J → x ∈ I ∩ J :=