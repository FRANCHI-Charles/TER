import ring_theory.ideal.basic

variables {R S : Type} [comm_ring R] [comm_ring S] (I : ideal R)


/- ### Intro
Voici une liste d'examples à faire une fois que vous aurez terminé le premier chapitre
de Atiyah-Macdonald -/


example (a b : R) : a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  intros ha hb,
exact I.add_mem ha hb, /- différence entre I.add_mem et add_mem ? -/
end


example (a x : R) : a ∈ I → (a * x) ∈ I ∧ (x * a) ∈ I :=
begin
  intro ha,
  split,
  rewrite mul_comm,
  all_goals {
    apply I.smul_mem,
    assumption},
end


/- Est-ce que vous pouvez expliquer pourquoi l'énoncé "la préimage d'un idéal par un morphisme
d'anneaux" est une `définition` et pas un `lemme`? -/
definition preimage (f : R →+* S) (J : ideal S) : (ideal R) :=
{ carrier := {x : R | f x ∈ J},
  add_mem' :=
  begin
    simp,
    intros a b hfa hfb,
    apply J.add_mem hfa hfb,
  end,

  zero_mem' :=
  begin
    simp only [set.mem_set_of_eq, map_zero, submodule.zero_mem],
  end,

  smul_mem' :=
  begin
    intros x r hfr,
    simp only [smul_eq_mul, set.mem_set_of_eq, map_mul],
    apply J.smul_mem,
    sorry,
  end
   }

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