import ring_theory.ideal.basic

variables {R S : Type} [comm_ring R] [comm_ring S] (I : ideal R)


/- ### Intro
Voici une liste d'examples à faire une fois que vous aurez terminé le premier chapitre
de Atiyah-Macdonald -/


example (a b : R) : a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  intros ha hb,
  exact I.add_mem ha hb,
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
/- "_" va afficher une ampoule et me permet de générer le squelette nécessaire pour consrtuire le terme
avce begin end, on peut utiliser "fconstructor" pour split le goal dans un ordre "logique"-/
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
    apply hfr,
  end
   }

example (f : R →+* S) (J : ideal S) (hJ: J.is_prime) : (preimage f J).is_prime :=
begin
  let h1 := hJ.1, /-différence entre have and let ?-/
    fconstructor,
    { rw ideal.ne_top_iff_one,
      have jj := (ideal.ne_top_iff_one J).mp h1,
      intro h,
      have : (f 1) ∈  J := h,
      rw map_one at this,
      exact jj this,
  },
  { sorry,

  },
end, 

/- Est-ce que vous pouvez expliquer pourquoi l'énoncé "l'intersection de deux idéaux est un idéal" est
une `définition` et pas un `lemme`? -/
definition intersection (J : ideal R) : ideal R :=
{ carrier := I ∩ J,
  add_mem' :=
  begin
    intros a b ha hb,
    cases ha with hai haj,
    cases hb with hbi hbj,
    split,
    apply I.add_mem,
    exact hai,
    exact hbi,
    apply J.add_mem,
    exact haj,
    exact hbj,
  end,

  zero_mem' := 
  begin
    split,
    exact I.zero_mem',
    exact J.zero_mem',
  end,

  smul_mem' :=
  begin
    intros c x hx,
    cases hx with hxi hxj,
    split,
    apply I.smul_mem',
    exact hxi,
    apply J.smul_mem',
    exact hxj,
  end }



-- Pourquoi l'exemple suivant ne compile pas, même avec la définition précédente?
example (J : ideal R) (x y : R) : x ∈ I → x ∈ J → x ∈ intersection J I :=
begin
  intros hI hJ,
  split,
  exact hJ,
  exact hI,
end