import ring_theory.localization.basic

open is_localization

variables {A : Type*} (B : Type*) [comm_ring A] [comm_ring B] [algebra A B]
variables {S : submonoid A} [is_localization S B]
-- L'hypothèse `is_localization S B` signifie que `B` est isomorphe au localisé `S⁻¹ B`.


lemma prod_units (u v : A) : is_unit u → is_unit v → is_unit (u * v) :=
begin
  intros hu hv,
  simp only [is_unit.mul_iff],
  split,
  exact hu,
  exact hv,
end

variable (f : A →+* A)
#check (f : A →+ A)
#check (f: A → A)

lemma inv_unit (u v : Aˣ) : is_unit (u⁻¹) :=
begin
  use u⁻¹,
  use u,
  exact mul_left_inv u, --mais `simp` aurait marché! Et si vous écrivez `squeeze_simp` il vous dit
  --comment il a fait! Pensez bien que si on doit suffrir pour montrer que dans un groupe le produit
  -- d'un élément avec son inverse fait l'identité, on peut se tirer une balle! C'est fort probablement
  -- quelque chose que `simp` doit savoir résoudre!

  exact mul_right_inv u,
  simp only [units.coe_mk],
end

example (a : S) : is_unit (algebra_map A B a) :=
begin
  exact _inst_4.map_units a,
end

lemma becomes_unit (a : A) : a ∈ S → is_unit (algebra_map A B a) :=
begin
  intro ha,
  --rw add_submonoid.mem_carrier
end

lemma from_S (a : A) (v : B) (h : algebra_map A B a = v) : ∃ s : S, mk' B a s = v := sorry

lemma unit_from_S (a : A) (v : Bˣ) : a ∈ S → is_unit ((algebra_map A B a) * v):= sorry


include B
variables {C : Type*} [comm_ring C] 
/-
Ce qu' on est en train de dire dans la définition suivante est que si vous avez un morphisme
d'anneaux `f : A → C` qui envoie tout élément de `S` sur une unité de `C`, alors vous pouvez étendre
`f` à un morphisme `F : B=S⁻¹A → C`. Moralement, comme les éléments de `B` sont de la forme `a/s`
avec `a ∈ A` et `s ∈ S` vous pouvez définir l'extension `F` par la formule `F(a/s) = f(a)/f(s)` ce
qui a un sens d'après l'hypothèse que `f(s)` est une unité.
-/

def extended {f : A →+* C} (hf : ∀ s : S, is_unit (f s)) : (B →+* C) := sorry

--***Question:***: Savez-vous quelle est la différence entre les parenthèses `(` et `{`?
lemma injective {f : A →+* C} (hf : ∀ s : S, is_unit (f s)) (h_inj: function.injective f) :
  function.injective (extended B hf) := sorry
