import ring_theory.localization.basic

open is_localization

variables {A : Type*} (B : Type*) [comm_ring A] [comm_ring B] [algebra A B]
variables {S : submonoid A} [is_localization S B]
-- L'hypothèse `is_localization S B` signifie que `B=S⁻¹ A`.
/-- The typeclass `is_localization (S : submodule A) B` where `B` is an `A`-algebra
expresses that `B` is isomorphic to the localization of `A` at `S`. -/

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
  apply map_units,
end

lemma becomes_unit (a : A) : a ∈ S → is_unit (algebra_map A B a) :=
begin
  intro ha,
 -- J'imagine qu'on est d'accord qu'il faut "en gros" faire la même chose que dans l'`exemple l.36`:
 -- Le problème est que si on fait
--  `apply map_units`, --on reçoit l'erreur
--  `invalid apply tactic, failed to unify`
--   `is_unit (⇑(algebra_map A B) a)` 
--  	 `with`
--   `is_unit (⇑(algebra_map ?m_3 ?m_1) ↑?m_7)`
-- Essayons de le comprendre: on voudrait `?m_3=A`, puis `?m_1=B` et `↑?m_7=a`. Pour voir ce qui
-- se passe, il est parfois commode d'utiliser un `have :=`, qui ne mène nulle part mais nous fait
-- voir ce que Lean attend: par exemple,
-- have premier := map_units,
-- fait apparaître un terme `premier` qui demande clairement en variables un Type `S` qui doit être un
-- `comm_semiring`, puis un terme `?m_1` qui n'apparaît pas mais dont on comprend que `S` doit
-- être une algèbre sur `?m_1` (regardez `_inst_3`), et après un terme `self` qui doit être une
-- preuve que `S` est un localisé à `?m_3`. Ces variables bizarres sont nommées ainsi automatiquement
-- par Lean, parce que si on lui fournit un terme de type `is_localization ?m_3 S` il comprendra qui
-- est `?m_3`. Chez nous, `B` est un localisé de `A` à `S`, donc à la fin on voudra
-- * ?m_1=A
-- * ?m_3=S
-- * S = B
-- On peut alors améliorer `premier` en
-- have deuxieme := map_units B,
-- et on aurait même envie de prendre `y = a` maintenant... *MAIS* on voit bien que `y` doit être un
-- terme de type `↥?m_3 = ↥S` et non pas de type `S`... il y a une flèchette vers le haut. En effet
-- `have := deuxieme a,`
-- (que je vous conseille de tester) donne un erreur. D'ailleurs, vous voyez que si vous
-- clickez sur `↥?m_3` vous voyez que ça doit être un `Type` alors que `?m_3` est un `submonoid`...
-- Le point est que `a` est un terme de type `A` et `deuxieme` veut un terme de type `S`: on peut le
-- créer!
let b : S := ⟨a, ha⟩,
-- Grâce à `ha`, qui nous dit que `a` *appartient* à `S`, on a crée un terme de type `↥S`, où la
-- flêche indique qu'on regarde maintenant `S` comme un type à part entière. On peut donc conclure
-- avec
  exact map_units B b,
  -- (si vous voyez plein de goals, encore, c'est parce que j'ai introduit plein de choses à vérifier
  -- dans `premier` et `deuxième`: si vous les commentez, vous voyez le `goals_accomplished`.
  -- D'ailleurs, on a pas besoin de déclarer `b`: on pourrait simplement faire
  -- exact map_units B ⟨a, ha⟩),
end

lemma from_S (a : A) (v : B) (h : algebra_map A B a = v) : ∃ s : S, mk' B a s = v :=
begin
 use (1:S),
 rw mk'_eq_iff_eq_mul,
 rw ← h,
 simp only [submonoid.coe_one, map_one, mul_one],
end

lemma unit_from_S (a : A) (v : Bˣ) : a ∈ S → is_unit ((algebra_map A B a) * v):=
begin
  intro ha,
  let b : S := ⟨a, ha⟩,
  apply prod_units,
  apply map_units B b,
  simp only [units.is_unit],
end

/- J'admets avoir résolu les deux derniers exercices plutôt en déduisant de ce que je pouvais comprendre des
lemmes de algebra_map et is_localization, qu'en les comprenant réellement -/


include B
variables {C : Type*} [comm_ring C] 
/-
Ce qu' on est en train de dire dans la définition suivante est que si vous avez un morphisme
d'anneaux `f : A → C` qui envoie tout élément de `S` sur une unité de `C`, alors vous pouvez étendre
`f` à un morphisme `F : B=S⁻¹A → C`. Moralement, comme les éléments de `B` sont de la forme `a/s`
avec `a ∈ A` et `s ∈ S` vous pouvez définir l'extension `F` par la formule `F(a/s) = f(a)/f(s)` ce
qui a un sens d'après l'hypothèse que `f(s)` est une unité.
-/

-- lemma sec_one : sec S (1 : B) = ⟨(1 : A) , (1 : S)⟩ :=
-- begin
--   unfold is_localization.sec,
--   simp only [one_mul],
--   rw is_localization.eq_iff_exists S B _ _,
  
-- end

noncomputable
def extended {f : A →+* C} (hf : ∀ s : S, is_unit (f s)) : (B →+* C) :=
{ to_fun := λ b, f((sec S b).1) * ((hf (sec S b).2).unit)⁻¹.1,
  map_one' :=
  begin
    simp only [units.val_eq_coe, units.mul_inv_eq_one, is_unit.unit_spec],
    have := @sec_spec' A _ S B _ _ _ 1,
    rw mul_one at this,
    -- exact this,
  end,
  map_mul' :=
  begin
    simp only [units.val_eq_coe],
    sorry
  end,
  map_zero' := sorry,
  map_add' := sorry }

--***Question:***: Savez-vous quelle est la différence entre les parenthèses `(` et `{`?
/- les () sont des éléments nécessaires à rentre pour que lean comprenne de quoi on parle, les {} peuvent être déduit
des autres hypothèses -/
lemma injective {f : A →+* C} (hf : ∀ s : S, is_unit (f s)) (h_inj: function.injective f) :
  function.injective (extended B hf) := sorry
