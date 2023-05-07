import algebra.module.localized_module
import ring_theory.localization.basic
import ring_theory.localization.module
import algebra.module.linear_map

open localized_module


variables {R : Type*} [comm_semiring R] (S : submonoid R)
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]
-- variables (hM : localized_module S M) (hN : localized_module S N)


lemma mk_wd (f : M →[R] N) : ∀ (p p' : M × S) (h1 : p ≈ p'), mk (f p.1) (p.2) = mk (f p'.1) (p'.2):=
begin
  intros x y hr,
  rw mk_eq,
  have h : ∃ (u : ↥S), u • x.snd • y.fst = u • y.snd • x.fst,

  swap,
  cases h with u hu,
  use u,
  have premier := map_smul f,
  have deuxieme := premier x.2 y.1, --fonctionne, mais je ne peux le faire en une ligne...
  rw ← deuxieme, -- x.2 ≠ ↑x.2  
end

/-
1 Trouver la bonne fonction pour le porblème de rw deuxième
2 Appliquer congr_arg et résoudre
3 comprendre ≃ et résoudre sans le swap
4 compléter extended -/  


def extended (f : M →[R] N) : (localized_module S M) →+[localization S] (localized_module S N) :=
{ to_fun := λ p1, lift_on p1 (λ x, mk (f(x.1)) (x.2)) (mk_wd S f),
  map_smul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }