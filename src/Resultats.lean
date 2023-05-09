import algebra.module.localized_module
import ring_theory.localization.basic
import ring_theory.localization.module
import algebra.module.linear_map
import tactic

noncomputable theory

open localized_module


variables {R : Type*} [comm_semiring R] (S : submonoid R)
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]
variables {P : Type*} [add_comm_monoid P] [module R P]


lemma mk_wd (f : M →+[R] N) : ∀ (p p' : M × S), mk p.1 p.2 = mk p'.1 p'.2 →
  mk (f p.1) (p.2) = mk (f p'.1) (p'.2):=
begin
  intros x y hr,
  rw mk_eq at ⊢ hr,
  obtain ⟨u, hu⟩ := hr,
  use u,
  simp only [submonoid.smul_def, ← distrib_mul_action_hom.map_smul] at hu ⊢,
  rw hu,
end

lemma mk_wd' (f : M →+[R] N) : ∀ (p p' : M × S), p ≈ p' →
  mk (f p.1) (p.2) = mk (f p'.1) (p'.2):=
begin
  intros p p' h,
  apply mk_wd,
  simp only [localized_module.mk, prod.mk.eta, h, quotient.eq],
end


def extended (f : M →+[R] N) : (localized_module S M) →+[localization S] (localized_module S N) :=
{ to_fun := λ p1, lift_on p1 (λ x, mk (f(x.1)) (x.2)) (mk_wd' S f),
  map_smul' :=
  begin
   intros m x,
  induction x using localized_module.induction_on with a s,
  induction m using localization.induction_on with m,
  rw mk_smul_mk,
  repeat {rw lift_on_mk},
  rw mk_smul_mk,
  simp only [map_smul],
  end,

  map_zero' :=
  begin
    rw ← zero_mk 1,
    rw lift_on_mk,
    dsimp only,
    rw map_zero,
    exact zero_mk 1,
  end,

  map_add' :=
  begin
    intros x y,
    induction x using localized_module.induction_on with a s1,
    induction y using localized_module.induction_on with b s2,
    rw mk_add_mk,
    repeat {rw lift_on_mk},
    rw mk_add_mk,
    simp only [map_add, submonoid.smul_def, ← distrib_mul_action_hom.map_smul],
  end }


  theorem extended_comp (f : M →+[R] N) (g : P →+[R] M) : extended S (f.comp g) = (extended S f).comp (extended S g) :=
  begin
    apply distrib_mul_action_hom.ext,
    intro x,
    induction x using localized_module.induction_on with a s,
    apply rfl,
  end