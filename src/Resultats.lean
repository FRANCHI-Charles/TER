import algebra.module.localized_module
import ring_theory.localization.basic
import ring_theory.localization.module
import algebra.module.linear_map

open is_localization


variables {R : Type*} [comm_semiring R] (S : submonoid R)
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]
-- variables (hM : localized_module S M) (hN : localized_module S N)


def extended (f : M →[R] N) : (localized_module S M) →+[localization S] (localized_module S N) :=
{ to_fun := sorry,
  map_smul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }