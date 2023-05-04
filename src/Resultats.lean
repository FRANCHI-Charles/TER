import algebra.module.localized_module
import ring_theory.localization.basic
import ring_theory.localization.module
import algebra.module.linear_map

open localized_module


variables {R : Type*} [comm_semiring R] (S : submonoid R)
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]
-- variables (hM : localized_module S M) (hN : localized_module S N)


def sec (b : localized_module S M) : M × S :=
begin
  
end

def extended (f : M →[R] N) : (localized_module S M) →+[localization S] (localized_module S N) :=
{ to_fun := λ p1, lift_on p1 (λ x, mk (f(x.1)) (x.2)),
  map_smul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }