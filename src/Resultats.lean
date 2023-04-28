import ring_theory.localization.basic
import ring_theory.localization.module
import algebra.module.linear_map

open is_localization


variables {R : Type*} (S : Type*) [comm_semiring R] [comm_semiring S] [algebra R S]
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]


def extended {f : M →+ N} [h : is_linear_map R f] :