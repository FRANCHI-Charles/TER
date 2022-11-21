import ring_theory.ideal.basic

variables {R S : Type} [comm_ring R] [comm_ring S] (I : ideal R)

example (a b : R) : a ∈ I → b ∈ I → (a + b) ∈ I :=
begin
  intros a b,
  --apply add_mem a b,
  
end

example (a x : R) : a ∈ I → (a * x) ∈ I ∧ (x * a) ∈ I := sorry

def preimage (f : R →+* S) (J : ideal S) : (ideal R) :=
{ carrier := {x : R | f x ∈ J},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

example (f : R →+* S) (J : ideal S) (hJ: J.is_prime) : (preimage f J).is_prime := sorry