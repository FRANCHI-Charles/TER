import data.real.basic
import tactic

namespace vilnius

/- Quelques bases -/

example (P Q : Prop) : P ∧ Q → Q :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  exact hQ,
end


example (P Q : Prop) : P → (Q → P ∧ Q) := --les paranthèses sont inutiles
begin
  intros hP hQ,
  split,
  exact hP,
  exact hQ,
end


example (P Q : Prop) : (P → ¬ Q) → (Q → ¬ P) :=
begin
  intro hPnQ,
  intro hQ,
  intro hP,
  apply hPnQ,
  exact hP,
  exact hQ,
end


/- 

Exemple avec les limites

-/
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε


theorem is_limit_add {a : ℕ → ℝ} {l : ℝ} (c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  intros e se,
  specialize ha e se,
  cases ha with N ha,
  use N,
  intros n sn,
  simp,
  specialize ha n sn,
  exact ha,
end




end vilnius