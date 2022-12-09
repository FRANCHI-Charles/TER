import data.real.basic
import tactic

namespace vilnius


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

end vilnius