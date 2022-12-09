import data.real.basic
import tactic

namespace vilnius


example (P Q : Prop) : P ∧ Q → Q :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  exact hQ,
end


example (P Q R : Prop) : (R → P) ∧ (P → Q) → (R → Q) :=
begin
  intro hPQR,
  intro hR,
  cases hPQR with hRP hPQ,
  apply hPQ,
  apply hRP,
  exact hR,
end

end vilnius