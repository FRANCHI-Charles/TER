import tactic

namespace vilnius


/- ### implication -/

example (P Q : Prop) : P → Q → P :=
begin
  intros hP HQ,
  exact hP,
end

/- ### not -/

example (P Q : Prop) : (P → ¬ Q) → (Q → ¬ P) :=
begin
  intros hPnQ hQ hP,
  apply hPnQ,
  exact hP,
  exact hQ,
end


/- ### and -/

example (P Q : Prop) : P ∧ Q → Q :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  exact hQ,
end

example (P Q : Prop) : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  exact hP,
  exact hQ,
end


example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
  split,
  exact hQ,
  exact hP,
end


example (P : Prop) : P ∧ ¬ P → false :=
begin
  intro hPnP,
  cases hPnP with hP hnP,
  apply hnP,
  exact hP,
end


/- ## Or -/


example (P Q : Prop) : ¬ P ∨ Q → P → Q :=
begin
  intros hnPQ hP,
  cases hnPQ with hnP hQ,
  by_contradiction,
  apply hnP,
  exact hP,
  exact hQ,
end


example (P Q R : Prop) : P ∨ (Q ∧ R) → ¬ P → ¬ Q → false :=
begin
  intros hPQR hnP hnQ,
  cases hPQR with hP hQR,
  apply hnP,
  exact hP,

  cases hQR with hQ hR,
  apply hnQ,
  exact hQ,
end


end vilnius

