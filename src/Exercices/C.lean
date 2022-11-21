import data.real.basic
import tactic
-- import C_Limits.fae_solutions.Course
-- open vilnius

namespace vilnius

--local notation `|` x `|` := abs x


-- Recall the
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

example {a : ℕ → ℝ} {l : ℝ} (c : ℝ) (ha : is_limit a l) :
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


example (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  split,
  intros ha e se,
  specialize ha e se,
  cases ha with N ha,
  use N,
  intros n sn,
  simp,
  specialize ha n sn,
  exact ha,

  intros ha e se,
  specialize ha e se,
  cases ha with N ha,
  use N,
  intros n sn,
  specialize ha n sn,
  simp only [tsub_zero] at ha,
  exact ha,
end


/- Helpful things:
'squeeze_simp' décrit ce que simp fait
`abs_pos : 0 < |a| ↔ a ≠ 0`
`div_pos : 0 < a → 0 < b → 0 < a / b`
`abs_mul x y : |x * y| = |x| * |y|`
`lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
I typically find these things myself with a combination of
the "guess the name of the lemma" game (and ctrl-space).


Recall also that we have proved the-/
theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
  begin
    intros e se,
    specialize h1 (e/2),
    specialize h2 (e/2),
    have h: e/2 > 0,
    apply div_pos,
    exact se,
    exact two_pos,
    specialize h1 h,
    specialize h2 h,

    cases h1 with N1 h1,
    cases h2 with N2 h2,
    use max N1 N2,
    intros n sn,
    simp,
    rewrite <- sub_sub,
    rw ← add_sub,
    rw sub_eq_add_neg _ l,
    rw add_comm _ (-l),
    rw ← add_assoc,
    rw ← sub_eq_add_neg,
    rw sub_eq_add_neg _ m,
    rw add_assoc (a n - l) (b n) (- m),
    rw ← sub_eq_add_neg _ m,
    apply lt_of_le_of_lt,
    apply abs_add (a n -l) (b n -m) ,
    rw ← add_halves e,
    apply add_lt_add (h1 n _) (h2 n _),
    apply le_of_max_le_left,
    exact sn, 
    apply le_of_max_le_left,
    rw max_comm,
    exact sn, 
  end


-- And now, over to you!

-- A hint for starting:
-- It might be worth dealing with `c = 0` as a special case. You
-- can start with 
-- `by_cases hc : c = 0`

theorem is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  by_cases hc : c=0,
  intros e se,
  rewrite hc,
  simp only [ge_iff_le, zero_mul, tsub_zero, abs_zero],
  use 0,
  intros n sn,
  exact se,

  intros e se,
  specialize h (e/|c|),
  have hec : e/|c| > 0,
    apply div_pos,
    exact se,
    rw abs_pos,
    exact hc,
  specialize h hec,
  cases h with N h,
  use N,
  intros n sn,
  simp only,
  rewrite <- mul_sub,
  rewrite abs_mul,
  have hc' : 0 < |c|,
    rewrite abs_pos,
    exact hc,
  rewrite mul_comm,
  rewrite ← lt_div_iff hc',
  exact h n sn,
end

theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  intros e se,
  specialize ha e se,
  specialize hc e se,
  cases ha with na ha,
  cases hc with nc hc,
  use max na nc,
  intros n sn,
  specialize hab n,
  specialize hbc n,
  specialize ha n,
  specialize hc n,
  specialize ha (le_of_max_le_left sn),
  specialize hc (le_of_max_le_right sn),
  rewrite abs_sub_lt_iff,
  split,

  rewrite sub_lt_iff_lt_add,
  apply lt_of_lt_of_le',
  rewrite ← sub_lt_iff_lt_add,
  apply lt_of_abs_lt,
  use hc,
  exact hbc,

  rewrite sub_lt,
  apply lt_of_lt_of_le,
  swap,
  use hab,
  rewrite ← sub_lt,
  apply lt_of_abs_lt,
  rewrite abs_sub_comm,
  exact ha,
end

example (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
  -- intros ε hε,**BAD IDEA**, you can do this much faster using the above theorems!
  apply is_limit_add,
  apply is_limit_mul_const_left,
  exact ha,

  apply is_limit_mul_const_left,
  exact hb,
end

example (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  sorry,
end

end vilnius