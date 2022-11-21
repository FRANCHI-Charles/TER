import data.real.basic
import tactic

open function real

namespace vilnius


example (X Y Z : Type) (f : X → Y) (g : Y → Z) 
  (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  intro z,
  have h1 : exists (y:Y), g y = z,
  apply hg,
  cases h1 with y hy,
  have h2 : exists (a:X), f a = y,
  apply hf,
  cases h2 with a ha,
  --use a,
  split,
  rw <- hy,
  rw <- ha,
end

/- ### The λ notation:
In Lean (or in Type Theory, rather) the way to define a function is to use λ expressions: here, you
should think that `λ = ∀`: so, the function
`λ x, 3*x ^ 2 + 1`
is nothing else that the function
`f(x)=3*x ^ 2 + 1` or `f : x ↦ 3*x ^ 2 + 1`.

As for usual functions, the name of the variable does not matter, so
`λ x, 3*x ^ 2 + 1` is the same as `λ w, 3*w ^ 2 + 1` 

The tactic to get rid of a `λ` term is
* `simp only` (possibly: at h)
because it "evaluates a λ-term", transforming, for instance
`(λ x, 2 * x + 1) 3` into `2 * 3 + 1`.
-/


definition A : ℕ → ℕ := λ n, n + 1 

example : injective A :=
begin
  intros x1 x2 hx,
  rewrite <- add_left_inj 1,
  assumption,
end

example : ¬ surjective A := 
begin
  intro h,
  rewrite A at h,
  rewrite surjective at h,
  specialize h 0,
  cases h with a h,
  --contrapose h,
  rewrite <- nat.succ_eq_add_one at h,
  apply nat.succ_ne_zero a h,
end

-- Recall the-
definition is_linear (f : ℝ → ℝ) : Prop := ∀ c x y, f (c * x + y) = c * f (x) + f(y) 

--as well as
theorem linear_at_0 (f : ℝ → ℝ) (H : is_linear f) : f 0 = 0 :=
begin
  rewrite <- add_left_inj (f 0),
  rewrite zero_add,
  nth_rewrite_lhs 0 <- one_mul (f 0),
  rw <- H,
  rw one_mul,
  rw add_zero,
end

-- And now a new

definition is_linear' (f : ℝ → ℝ) : Prop :=
(∀ x y, f ( x + y) = f (x) + f (y)) ∧ (∀ c x, f (c * x) = c * f (x))

theorem linear_eq (f : ℝ → ℝ) : is_linear f ↔ is_linear' f :=
begin
  split,
    intros hl,
    split,
      intros x1 x2,
      nth_rewrite_lhs 0 <- one_mul x1,
      rw hl,
      rw one_mul,

      intros c x,
      rw <- add_zero (c*x:real),
      rw hl,
      rw linear_at_0 f,
      rw add_zero,
      assumption,
    
    intro hl,
    cases hl with hs hp,
    intros c x y,
    rw hs,
    rw hp,
end

--Recall the
definition is_affine (f : ℝ → ℝ) : Prop := ∃ a, ∀ x y, f (y) - f(x) = a * (y - x)

-- together with the
theorem linear_add_cnst_of_affine (f : ℝ → ℝ) : is_affine f → (∃ a : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, a)) ∧ is_linear g) :=
  begin
    intro haf,
    cases haf with a haf,
    use (f 0),
    use (λ (x : ℝ), a*x),
    split,
    swap,
      intros c x y,
      simp only,
      rewrite mul_add a (c*x) y,
      rewrite <- mul_assoc,
      rewrite <- mul_assoc,
      rewrite mul_comm a c,

      ext,
      simp,
      rw <- sub_eq_iff_eq_add,
      nth_rewrite_rhs 0 <- sub_zero x,
      specialize haf (0:ℝ) x,
      assumption,
  end


-- as well as

theorem affine_of_linear_add_cnst (f : ℝ → ℝ) : (∃ b : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, b)) ∧ is_linear g) → is_affine f :=
  begin
    intros ht,
    cases ht with b ht,
    cases ht with g ht,
    cases ht with ha hl,
      rw linear_eq at hl,
      cases hl with hs hp,
    use (g 1),
    intros x y,
    rewrite ha,
    simp,
    rw mul_sub,
    rewrite mul_comm,
    nth_rewrite_rhs 1 mul_comm,
    rw <- hp,
    rw mul_one,
    rw <- hp,
    rw mul_one,
  end

-- that we proved in the lesson.

example (f : ℝ → ℝ) : is_affine f ↔ ∃ a : ℝ, ∃ g : ℝ → ℝ, (f = g + (λ x, a)) ∧ is_linear g := -- iff.intro (linear_add_cnst_of_affine _) (affine_of_linear_add_cnst _)
begin
  split,
  apply linear_add_cnst_of_affine f,
  apply affine_of_linear_add_cnst f,
end

end vilnius
