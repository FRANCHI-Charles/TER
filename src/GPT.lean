import data.real.basic
import topology.algebra.monoid
import tactic

def lim_add_suite (a : ℕ → ℝ) (b : ℕ → ℝ) (l l' : ℝ) (H1 : (∀ ε > 0, ∃ N, ∀ n ≥ N, abs (a n - l) < ε)) (H2 : (∀ ε > 0, ∃ N, ∀ n ≥ N, abs (b n - l') < ε)) :
  (∀ ε > 0, ∃ N, ∀ n ≥ N, abs ((a n + b n) - (l + l')) < ε) :=
begin
  intros ε Hε,
  have Hε2 : ε/2 > 0,
    apply div_pos,
    exact Hε,
    exact two_pos,

  cases H1 (ε/2) Hε2 with N1 HN1,
  cases H2 (ε/2) Hε2 with N2 HN2,
  use max N1 N2,
  intros n Hn,
  have H1n := HN1 n (le_trans (le_max_left _ _) Hn),
  have H2n := HN2 n (le_trans (le_max_right _ _) Hn),
  calc
    abs ((a n + b n) - (l + l')) = abs ((a n - l) + (b n - l'))  : by ring_nf
      ... ≤ abs(a n - l) + abs(b n - l') : abs_add (a n - l) (b n - l')
      ... < ε/2 + ε/2 : add_lt_add H1n H2n
      ... = ε : by ring,
end