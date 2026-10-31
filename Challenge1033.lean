module

public import Mathlib

/-!
# Challenge: Erdős Problem 1033 (Bollobás–Erdős triangle degree sums) is false

Let `h(n)` be such that every graph on `n` vertices with more than `n² / 4` edges contains a
triangle whose vertices have degrees summing to at least `h(n)`. Bollobás and Erdős asked whether
`h(n) ≥ (2(√3 - 1) - o(1)) n` (https://www.erdosproblems.com/1033). The answer is no: a blow-up
of the butterfly graph (erdosproblems.com forum, June–July 2026; W. CvB, *Optimized density
argument for Erdős 1033*) has more than `n² / 4` edges and every triangle degree sum at most
`1.4641 n`. The statement below is exactly `Erdos1033.erdos_1033` of
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1033.lean`). This file
imports only Mathlib.
-/

public section

open Filter Finset

namespace Erdos1033

/-- Erdős Problem 1033 (Bollobás–Erdős), main question, answered in the negative: it is **not** true
that for every `ε > 0` and all large `n`, every graph on `n` vertices with more than `n² / 4` edges
contains a triangle whose vertex degrees sum to at least `(2(√3 - 1) - ε) n`. -/
theorem erdos_1033 :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      n ^ 2 < 4 * #G.edgeFinset →
        ∃ t, G.IsNClique 3 t ∧
          (2 * (Real.sqrt 3 - 1) - ε) * n ≤ ∑ v ∈ t, (G.degree v : ℝ) := by
  sorry

end Erdos1033
