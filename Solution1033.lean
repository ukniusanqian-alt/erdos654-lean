module

public import JspLean

/-!
# Solution

The proof lives in `JspLean/Erdos1033.lean` (namespace `Erdos1033Proof`).
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
  exact Erdos1033Proof.erdos_1033

end Erdos1033
