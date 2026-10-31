module

public import JspLean

/-!
# Solution

The proof lives in `JspLean/Erdos654.lean` (namespace `Erdos654Proof`). This file restates the
challenge definitions verbatim and bridges to the library theorems by definitional equality.
-/

public section

open Finset EuclideanGeometry
open scoped Classical

namespace Erdos654

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- No four points of `X` lie on a common circle. In the plane, `Cospherical` means lying on a
common circle; four distinct collinear points are never cospherical, so collinear points are
allowed. (Definition copied verbatim from google-deepmind/formal-conjectures.) -/
def NoFourConcyclic (X : Set ℝ²) : Prop :=
  ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

/-- The number of distinct distances from `pt` to the other points of `points`. (Definition
copied verbatim from google-deepmind/formal-conjectures.) -/
noncomputable def distinctDistancesFrom (points : Finset ℝ²) (pt : ℝ²) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

/-- Aletheia (T. Feng et al., arXiv:2601.22401, §3.1, Theorem 3): for every `m ≥ 10` there is a
set of `n = 4m` points in the plane, no four on a circle, such that every point has fewer than
`3m = 3n/4` distinct distances to the other points. -/
theorem erdos_654.variants.feng (m : ℕ) (hm : 10 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m :=
  Erdos654Proof.feng m hm

/-- Erdős Problem 654, first question, answered in the negative: it is **not** true that for
every `ε > 0` and all large `n`, every `n`-point set in the plane with no four points on a circle
contains a point with more than `(1 - ε) n` distinct distances to the other points. -/
theorem erdos_654.parts.i :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) :=
  Erdos654Proof.parts_i

end Erdos654
