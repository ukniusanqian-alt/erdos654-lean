module

public import Mathlib

/-!
# Erdős Problem 654: Lean 4 formalization of the Aletheia counterexample

Reference: T. Feng et al., *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on
the Erdős Problems*, arXiv:2601.22401 (2026), §3.1.  Problem page: erdosproblems.com/654.

The definitions `NoFourConcyclic` and `distinctDistancesFrom` are copied verbatim from
google-deepmind/formal-conjectures (Apache-2.0) so that the statements below coincide with
`Erdos654.erdos_654.variants.feng` and `Erdos654.erdos_654.parts.i` there.

Construction (slightly simplified exponents, same idea): for `m ≥ 1` take the `2m` points
`(0, ±3^(k+1))`, `k < m`, on the y-axis and the `2m` points `(±2^(j+1), 0)`, `j < m`, on the
x-axis.  A circle meets each axis in at most two points, and if it meets both axes in two points
`(0,y₁),(0,y₂)`, `(x₁,0),(x₂,0)` then `y₁y₂ = x₁x₂` (power of the origin); taking absolute
values gives `3^a = 2^b` with `b ≥ 2`, impossible by parity.  Every point sees at most
`2m - 1` distances to its own axis and at most `m` to the other axis (the two symmetric points
`(±2^(j+1),0)` are equidistant from any point of the y-axis), so fewer than `3m = 3n/4`.
-/

open Finset EuclideanGeometry
open scoped Classical

@[expose] public noncomputable section

namespace Erdos654Proof

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- formal-conjectures definition. -/
def NoFourConcyclic (X : Set ℝ²) : Prop :=
  ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

/-- formal-conjectures definition. -/
noncomputable def distinctDistancesFrom (points : Finset ℝ²) (pt : ℝ²) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

/-- The point `(0, y)`. -/
def py (y : ℝ) : ℝ² := !₂[0, y]
/-- The point `(x, 0)`. -/
def px (x : ℝ) : ℝ² := !₂[x, 0]

@[simp] lemma py_zero (y : ℝ) : py y 0 = 0 := by simp [py]
@[simp] lemma py_one (y : ℝ) : py y 1 = y := by simp [py]
@[simp] lemma px_zero (x : ℝ) : px x 0 = x := by simp [px]
@[simp] lemma px_one (x : ℝ) : px x 1 = 0 := by simp [px]

lemma py_injective : Function.Injective py := by
  intro a b h
  have := congrArg (fun v : ℝ² => v 1) h
  simpa using this

lemma px_injective : Function.Injective px := by
  intro a b h
  have := congrArg (fun v : ℝ² => v 0) h
  simpa using this

lemma px_ne_py (x y : ℝ) (hx : x ≠ 0) : px x ≠ py y := by
  intro h
  have := congrArg (fun v : ℝ² => v 0) h
  simp at this
  exact hx this

lemma sq_dist_py (y : ℝ) (c : ℝ²) : dist (py y) c ^ 2 = (c 0) ^ 2 + (y - c 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
  simp [Real.dist_eq, sq_abs]

lemma sq_dist_px (x : ℝ) (c : ℝ²) : dist (px x) c ^ 2 = (x - c 0) ^ 2 + (c 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sq_sqrt (by positivity)]
  simp [Real.dist_eq, sq_abs]

lemma dist_px_py (x y : ℝ) : dist (px x) (py y) = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma dist_py_px (y x : ℝ) : dist (py y) (px x) = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [dist_comm, dist_px_py]

/-! ### Algebra: a circle meets a line in at most two points, and the power of a point -/

lemma eq_of_three_roots {a b s y₁ y₂ y₃ : ℝ} (h₁ : a + (y₁ - b) ^ 2 = s)
    (h₂ : a + (y₂ - b) ^ 2 = s) (h₃ : a + (y₃ - b) ^ 2 = s) (h₁₂ : y₁ ≠ y₂) (h₁₃ : y₁ ≠ y₃) :
    y₂ = y₃ := by
  have e₁₂ : (y₁ - y₂) * (y₁ + y₂ - 2 * b) = 0 := by linear_combination h₁ - h₂
  have e₁₃ : (y₁ - y₃) * (y₁ + y₃ - 2 * b) = 0 := by linear_combination h₁ - h₃
  rcases mul_eq_zero.1 e₁₂ with h | h
  · exact absurd (sub_eq_zero.1 h) h₁₂
  rcases mul_eq_zero.1 e₁₃ with h' | h'
  · exact absurd (sub_eq_zero.1 h') h₁₃
  linarith

lemma prod_of_two_roots {a b s y₁ y₂ : ℝ} (h₁ : a + (y₁ - b) ^ 2 = s)
    (h₂ : a + (y₂ - b) ^ 2 = s) (h₁₂ : y₁ ≠ y₂) : y₁ * y₂ = a + b ^ 2 - s := by
  have e : (y₁ - y₂) * (y₁ + y₂ - 2 * b) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.1 e with h | h
  · exact absurd (sub_eq_zero.1 h) h₁₂
  have hb : y₁ + y₂ - 2 * b = 0 := h
  linear_combination (-1 : ℝ) * h₁ + y₁ * hb

/-! ### The point configuration -/

/-- Points `(0, ±3^(k+1))`, `k < m`. -/
def yPts (m : ℕ) : Finset ℝ² :=
  ((range m).image fun k => py ((3 : ℝ) ^ (k + 1))) ∪
    ((range m).image fun k => py (-(3 : ℝ) ^ (k + 1)))

/-- Points `(±2^(j+1), 0)`, `j < m`. -/
def xPts (m : ℕ) : Finset ℝ² :=
  ((range m).image fun j => px ((2 : ℝ) ^ (j + 1))) ∪
    ((range m).image fun j => px (-(2 : ℝ) ^ (j + 1)))

/-- The configuration of `4m` points. -/
def config (m : ℕ) : Finset ℝ² := yPts m ∪ xPts m

lemma exists_of_mem_yPts {m : ℕ} {p : ℝ²} (hp : p ∈ yPts m) :
    ∃ k, k < m ∧ ∃ y : ℝ, p = py y ∧ |y| = 3 ^ (k + 1) := by
  simp only [yPts, mem_union, mem_image, mem_range] at hp
  rcases hp with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · exact ⟨k, hk, _, rfl, abs_of_pos (by positivity)⟩
  · exact ⟨k, hk, _, rfl, by rw [abs_neg]; exact abs_of_pos (by positivity)⟩

lemma exists_of_mem_xPts {m : ℕ} {p : ℝ²} (hp : p ∈ xPts m) :
    ∃ j, j < m ∧ ∃ x : ℝ, p = px x ∧ |x| = 2 ^ (j + 1) := by
  simp only [xPts, mem_union, mem_image, mem_range] at hp
  rcases hp with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨j, hj, _, rfl, abs_of_pos (by positivity)⟩
  · exact ⟨j, hj, _, rfl, by rw [abs_neg]; exact abs_of_pos (by positivity)⟩

lemma pow3_inj : Function.Injective fun k : ℕ => py ((3 : ℝ) ^ (k + 1)) := by
  intro a b h
  have h' : (3 : ℝ) ^ (a + 1) = 3 ^ (b + 1) := py_injective h
  have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) h'
  omega

lemma pow3neg_inj : Function.Injective fun k : ℕ => py (-(3 : ℝ) ^ (k + 1)) := by
  intro a b h
  have h' : (3 : ℝ) ^ (a + 1) = 3 ^ (b + 1) := neg_inj.1 (py_injective h)
  have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≠ 1) h'
  omega

lemma pow2_inj : Function.Injective fun j : ℕ => px ((2 : ℝ) ^ (j + 1)) := by
  intro a b h
  have h' : (2 : ℝ) ^ (a + 1) = 2 ^ (b + 1) := px_injective h
  have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h'
  omega

lemma pow2neg_inj : Function.Injective fun j : ℕ => px (-(2 : ℝ) ^ (j + 1)) := by
  intro a b h
  have h' : (2 : ℝ) ^ (a + 1) = 2 ^ (b + 1) := neg_inj.1 (px_injective h)
  have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h'
  omega

lemma card_yPts (m : ℕ) : #(yPts m) = 2 * m := by
  have hdisj : Disjoint ((range m).image fun k => py ((3 : ℝ) ^ (k + 1)))
      ((range m).image fun k => py (-(3 : ℝ) ^ (k + 1))) := by
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_image, mem_range] at hp hp'
    obtain ⟨k, -, rfl⟩ := hp
    obtain ⟨k', -, h⟩ := hp'
    have := py_injective h
    have h3 : (0 : ℝ) < 3 ^ (k + 1) := by positivity
    have h3' : (0 : ℝ) < 3 ^ (k' + 1) := by positivity
    linarith
  rw [yPts, card_union_of_disjoint hdisj, card_image_of_injective _ pow3_inj,
    card_image_of_injective _ pow3neg_inj, card_range]
  ring

lemma card_xPts (m : ℕ) : #(xPts m) = 2 * m := by
  have hdisj : Disjoint ((range m).image fun j => px ((2 : ℝ) ^ (j + 1)))
      ((range m).image fun j => px (-(2 : ℝ) ^ (j + 1))) := by
    rw [disjoint_left]
    intro p hp hp'
    simp only [mem_image, mem_range] at hp hp'
    obtain ⟨j, -, rfl⟩ := hp
    obtain ⟨j', -, h⟩ := hp'
    have := px_injective h
    have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    have h2' : (0 : ℝ) < 2 ^ (j' + 1) := by positivity
    linarith
  rw [xPts, card_union_of_disjoint hdisj, card_image_of_injective _ pow2_inj,
    card_image_of_injective _ pow2neg_inj, card_range]
  ring

lemma disjoint_yPts_xPts (m : ℕ) : Disjoint (yPts m) (xPts m) := by
  rw [disjoint_left]
  intro p hp hp'
  obtain ⟨k, -, y, rfl, -⟩ := exists_of_mem_yPts hp
  obtain ⟨j, -, x, hx, hxabs⟩ := exists_of_mem_xPts hp'
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hxabs
    have : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    linarith
  exact px_ne_py x y hx0 hx.symm

lemma card_config (m : ℕ) : #(config m) = 4 * m := by
  rw [config, card_union_of_disjoint (disjoint_yPts_xPts m), card_yPts, card_xPts]; ring

/-! ### No four points on a circle -/

lemma not_cospherical_four (m : ℕ) (T : Finset ℝ²) (hT : T ⊆ config m) (h4 : #T = 4) :
    ¬ Cospherical (T : Set ℝ²) := by
  rintro ⟨c, r, hc⟩
  -- circle equations
  have hy : ∀ y : ℝ, py y ∈ T → (c 0) ^ 2 + (y - c 1) ^ 2 = r ^ 2 := by
    intro y hyT
    rw [← sq_dist_py, hc _ (by exact_mod_cast hyT)]
  have hx : ∀ x : ℝ, px x ∈ T → (c 1) ^ 2 + (x - c 0) ^ 2 = r ^ 2 := by
    intro x hxT
    have h := sq_dist_px x c
    rw [hc _ (by exact_mod_cast hxT)] at h
    linarith
  set TY := T.filter (fun p => p ∈ yPts m) with hTY
  set TX := T.filter (fun p => p ∉ yPts m) with hTX
  have hsum : #TY + #TX = 4 := by rw [← h4]; exact card_filter_add_card_filter_not _
  have hTXsub : ∀ p ∈ TX, p ∈ xPts m := by
    intro p hp
    rw [hTX, mem_filter] at hp
    have := hT hp.1
    rw [config, mem_union] at this
    tauto
  -- at most two points on the y-axis
  have hTY2 : #TY ≤ 2 := by
    by_contra hcon
    obtain ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, h₁₂, h₁₃, h₂₃⟩ :=
      two_lt_card_iff.1 (show 2 < #TY by omega)
    rw [hTY, mem_filter] at hp₁ hp₂ hp₃
    obtain ⟨-, -, y₁, rfl, -⟩ := exists_of_mem_yPts hp₁.2
    obtain ⟨-, -, y₂, rfl, -⟩ := exists_of_mem_yPts hp₂.2
    obtain ⟨-, -, y₃, rfl, -⟩ := exists_of_mem_yPts hp₃.2
    have e := eq_of_three_roots (hy _ hp₁.1) (hy _ hp₂.1) (hy _ hp₃.1)
      (fun h => h₁₂ (by rw [h])) (fun h => h₁₃ (by rw [h]))
    exact h₂₃ (by rw [e])
  -- at most two points on the x-axis
  have hTX2 : #TX ≤ 2 := by
    by_contra hcon
    obtain ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, h₁₂, h₁₃, h₂₃⟩ :=
      two_lt_card_iff.1 (show 2 < #TX by omega)
    have q₁ := hTXsub _ hp₁
    have q₂ := hTXsub _ hp₂
    have q₃ := hTXsub _ hp₃
    rw [hTX, mem_filter] at hp₁ hp₂ hp₃
    obtain ⟨-, -, x₁, rfl, -⟩ := exists_of_mem_xPts q₁
    obtain ⟨-, -, x₂, rfl, -⟩ := exists_of_mem_xPts q₂
    obtain ⟨-, -, x₃, rfl, -⟩ := exists_of_mem_xPts q₃
    have e := eq_of_three_roots (hx _ hp₁.1) (hx _ hp₂.1) (hx _ hp₃.1)
      (fun h => h₁₂ (by rw [h])) (fun h => h₁₃ (by rw [h]))
    exact h₂₃ (by rw [e])
  -- hence exactly two on each axis
  obtain ⟨p₁, p₂, hp₁, hp₂, h₁₂⟩ := one_lt_card_iff.1 (show 1 < #TY by omega)
  obtain ⟨q₁, q₂, hq₁, hq₂, hq₁₂⟩ := one_lt_card_iff.1 (show 1 < #TX by omega)
  have r₁ := hTXsub _ hq₁
  have r₂ := hTXsub _ hq₂
  rw [hTY, mem_filter] at hp₁ hp₂
  rw [hTX, mem_filter] at hq₁ hq₂
  obtain ⟨k₁, -, y₁, rfl, hy₁⟩ := exists_of_mem_yPts hp₁.2
  obtain ⟨k₂, -, y₂, rfl, hy₂⟩ := exists_of_mem_yPts hp₂.2
  obtain ⟨j₁, -, x₁, rfl, hx₁⟩ := exists_of_mem_xPts r₁
  obtain ⟨j₂, -, x₂, rfl, hx₂⟩ := exists_of_mem_xPts r₂
  have hy₁₂ : y₁ ≠ y₂ := fun h => h₁₂ (by rw [h])
  have hx₁₂ : x₁ ≠ x₂ := fun h => hq₁₂ (by rw [h])
  -- power of the origin
  have py12 := prod_of_two_roots (hy _ hp₁.1) (hy _ hp₂.1) hy₁₂
  have px12 := prod_of_two_roots (hx _ hq₁.1) (hx _ hq₂.1) hx₁₂
  have hprod : y₁ * y₂ = x₁ * x₂ := by rw [py12, px12]; ring
  have habs : (3 : ℝ) ^ (k₁ + 1) * 3 ^ (k₂ + 1) = 2 ^ (j₁ + 1) * 2 ^ (j₂ + 1) := by
    have := congrArg abs hprod
    rwa [abs_mul, abs_mul, hy₁, hy₂, hx₁, hx₂] at this
  have hnat : (3 : ℕ) ^ (k₁ + 1) * 3 ^ (k₂ + 1) = 2 ^ (j₁ + 1) * 2 ^ (j₂ + 1) := by
    exact_mod_cast habs
  have hodd : Odd ((3 : ℕ) ^ (k₁ + 1) * 3 ^ (k₂ + 1)) :=
    (Odd.pow (by decide)).mul (Odd.pow (by decide))
  have heven : Even ((2 : ℕ) ^ (j₁ + 1) * 2 ^ (j₂ + 1)) :=
    (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
  rw [hnat] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) heven

lemma noFourConcyclic_config (m : ℕ) : NoFourConcyclic (config m : Set ℝ²) := by
  intro T hT h4
  obtain ⟨S, rfl⟩ := ((config m).finite_toSet.subset hT).exists_finset_coe
  rw [Set.ncard_coe_finset] at h4
  exact not_cospherical_four m S (by exact_mod_cast hT) h4

/-! ### Few distinct distances from every point -/

lemma card_image_dist_xPts_le (m : ℕ) (Y : ℝ) :
    #((xPts m).image fun p => dist p (py Y)) ≤ m := by
  unfold xPts
  rw [image_union, image_image, image_image]
  have : ((fun p : ℝ² => dist p (py Y)) ∘ fun j : ℕ => px (-(2 : ℝ) ^ (j + 1))) =
      ((fun p : ℝ² => dist p (py Y)) ∘ fun j : ℕ => px ((2 : ℝ) ^ (j + 1))) := by
    funext j
    simp only [Function.comp, dist_px_py, neg_sq]
  rw [this, union_idempotent]
  exact card_image_le.trans (by simp)

lemma card_image_dist_yPts_le (m : ℕ) (X : ℝ) :
    #((yPts m).image fun p => dist p (px X)) ≤ m := by
  unfold yPts
  rw [image_union, image_image, image_image]
  have : ((fun p : ℝ² => dist p (px X)) ∘ fun k : ℕ => py (-(3 : ℝ) ^ (k + 1))) =
      ((fun p : ℝ² => dist p (px X)) ∘ fun k : ℕ => py ((3 : ℝ) ^ (k + 1))) := by
    funext k
    simp only [Function.comp, dist_py_px, neg_sq]
  rw [this, union_idempotent]
  exact card_image_le.trans (by simp)

/-- Generic counting bound: a point `u ∈ B` with `#B = 2m` sees at most `2m - 1` distances
within `B` and at most `m` distances to `C`. -/
lemma dd_le (B C : Finset ℝ²) (u : ℝ²) (m : ℕ) (hu : u ∈ B) (hB : #B = 2 * m)
    (hC : #(C.image fun p => dist p u) ≤ m) :
    distinctDistancesFrom (B ∪ C) u ≤ 2 * m - 1 + m := by
  unfold distinctDistancesFrom
  calc #(((B ∪ C).erase u).image fun p => dist p u)
      ≤ #(((B.erase u) ∪ C).image fun p => dist p u) := by
        apply card_le_card
        apply image_subset_image
        intro p hp
        rw [mem_erase, mem_union] at hp
        rw [mem_union, mem_erase]
        tauto
    _ = #(((B.erase u).image fun p => dist p u) ∪ (C.image fun p => dist p u)) := by
        rw [image_union]
    _ ≤ #((B.erase u).image fun p => dist p u) + #(C.image fun p => dist p u) := card_union_le _ _
    _ ≤ #(B.erase u) + m := Nat.add_le_add card_image_le hC
    _ = 2 * m - 1 + m := by rw [card_erase_of_mem hu, hB]

lemma dd_lt (m : ℕ) (hm : 1 ≤ m) : ∀ x ∈ config m, distinctDistancesFrom (config m) x < 3 * m := by
  intro u hu
  rw [config, mem_union] at hu
  rcases hu with hu | hu
  · obtain ⟨-, -, Y, rfl, -⟩ := exists_of_mem_yPts hu
    have := dd_le (yPts m) (xPts m) (py Y) m hu (card_yPts m) (card_image_dist_xPts_le m Y)
    rw [config]
    omega
  · obtain ⟨-, -, X, rfl, -⟩ := exists_of_mem_xPts hu
    have := dd_le (xPts m) (yPts m) (px X) m hu (card_xPts m) (card_image_dist_yPts_le m X)
    rw [config, union_comm]
    omega

/-! ### Main statements (matching formal-conjectures) -/

/-- `Erdos654.erdos_654.variants.feng` -/
theorem feng (m : ℕ) (hm : 10 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m :=
  ⟨config m, card_config m, noFourConcyclic_config m, dd_lt m (by omega)⟩

/-- `Erdos654.erdos_654.parts.i`: it is false that some point always has `(1-o(1))n`
distinct distances. -/
theorem parts_i :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  intro H
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (H (1 / 8) (by norm_num))
  set m := max N 10 with hm
  obtain ⟨A, hA, hAc, hAd⟩ := feng m (le_max_right _ _)
  have h4 : N ≤ 4 * m := by have := le_max_left N 10; omega
  obtain ⟨x, hx, hlt⟩ := hN (4 * m) h4 A hA hAc
  have h1 : (distinctDistancesFrom A x : ℝ) < 3 * m := by exact_mod_cast hAd x hx
  have hm10 : (10 : ℝ) ≤ m := by exact_mod_cast le_max_right N 10
  push_cast at hlt
  linarith

end Erdos654Proof

end
