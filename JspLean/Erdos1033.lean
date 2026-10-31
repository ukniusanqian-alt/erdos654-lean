module

public import Mathlib

/-!
# Erdős Problem 1033: a blow-up of the butterfly graph

Problem (Bollobás–Erdős, see https://www.erdosproblems.com/1033): let `h(n)` be such that every
graph on `n` vertices with more than `n² / 4` edges contains a triangle whose vertices have degree
sum at least `h(n)`. Is `h(n) ≥ (2(√3 - 1) - o(1)) n`?

The answer is no. The counterexample is a blow-up of the butterfly graph (two triangles `abc`
and `ade` sharing the vertex `a`), found on the erdosproblems.com forum (June–July 2026) and
optimized in W. CvB, *Optimized density argument for Erdős 1033* (2026). This file uses an
explicit integer version of that blow-up, with partial bipartite graphs given by circulant rules
instead of random subgraphs. For every `t ≥ 1` the graph has `n = 668 t` vertices,
`111561 t²` edges (so `4|E| = 446244 t² > 446224 t² = n²`), and every triangle has degree sum
exactly `978 t`, while `978 / 668 = 1.46407… < 2(√3 - 1) = 1.46410…`.

Parts (sizes for scale `t`): `a = Fin 6 × Fin (48 t)`, `b = Fin (170 t)`, `c = Fin (48 t)`,
`d = e = Fin (81 t)`. Edges: all `a–b`, `b–c`, `a–d`, `a–e`; `(r, i) ∈ a` is joined to `j ∈ c` iff
`(i + j) mod 48t < 20 t`; `i ∈ d` is joined to `j ∈ e` iff `(i + j) mod 81t < 25 t`.
Degrees: `a: 352 t`, `b: 336 t`, `c: 290 t`, `d, e: 313 t`.
-/

open Finset SimpleGraph
open scoped Classical

@[expose] public noncomputable section

namespace Erdos1033Proof

/-- The vertex type at scale `t`: parts `a, b, c, d, e`. -/
abbrev V (t : ℕ) : Type :=
  (Fin 6 × Fin (48 * t)) ⊕ (Fin (170 * t) ⊕ (Fin (48 * t) ⊕ (Fin (81 * t) ⊕ Fin (81 * t))))

/-- The part (`0 = a, 1 = b, 2 = c, 3 = d, 4 = e`) of a vertex. -/
def part {t : ℕ} : V t → Fin 5
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr (.inl _))) => 3
  | .inr (.inr (.inr (.inr _))) => 4

/-- One orientation of the edge relation. -/
def rel {t : ℕ} : V t → V t → Prop
  | .inl _, .inr (.inl _) => True
  | .inr (.inl _), .inr (.inr (.inl _)) => True
  | .inl (_, i), .inr (.inr (.inl j)) => (i + j).val < 20 * t
  | .inl _, .inr (.inr (.inr (.inl _))) => True
  | .inl _, .inr (.inr (.inr (.inr _))) => True
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr j))) => (i + j).val < 25 * t
  | _, _ => False

/-- The blown-up butterfly graph at scale `t`. -/
def graph (t : ℕ) : SimpleGraph (V t) where
  Adj u v := rel u v ∨ rel v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by
    rcases u with ⟨r, i⟩ | b | c | d | e <;> simp [rel] at h⟩

/-- Degree coefficients per part. -/
def coef : Fin 5 → ℕ := ![352, 336, 290, 313, 313]

/-- Adjacency of the base butterfly graph on parts. -/
def baseAdj (p q : Fin 5) : Prop :=
  p ≠ q ∧ ¬ ((p = 1 ∨ p = 2) ∧ (q = 3 ∨ q = 4)) ∧ ¬ ((q = 1 ∨ q = 2) ∧ (p = 3 ∨ p = 4))

instance (p q : Fin 5) : Decidable (baseAdj p q) := by unfold baseAdj; infer_instance

theorem triangle_coef : ∀ p q r : Fin 5, baseAdj p q → baseAdj p r → baseAdj q r →
    coef p + coef q + coef r ≤ 978 := by
  decide

/-! ### Counting lemmas for the circulant rules -/

theorem sum_lt_range (m K : ℕ) (hK : K ≤ m) :
    (∑ j : Fin m, if j.val < K then 1 else 0) = K := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < K then 1 else 0) m, Finset.sum_boole]
  have : (range m).filter (· < K) = range K := by
    ext x; simp only [mem_filter, mem_range]; omega
  simp [this]

theorem sum_add_left_lt (m K : ℕ) (hK : K ≤ m) (x : Fin m) :
    (∑ j : Fin m, if (x + j).val < K then 1 else 0) = K := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp at hK; simp [hK]
  have : NeZero m := ⟨hm.ne'⟩
  rw [Fintype.sum_equiv (Equiv.addLeft x) (fun j => if (x + j).val < K then 1 else 0)
    (fun j => if j.val < K then 1 else 0) (fun j => rfl)]
  exact sum_lt_range m K hK

theorem sum_add_right_lt (m K : ℕ) (hK : K ≤ m) (x : Fin m) :
    (∑ i : Fin m, if (i + x).val < K then 1 else 0) = K := by
  simp_rw [add_comm _ x]
  exact sum_add_left_lt m K hK x

/-! ### Degrees -/

theorem degree_eq_sum (t : ℕ) (v : V t) :
    (graph t).degree v = ∑ w : V t, if (graph t).Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]

theorem degree_eq (t : ℕ) (v : V t) : (graph t).degree v = coef (part v) * t := by
  rw [degree_eq_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rcases v with ⟨r, i⟩ | b | c | d | e
  · have h := sum_add_left_lt (48 * t) (20 * t) (by omega) i
    simp [graph, rel, part, coef, h]
    ring
  · simp [graph, rel, part, coef]
    ring
  · have h := sum_add_right_lt (48 * t) (20 * t) (by omega) c
    simp [graph, rel, part, coef, h]
    ring
  · have h := sum_add_left_lt (81 * t) (25 * t) (by omega) d
    simp [graph, rel, part, coef, h]
    ring
  · have h := sum_add_right_lt (81 * t) (25 * t) (by omega) e
    simp [graph, rel, part, coef, h]
    ring

theorem card_V (t : ℕ) : Fintype.card (V t) = 668 * t := by
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

theorem card_edgeFinset (t : ℕ) : #(graph t).edgeFinset = 111561 * t ^ 2 := by
  have h := (graph t).sum_degrees_eq_twice_card_edges
  simp only [degree_eq, Fintype.sum_sum_type, Fintype.sum_prod_type, part, coef] at h
  simp only [Fin.isValue, Matrix.cons_val, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at h
  have h2 : 2 * #(graph t).edgeFinset = 2 * (111561 * t ^ 2) := by
    rw [← h]; ring
  omega

/-! ### Triangles -/

theorem part_adj {t : ℕ} {u v : V t} (h : (graph t).Adj u v) : baseAdj (part u) (part v) := by
  rcases u with ⟨r, i⟩ | b | c | d | e <;> rcases v with ⟨r', i'⟩ | b' | c' | d' | e' <;>
    simp [graph, rel] at h <;> simp [part, baseAdj] <;> decide

theorem triangle_sum_le {t : ℕ} {s : Finset (V t)} (hs : (graph t).IsNClique 3 s) :
    ∑ v ∈ s, (graph t).degree v ≤ 978 * t := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.1 hs
  have hne1 : x ≠ y := hxy.ne
  have hne2 : x ≠ z := hxz.ne
  have hne3 : y ≠ z := hyz.ne
  rw [sum_insert (by simp [hne1, hne2]), sum_insert (by simp [hne3]), sum_singleton,
    degree_eq, degree_eq, degree_eq]
  have := triangle_coef _ _ _ (part_adj hxy) (part_adj hxz) (part_adj hyz)
  nlinarith

/-! ### The real-number gap -/

theorem gap : (978 : ℝ) / 668 < 2 * (Real.sqrt 3 - 1) := by
  have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have : (978 : ℝ) / 668 + 2 < Real.sqrt 12 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-! ### Main statement (as in google-deepmind/formal-conjectures) -/

theorem erdos_1033 :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      n ^ 2 < 4 * #G.edgeFinset →
        ∃ t, G.IsNClique 3 t ∧
          (2 * (Real.sqrt 3 - 1) - ε) * n ≤ ∑ v ∈ t, (G.degree v : ℝ) := by
  intro H
  set ε : ℝ := (2 * (Real.sqrt 3 - 1) - 978 / 668) / 2 with hε_def
  have hε : ε > 0 := by have := gap; rw [hε_def]; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (H ε hε)
  set t := N + 1 with ht
  have hn : N ≤ 668 * t := by omega
  let e : V t ≃ Fin (668 * t) := Fintype.equivFinOfCardEq (card_V t)
  let G' : SimpleGraph (Fin (668 * t)) := (graph t).map e.toEmbedding
  have hedges : #G'.edgeFinset = 111561 * t ^ 2 := by
    rw [← card_edgeFinset t]
    convert card_edgeFinset_map e.toEmbedding (graph t)
  have hdeg : ∀ v : V t, G'.degree (e.toEmbedding v) = (graph t).degree v := fun v => by
    convert degree_map_apply (graph t) e.toEmbedding v
  have hE : (668 * t) ^ 2 < 4 * #G'.edgeFinset := by
    rw [hedges]
    have h1 : (668 * t) ^ 2 = 446224 * t ^ 2 := by ring
    have h2 : 0 < t ^ 2 := by positivity
    rw [h1]
    omega
  obtain ⟨s, hs, hsum⟩ := hN (668 * t) hn G' hE
  obtain ⟨s0, hs0, rfl⟩ := (isNClique_map_iff (by norm_num)).1 hs
  rw [sum_map] at hsum
  simp only [hdeg] at hsum
  have hle : (∑ v ∈ s0, ((graph t).degree v : ℝ)) ≤ 978 * t := by
    exact_mod_cast triangle_sum_le hs0
  have htpos : (0 : ℝ) < t := by positivity
  have key : (2 * (Real.sqrt 3 - 1) - ε) * ((668 * t : ℕ) : ℝ) > 978 * t := by
    have h1 : 2 * (Real.sqrt 3 - 1) - ε > 978 / 668 := by
      have := gap
      rw [hε_def]
      linarith
    have h2 : (0 : ℝ) < ((668 * t : ℕ) : ℝ) := by positivity
    calc (2 * (Real.sqrt 3 - 1) - ε) * ((668 * t : ℕ) : ℝ)
        > 978 / 668 * ((668 * t : ℕ) : ℝ) := mul_lt_mul_of_pos_right h1 h2
      _ = 978 * t := by push_cast; ring
  linarith

end Erdos1033Proof
