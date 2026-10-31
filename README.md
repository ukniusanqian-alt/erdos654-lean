# Erdős Problem 654 — Lean 4 formalization of the Aletheia counterexample

**Problem.** [erdosproblems.com/654](https://www.erdosproblems.com/654) (Justin Sun Prize catalog
[JSP-000530](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000530)).
Let $f(n)$ be such that any $n$ points in $\mathbb{R}^2$ with no four on a circle contain a point
with at least $f(n)$ distinct distances to the others. Erdős asked whether $f(n) > (1-o(1))n$.

**Answer: no.** Aletheia (T. Feng et al., *Semi-Autonomous Mathematics Discovery with Gemini: A
Case Study on the Erdős Problems*, [arXiv:2601.22401](https://arxiv.org/abs/2601.22401), §3.1,
Theorem 3) gave, for every $m \ge 10$, a set of $n = 4m$ points with no four concyclic in which
every point has fewer than $\tfrac34 n$ distinct distances.

**This repository** contains a complete, `sorry`-free Lean 4 / Mathlib proof of that counterexample,
in the exact statements used by
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/654.lean):

| formal-conjectures theorem | this repository | file |
| --- | --- | --- |
| `Erdos654.erdos_654.variants.feng` | `Erdos654Proof.feng` (restated as `Erdos654.erdos_654.variants.feng` in `Solution.lean`) | `JspLean/Erdos654.lean` |
| `Erdos654.erdos_654.parts.i` | `Erdos654Proof.parts_i` (restated as `Erdos654.erdos_654.parts.i` in `Solution.lean`) | `JspLean/Erdos654.lean` |

The definitions `NoFourConcyclic` (∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T) and
`distinctDistancesFrom` (#((points.erase pt).image (dist · pt))) are copied verbatim from
formal-conjectures (Apache-2.0, see LICENSE) so that the statements coincide; `ℝ²` is
`EuclideanSpace ℝ (Fin 2)`.

## The construction and proof (as formalized)

Points `(0, ±3^(k+1))` for `k < m` on the y-axis and `(±2^(j+1), 0)` for `j < m` on the x-axis
(`4m` points; the exponents are shifted by one relative to the paper's `K = {10,…,m+9}`, which
changes nothing in the argument).

* **No four concyclic.** A circle `(a,b,r)` meets the y-axis in points `(0,y)` with
  `a² + (y-b)² = r²`, a quadratic in `y`, so at most two such points (`eq_of_three_roots`);
  likewise for the x-axis. Four points of the set on one circle therefore split 2 + 2. Vieta gives
  `y₁y₂ = a² + b² − r² = x₁x₂` (`prod_of_two_roots`, the power of the origin), so
  `3^(k₁+1)·3^(k₂+1) = 2^(j₁+1)·2^(j₂+1)` after taking absolute values — odd = even, contradiction
  (`not_cospherical_four`).
* **Fewer than 3m distinct distances.** A point on one axis sees at most `2m − 1` distances to
  its own axis and at most `m` to the other axis, because `(±2^(j+1), 0)` are equidistant from
  every point of the y-axis (`card_image_dist_xPts_le`, `dd_le`, `dd_lt`).
* `parts_i` follows from `feng` with `ε = 1/8`.

## Layout (Palomar format)

`Challenge.lean` is the small auditable statement (imports only Mathlib, deliberate `sorry`); `Solution.lean` restates it verbatim and closes it with the library proof; `comparator.json` lists the compared theorems and definitions; `formalization.yaml` records sources, authorship and AI use.

## Reproduction

Toolchain `leanprover/lean4:v4.36.0-rc2` (`lean-toolchain`); Mathlib pinned in `lake-manifest.json`
to `9d581dfff2e41de989072ea63abf3daf69311520` (tag `v4.36.0-rc2`).

```sh
lake exe cache get          # Mathlib oleans
lake build                  # builds JspLean.Erdos654
lake env lean JspLean/Erdos654.lean   # no output = no errors
grep -nE 'sorry|admit|native_decide' JspLean/Erdos654.lean   # no matches
```

Axiom audit (append to the file or run in a scratch file importing it):

```
#print axioms Erdos654Proof.parts_i
-- 'Erdos654Proof.parts_i' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Erdos654Proof.feng
-- 'Erdos654Proof.feng' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Attribution

Mathematical solution: Aletheia / T. Feng et al. [arXiv:2601.22401](https://arxiv.org/abs/2601.22401) §3.1.
Lean formalization: written by Claude (Anthropic, Fable 5.1) directed by the repository owner,
2026-10-31. Statement definitions: google-deepmind/formal-conjectures (Apache-2.0).

---

# Erdős Problem 1033 — butterfly blow-up (also in this repository)

**Problem.** [erdosproblems.com/1033](https://www.erdosproblems.com/1033) (Bollobás–Erdős): is
`h(n) ≥ (2(√3 - 1) - o(1)) n`, where `h(n)` is the largest degree sum of a triangle guaranteed in
every `n`-vertex graph with more than `n²/4` edges? **Answer: no.**

`JspLean/Erdos1033.lean` proves `Erdos1033Proof.erdos_1033`, restated verbatim as
`Erdos1033.erdos_1033` (statement of
[formal-conjectures 1033.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1033.lean))
in `Challenge1033.lean` / `Solution1033.lean`; Comparator config `comparator1033.json`, metadata
`meta1033/formalization.yaml`.

Construction, for every `t ≥ 1`: parts `a = Fin 6 × Fin 48t`, `b = Fin 170t`, `c = Fin 48t`,
`d = e = Fin 81t`; all edges `a–b, b–c, a–d, a–e`; `(r,i) ∈ a ~ j ∈ c` iff `(i + j) mod 48t < 20t`;
`i ∈ d ~ j ∈ e` iff `(i + j) mod 81t < 25t`. Then `n = 668t`, degrees are `352t, 336t, 290t, 313t, 313t`,
`|E| = 111561 t² > n²/4`, and every triangle (type `abc` or `ade`) has degree sum `978t`, with
`978/668 = 1.46407… < 2(√3 - 1) = 1.46410…`. This adapts the butterfly blow-up of Rickyc/ChatGPT on
the erdosproblems.com forum and W. CvB's optimized note, replacing random subgraphs by circulant ones.
Axioms: `propext, Classical.choice, Quot.sound`.
