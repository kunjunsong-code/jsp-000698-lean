/-
JSP-000698 — the concrete cycle-plus-triangles multigraph, edge-indexed.

Vertices `Fin (3*n)`.  Edge occurrences are indexed by `α = Fin (3*n) ⊕ (Fin n × Fin 3)`:

* `Sum.inl i`      : the Hamilton-cycle edge `i → i+1` (indices mod `3*n`);
* `Sum.inr (k, j)` : the side `tri (k,j) → tri (k, j+1)` of triangle `k`.

Since the Hamilton cycle and the triangles may share edges, `cptE` is a map into
`Fin (3*n) × Fin (3*n)` rather than an injective edge set: coincident edges are recorded as
distinct occurrences, exactly as `Jsp.EdgeIndexed` requires.  A proper 3-coloring of this
multigraph — a coloring making the two endpoints of *every* occurrence different — is exactly
a proper 3-coloring of the cycle-plus-triangles graph.

`cpt_three_coloring` is the final Alon–Tarsi reduction: non-vanishing of the coefficient of
`∏_v x_v²` in the edge polynomial of `cptE` yields a proper 3-coloring.  The non-vanishing of
that coefficient for this `cptE` is the remaining research target (`Jsp.CPT698Coeff`).
-/
import Jsp.EdgeIndexed

namespace Jsp698

open MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- Cyclic successor on `Fin (3*n)`: `i ↦ i+1 (mod 3*n)`. -/
def cycleSucc (i : Fin (3 * n)) : Fin (3 * n) :=
  if h : i.val + 1 = 3 * n then ⟨0, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- Edge map of the concrete cycle-plus-triangles multigraph. -/
def cptE (tri : Fin n × Fin 3 ↪ Fin (3 * n)) :
    (Fin (3 * n) ⊕ (Fin n × Fin 3)) → Fin (3 * n) × Fin (3 * n)
  | Sum.inl i => (i, cycleSucc i)
  | Sum.inr kj => (tri kj, tri ⟨kj.1, kj.2 + 1⟩)

/-- **Final reduction.**  A non-vanishing coefficient of `∏_v x_v²` in the edge polynomial of
the concrete cycle-plus-triangles multigraph yields a proper 3-coloring. -/
theorem cpt_three_coloring (tri : Fin n × Fin 3 ↪ Fin (3 * n))
    (hcoeff : (edgePolyI (cptE tri)).coeff (twoIndexI (V := Fin (3 * n))) ≠ 0) :
    ∃ c : Fin (3 * n) → Fin 3,
      (∀ i, c i ≠ c (cycleSucc i)) ∧
        (∀ k j, c (tri (k, j)) ≠ c (tri (k, j + 1))) := by
  have hcard : Fintype.card (Fin (3 * n) ⊕ (Fin n × Fin 3))
      = 2 * Fintype.card (Fin (3 * n)) := by
    simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  have hlt : (edgePolyI (cptE tri)).totalDegree
      ≤ (twoIndexI (V := Fin (3 * n))).degree := by
    calc (edgePolyI (cptE tri)).totalDegree
        ≤ Fintype.card (Fin (3 * n) ⊕ (Fin n × Fin 3)) := totalDegree_edgePolyI _
      _ = 2 * Fintype.card (Fin (3 * n)) := hcard
      _ = (twoIndexI (V := Fin (3 * n))).degree := (twoIndexI_degree).symm
  have hle : (twoIndexI (V := Fin (3 * n))).degree
      ≤ (edgePolyI (cptE tri)).totalDegree :=
    MvPolynomial.le_totalDegree (by
      rw [MvPolynomial.mem_support_iff]; exact hcoeff)
  have hdeg : (edgePolyI (cptE tri)).totalDegree
      = (twoIndexI (V := Fin (3 * n))).degree := le_antisymm hlt hle
  obtain ⟨c, hc⟩ := exists_three_coloring_of_coeff_ne_zero_I (cptE tri) hcoeff hdeg
  exact ⟨c, fun i => hc (Sum.inl i), fun k j => hc (Sum.inr (k, j))⟩

end Jsp698
