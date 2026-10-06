/-
JSP-000698 — transport from the concrete cycle-plus-triangles multigraph to the general
statement `Jsp698Statement`.

`Jsp.CPT698` proves the final Alon–Tarsi reduction for the *concrete* multigraph whose
vertices are `Fin (3*n)` and whose triangles are enumerated by an embedding
`tri : Fin n × Fin 3 ↪ Fin (3*n)`.  Here we connect an arbitrary graph satisfying the
abstract `IsCPTGraph` predicate to that concrete model:

* the `n` fibres `{v // f v = k}` of `f` (each of cardinality `3`) are enumerated by
  `Fin 3` via `Fintype.equivFinOfCardEq`, yielding an embedding `tri`;
* the Hamilton-cycle edges and the fibres of the abstract graph match the cycle edges and
  triangle sides of `cptE` up to the relabelling `e : V ≃ Fin (3*n)`;
* a proper coloring of the concrete multigraph therefore pulls back along `e` to a proper
  coloring of the abstract graph.

The result reduces the full statement `Jsp698Statement` to the single remaining (research
level) coefficient computation `c5`: non-vanishing of `coeff (∏_v x_v²)` for `cptE`.
-/
import Jsp.CPT698
import Jsp.CyclePlusTriangles

namespace Jsp698

variable {n : ℕ}

/-- The value of the cyclic successor is `(i + 1) mod (3 * n)`. -/
lemma cycleSucc_val (i : Fin (3 * n)) :
    (cycleSucc i).val = (i.val + 1) % (3 * n) := by
  rw [cycleSucc]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt]; have := i.isLt; omega

/-- In `Fin 3`, two distinct elements are cyclically consecutive. -/
lemma fin3_ne_iff {t1 t2 : Fin 3} (h : t1 ≠ t2) : t2 = t1 + 1 ∨ t1 = t2 + 1 := by
  fin_cases t1 <;> fin_cases t2 <;> simp_all

/-- **Transport.**  If the coefficient of `∏_v x_v²` does not vanish for every concrete
cycle-plus-triangles multigraph, then every cycle-plus-triangles graph is 3-colorable.  This
reduces `Jsp698Statement` to the single coefficient computation. -/
theorem jsp698_of_coeff_ne_zero
    (hcoeff : ∀ {n : ℕ} (tri : Fin n × Fin 3 ↪ Fin (3 * n)),
        (edgePolyI (cptE tri)).coeff (twoIndexI (V := Fin (3 * n))) ≠ 0) :
    Jsp698Statement := by
  intro V _ G hG
  obtain ⟨n, e, f, hcard, hadj⟩ := hG
  classical
  let F : (k : Fin n) → Fin 3 ≃ {v : V // f v = k} :=
    fun k => (Fintype.equivFinOfCardEq (hcard k)).symm
  let g : Fin n × Fin 3 → Fin (3 * n) := fun p => e ((F p.1 p.2).1)
  have hg_inj : Function.Injective g := by
    rintro ⟨k1, t1⟩ ⟨k2, t2⟩ h
    have h1 : (F k1 t1).1 = (F k2 t2).1 := e.injective h
    have hk : k1 = k2 := by
      have hf : f (F k1 t1).1 = f (F k2 t2).1 := by rw [h1]
      rwa [(F k1 t1).2, (F k2 t2).2] at hf
    subst hk
    have h2 : F k1 t1 = F k1 t2 := Subtype.ext h1
    exact Prod.ext rfl ((F k1).injective h2)
  let tri : Fin n × Fin 3 ↪ Fin (3 * n) := ⟨g, hg_inj⟩
  have htri : ∀ (k : Fin n) (t : Fin 3), tri (k, t) = e ((F k t).1) := fun k t => rfl
  have hsurj : ∀ (k : Fin n) (v : V), f v = k → ∃ t : Fin 3, e v = tri (k, t) := by
    intro k v hv
    obtain ⟨t, ht⟩ := (F k).surjective ⟨v, hv⟩
    refine ⟨t, ?_⟩
    have hval : (F k t).1 = v := congrArg Subtype.val ht
    rw [htri, hval]
  obtain ⟨c, hcyc, htri_adj⟩ := cpt_three_coloring tri (hcoeff tri)
  refine ⟨fun v => c (e v), ?_⟩
  intro u v huv
  show c (e u) ≠ c (e v)
  rw [hadj u v] at huv
  rcases huv with h | ⟨hne, hfib⟩
  · rcases h with h | h
    · have hev : e v = cycleSucc (e u) := (Fin.ext (by rw [cycleSucc_val, h])).symm
      rw [hev]; exact hcyc (e u)
    · have heu : e u = cycleSucc (e v) := (Fin.ext (by rw [cycleSucc_val, h])).symm
      rw [heu]; exact (hcyc (e v)).symm
  · obtain ⟨t1, ht1⟩ := hsurj (f u) u rfl
    obtain ⟨t2, ht2⟩ := hsurj (f u) v (by rw [hfib])
    have htne : t1 ≠ t2 := by
      intro hh
      exact hne (e.injective (by rw [ht1, ht2, hh]))
    have hne3 : ∀ (k : Fin n) (a b : Fin 3), a ≠ b →
        c (tri (k, a)) ≠ c (tri (k, b)) := by
      intro k a b h
      rcases fin3_ne_iff h with h' | h'
      · rw [h']; exact htri_adj k a
      · rw [h']; exact (htri_adj k b).symm
    rw [ht1, ht2]
    exact hne3 (f u) t1 t2 htne

end Jsp698
