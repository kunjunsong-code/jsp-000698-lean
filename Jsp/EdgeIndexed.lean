/-
JSP-000698 — edge-indexed graph polynomial framework.

The cycle-plus-triangles graph is naturally a *multigraph*: the Hamilton cycle and the
triangles may share edges, so an edge set must be counted with multiplicity.  We therefore
index edges by an arbitrary finite type `α` via a map `E : α → V × V` (each `a : α` is one
edge occurrence, ordered from `(E a).1` to `(E a).2`, giving the orientation).

This file redoes the algebraic reduction of `Jsp.Reduction` / `Jsp.AlonTarsi` in that
edge-indexed setting, sorry-free:

* `edgePolyI E = ∏ a, (X (E a).1 - X (E a).2)`;
* the coefficient of a multi-index `t` is the signed count of those sub-multisets whose
  in/out exponent vector equals `t` (`coeff_edgePolyI_eq_sum`);
* for a two-out-regular orientation (`outIdxI E = twoIndexI`) the coefficient of the
  all-`2` index is the Alon–Tarsi quantity `∑_{S Eulerian} (-1)^{|S|}` (`coeff_twoIndexI`);
* and non-vanishing of that coefficient forces a proper 3-coloring
  (`exists_three_coloring_of_coeff_ne_zero_I`), via Mathlib's Combinatorial Nullstellensatz.
-/
import Mathlib

namespace Jsp698

open MvPolynomial
open scoped BigOperators

variable {α V : Type*}

/-- Graph polynomial of an edge-indexed multigraph: `∏ a, (x_{(E a).1} - x_{(E a).2})`. -/
noncomputable def edgePolyI [Fintype α] [DecidableEq V] (E : α → V × V) : MvPolynomial V ℚ :=
  ∏ a : α, (X (E a).1 - X (E a).2)

/-- The multi-index `v ↦ 2`. -/
noncomputable def twoIndexI [Fintype V] : V →₀ ℕ := ∑ v : V, Finsupp.single v 2

/-- Out-degree exponent vector over a finite set of edges indexed by `S`. -/
noncomputable def outIdxF [DecidableEq V] (E : α → V × V) (S : Finset α) : V →₀ ℕ :=
  ∑ a ∈ S, Finsupp.single (E a).1 1

/-- In-degree exponent vector over a finite set of edges indexed by `S`. -/
noncomputable def inIdxF [DecidableEq V] (E : α → V × V) (S : Finset α) : V →₀ ℕ :=
  ∑ a ∈ S, Finsupp.single (E a).2 1

lemma twoIndexI_apply [Fintype V] [DecidableEq V] (v : V) : (twoIndexI (V := V)) v = 2 := by
  classical
  simp [twoIndexI, Finsupp.single_apply]

/-- The degree of the all-`2` index is twice the number of vertices. -/
lemma twoIndexI_degree [Fintype V] :
    (twoIndexI (V := V)).degree = 2 * Fintype.card V := by
  classical
  have hsupp : (twoIndexI (V := V)).support = Finset.univ := by
    ext v
    simp [Finsupp.mem_support_iff, twoIndexI_apply]
  simp [Finsupp.degree, hsupp, twoIndexI_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.mul_comm]

variable [Fintype α] [DecidableEq α] [DecidableEq V]

omit [Fintype α] [DecidableEq V] in
lemma prod_X_proj_eq_monomial (E : α → V × V) (S : Finset α) (p : V × V → V) :
    (∏ a ∈ S, (X (p (E a)) : MvPolynomial V ℚ)) =
      monomial (∑ a ∈ S, Finsupp.single (p (E a)) 1) 1 := by
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X, monomial_mul]
    simp

lemma prod_fst_eq_monomial (E : α → V × V) (S : Finset α) :
    (∏ a ∈ S, (X (E a).1 : MvPolynomial V ℚ)) = monomial (outIdxF E S) 1 :=
  prod_X_proj_eq_monomial E S Prod.fst

lemma prod_snd_eq_monomial (E : α → V × V) (S : Finset α) :
    (∏ a ∈ S, (X (E a).2 : MvPolynomial V ℚ)) = monomial (inIdxF E S) 1 :=
  prod_X_proj_eq_monomial E S Prod.snd

omit [Fintype α] [DecidableEq α] in
lemma neg_one_pow_eq_C (n : ℕ) :
    ((-1 : MvPolynomial V ℚ) ^ n) = C ((-1 : ℚ) ^ n) := by
  have h : (-1 : MvPolynomial V ℚ) = C (-1) := by rw [map_neg, map_one]
  rw [h, ← map_pow]

/-- **Edge-indexed Alon–Tarsi coefficient identity.** -/
theorem coeff_edgePolyI_eq_sum (E : α → V × V) (t : V →₀ ℕ) :
    (edgePolyI E).coeff t =
      ∑ S ∈ Finset.univ.powerset,
        (if outIdxF E (Finset.univ \ S) + inIdxF E S = t then ((-1 : ℚ) ^ S.card) else 0) := by
  classical
  simp only [edgePolyI]
  rw [Finset.prod_sub (fun a => (X (E a).1 : MvPolynomial V ℚ))
    (fun a => (X (E a).2 : MvPolynomial V ℚ)) Finset.univ, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [neg_one_pow_eq_C, prod_fst_eq_monomial E (Finset.univ \ S), prod_snd_eq_monomial E S]
  rw [mul_assoc, monomial_mul, C_mul_monomial, MvPolynomial.coeff_monomial]
  simp

lemma outIdxF_sdiff_add (E : α → V × V) (S : Finset α) :
    outIdxF E (Finset.univ \ S) + outIdxF E S = outIdxF E Finset.univ := by
  unfold outIdxF
  rw [Finset.sum_sdiff (Finset.subset_univ S)]

/-- **Edge-indexed Alon–Tarsi identity, two-regular form.**

If every vertex has out-degree `2`, the coefficient of the all-`2` index equals the signed
count of balanced (Eulerian) sub-multisets. -/
theorem coeff_twoIndexI [Fintype V] (E : α → V × V)
    (hout : outIdxF E Finset.univ = twoIndexI (V := V)) :
    (edgePolyI E).coeff (twoIndexI (V := V)) =
      ∑ S ∈ Finset.univ.powerset,
        (if inIdxF E S = outIdxF E S then ((-1 : ℚ) ^ S.card) else 0) := by
  classical
  rw [coeff_edgePolyI_eq_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hsplit := outIdxF_sdiff_add E S
  have hcond : (outIdxF E (Finset.univ \ S) + inIdxF E S = twoIndexI (V := V)) ↔
      (inIdxF E S = outIdxF E S) := by
    rw [← hout, ← hsplit]
    constructor
    · intro hh
      ext v
      have hv : outIdxF E (Finset.univ \ S) v + inIdxF E S v =
          outIdxF E (Finset.univ \ S) v + outIdxF E S v := by
        simpa using congrArg (fun f : V →₀ ℕ => f v) hh
      exact Nat.add_left_cancel hv
    · intro hh; rw [hh]
  by_cases h : inIdxF E S = outIdxF E S
  · rw [if_pos (hcond.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]

/-- Total degree of the edge polynomial is at most the number of edges. -/
lemma totalDegree_edgePolyI [Fintype V] (E : α → V × V) :
    (edgePolyI E).totalDegree ≤ Fintype.card α := by
  classical
  rw [edgePolyI]
  calc (∏ a : α, (X (E a).1 - X (E a).2 : MvPolynomial V ℚ)).totalDegree
      ≤ ∑ a ∈ Finset.univ, (X (E a).1 - X (E a).2 : MvPolynomial V ℚ).totalDegree :=
        MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ _a ∈ Finset.univ, (1 : ℕ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (MvPolynomial.totalDegree_sub _ _).trans ?_
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
        simp
    _ = Fintype.card α := by simp

/-- **Reduction step (edge-indexed).** Non-vanishing of the coefficient of the all-`2` index,
together with full degree `2*|V|`, yields a proper 3-coloring. -/
theorem exists_three_coloring_of_coeff_ne_zero_I [Fintype V] (E : α → V × V)
    (hcoeff : (edgePolyI E).coeff (twoIndexI (V := V)) ≠ 0)
    (hdeg : (edgePolyI E).totalDegree = (twoIndexI (V := V)).degree) :
    ∃ c : V → Fin 3, ∀ a : α, c (E a).1 ≠ c (E a).2 := by
  classical
  have htS : ∀ v : V, (twoIndexI (V := V)) v < ({0, 1, 2} : Finset ℚ).card := by
    intro v
    rw [twoIndexI_apply]
    norm_num
  obtain ⟨s, hs, hne⟩ :=
    combinatorial_nullstellensatz_exists_eval_nonzero (edgePolyI E)
      (twoIndexI (V := V)) hcoeff hdeg (fun _ : V => ({0, 1, 2} : Finset ℚ)) htS
  have heval_eq : eval s (edgePolyI E) = ∏ a : α, (s (E a).1 - s (E a).2) := by
    simp [edgePolyI]
  have hprod : ∏ a : α, (s (E a).1 - s (E a).2) ≠ 0 := by
    rw [← heval_eq]; exact hne
  have hdiff : ∀ a : α, s (E a).1 ≠ s (E a).2 :=
    fun a => sub_ne_zero.mp ((Finset.prod_ne_zero_iff.mp hprod) a (Finset.mem_univ a))
  have hmem : ∀ v, s v = 0 ∨ s v = 1 ∨ s v = 2 := by
    intro v
    have := hs v
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  let c : V → Fin 3 := fun v => if s v = 0 then 0 else if s v = 1 then 1 else 2
  have hc : ∀ v, ((c v : Fin 3) : ℚ) = s v := by
    intro v
    rcases hmem v with h | h | h
    · simp [c, h]
    · simp [c, h]
    · have h0 : s v ≠ 0 := by rw [h]; norm_num
      have h1 : s v ≠ 1 := by rw [h]; norm_num
      simp only [c, h0, h1, if_false, h]
      norm_num
  exact ⟨c, fun a ha => hdiff a (by rw [← hc (E a).1, ← hc (E a).2, ha])⟩

end Jsp698