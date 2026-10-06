import Mathlib

/-!
# Petrov's parity theorem (arXiv:1512.06205, Theorem 1)

Given a finite index type `ι`, a finite vertex type `V`, a partition `part : V → ι`
into odd fibres, and a graph `G` on `V` such that
(H1) each fibre is independent, and
(H2) for `i ≠ j` every vertex of fibre `i` has an even number of neighbours in fibre `j`,
the number of transversals `g` whose image induces an Eulerian subgraph is odd.

The proof is the elementary mod-2 argument via "special sequences":
Step 1 reduces the parity of `|SS|` (pairs `(x, f)`) to the parity of the Eulerian
transversals; Step 2 shows `|SS|` is odd by pairing functions along the reversal of
long cycles of their functional graph, together with a leaf/2-cycle parity argument.
-/

namespace Jsp698

open Function
open Classical

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]

/-! ## Basic combinatorial objects -/

/-- The transversals: functions picking one vertex from each fibre. -/
def transvS (part : V → ι) : Finset (ι → V) :=
  Finset.univ.filter (fun x => ∀ i, part (x i) = i)

/-- Possible values of `f i`: either `i` itself, or a neighbour of `x i` among the `x j`. -/
def allowed (G : SimpleGraph V) [DecidableRel G.Adj] (x : ι → V) (i : ι) : Finset ι :=
  insert i (Finset.univ.filter (fun j => G.Adj (x i) (x j)))

/-- For a fixed `x`, the functions `f` valid at `x`. -/
def TfS (G : SimpleGraph V) [DecidableRel G.Adj] (x : ι → V) : Finset (ι → ι) :=
  Finset.univ.filter (fun f => ∀ i, f i = i ∨ G.Adj (x i) (x (f i)))

/-- For a fixed `f`, the transversals `x` valid at `f`. -/
def XfS (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] (f : ι → ι) :
    Finset (ι → V) :=
  Finset.univ.filter (fun x =>
    (∀ i, part (x i) = i) ∧ (∀ i, f i = i ∨ G.Adj (x i) (x (f i))))

/-- The "special sequences" encoded as pairs `(x, f)`. -/
def SS (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset ((ι → V) × (ι → ι)) :=
  Finset.univ.filter (fun p =>
    (∀ i, part (p.1 i) = i) ∧ (∀ i, p.2 i = i ∨ G.Adj (p.1 i) (p.1 (p.2 i))))

/-- The Eulerian transversals: every chosen vertex has an even number of neighbours
among the other chosen vertices. -/
def EulerSet (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (ι → V) :=
  Finset.univ.filter (fun x =>
    (∀ i, part (x i) = i) ∧
      (∀ i, Even (Finset.univ.filter (fun j => G.Adj (x i) (x j))).card))

/-! ## Parity helpers -/

/-- A product of natural numbers is odd iff every factor is odd. -/
lemma odd_finset_prod {α : Type*} (s : Finset α) (g : α → ℕ) :
    Odd (∏ i ∈ s, g i) ↔ ∀ i ∈ s, Odd (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Nat.odd_mul, ih]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h1
        · exact h2 i hi
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
          fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- If `σ` is a fixed-point-free involution preserving `s` and `h` is `σ`-invariant on `s`,
then `∑ a ∈ s, h a` is even. -/
lemma even_sum_of_involution {α : Type*} (s : Finset α)
    (h : α → ℕ) (σ : α → α) (hmem : ∀ a ∈ s, σ a ∈ s)
    (hinv : ∀ a ∈ s, σ (σ a) = a) (hne : ∀ a ∈ s, σ a ≠ a)
    (heq : ∀ a ∈ s, h (σ a) = h a) : Even (∑ a ∈ s, h a) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have hsub : {x, σ x} ⊆ s := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · rw [Finset.mem_singleton] at hy; exact hy ▸ hmem x hx
  have hss : s \ {x, σ x} ⊂ s :=
    (Finset.ssubset_iff_of_subset (fun a ha => (Finset.mem_sdiff.mp ha).1)).mpr ⟨x, hx, by simp⟩
  have hmem' : ∀ a ∈ s \ {x, σ x}, σ a ∈ s \ {x, σ x} := by
    intro a ha
    obtain ⟨has, hna⟩ := Finset.mem_sdiff.mp ha
    have hnx : a ≠ x := fun h => hna (by simp [h])
    have hnsx : a ≠ σ x := fun h => hna (by simp [h])
    refine Finset.mem_sdiff.mpr ⟨hmem a has, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hnsx (by rw [← hinv a has, h]), fun h => hnx (by rw [← hinv a has, ← hinv x hx, h])⟩
  have hinv' : ∀ a ∈ s \ {x, σ x}, σ (σ a) = a := fun a ha => hinv a (Finset.mem_sdiff.mp ha).1
  have hne' : ∀ a ∈ s \ {x, σ x}, σ a ≠ a := fun a ha => hne a (Finset.mem_sdiff.mp ha).1
  have heq' : ∀ a ∈ s \ {x, σ x}, h (σ a) = h a := fun a ha => heq a (Finset.mem_sdiff.mp ha).1
  have hrec := ih (s \ {x, σ x}) hss hmem' hinv' hne' heq'
  have hpair : (∑ a ∈ ({x, σ x} : Finset α), h a) = 2 * h x := by
    rw [Finset.sum_pair (Ne.symm (hne x hx)), heq x hx, two_mul]
  rw [← Finset.sum_sdiff hsub, hpair]
  exact hrec.add ⟨h x, by ring⟩

/-! ## Step 1 -/

/-- The number of valid `f` for a fixed `x` is the product of the sizes of the `allowed` sets. -/
lemma TfS_card (G : SimpleGraph V) [DecidableRel G.Adj] (x : ι → V) :
    (TfS G x).card
      = ∏ i, ((Finset.univ.filter (fun j => G.Adj (x i) (x j))).card + 1) := by
  have hT : TfS G x = Finset.univ.filter (fun f : ι → ι => ∀ i, f i ∈ allowed G x i) := by
    apply Finset.filter_congr
    intro f _
    simp only [allowed, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hT]
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr Equiv.subtypePiEquivPi, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_coe, allowed]
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact G.irrefl)]

/-- `∏ i, (d i + 1)` is odd iff every `d i` is even. -/
lemma odd_prod_add_one (x : ι → V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Odd (∏ i, ((Finset.univ.filter (fun j => G.Adj (x i) (x j))).card + 1))
      ↔ ∀ i, Even (Finset.univ.filter (fun j => G.Adj (x i) (x j))).card := by
  rw [odd_finset_prod]
  constructor
  · intro h i
    have := h i (Finset.mem_univ i)
    rwa [Nat.odd_add_one, Nat.not_odd_iff_even] at this
  · intro h i _
    rw [Nat.odd_add_one, Nat.not_odd_iff_even]
    exact h i

/-- `|SS|` as a sum over `f` of `|XfS f|`. -/
lemma SS_card_f (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (SS part G).card
      = ∑ f ∈ (Finset.univ : Finset (ι → ι)), (XfS part G f).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_nbij' (fun p => (⟨p.2, p.1⟩ : Sigma fun _ : ι → ι => ι → V))
    (fun q => (q.2, q.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, XfS, Finset.mem_filter]
    exact ⟨hp.1, hp.2⟩
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, XfS, Finset.mem_filter] at hq
    simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hq.1, hq.2⟩
  · intro p _
    cases p
    rfl
  · rintro ⟨f, x⟩ _
    rfl

/-- `|SS|` as a sum over transversals `x` of `|TfS x|`. -/
lemma SS_card_x (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (SS part G).card = ∑ x ∈ transvS part, (TfS G x).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_nbij' (fun p => (⟨p.1, p.2⟩ : Sigma fun _ : ι → V => ι → ι))
    (fun q => (q.1, q.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · simp only [transvS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp.1
    · simp only [TfS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp.2
  · intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hq1, hq2⟩ := hq
    simp only [SS, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · simpa only [transvS, Finset.mem_filter, Finset.mem_univ, true_and] using hq1
    · simpa only [TfS, Finset.mem_filter, Finset.mem_univ, true_and] using hq2
  · intro p _
    cases p
    rfl
  · rintro ⟨x, f⟩ _
    rfl

/-- **Step 1.** `|SS|` is odd iff the number of Eulerian transversals is odd. -/
theorem odd_SS_iff_odd_Euler (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Odd (SS part G).card ↔ Odd (EulerSet part G).card := by
  rw [SS_card_x]
  simp_rw [TfS_card]
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hset : (transvS part).filter
      (fun x => Odd (∏ i, ((Finset.univ.filter (fun j => G.Adj (x i) (x j))).card + 1)))
      = EulerSet part G := by
    ext x
    simp only [Finset.mem_filter, EulerSet, transvS, Finset.mem_univ, true_and]
    exact and_congr_right (fun _ => odd_prod_add_one x G)
  rw [hset]

/-! ## Involutions and parity -/

/-- A fixed-point-free involution on a finite type forces even cardinality. -/
lemma even_card_of_involutive {α : Type*} [Fintype α] (σ : α → α)
    (hσ : Function.Involutive σ) (hne : ∀ x, σ x ≠ x) :
    Even (Fintype.card α) := by
  classical
  letI : LinearOrder α :=
    LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  set A : Finset α := Finset.univ.filter (fun x => x < σ x) with hA
  set B : Finset α := Finset.univ.filter (fun x => σ x < x) with hB
  have hBA : B = A.image σ := by
    ext y; constructor
    · intro hy
      rw [hB] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine Finset.mem_image.mpr ⟨σ y, ?_, ?_⟩
      · rw [hA]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hσ y]; exact hy
      · exact hσ y
    · intro hy
      rw [hB]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rw [hA] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hσ x]; exact hx
  have hUnion : A ∪ B = Finset.univ := by
    rw [hA, hB, ← Finset.filter_or]
    exact Finset.filter_true_of_mem (fun x _ => by
      rcases lt_trichotomy x (σ x) with h | h | h
      · exact Or.inl h
      · exact absurd h.symm (hne x)
      · exact Or.inr h)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [hA] at hxA; rw [hB] at hxB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    exact absurd hxA (not_lt.mpr hxB.le)
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hUnion, hBA, Finset.card_image_of_injective _ hσ.injective, Finset.card_univ] at hcard
  exact ⟨A.card, hcard⟩

/-- Every finite type of even cardinality admits a fixed-point-free involution. -/
lemma exists_involutive_no_fixed_of_even {α : Type*} [Fintype α]
    (h : Even (Fintype.card α)) :
    ∃ σ : α → α, Function.Involutive σ ∧ ∀ x, σ x ≠ x := by
  classical
  by_cases hempty : IsEmpty α
  · haveI := hempty
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  · haveI : Nonempty α := not_isEmpty_iff.mp hempty
    have hcard : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ‹Nonempty α›
    have hn2 : Fintype.card α % 2 = 0 := Nat.even_iff.mp h
    refine ⟨fun x => (Fintype.equivFin α).symm
        ((Fintype.equivFin α x) + (⟨Fintype.card α / 2, by omega⟩ : Fin (Fintype.card α))),
      ?_, ?_⟩
    · intro x
      have hcc : (⟨Fintype.card α / 2, by omega⟩ : Fin (Fintype.card α)) +
          ⟨Fintype.card α / 2, by omega⟩ = 0 := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_zero]
        have hsum : Fintype.card α / 2 + Fintype.card α / 2 = Fintype.card α := by omega
        rw [hsum]; simp
      simp only [Equiv.apply_symm_apply]
      rw [add_assoc, hcc, add_zero, Equiv.symm_apply_apply]
    · intro x hx
      have h1 : (Fintype.equivFin α) x + (⟨Fintype.card α / 2, by omega⟩ : Fin (Fintype.card α))
          = (Fintype.equivFin α) x := by
        have := congrArg (Fintype.equivFin α) hx
        simpa [Equiv.apply_symm_apply] using this
      have hc0 : (⟨Fintype.card α / 2, by omega⟩ : Fin (Fintype.card α)) = 0 := by
        have h2 : (Fintype.equivFin α) x + (⟨Fintype.card α / 2, by omega⟩ : Fin (Fintype.card α))
            = (Fintype.equivFin α) x + 0 := by rw [add_zero]; exact h1
        exact add_left_cancel h2
      have hc : Fintype.card α / 2 = 0 := by
        have := congrArg Fin.val hc0; simpa using this
      omega

/-! ## Step 2: reversal of the cycles of a functional graph -/

/-- A function has a *long cycle* if some point has minimal period at least `3`. -/
def HasLongCycle (f : ι → ι) : Prop := ∃ i, 3 ≤ Function.minimalPeriod f i

/-- Reverse every cycle of the functional graph of `f`, keeping the attached trees. -/
noncomputable def revF (f : ι → ι) : ι → ι :=
  fun i => if h : i ∈ Function.periodicPts f then
    f^[Function.minimalPeriod f i - 1] i else f i

lemma revF_of_not_periodic (f : ι → ι) {i : ι} (h : i ∉ Function.periodicPts f) :
    revF f i = f i := by
  simp only [revF, dif_neg h]

lemma revF_of_periodic (f : ι → ι) {i : ι} (h : i ∈ Function.periodicPts f) :
    revF f i = f^[Function.minimalPeriod f i - 1] i := by
  simp only [revF, dif_pos h]

lemma apply_revF_of_periodic (f : ι → ι) {i : ι} (h : i ∈ Function.periodicPts f) :
    f (revF f i) = i := by
  rw [revF_of_periodic f h,
    ← Function.iterate_succ_apply' f (Function.minimalPeriod f i - 1) i,
    show (Function.minimalPeriod f i - 1).succ = Function.minimalPeriod f i from by
      have := Function.minimalPeriod_pos_of_mem_periodicPts h; omega,
    Function.iterate_minimalPeriod]

/-! ### The rank: distance from a point to its eventual cycle -/

lemma exists_iterate_mem_periodicPts (f : ι → ι) (i : ι) :
    ∃ m, f^[m] i ∈ Function.periodicPts f := by
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, f^[m] i = f^[n] i ∧ m ≠ n := by
    simpa [Function.Injective] using
      not_injective_infinite_finite (fun t : ℕ => f^[t] i)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨m, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) ?_⟩
    show f^[n - m] (f^[m] i) = f^[m] i
    rw [(Function.iterate_add_apply f (n - m) m i).symm, Nat.sub_add_cancel hlt.le, heq]
  · refine ⟨n, Function.mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) ?_⟩
    show f^[m - n] (f^[n] i) = f^[n] i
    rw [(Function.iterate_add_apply f (m - n) n i).symm, Nat.sub_add_cancel hlt.le, ← heq]

/-- `rank f i` is the first time the orbit of `i` under `f` becomes periodic. -/
noncomputable def rank (f : ι → ι) (i : ι) : ℕ :=
  Nat.find (exists_iterate_mem_periodicPts f i)

lemma rank_spec (f : ι → ι) (i : ι) :
    f^[rank f i] i ∈ Function.periodicPts f :=
  Nat.find_spec (exists_iterate_mem_periodicPts f i)

lemma rank_min (f : ι → ι) (i : ι) {m : ℕ}
    (h : f^[m] i ∈ Function.periodicPts f) : rank f i ≤ m :=
  Nat.find_min' (exists_iterate_mem_periodicPts f i) h

lemma rank_eq_zero_iff (f : ι → ι) (i : ι) :
    rank f i = 0 ↔ i ∈ Function.periodicPts f := by
  constructor
  · intro h
    have := rank_spec f i
    rw [h] at this
    exact this
  · intro h
    exact Nat.eq_zero_of_le_zero (rank_min f i (by simpa using h))

lemma rank_pos_iff (f : ι → ι) (i : ι) :
    0 < rank f i ↔ i ∉ Function.periodicPts f := by
  rw [← not_iff_not]
  simp only [not_lt, Nat.le_zero, rank_eq_zero_iff, not_not]

lemma rank_apply (f : ι → ι) (i : ι) (h : i ∉ Function.periodicPts f) :
    rank f (f i) = rank f i - 1 := by
  have hpos : 0 < rank f i := (rank_pos_iff f i).mpr h
  refine le_antisymm ?_ ?_
  · apply rank_min
    simpa [show f^[rank f i - 1] (f i) = f^[rank f i] i from by
      rw [(Function.iterate_succ_apply f (rank f i - 1) i).symm,
        show (rank f i - 1).succ = rank f i from by omega]] using rank_spec f i
  · have h2 : f^[rank f (f i) + 1] i ∈ Function.periodicPts f := by
      simpa [Function.iterate_succ_apply f (rank f (f i)) i] using rank_spec f (f i)
    have := rank_min f i h2
    omega

/-! ### Reversal preserves validity -/

lemma val_imp_val_revF (G : SimpleGraph V) [DecidableRel G.Adj] (x : ι → V) (f : ι → ι)
    (hv : ∀ i, f i = i ∨ G.Adj (x i) (x (f i))) :
    ∀ j, revF f j = j ∨ G.Adj (x j) (x (revF f j)) := by
  intro j
  by_cases hj : j ∈ Function.periodicPts f
  · rw [revF_of_periodic f hj]
    by_cases h1 : Function.minimalPeriod f j = 1
    · left
      simp [h1]
    · have hp := hv (f^[Function.minimalPeriod f j - 1] j)
      have hfp : f (f^[Function.minimalPeriod f j - 1] j) = j := by
        rw [show f (f^[Function.minimalPeriod f j - 1] j)
              = f^[Function.minimalPeriod f j] j from by
            rw [(Function.iterate_succ_apply' f (Function.minimalPeriod f j - 1) j).symm,
              show (Function.minimalPeriod f j - 1).succ = Function.minimalPeriod f j from by
                have := Function.minimalPeriod_pos_of_mem_periodicPts hj; omega],
          Function.iterate_minimalPeriod]
      rcases hp with h | h
      · left
        exact h.symm.trans hfp
      · right
        rw [hfp] at h
        exact G.symm h
  · rw [revF_of_not_periodic f hj]
    exact hv j

lemma val_of_revF_imp (G : SimpleGraph V) [DecidableRel G.Adj] (x : ι → V) (f : ι → ι)
    (hv : ∀ j, revF f j = j ∨ G.Adj (x j) (x (revF f j))) :
    ∀ i, f i = i ∨ G.Adj (x i) (x (f i)) := by
  intro i
  by_cases hi : i ∈ Function.periodicPts f
  · by_cases hfi : f i = i
    · exact Or.inl hfi
    · right
      have hfip : f i ∈ Function.periodicPts f :=
        Function.mk_mem_periodicPts (Function.minimalPeriod_pos_of_mem_periodicPts hi)
          ((Function.isPeriodicPt_minimalPeriod f i).apply)
      have hpre : revF f (f i) = i := by
        rw [revF_of_periodic f hfip, Function.minimalPeriod_apply hi]
        rw [show f^[Function.minimalPeriod f i - 1] (f i) = i from by
          rw [(Function.iterate_succ_apply f (Function.minimalPeriod f i - 1) i).symm,
            show (Function.minimalPeriod f i - 1).succ = Function.minimalPeriod f i from by
              have := Function.minimalPeriod_pos_of_mem_periodicPts hi; omega,
            Function.iterate_minimalPeriod]]
      have hp := hv (f i)
      rw [hpre] at hp
      rcases hp with h | h
      · exact absurd h.symm hfi
      · exact G.symm h
  · have := hv i
    rw [revF_of_not_periodic f hi] at this
    exact this

/-! ### Reversal preserves periodic structure -/

lemma revF_iterate_of_periodic (f : ι → ι) {i : ι} (hi : i ∈ Function.periodicPts f) :
    ∀ m ≤ Function.minimalPeriod f i,
      (revF f)^[m] i = f^[Function.minimalPeriod f i - m] i := by
  intro m
  induction m with
  | zero => intro _; simp [Function.iterate_minimalPeriod]
  | succ m ih =>
    intro hm
    have hK := Function.minimalPeriod_pos_of_mem_periodicPts hi
    rw [Function.iterate_succ_apply']
    rw [ih (by omega)]
    have hper : f^[Function.minimalPeriod f i - m] i ∈ Function.periodicPts f :=
      Function.mk_mem_periodicPts hK
        ((Function.isPeriodicPt_minimalPeriod f i).apply_iterate (Function.minimalPeriod f i - m))
    rw [revF_of_periodic f hper,
      Function.minimalPeriod_apply_iterate hi (Function.minimalPeriod f i - m)]
    rw [← Function.iterate_add_apply f (Function.minimalPeriod f i - 1)
      (Function.minimalPeriod f i - m) i]
    rw [show Function.minimalPeriod f i - 1 + (Function.minimalPeriod f i - m)
          = (Function.minimalPeriod f i - (m + 1)) + Function.minimalPeriod f i from by omega]
    rw [Function.iterate_add_minimalPeriod_eq]

lemma revF_iterate_eq (f : ι → ι) {i : ι} (hi : i ∈ Function.periodicPts f) :
    (revF f)^[Function.minimalPeriod f i - 1] i = f i := by
  have hiter := revF_iterate_of_periodic f hi (Function.minimalPeriod f i - 1) (by
    have := Function.minimalPeriod_pos_of_mem_periodicPts hi; omega)
  rw [hiter, show Function.minimalPeriod f i - (Function.minimalPeriod f i - 1) = 1 from by
    have := Function.minimalPeriod_pos_of_mem_periodicPts hi; omega]
  simp

lemma revF_mem_periodicPts (f : ι → ι) {i : ι} (h : i ∈ Function.periodicPts f) :
    revF f i ∈ Function.periodicPts f := by
  rw [revF_of_periodic f h]
  exact Function.mk_mem_periodicPts (Function.minimalPeriod_pos_of_mem_periodicPts h)
    ((Function.isPeriodicPt_minimalPeriod f i).apply_iterate _)

lemma rank_revF_of_periodic (f : ι → ι) {j : ι} (h : j ∈ Function.periodicPts f) :
    rank f (revF f j) = 0 :=
  (rank_eq_zero_iff f (revF f j)).mpr (revF_mem_periodicPts f h)

lemma rank_revF_of_not_periodic (f : ι → ι) {j : ι} (h : j ∉ Function.periodicPts f) :
    rank f (revF f j) = rank f j - 1 := by
  rw [revF_of_not_periodic f h, rank_apply f j h]

lemma rank_revF_iterate_le (f : ι → ι) (j : ι) :
    ∀ m, rank f ((revF f)^[m] j) ≤ rank f j - m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : (revF f)^[m] j ∈ Function.periodicPts f
    · rw [rank_revF_of_periodic f h]; exact Nat.zero_le _
    · rw [rank_revF_of_not_periodic f h]; omega

lemma periodicPts_revF (f : ι → ι) :
    Function.periodicPts (revF f) = Function.periodicPts f := by
  apply Set.Subset.antisymm
  · intro i hi
    obtain ⟨p, hp, hpg⟩ := hi
    have hle := rank_revF_iterate_le f i p
    rw [show (revF f)^[p] i = i from hpg] at hle
    have hz : rank f i = 0 := by omega
    exact (rank_eq_zero_iff f i).mp hz
  · intro i hi
    have hk := Function.minimalPeriod_pos_of_mem_periodicPts hi
    have hiter := revF_iterate_of_periodic f hi (Function.minimalPeriod f i) le_rfl
    exact Function.mk_mem_periodicPts hk (by simpa using hiter)

lemma minimalPeriod_revF (f : ι → ι) {i : ι} (hi : i ∈ Function.periodicPts f) :
    Function.minimalPeriod (revF f) i = Function.minimalPeriod f i := by
  set K := Function.minimalPeriod f i with hKdef
  have hK : 0 < K := by
    rw [hKdef]; exact Function.minimalPeriod_pos_of_mem_periodicPts hi
  have hik : IsPeriodicPt (revF f) K i := by
    show (revF f)^[K] i = i
    have h := revF_iterate_of_periodic f hi K le_rfl
    rw [h, show Function.minimalPeriod f i - K = 0 from by rw [← hKdef]; exact Nat.sub_self K]
    simp
  refine le_antisymm (hik.minimalPeriod_le hK) ?_
  set m := Function.minimalPeriod (revF f) i with hmdef
  have hi' : i ∈ Function.periodicPts (revF f) := by rw [periodicPts_revF f]; exact hi
  have hmpos : 0 < m := by
    rw [hmdef]; exact Function.minimalPeriod_pos_of_mem_periodicPts hi'
  by_cases hm0 : m = 0
  · omega
  have hgm : (revF f)^[m] i = i := Function.isPeriodicPt_minimalPeriod (revF f) i
  have hmod : (revF f)^[m % K] i = (revF f)^[m] i := hik.iterate_mod_apply m
  have hmK : m % K ≤ K := (Nat.mod_lt m hK).le
  have hiter' := revF_iterate_of_periodic f hi (m % K) hmK
  have hfi : f^[K - m % K] i = i := by rw [← hiter', hmod, hgm]
  have hper' : IsPeriodicPt f (K - m % K) i := hfi
  have hdvd : K ∣ m % K := by
    have h1 : IsPeriodicPt f K i := by
      rw [hKdef]; exact Function.isPeriodicPt_minimalPeriod f i
    have hsub := h1.sub hper'
    rw [show K - (K - m % K) = m % K from by omega] at hsub
    rw [hKdef]
    exact (Function.isPeriodicPt_iff_minimalPeriod_dvd).mp hsub
  have hm0' : m % K = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt m hK)
  have hKm : K ∣ m := by
    conv_rhs => rw [← Nat.div_add_mod m K]
    rw [hm0', add_zero, mul_comm]
    exact Nat.dvd_mul_left K (m / K)
  exact Nat.le_of_dvd hmpos hKm

lemma revF_involutive (f : ι → ι) : revF (revF f) = f := by
  funext i
  by_cases hi : i ∈ Function.periodicPts f
  · have hi' : i ∈ Function.periodicPts (revF f) := by
      rw [periodicPts_revF f]; exact hi
    rw [revF_of_periodic (revF f) hi', minimalPeriod_revF f hi]
    exact revF_iterate_eq f hi
  · have hi' : i ∉ Function.periodicPts (revF f) := by
      rw [periodicPts_revF f]; exact hi
    rw [revF_of_not_periodic (revF f) hi', revF_of_not_periodic f hi]

lemma revF_eq_self_iff_not_hasLongCycle (f : ι → ι) :
    revF f = f ↔ ¬ HasLongCycle f := by
  constructor
  · intro h
    rintro ⟨i, hk⟩
    have hi : i ∈ Function.periodicPts f :=
      (Function.minimalPeriod_pos_iff_mem_periodicPts).mp (by omega)
    have hK2 : 1 < Function.minimalPeriod f i := by omega
    have hfix : f^[Function.minimalPeriod f i - 1] i = f i := by
      have := congrFun h i
      rwa [revF_of_periodic f hi] at this
    have hfeq : f (f^[Function.minimalPeriod f i - 2] i) = f i := by
      rw [show f (f^[Function.minimalPeriod f i - 2] i)
            = f^[Function.minimalPeriod f i - 1] i from by
        rw [(Function.iterate_succ_apply' f (Function.minimalPeriod f i - 2) i).symm,
          show (Function.minimalPeriod f i - 2).succ = Function.minimalPeriod f i - 1 from by
            omega],
        hfix]
    have hx : IsPeriodicPt f (Function.minimalPeriod f i) (f^[Function.minimalPeriod f i - 2] i) :=
      (Function.isPeriodicPt_minimalPeriod f i).apply_iterate _
    have hy : IsPeriodicPt f (Function.minimalPeriod f i) i :=
      Function.isPeriodicPt_minimalPeriod f i
    have heq : f^[Function.minimalPeriod f i - 2] i = i :=
      hx.eq_of_apply_eq_same hy (by omega) hfeq
    have h2 : IsPeriodicPt f 2 i := by
      have hsub := (Function.isPeriodicPt_minimalPeriod f i).sub (show IsPeriodicPt f
        (Function.minimalPeriod f i - 2) i from heq)
      rwa [show Function.minimalPeriod f i - (Function.minimalPeriod f i - 2) = 2 from by
        omega] at hsub
    have hdvd : Function.minimalPeriod f i ∣ 2 :=
      (Function.isPeriodicPt_iff_minimalPeriod_dvd).mp h2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · intro h
    funext i
    by_cases hi : i ∈ Function.periodicPts f
    · rw [revF_of_periodic f hi]
      have hK := Function.minimalPeriod_pos_of_mem_periodicPts hi
      have hle : Function.minimalPeriod f i ≤ 2 := by
        by_contra hc
        exact h ⟨i, by omega⟩
      by_cases h1 : Function.minimalPeriod f i = 1
      · rw [h1, Nat.sub_self]
        exact ((Function.minimalPeriod_eq_one_iff_isFixedPt).mp h1).eq.symm
      · have h2 : Function.minimalPeriod f i = 2 := by omega
        rw [h2]; simp
    · rw [revF_of_not_periodic f hi]

lemma revF_ne_self_iff_hasLongCycle (f : ι → ι) :
    revF f ≠ f ↔ HasLongCycle f := by
  rw [Ne, revF_eq_self_iff_not_hasLongCycle, not_not]

lemma hasLongCycle_revF (f : ι → ι) (h : HasLongCycle f) : HasLongCycle (revF f) := by
  have hne : revF f ≠ f := (revF_ne_self_iff_hasLongCycle f).mpr h
  rw [← revF_ne_self_iff_hasLongCycle (revF f), revF_involutive f]
  exact hne.symm

lemma revF_apply_apply (f : ι → ι) {i : ι} (hi : i ∈ Function.periodicPts f) :
    revF f (f i) = i := by
  have hK := Function.minimalPeriod_pos_of_mem_periodicPts hi
  have hfi : f i ∈ Function.periodicPts f :=
    Function.mk_mem_periodicPts hK ((Function.isPeriodicPt_minimalPeriod f i).apply)
  rw [revF_of_periodic f hfi, Function.minimalPeriod_apply hi]
  rw [show f^[Function.minimalPeriod f i - 1] (f i) = i from by
    rw [(Function.iterate_succ_apply f (Function.minimalPeriod f i - 1) i).symm,
      show (Function.minimalPeriod f i - 1).succ = Function.minimalPeriod f i from by omega,
      Function.iterate_minimalPeriod]]

/-! ### Reversal preserves the validity of a transversal -/

lemma mem_XfS_revF (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] (f : ι → ι)
    {x : ι → V} (hx : x ∈ XfS part G f) : x ∈ XfS part G (revF f) := by
  simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  refine ⟨hx.1, ?_⟩
  intro i
  by_cases hi : i ∈ Function.periodicPts f
  · rw [revF_of_periodic f hi]
    by_cases h1 : Function.minimalPeriod f i = 1
    · left; rw [h1]; simp
    · right
      have hK := Function.minimalPeriod_pos_of_mem_periodicPts hi
      have hjne : f^[Function.minimalPeriod f i - 1] i ≠ i := by
        intro hc
        have hp : IsPeriodicPt f (Function.minimalPeriod f i - 1) i := hc
        have hle := hp.minimalPeriod_le (by omega : 0 < Function.minimalPeriod f i - 1)
        omega
      have hfK : f (f^[Function.minimalPeriod f i - 1] i) = i := by
        rw [show f (f^[Function.minimalPeriod f i - 1] i)
              = f^[Function.minimalPeriod f i] i from by
          rw [(Function.iterate_succ_apply' f (Function.minimalPeriod f i - 1) i).symm,
            show (Function.minimalPeriod f i - 1).succ = Function.minimalPeriod f i from by
              omega],
          Function.iterate_minimalPeriod]
      have hcond := hx.2 (f^[Function.minimalPeriod f i - 1] i)
      rw [hfK] at hcond
      rcases hcond with hc | hc
      · exact absurd hc.symm hjne
      · exact G.symm hc
  · rw [revF_of_not_periodic f hi]
    exact hx.2 i

lemma mem_XfS_of_revF (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] (f : ι → ι)
    {x : ι → V} (hx : x ∈ XfS part G (revF f)) : x ∈ XfS part G f := by
  simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  refine ⟨hx.1, ?_⟩
  intro i
  by_cases hi : i ∈ Function.periodicPts f
  · by_cases h1 : Function.minimalPeriod f i = 1
    · left
      exact ((Function.minimalPeriod_eq_one_iff_isFixedPt).mp h1).eq
    · right
      have hK := Function.minimalPeriod_pos_of_mem_periodicPts hi
      have hfi_ne : f i ≠ i := fun hc => h1 ((Function.minimalPeriod_eq_one_iff_isFixedPt).mpr hc)
      have hpre : revF f (f i) = i := revF_apply_apply f hi
      have hj := hx.2 ((revF f)^[Function.minimalPeriod f i - 1] i)
      rw [revF_iterate_eq f hi] at hj
      rw [hpre] at hj
      rcases hj with hc | hc
      · exact absurd hc.symm hfi_ne
      · exact G.symm hc
  · have := hx.2 i
    rw [revF_of_not_periodic f hi] at this
    exact this

lemma XfS_revF_eq (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] (f : ι → ι) :
    XfS part G (revF f) = XfS part G f := by
  ext x
  exact ⟨fun hx => mem_XfS_of_revF part G f hx, fun hx => mem_XfS_revF part G f hx⟩

lemma XfS_revF_card (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] (f : ι → ι) :
    (XfS part G (revF f)).card = (XfS part G f).card := by
  rw [XfS_revF_eq]

/-! ## A sum of even naturals is even -/

lemma even_sum_of_even {α : Type*} (s : Finset α) (f : α → ℕ)
    (h : ∀ a ∈ s, Even (f a)) : Even (∑ a ∈ s, f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact (h a (Finset.mem_cons_self a s)).add
        (ih (fun b hb => h b (Finset.mem_cons_of_mem hb)))

/-! ## A free coordinate forces an even count -/

/-- Restriction to the coordinates other than `p`. -/
def dropOne (p : ι) (x : ι → V) : ({i // i ≠ p} → V) := fun i => x i.1

/-- Extend `r` (defined off `p`) by the value `u` at `p`. -/
def padOne (p : ι) (r : {i // i ≠ p} → V) (u : V) : ι → V :=
  fun i => if h : i = p then u else r ⟨i, h⟩

@[simp] lemma padOne_self (p : ι) (r : {i // i ≠ p} → V) (u : V) :
    padOne p r u p = u := by simp [padOne]

@[simp] lemma padOne_of_ne (p : ι) (r : {i // i ≠ p} → V) (u : V) {i : ι} (hi : i ≠ p) :
    padOne p r u i = r ⟨i, hi⟩ := by simp only [padOne, dif_neg hi]

/-- If no index maps to `p`, the number of valid `x` agrees with the number of
neighbours of the fixed vertex `r (f p)` inside fibre `p`. -/
lemma leaf_fiber_card (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : ι → ι) (p : ι) (hp : ∀ i, f i ≠ p)
    (r : {i // i ≠ p} → V) {x₀ : ι → V} (hx₀ : x₀ ∈ XfS part G f)
    (hr : dropOne p x₀ = r) :
    ((XfS part G f).filter (fun x => dropOne p x = r)).card
      = (Finset.univ.filter (fun u : V => part u = p ∧ G.Adj (r ⟨f p, hp p⟩) u)).card := by
  classical
  have hx₀t : ∀ i, part (x₀ i) = i := by
    have h := hx₀; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
  have hx₀c : ∀ i, f i = i ∨ G.Adj (x₀ i) (x₀ (f i)) := by
    have h := hx₀; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.2
  have hrx : ∀ (i : ι) (hi : i ≠ p), r ⟨i, hi⟩ = x₀ i := by
    intro i hi
    have := congrFun hr ⟨i, hi⟩
    simpa [dropOne] using this.symm
  refine Finset.card_nbij' (fun x => x p) (padOne p r) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxX, hxr⟩ := hx
    have hxt : ∀ i, part (x i) = i := by
      have h := hxX; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
    have hxc : ∀ i, f i = i ∨ G.Adj (x i) (x (f i)) := by
      have h := hxX; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt p, ?_⟩
    have h := hxc p
    rcases h with h | h
    · exact absurd h (hp p)
    · rw [show x (f p) = r ⟨f p, hp p⟩ from by
        have := congrFun hxr ⟨f p, hp p⟩; simpa [dropOne] using this] at h
      exact G.symm h
  · intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hup, huadj⟩ := hu
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [XfS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro i
        by_cases hi : i = p
        · subst i; rw [padOne_self]; exact hup
        · rw [padOne_of_ne p r u hi, hrx i hi]; exact hx₀t i
      · intro i
        by_cases hi : i = p
        · subst i
          right
          rw [padOne_self, padOne_of_ne p r u (hp p)]
          exact G.symm huadj
        · rw [padOne_of_ne p r u hi, padOne_of_ne p r u (hp i), hrx i hi, hrx (f i) (hp i)]
          exact hx₀c i
    · funext i
      simp only [dropOne, padOne, dif_neg i.2]
  · intro x hx
    show padOne p r (x p) = x
    have hxr : dropOne p x = r := (Finset.mem_filter.mp hx).2
    funext i
    by_cases hi : i = p
    · subst i; rw [padOne_self]
    · rw [padOne_of_ne p r (x p) hi]
      have := congrFun hxr ⟨i, hi⟩
      simp only [dropOne] at this
      rw [← this]
  · intro u _
    exact padOne_self p r u

/-- A non-surjective `f` contributes an even number of valid transversals. -/
lemma even_XfS_of_not_surjective (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ i j : ι, i ≠ j → ∀ v : V, part v = i →
      Even (Finset.univ.filter (fun u : V => part u = j ∧ G.Adj v u)).card)
    (f : ι → ι) (hn : ¬ Function.Surjective f) : Even (XfS part G f).card := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, ∀ i, f i ≠ p := by
    rw [Function.Surjective] at hn; push_neg at hn; exact hn
  rw [Finset.card_eq_sum_card_image (dropOne p) (XfS part G f)]
  apply even_sum_of_even
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨x₀, hx₀, hx₀r⟩ := hr
  rw [leaf_fiber_card part G f p hp r hx₀ hx₀r]
  have hv : part (r ⟨f p, hp p⟩) = f p := by
    have h1 : r ⟨f p, hp p⟩ = x₀ (f p) := by
      have := congrFun hx₀r ⟨f p, hp p⟩
      simpa [dropOne] using this.symm
    rw [h1]
    have h := hx₀; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1 (f p)
  exact h2 (f p) p (hp p) (r ⟨f p, hp p⟩) hv

/-! ## The identity function contributes an odd number -/

lemma transvS_card (part : V → ι) :
    (transvS part).card = ∏ i, (Finset.univ.filter (fun v : V => part v = i)).card := by
  have h : transvS part
      = Fintype.piFinset (fun i => Finset.univ.filter (fun v : V => part v = i)) := by
    ext x
    simp only [transvS, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]

lemma XfS_id_eq (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] :
    XfS part G id = transvS part := by
  ext x
  simp only [XfS, transvS, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h; exact ⟨h, fun i => Or.inl rfl⟩

lemma odd_XfS_id (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hodd : ∀ i, Odd (Finset.univ.filter (fun v : V => part v = i)).card) :
    Odd (XfS part G id).card := by
  rw [XfS_id_eq, transvS_card, odd_finset_prod]
  intro i _
  exact hodd i

/-! ## Functions with a long cycle contribute an even total -/

lemma even_hasLongCycle_sum (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (∑ f ∈ (Finset.univ.filter (fun f : ι → ι => HasLongCycle f)),
      (XfS part G f).card) := by
  refine even_sum_of_involution _ _ revF ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨Finset.mem_univ _, hasLongCycle_revF f hf.2⟩
  · intro f _; exact revF_involutive f
  · intro f hf
    rw [Finset.mem_filter] at hf
    exact (revF_ne_self_iff_hasLongCycle f).mpr hf.2
  · intro f _; exact XfS_revF_card part G f

/-! ## Two-cycles -/

/-- The identity has no long cycle. -/
lemma not_hasLongCycle_id : ¬ HasLongCycle (id : ι → ι) := by
  rintro ⟨i, hi⟩
  rw [Function.minimalPeriod_id] at hi
  omega

/-- An injective function without long cycles is an involution. -/
lemma apply_apply_eq_self_of_not_hasLongCycle (f : ι → ι) (hinj : Function.Injective f)
    (hfnl : ¬ HasLongCycle f) (x : ι) : f (f x) = x := by
  have hper : x ∈ Function.periodicPts f := by
    have h : Function.periodicPts f = Set.univ :=
      Function.injective_iff_periodicPts_eq_univ.mp hinj
    rw [h]; exact Set.mem_univ x
  have hmpos : 0 < Function.minimalPeriod f x :=
    Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hmle : Function.minimalPeriod f x ≤ 2 := by
    have hlt : Function.minimalPeriod f x < 3 := by
      by_contra hcon
      push_neg at hcon
      exact hfnl ⟨x, hcon⟩
    omega
  have hcases : Function.minimalPeriod f x = 1 ∨ Function.minimalPeriod f x = 2 := by omega
  rcases hcases with hm | hm
  · have hx : f x = x := by
      have h := Function.iterate_minimalPeriod (f := f) (x := x)
      rw [hm] at h
      simpa using h
    simp [hx]
  · have h := Function.iterate_minimalPeriod (f := f) (x := x)
    rw [hm] at h
    simpa using h

/-- A non-identity injective function without a long cycle has a 2-cycle. -/
lemma exists_two_cycle (f : ι → ι) (hinj : Function.Injective f)
    (hfnl : ¬ HasLongCycle f) (hfne : f ≠ id) :
    ∃ a b, a ≠ b ∧ f a = b ∧ f b = a := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ a := by
    by_contra hcon
    push_neg at hcon
    exact hfne (funext hcon)
  exact ⟨a, f a, Ne.symm ha, rfl,
    apply_apply_eq_self_of_not_hasLongCycle f hinj hfnl a⟩

/-- For a 2-cycle `a → b → a`, the fibre of `dropOne b` at `r` has the cardinality of a
neighbourhood of the free coordinate. -/
lemma twoCycle_fiber_card (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : ι → ι) (hinj : Function.Injective f) {a b : ι} (hab : a ≠ b)
    (hfa : f a = b) (hfb : f b = a)
    (r : {i // i ≠ b} → V) {x₀ : ι → V} (hx₀ : x₀ ∈ XfS part G f)
    (hr : dropOne b x₀ = r) :
    ((XfS part G f).filter (fun x => dropOne b x = r)).card
      = (Finset.univ.filter (fun u : V => part u = b ∧ G.Adj (r ⟨a, hab⟩) u)).card := by
  classical
  have hx₀t : ∀ i, part (x₀ i) = i := by
    have h := hx₀; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
  have hx₀c : ∀ i, f i = i ∨ G.Adj (x₀ i) (x₀ (f i)) := by
    have h := hx₀; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.2
  have hxr : ∀ (i : ι) (hi : i ≠ b), x₀ i = r ⟨i, hi⟩ := by
    intro i hi
    have := congrFun hr ⟨i, hi⟩
    simpa [dropOne] using this
  refine Finset.card_nbij' (fun x => x b) (padOne b r) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxX, hxr'⟩ := hx
    have hxt : ∀ i, part (x i) = i := by
      have h := hxX; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1
    have hxc : ∀ i, f i = i ∨ G.Adj (x i) (x (f i)) := by
      have h := hxX; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt b, ?_⟩
    have h := hxc a
    rcases h with h | h
    · exact absurd (h.symm.trans hfa) hab
    · rw [hfa] at h
      rw [show x a = r ⟨a, hab⟩ from by
        have := congrFun hxr' ⟨a, hab⟩
        simpa [dropOne] using this] at h
      exact h
  · intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hup, huadj⟩ := hu
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [XfS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro i
        by_cases hib : i = b
        · subst i; rw [padOne_self]; exact hup
        · rw [padOne_of_ne b r u hib, ← hxr i hib]; exact hx₀t i
      · intro i
        by_cases hib : i = b
        · subst i
          right
          rw [hfb, padOne_self, padOne_of_ne b r u hab]
          exact G.symm huadj
        · by_cases hia : i = a
          · subst i
            right
            rw [hfa, padOne_of_ne b r u hab, padOne_self]
            exact huadj
          · have hfib : f i ≠ b := fun h => hia (hinj (h.trans hfa.symm))
            rw [padOne_of_ne b r u hib, padOne_of_ne b r u hfib,
              ← hxr i hib, ← hxr (f i) hfib]
            exact hx₀c i
    · funext i
      simp only [dropOne, padOne, dif_neg i.2]
  · intro x hx
    show padOne b r (x b) = x
    have hxr' : dropOne b x = r := (Finset.mem_filter.mp hx).2
    funext i
    by_cases hib : i = b
    · subst i; rw [padOne_self]
    · rw [padOne_of_ne b r (x b) hib]
      have := congrFun hxr' ⟨i, hib⟩
      simp only [dropOne] at this
      rw [← this]
  · intro u _
    exact padOne_self b r u

/-- A 2-cycled function contributes an even number of valid transversals. -/
lemma even_XfS_of_twoCycle (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ i j : ι, i ≠ j → ∀ v : V, part v = i →
      Even (Finset.univ.filter (fun u : V => part u = j ∧ G.Adj v u)).card)
    (f : ι → ι) (hinj : Function.Injective f) {a b : ι} (hab : a ≠ b)
    (hfa : f a = b) (hfb : f b = a) : Even (XfS part G f).card := by
  classical
  rw [Finset.card_eq_sum_card_image (dropOne b) (XfS part G f)]
  apply even_sum_of_even
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨x₀, hx₀, hx₀r⟩ := hr
  rw [twoCycle_fiber_card part G f hinj hab hfa hfb r hx₀ hx₀r]
  have hv : part (r ⟨a, hab⟩) = a := by
    have h1 : x₀ a = r ⟨a, hab⟩ := by
      have := congrFun hx₀r ⟨a, hab⟩
      simpa [dropOne] using this
    rw [← h1]
    have h := hx₀; simp only [XfS, Finset.mem_filter, Finset.mem_univ, true_and] at h; exact h.1 a
  exact h2 a b hab (r ⟨a, hab⟩) hv

/-- A non-identity function without long cycles contributes an even number of transversals. -/
lemma even_XfS_of_longCycleFree (part : V → ι) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ i j : ι, i ≠ j → ∀ v : V, part v = i →
      Even (Finset.univ.filter (fun u : V => part u = j ∧ G.Adj v u)).card)
    (f : ι → ι) (hfne : f ≠ id) (hfnl : ¬ HasLongCycle f) :
    Even (XfS part G f).card := by
  by_cases hsurj : Function.Surjective f
  · have hinj : Function.Injective f := Finite.injective_iff_surjective.mpr hsurj
    obtain ⟨a, b, hab, hfa, hfb⟩ := exists_two_cycle f hinj hfnl hfne
    exact even_XfS_of_twoCycle part G h2 f hinj hab hfa hfb
  · exact even_XfS_of_not_surjective part G h2 f hsurj

/-! ## Final assembly -/

/-- **Petrov's parity theorem** (arXiv:1512.06205, Theorem 1). -/
theorem petrov_parity (part : V → ι)
    (hodd : ∀ i, Odd (Finset.univ.filter (fun v : V => part v = i)).card)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h1 : ∀ i, ∀ v w : V, part v = i → part w = i → ¬ G.Adj v w)
    (h2 : ∀ i j : ι, i ≠ j → ∀ v : V, part v = i →
      Even (Finset.univ.filter (fun u : V => part u = j ∧ G.Adj v u)).card) :
    Odd (Finset.univ.filter (fun g : ι → V =>
      (∀ i, part (g i) = i) ∧
        (∀ i, Even (Finset.univ.filter (fun j : ι => G.Adj (g i) (g j))).card))).card := by
  have hEuler : Odd (EulerSet part G).card := by
    apply (odd_SS_iff_odd_Euler part G).mp
    rw [SS_card_f]
    have hsplit : (∑ f ∈ (Finset.univ : Finset (ι → ι)), (XfS part G f).card)
        = (∑ f ∈ (Finset.univ.filter (fun f : ι → ι => HasLongCycle f)), (XfS part G f).card)
          + (∑ f ∈ (Finset.univ.filter (fun f : ι → ι => ¬ HasLongCycle f)),
              (XfS part G f).card) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : ι → ι => HasLongCycle f)
        (fun f => (XfS part G f).card)).symm
    rw [hsplit]
    refine (even_hasLongCycle_sum part G).add_odd ?_
    have hid : id ∈ (Finset.univ.filter (fun f : ι → ι => ¬ HasLongCycle f)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, not_hasLongCycle_id⟩
    have hBsplit : (∑ f ∈ (Finset.univ.filter (fun f : ι → ι => ¬ HasLongCycle f)),
          (XfS part G f).card)
        = (∑ f ∈ (Finset.univ.filter (fun f : ι → ι => ¬ HasLongCycle f)).erase id,
              (XfS part G f).card)
          + (XfS part G id).card :=
      (Finset.sum_erase_add _ (fun f => (XfS part G f).card) hid).symm
    rw [hBsplit]
    refine (even_sum_of_even _ _ ?_).add_odd (odd_XfS_id part G hodd)
    intro f hf
    rw [Finset.mem_erase] at hf
    obtain ⟨hfne, hfB⟩ := hf
    rw [Finset.mem_filter] at hfB
    exact even_XfS_of_longCycleFree part G h2 f hfne hfB.2
  exact hEuler

end Jsp698