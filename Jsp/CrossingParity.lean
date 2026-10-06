/-
JSP-000698 — chord-crossing parity (Petrov's geometric corollary).

Petrov, *General Parity Result and Cycle-plus-Triangles Graphs*
(arXiv:1512.06205), Corollary after Theorem 1: for closed polygonal lines
`P_1, …, P_n` inscribed in a circle, each with an odd number of edges and
pairwise vertex-disjoint, the number of ways to choose one edge from each `P_i`
so that every chosen edge crosses an even number of the other chosen edges is odd.

Here we instantiate this for `n` triangles (each a closed 3-gon whose three sides
are chords), whose `3n` vertices lie on a circle modelled by `Fin m`.  The
instance is produced by applying `petrov_parity` to the chord-crossing graph.
-/
import Jsp.PetrovParity

namespace Jsp698

open Classical

/-! ## Clockwise distance on `Fin m` -/

/-- Clockwise distance from `p` to `q` on a cycle of length `m`. -/
def db (m p q : ℕ) : ℕ := if p ≤ q then q - p else m - p + q

/-- Clockwise distance between two points of `Fin m`. -/
def cdist {m : ℕ} (a b : Fin m) : ℕ := db m a.val b.val

@[simp] lemma cdist_def {m : ℕ} (a b : Fin m) : cdist a b = db m a.val b.val := rfl

lemma cdist_self {m : ℕ} (a : Fin m) : cdist a a = 0 := by
  simp [cdist, db]

lemma cdist_pos {m : ℕ} (a b : Fin m) (h : a ≠ b) : 0 < cdist a b := by
  have ha := a.isLt
  have hb := b.isLt
  have hne : a.val ≠ b.val := fun hh => h (Fin.ext hh)
  simp only [cdist, db]
  split_ifs <;> omega

lemma cdist_lt {m : ℕ} (a b : Fin m) : cdist a b < m := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [cdist, db]
  split_ifs <;> omega

lemma cdist_add {m : ℕ} (a b : Fin m) (h : a ≠ b) : cdist a b + cdist b a = m := by
  have ha := a.isLt
  have hb := b.isLt
  have hne : a.val ≠ b.val := fun hh => h (Fin.ext hh)
  simp only [cdist, db]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_pos hlt.le, if_neg (not_le.mpr hlt)]; omega
  · rw [if_neg (not_le.mpr hlt), if_pos hlt.le]; omega

/-! ## The four-point crossing identity -/

/-- For four distinct points, `x` and `y` lie on opposite sides of the chord `ab`
if and only if `a` and `b` lie on opposite sides of the chord `xy`. -/
lemma cross_core {m : ℕ} {a b x y : Fin m}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) :
    (cdist a x < cdist a b ↔ cdist a y < cdist a b) ↔
      (cdist x a < cdist x y ↔ cdist x b < cdist x y) := by
  have ha := a.isLt
  have hb := b.isLt
  have hx := x.isLt
  have hy := y.isLt
  have hpq : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
  have hrs : x.val ≠ y.val := fun hh => hxy (Fin.ext hh)
  have hpr : a.val ≠ x.val := fun hh => hax (Fin.ext hh)
  have hps : a.val ≠ y.val := fun hh => hay (Fin.ext hh)
  have hqr : b.val ≠ x.val := fun hh => hbx (Fin.ext hh)
  have hqs : b.val ≠ y.val := fun hh => hby (Fin.ext hh)
  simp only [cdist, db]
  split_ifs <;> omega

/-- The chords `(a,b)` and `(x,y)` cross, expressed via the clockwise arc from
`a` to `b`. -/
def cross {m : ℕ} (a b x y : Fin m) : Prop :=
  ¬ (cdist a x < cdist a b ↔ cdist a y < cdist a b)

lemma cross_symm {m : ℕ} {a b x y : Fin m}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) :
    cross a b x y ↔ cross x y a b := by
  unfold cross
  exact not_congr (cross_core hab hxy hax hay hbx hby)

/-! ## Triangles on the circle -/

variable {n m : ℕ}

/-- First endpoint of the side `u` of the configuration. -/
def s1 (tri : Fin n × Fin 3 ↪ Fin m) (u : Fin n × Fin 3) : Fin m := tri u

/-- Second endpoint of the side `u` (the side joins `s1 tri u` to `s2 tri u`). -/
def s2 (tri : Fin n × Fin 3 ↪ Fin m) (u : Fin n × Fin 3) : Fin m := tri ⟨u.1, u.2 + 1⟩

lemma fin3_add_one_ne (t : Fin 3) : t + 1 ≠ t := by
  fin_cases t <;> decide

lemma s1_ne_s2 (tri : Fin n × Fin 3 ↪ Fin m) (u : Fin n × Fin 3) :
    s1 tri u ≠ s2 tri u := by
  intro h
  rw [s1, s2] at h
  have h2 : u.2 = u.2 + 1 := congrArg Prod.snd (tri.injective h)
  exact fin3_add_one_ne u.2 h2.symm

lemma s1_ne_s1 (tri : Fin n × Fin 3 ↪ Fin m) {u v : Fin n × Fin 3} (h : u.1 ≠ v.1) :
    s1 tri u ≠ s1 tri v := by
  intro hh
  rw [s1, s1] at hh
  have h2 := tri.injective hh
  have h3 : u.1 = v.1 := congrArg Prod.fst h2
  exact h h3

lemma s1_ne_s2' (tri : Fin n × Fin 3 ↪ Fin m) {u v : Fin n × Fin 3} (h : u.1 ≠ v.1) :
    s1 tri u ≠ s2 tri v := by
  intro hh
  rw [s1, s2] at hh
  have h2 := tri.injective hh
  have h3 : u.1 = (v.1, v.2 + 1).1 := congrArg Prod.fst h2
  exact h h3

lemma s2_ne_s1 (tri : Fin n × Fin 3 ↪ Fin m) {u v : Fin n × Fin 3} (h : u.1 ≠ v.1) :
    s2 tri u ≠ s1 tri v := by
  intro hh
  rw [s2, s1] at hh
  have h2 := tri.injective hh
  have h3 : (u.1, u.2 + 1).1 = v.1 := congrArg Prod.fst h2
  exact h h3

lemma s2_ne_s2 (tri : Fin n × Fin 3 ↪ Fin m) {u v : Fin n × Fin 3} (h : u.1 ≠ v.1) :
    s2 tri u ≠ s2 tri v := by
  intro hh
  rw [s2, s2] at hh
  have h2 := tri.injective hh
  have h3 : (u.1, u.2 + 1).1 = (v.1, v.2 + 1).1 := congrArg Prod.fst h2
  exact h h3

/-- The chord-crossing graph on the sides of the triangles. -/
def chordGraph (tri : Fin n × Fin 3 ↪ Fin m) : SimpleGraph (Fin n × Fin 3) where
  Adj u v := u.1 ≠ v.1 ∧ cross (s1 tri u) (s2 tri u) (s1 tri v) (s2 tri v)
  symm := by
    rintro u v ⟨huv, hc⟩
    exact ⟨huv.symm,
      (cross_symm (s1_ne_s2 tri u) (s1_ne_s2 tri v)
        (s1_ne_s1 tri huv) (s1_ne_s2' tri huv)
        (s2_ne_s1 tri huv) (s2_ne_s2 tri huv)).mp hc⟩
  loopless := fun u h => h.1 rfl

/-! ## Parity helpers -/

/-- `P ≠ Q` for propositions means "not both, not neither". -/
lemma prop_ne_iff (P Q : Prop) : (P ≠ Q) ↔ ¬ (P ↔ Q) := by
  constructor
  · intro h hpq; exact h (propext hpq)
  · intro h heq; exact h (iff_of_eq heq)

/-- The number of sign changes around a 3-cycle is even. -/
lemma even_changes_fin3 (B : Fin 3 → Prop) [DecidablePred B] :
    Even (Finset.univ.filter (fun t : Fin 3 => B t ≠ B (t + 1))).card := by
  have e0 : (0 : Fin 3) + 1 = 1 := by decide
  have e1 : (1 : Fin 3) + 1 = 2 := by decide
  have e2 : (2 : Fin 3) + 1 = 0 := by decide
  have hcard : (Finset.univ.filter (fun t : Fin 3 => B t ≠ B (t + 1))).card
      = (if B 0 ≠ B 1 then 1 else 0) + (if B 1 ≠ B 2 then 1 else 0)
        + (if B 2 ≠ B 0 then 1 else 0) := by
    rw [Finset.card_filter, Fin.sum_univ_three, e0, e1, e2]
  rw [hcard]
  by_cases h0 : B 0 <;> by_cases h1 : B 1 <;> by_cases h2 : B 2 <;> simp_all

/-! ## The instance -/

/-- The fibre over `i` has three elements. -/
lemma fiber_card (i : Fin n) :
    (Finset.univ.filter (fun v : Fin n × Fin 3 => v.1 = i)).card = 3 := by
  have h : (Finset.univ.filter (fun v : Fin n × Fin 3 => v.1 = i))
      = (Finset.univ : Finset (Fin 3)).image (fun t : Fin 3 => (i, t)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hv
      exact ⟨v.2, Prod.ext hv.symm rfl⟩
    · rintro ⟨t, rfl⟩
      rfl
  rw [h, Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).2),
    Finset.card_univ, Fintype.card_fin]

/-- Adjacency in the crossing graph, unfolded at a side `(j, t)`. -/
lemma chordGraph_adj (tri : Fin n × Fin 3 ↪ Fin m) (v : Fin n × Fin 3) (j : Fin n)
    (t : Fin 3) (hvj : v.1 ≠ j) :
    (chordGraph tri).Adj v (j, t) ↔
      (cdist (s1 tri v) (tri (j, t)) < cdist (s1 tri v) (s2 tri v)) ≠
        (cdist (s1 tri v) (tri (j, t + 1)) < cdist (s1 tri v) (s2 tri v)) := by
  have hvjT : (v.1 ≠ j) = True := eq_true hvj
  simp only [chordGraph, cross, s1, s2, hvjT, true_and, prop_ne_iff]

attribute [-instance] Nat.decidableForallFin in
/-- **Petrov's chord-crossing parity for triangles.**  The number of ways to choose
one side of each of `n` vertex-disjoint triangles inscribed in a circle, so that
every chosen side crosses an even number of the other chosen sides, is odd. -/
theorem chord_even_crossing_odd (tri : Fin n × Fin 3 ↪ Fin m) :
    Odd (Finset.univ.filter (fun g : Fin n → Fin n × Fin 3 =>
      (∀ i, (g i).1 = i) ∧
        (∀ i, Even (Finset.univ.filter (fun j : Fin n =>
          (chordGraph tri).Adj (g i) (g j))).card))).card := by
  refine petrov_parity (fun v : Fin n × Fin 3 => v.1)
    (fun i => ?_) (chordGraph tri) (fun i v w hv hw => ?_) (fun i j hij v hv => ?_)
  · rw [fiber_card i]
    exact ⟨1, by norm_num⟩
  · intro hAdj
    exact hAdj.1 (hv.trans hw.symm)
  · obtain ⟨a, b⟩ := v
    have hv' : a = i := hv
    have hne : (a, b).1 ≠ j := by rw [hv']; exact hij
    have hset : (Finset.univ.filter (fun u : Fin n × Fin 3 =>
          u.1 = j ∧ (chordGraph tri).Adj (a, b) u))
        = Finset.image (fun t : Fin 3 => (j, t))
            (Finset.univ.filter (fun t : Fin 3 =>
              (cdist (s1 tri (a, b)) (tri (j, t)) < cdist (s1 tri (a, b)) (s2 tri (a, b))) ≠
                (cdist (s1 tri (a, b)) (tri (j, t + 1)) < cdist (s1 tri (a, b)) (s2 tri (a, b))))) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨hu1, hu2⟩
        have h1 : (a, b).1 ≠ u.1 := by rw [hv', hu1]; exact hij
        have hQ : (cdist (s1 tri (a, b)) (tri (j, u.2)) < cdist (s1 tri (a, b)) (s2 tri (a, b))) ≠
            (cdist (s1 tri (a, b)) (tri (j, u.2 + 1)) < cdist (s1 tri (a, b)) (s2 tri (a, b))) := by
          have h2 := (chordGraph_adj tri (a, b) u.1 u.2 h1).mp hu2
          rw [hu1] at h2
          exact h2
        exact ⟨u.2, hQ, Prod.ext hu1.symm rfl⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨rfl, ?_⟩
        exact (chordGraph_adj tri (a, b) j t hne).mpr ht
    rw [hset, Finset.card_image_of_injective (f := fun t : Fin 3 => (j, t)) _
      (fun a b hab => (Prod.ext_iff.mp hab).2)]
    exact even_changes_fin3
      (fun t : Fin 3 => cdist (s1 tri (a, b)) (tri (j, t)) < cdist (s1 tri (a, b)) (s2 tri (a, b)))

end Jsp698
