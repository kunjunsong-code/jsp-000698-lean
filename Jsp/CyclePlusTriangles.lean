/-
JSP-000698 — the cycle-plus-triangles theorem: the formal statement.

Problem (Du-Hsu-Hwang 1986; strengthened by Erdos 1987; proved by Fleischner-Stiebitz 1992):
  Is every graph formed by vertex-disjoint triangles and a spanning Hamilton cycle
  three-colorable?

This file records, sorry-free, the *faithful general statement* of the problem together
with the notion of 3-colorability. It contains no proof of the statement: the known
proofs (Alon-Tarsi via the Combinatorial Nullstellensatz; later an elementary parity
argument of Sachs) are research-level and are not available in Mathlib.

The algebraic *reduction* of the statement — from the non-vanishing of the Alon-Tarsi
coefficient of the graph polynomial to 3-colorability — is developed, sorry-free, in
`Jsp.Reduction` and `Jsp.AlonTarsi`. What remains for a complete proof is the
non-vanishing of that coefficient for the cycle-plus-triangles orientation
(`AlonTarsi698Coefficient`), formalizing which is the outstanding research-level step.
-/
import Mathlib

namespace Jsp698

open SimpleGraph

/-- A graph is 3-colorable if it admits a proper coloring with three colors. -/
def ThreeColorable {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Fin 3, ∀ u v, G.Adj u v → c u ≠ c v

/-- `G` is a *cycle-plus-triangles* graph if it is the union of a Hamiltonian cycle and
`n` pairwise vertex-disjoint triangles. Concretely, there is a bijection
`e : V ≃ Fin (3*n)` witnessing the spanning Hamiltonian cycle (consecutive images are
adjacent) and a map `f : V → Fin n` whose fibres are the `n` triples, each inducing a
triangle; the edge set of `G` is exactly the union of these cycle and triangle edges. -/
def IsCPTGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (e : V ≃ Fin (3 * n)) (f : V → Fin n),
    (∀ k : Fin n, Fintype.card {v : V // f v = k} = 3) ∧
    (∀ u v : V, G.Adj u v ↔
      (((e u).1 + 1) % (3 * n) = (e v).1 ∨ ((e v).1 + 1) % (3 * n) = (e u).1)
        ∨ (u ≠ v ∧ f u = f v))

/-- **The formal statement of JSP-000698.**

Every cycle-plus-triangles graph is 3-colorable. This is the target proposition; it is
stated here faithfully but not proved in this development. -/
def Jsp698Statement : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V), IsCPTGraph G → ThreeColorable G

end Jsp698