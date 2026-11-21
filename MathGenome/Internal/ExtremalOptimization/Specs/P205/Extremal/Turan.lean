import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! Independent statements for paper.tex, Theorem 1.1 (W01).
`CliqueFree` forbids subgraph copies, with no inducedness condition.
Natural-number division represents the floor in Mantel's bound. -/
namespace P205.Extremal.TuranSpecs

open SimpleGraph

/-- The edge bound and complete equality classification, on any finite vertex type. -/
def extremalStatement : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ), 0 < r → G.CliqueFree (r + 1) →
    G.edgeFinset.card ≤ (turanGraph (Fintype.card V) r).edgeFinset.card ∧
    (G.edgeFinset.card = (turanGraph (Fintype.card V) r).edgeFinset.card ↔
      Nonempty (G ≃g turanGraph (Fintype.card V) r))

/-- A partition indexed by all `r` parts, including empty parts, exhibiting the
canonical graph as complete multipartite with balanced sizes. -/
def balancedStatement : Prop :=
  ∀ (n r : ℕ), 0 < r →
    ∃ P : Fin r → Finset (Fin n),
      (∀ v, ∃! i, v ∈ P i) ∧
      (∀ v w, (turanGraph n r).Adj v w ↔ ¬∃ i, v ∈ P i ∧ w ∈ P i) ∧
      (∀ i, (P i).card = n / r + if i.val < n % r then 1 else 0)

/-- The exact binomial formula for every quotient/remainder decomposition. -/
def edgeFormulaStatement : Prop :=
  ∀ (n r q b : ℕ), 0 < r → b < r → n = q * r + b →
    (turanGraph n r).edgeFinset.card =
      n.choose 2 - (r - b) * q.choose 2 - b * (q + 1).choose 2

/-- Mantel's bound; `n ^ 2 / 4` is natural-number floor division. -/
def mantelStatement : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → G.edgeFinset.card ≤ Fintype.card V ^ 2 / 4

end P205.Extremal.TuranSpecs
