import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models

/-! Edmonds' finite matroid intersection theorem (paper.tex, Theorem 9.8).
The ambient type is arbitrary; only the common actual ground is finite.
The witnesses explicitly attain both extrema, including on an empty ground. -/
namespace Specs.P205.Matroids
universe u

/-- Every common independent set is bounded by every ground split. -/
def IntersectionUpperBound : Prop :=
  ∀ {α : Type u} (M N : Matroid α) [M.Finite] [N.Finite], M.E = N.E →
  ∀ I U : Set α, M.Indep I → N.Indep I → U ⊆ M.E →
    I.ncard ≤ rankValue M U + rankValue N (M.E \ U)

/-- A common independent set and a split attain the same value; they are
respectively a maximum and a minimum over the full original families. -/
def IntersectionAttainment : Prop :=
  ∀ {α : Type u} (M N : Matroid α) [M.Finite] [N.Finite], M.E = N.E →
  ∃ I U : Set α, M.Indep I ∧ N.Indep I ∧ U ⊆ M.E ∧
    I.ncard = rankValue M U + rankValue N (M.E \ U) ∧
    (∀ J : Set α, M.Indep J → N.Indep J → J.ncard ≤ I.ncard) ∧
    (∀ V : Set α, V ⊆ M.E →
      rankValue M U + rankValue N (M.E \ U) ≤
        rankValue M V + rankValue N (M.E \ V))

end Specs.P205.Matroids
