import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Series

/-! Equivariant Jordan–Hölder uniqueness for chief factors (paper.tex, Theorem 1.3). -/

namespace Specs.ALG02GroupTheory.Chief.Uniqueness

open Specs.ALG02GroupTheory.Chief.Series

universe u

/-- The lengths agree, and a bijection of step indices matches the actual
quotients equivariantly. Indexing every occurrence separately records the
multiplicity of each isomorphism class. -/
def ChiefSeriesUniqueness : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (s t : Chain G),
    s.length = t.length ∧
      ∃ e : Fin s.length ≃ Fin t.length, ∀ i : Fin s.length,
        Nonempty (gEquivValue G (chiefFactorValue s i) (chiefFactorValue t (e i)))

end Specs.ALG02GroupTheory.Chief.Uniqueness
