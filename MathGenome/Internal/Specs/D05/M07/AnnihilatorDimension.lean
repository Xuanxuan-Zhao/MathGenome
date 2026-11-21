import MathGenome.Internal.Specs.D05.M07.Annihilator
import MathGenome.Internal.Specs.D05.M07.DualBasis

/-!
Independent specifications for K05.07.annihilator_dimension
(paper.tex:1029–1035).

The annihilator is the canonical submodule of the algebraic dual consisting of
functionals vanishing on `U`, as specified in K05.07.annihilator. Dimensions are
natural-number dimensions over the same field. Finiteness of the annihilator is
part of the conclusion, rather than an additional premise. The endpoint
identities hold even when the ambient space is infinite dimensional.
-/

namespace Specs.D05.M07.AnnihilatorDimension

/-- The annihilator is finite dimensional and has the complementary dimension. -/
def annihilator_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    FiniteDimensional K U.dualAnnihilator ∧
      Module.finrank K U.dualAnnihilator = Module.finrank K V - Module.finrank K U

/-- The paper's formula with the dimensions named explicitly as `n` and `k`. -/
def annihilator_dimension_of_dimensions : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V) (n k : ℕ),
    Module.finrank K V = n → Module.finrank K U = k →
      Module.finrank K U.dualAnnihilator = n - k

/-- A functional vanishing on the whole space is the zero functional. -/
def annihilator_top : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (⊤ : Submodule K V).dualAnnihilator = (⊥ : Submodule K (Module.Dual K V))

/-- Every linear functional vanishes on the zero subspace. -/
def annihilator_bot : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    (⊥ : Submodule K V).dualAnnihilator = (⊤ : Submodule K (Module.Dual K V))

end Specs.D05.M07.AnnihilatorDimension
