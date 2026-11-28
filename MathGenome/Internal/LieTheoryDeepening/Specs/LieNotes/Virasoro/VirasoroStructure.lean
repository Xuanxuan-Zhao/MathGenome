import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Virasoro.VirasoroCocycle

/-! The center and derived algebra of the canonical Virasoro algebra in Theorem KM11. -/

namespace LieNotes.Virasoro.VirasoroSpec

/-- The elements commuting with the whole algebra form the complex line through (C). -/
def Center : Prop :=
  ∀ x : Vir, (∀ y : Vir, bracket y x = 0) ↔ x ∈ Submodule.span ℂ {central}

/-- The derived algebra is the linear span of the brackets, which is all of Virasoro. -/
def Perfectness : Prop :=
  Submodule.span ℂ {bracket x y | (x : Vir) (y : Vir)} = ⊤

end LieNotes.Virasoro.VirasoroSpec
