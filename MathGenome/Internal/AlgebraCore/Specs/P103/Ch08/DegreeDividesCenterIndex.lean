import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.DegreeDividesOrder
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Center

/-! The two divisibility conclusions of paper.tex 1685–1689.
Irreducibility uses the shared convention, including nonzeroness; finite
dimensionality is a consequence, not an additional hypothesis. -/
universe u v
namespace P103.Ch08.DegreeDividesCenterIndexSpecs

def degree_divides_center_indexType : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ → Module.finrank ℂ V ∣ (Subgroup.center G).index

def degree_divisibilityType : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ →
      Module.finrank ℂ V ∣ Nat.card G ∧
      Module.finrank ℂ V ∣ (Subgroup.center G).index

end P103.Ch08.DegreeDividesCenterIndexSpecs
