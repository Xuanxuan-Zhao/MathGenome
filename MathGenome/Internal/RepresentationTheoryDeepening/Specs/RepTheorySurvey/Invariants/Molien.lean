import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.SymmetricPowerTrace
import Mathlib.RepresentationTheory.Basic

open scoped BigOperators

namespace RepTheorySurvey.Invariants

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]

/-- The degree-`d` elements of the symmetric algebra on `W` fixed by every group element. -/
def symmetricDegreeInvariants (ρ : Representation k G W) (d : ℕ) :
    Submodule k (symmetricDegree k W d) :=
  ⨅ g : G, LinearMap.ker (symmetricDegreeMap d (ρ g) - 1)

end RepTheorySurvey.Invariants

namespace Specs.RepTheorySurvey.Invariants.Molien

open _root_.RepTheorySurvey.Invariants

/-- Molien's formula for the symmetric algebra of the given representation. -/
def formula : Prop :=
  ∀ {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]
    [CharZero k] [Finite G] [Module.Finite k W] (ρ : Representation k G W),
    letI := Fintype.ofFinite G
    PowerSeries.mk (fun d => (Module.finrank k (symmetricDegreeInvariants ρ d) : k)) =
      PowerSeries.C (Nat.card G : k)⁻¹ * ∑ g : G, (symmetricTraceDenominator (ρ g))⁻¹

end Specs.RepTheorySurvey.Invariants.Molien
