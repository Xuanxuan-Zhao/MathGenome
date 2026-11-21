import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.Substitution

/-! Independent specifications for the compositional-inverse assertion of
paper.tex, p204:W12. The coefficient ring is any commutative ring with identity.
The shared substitution is used, and both inverse identities are required. -/

noncomputable section

universe u

namespace Specs.FiniteCombinatorics.Series.CompositionalInverse

open Specs.FiniteCombinatorics.Series.Substitution

/-- A zero-constant series has a two-sided zero-constant compositional inverse
exactly when its linear coefficient is a unit. -/
def ExistsInverseIff : Prop :=
  ∀ {R : Type u} [CommRing R] (B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
    ((∃ C : PowerSeries R, PowerSeries.constantCoeff C = 0 ∧
      composeValue B C = PowerSeries.X ∧ composeValue C B = PowerSeries.X) ↔
      IsUnit (PowerSeries.coeff 1 B))

/-- Uniqueness holds even among zero-constant right compositional inverses. -/
def InverseUnique : Prop :=
  ∀ {R : Type u} [CommRing R] (B C D : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
    PowerSeries.constantCoeff C = 0 → PowerSeries.constantCoeff D = 0 →
    composeValue B C = PowerSeries.X → composeValue B D = PowerSeries.X → C = D

/-- The linear coefficient of any zero-constant compositional inverse is the
inverse of the unit linear coefficient of B. The inverse is taken in Rˣ,
so the statement requires neither a field nor a division operation on R. -/
def InverseLinearCoefficient : Prop :=
  ∀ {R : Type u} [CommRing R] (B C : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
    ∀ hB1 : IsUnit (PowerSeries.coeff 1 B),
    PowerSeries.constantCoeff C = 0 → composeValue B C = PowerSeries.X →
    PowerSeries.coeff 1 C = ↑(hB1.unit⁻¹)

end Specs.FiniteCombinatorics.Series.CompositionalInverse
