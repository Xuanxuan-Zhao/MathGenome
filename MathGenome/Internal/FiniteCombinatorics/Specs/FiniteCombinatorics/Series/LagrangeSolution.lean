import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.CompositionalInverse
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.MultiplicativeInverse

/-! Independent specifications for the existence and uniqueness assertion of
paper.tex, p204:W18. A unit `a₀` represents the constant coefficient of `φ`;
the theorems require the equality explicitly. All series are formal. -/

noncomputable section
universe u

namespace Specs.FiniteCombinatorics.Series.LagrangeSolution

open Specs.FiniteCombinatorics.Series.Substitution

def reversionType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R], PowerSeries R → Rˣ → PowerSeries R

/-- The series g(u) = u/φ(u), with division interpreted by a unit inverse. -/
def reversionValue : reversionType :=
  fun {_} [_] [_] φ a₀ => PowerSeries.X * PowerSeries.invOfUnit φ a₀

def solutionType : Type (u + 1) := reversionType

/-- The canonical compositional inverse of g. Its construction is available
without division by general elements of the coefficient ring. -/
def solutionValue : solutionType :=
  fun {_} [_] [_] φ a₀ =>
    (reversionValue φ a₀).substInvOfIsUnit (by
      change IsUnit (PowerSeries.coeff (0 + 1)
        (PowerSeries.X * PowerSeries.invOfUnit φ a₀))
      rw [PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_invOfUnit]
      exact (a₀⁻¹).isUnit)

def SolutionProperties : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (φ : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff φ = (a₀ : R) →
    PowerSeries.constantCoeff (solutionValue φ a₀) = 0 ∧
      solutionValue φ a₀ = PowerSeries.X * composeValue φ (solutionValue φ a₀)

def InverseRelations : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (φ : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff φ = (a₀ : R) →
    composeValue (reversionValue φ a₀) (solutionValue φ a₀) = PowerSeries.X ∧
      composeValue (solutionValue φ a₀) (reversionValue φ a₀) = PowerSeries.X

/-- Uniqueness among all zero-constant solutions, not merely a selected
class of compositional inverses. -/
def SolutionUnique : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (φ : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff φ = (a₀ : R) → ∀ F : PowerSeries R,
      PowerSeries.constantCoeff F = 0 →
      F = PowerSeries.X * composeValue φ F → F = solutionValue φ a₀

def ExistsUniqueSolution : Prop :=
  ∀ {R : Type u} [CommRing R] [Algebra ℚ R] (φ : PowerSeries R),
    IsUnit (PowerSeries.constantCoeff φ) →
      ∃! F : PowerSeries R, PowerSeries.constantCoeff F = 0 ∧
        F = PowerSeries.X * composeValue φ F

end Specs.FiniteCombinatorics.Series.LagrangeSolution
