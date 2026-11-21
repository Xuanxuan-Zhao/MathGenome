import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.LagrangeSolution
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.CompositionalInverse
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.MultiplicativeInverse

/-! The unique formal solution of F = X φ(F), paper.tex, p204:W18.
Multiplicative inverses use a specified unit constant coefficient, so rings
with zero divisors and the zero ring are included. -/

noncomputable section
universe u

namespace FiniteCombinatorics.Series

/-- The series g(u) = u/φ(u). The identities below require φ(0) = a₀. -/
def lagrangeReversion {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ) : PowerSeries R :=
  PowerSeries.X * PowerSeries.invOfUnit φ a₀

/-- Construct the solution as the compositional inverse of g. -/
def lagrangeSolution {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ) : PowerSeries R :=
  Specs.FiniteCombinatorics.Series.LagrangeSolution.solutionValue φ a₀

theorem constantCoeff_lagrangeReversion {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ) :
    PowerSeries.constantCoeff (lagrangeReversion φ a₀) = 0 := by
  simp [lagrangeReversion]

/-- Both inverse identities for the constructed solution. -/
theorem lagrange_inverse_relations {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ)
    (_hφ : PowerSeries.constantCoeff φ = (a₀ : R)) :
    compose (lagrangeReversion φ a₀) (lagrangeSolution φ a₀) = PowerSeries.X ∧
      compose (lagrangeSolution φ a₀) (lagrangeReversion φ a₀) = PowerSeries.X := by
  dsimp [lagrangeReversion, lagrangeSolution,
    Specs.FiniteCombinatorics.Series.LagrangeSolution.solutionValue,
    Specs.FiniteCombinatorics.Series.LagrangeSolution.reversionValue, compose]
  exact ⟨PowerSeries.subst_substInvOfIsUnit_right _ (by simp) _,
    PowerSeries.subst_substInvOfIsUnit_left _ (by simp) _⟩

/-- Multiplying by φ(F) or its inverse shows that reversion and the
functional equation are equivalent for every zero-constant F. -/
theorem compose_lagrangeReversion_eq_X_iff {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ)
    (hφ : PowerSeries.constantCoeff φ = (a₀ : R))
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = 0) :
    compose (lagrangeReversion φ a₀) F = PowerSeries.X ↔
      F = PowerSeries.X * compose φ F := by
  let ψ := PowerSeries.invOfUnit φ a₀
  have hφψ : compose φ F * compose ψ F = 1 := by
    rw [← compose_mul φ ψ F hF]
    have h := (invOfUnit_two_sided φ a₀ hφ).1
    rw [show φ * ψ = 1 from h]
    simpa only [map_one] using compose_C (1 : R) F hF
  have hψφ : compose ψ F * compose φ F = 1 := by
    rw [mul_comm]
    exact hφψ
  have hg : compose (lagrangeReversion φ a₀) F = F * compose ψ F := by
    rw [lagrangeReversion, compose_mul _ _ F hF, X_compose F hF]
  rw [hg]
  constructor
  · intro h
    calc
      F = F * (compose ψ F * compose φ F) := by rw [hψφ, mul_one]
      _ = (F * compose ψ F) * compose φ F := (mul_assoc _ _ _).symm
      _ = PowerSeries.X * compose φ F := by rw [h]
  · intro h
    calc
      F * compose ψ F = (PowerSeries.X * compose φ F) * compose ψ F := by rw [← h]
      _ = PowerSeries.X * (compose φ F * compose ψ F) := mul_assoc _ _ _
      _ = PowerSeries.X := by rw [hφψ, mul_one]

/-- The constructed solution is zero-constant and solves F = X φ(F). -/
theorem lagrange_solution_properties {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ)
    (hφ : PowerSeries.constantCoeff φ = (a₀ : R)) :
    PowerSeries.constantCoeff (lagrangeSolution φ a₀) = 0 ∧
      lagrangeSolution φ a₀ = PowerSeries.X * compose φ (lagrangeSolution φ a₀) := by
  have hF : PowerSeries.constantCoeff (lagrangeSolution φ a₀) = 0 := by
    exact PowerSeries.constantCoeff_substInvOfIsUnit _ _
  exact ⟨hF, (compose_lagrangeReversion_eq_X_iff φ a₀ hφ _ hF).mp
    (lagrange_inverse_relations φ a₀ hφ).1⟩

/-- Every zero-constant solution equals the constructed one. -/
theorem lagrange_solution_unique {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (a₀ : Rˣ)
    (hφ : PowerSeries.constantCoeff φ = (a₀ : R))
    (F : PowerSeries R) (hF : PowerSeries.constantCoeff F = 0)
    (heq : F = PowerSeries.X * compose φ F) : F = lagrangeSolution φ a₀ := by
  apply compositional_inverse_unique (lagrangeReversion φ a₀) F (lagrangeSolution φ a₀)
    (constantCoeff_lagrangeReversion φ a₀) hF
    (lagrange_solution_properties φ a₀ hφ).1
  · exact (compose_lagrangeReversion_eq_X_iff φ a₀ hφ F hF).mpr heq
  · exact (lagrange_inverse_relations φ a₀ hφ).1

/-- Existence and uniqueness in the form stated in W18. -/
theorem exists_unique_lagrange_solution {R : Type u} [CommRing R] [Algebra ℚ R]
    (φ : PowerSeries R) (hφ : IsUnit (PowerSeries.constantCoeff φ)) :
    ∃! F : PowerSeries R, PowerSeries.constantCoeff F = 0 ∧
      F = PowerSeries.X * compose φ F := by
  have h : PowerSeries.constantCoeff φ = (hφ.unit : R) := hφ.unit_spec.symm
  refine ⟨lagrangeSolution φ hφ.unit, lagrange_solution_properties φ hφ.unit h, ?_⟩
  intro F hF
  exact lagrange_solution_unique φ hφ.unit h F hF.1 hF.2

end FiniteCombinatorics.Series
