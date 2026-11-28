import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Molien
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.FiniteAveraging
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.SymmetricPowerTrace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

open scoped BigOperators

namespace RepTheorySurvey.Invariants

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]

private def symmetricDegreeRepresentation (ρ : Representation k G W) (d : ℕ) :
    Representation k G (symmetricDegree k W d) where
  toFun g := symmetricDegreeMap d (ρ g)
  map_one' := by rw [map_one, symmetricDegreeMap_one]
  map_mul' g h := by rw [map_mul, symmetricDegreeMap_mul]

private theorem symmetricDegreeRepresentation_invariants (ρ : Representation k G W) (d : ℕ) :
    (symmetricDegreeRepresentation ρ d).invariants = symmetricDegreeInvariants ρ d := by
  ext v
  simp [symmetricDegreeInvariants, symmetricDegreeRepresentation, LinearMap.sub_apply, sub_eq_zero]

/-- Molien's formula for the dimensions of the invariants of the homogeneous symmetric powers. -/
theorem molien [CharZero k] [Finite G] [Module.Finite k W] (ρ : Representation k G W) :
    letI := Fintype.ofFinite G
    PowerSeries.mk (fun d => (Module.finrank k (symmetricDegreeInvariants ρ d) : k)) =
      PowerSeries.C (Nat.card G : k)⁻¹ * ∑ g : G, (symmetricTraceDenominator (ρ g))⁻¹ := by
  let : Fintype G := Fintype.ofFinite G
  let action := (LinearMap.GeneralLinearGroup.generalLinearEquiv k W).toMonoidHom.comp ρ.asGroupHom
  have htrace (g : G) :
      PowerSeries.mk (fun d => LinearMap.trace k (symmetricDegree k W d)
        (symmetricDegreeMap d (ρ g))) = (symmetricTraceDenominator (ρ g))⁻¹ := by
    have h := symmetricPowerTrace (action g) (action.isOfFinOrder (isOfFinOrder_of_finite g))
    simpa only [action, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap, Representation.asGroupHom_apply]
      using h
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, map_sum]
  simp_rw [← htrace, PowerSeries.coeff_mk]
  let σ := symmetricDegreeRepresentation ρ d
  have hcard : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne'
  let : Module.Free k σ.invariants := Module.Free.of_divisionRing k σ.invariants
  let : Module.Free k (LinearMap.ker (GroupRepresentation.finiteAverage σ)) :=
    Module.Free.of_divisionRing k (LinearMap.ker (GroupRepresentation.finiteAverage σ))
  have hproj : LinearMap.trace k (symmetricDegree k W d) (GroupRepresentation.finiteAverage σ) =
      (Module.finrank k σ.invariants : k) :=
    (GroupRepresentation.finiteAverage_isProj σ hcard).trace
  rw [symmetricDegreeRepresentation_invariants] at hproj
  change LinearMap.trace k (symmetricDegree k W d)
    ((Nat.card G : k)⁻¹ • ∑ g : G, symmetricDegreeMap d (ρ g)) = _ at hproj
  simpa only [map_smul, map_sum, smul_eq_mul] using hproj.symm

end RepTheorySurvey.Invariants
