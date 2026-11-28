import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PowerSeries.Inverse

open Module
open scoped TensorProduct

namespace RepTheorySurvey.Invariants

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]

/-- The degree-`d` subspace of the symmetric algebra on `W`. -/
def symmetricDegree (k W : Type*) [Field k] [AddCommGroup W] [Module k W] (d : ℕ) :
    Submodule k (SymmetricAlgebra k W) :=
  (LinearMap.range (SymmetricAlgebra.ι k W)) ^ d

/-- The algebra endomorphism induced from the map on the generators. -/
def symmetricAlgebraMap (f : W →ₗ[k] W) : SymmetricAlgebra k W →ₐ[k] SymmetricAlgebra k W :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k W).comp f)

theorem symmetricAlgebraMap_mem (f : W →ₗ[k] W) {d : ℕ} {x : SymmetricAlgebra k W}
    (hx : x ∈ symmetricDegree k W d) : symmetricAlgebraMap f x ∈ symmetricDegree k W d := by
  have hr : Submodule.map (symmetricAlgebraMap f).toLinearMap
      (LinearMap.range (SymmetricAlgebra.ι k W)) ≤ LinearMap.range (SymmetricAlgebra.ι k W) := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨f w, by simp [symmetricAlgebraMap]⟩
  have hm : Submodule.map (symmetricAlgebraMap f).toLinearMap
      (symmetricDegree k W d) ≤ symmetricDegree k W d := by
    unfold symmetricDegree
    rw [Submodule.map_pow]
    exact pow_le_pow_left' hr _
  exact hm (Submodule.mem_map_of_mem hx)

/-- The linear map induced by `f` on the degree-`d` symmetric power. -/
def symmetricDegreeMap (d : ℕ) (f : W →ₗ[k] W) :
    Module.End k (symmetricDegree k W d) :=
  (symmetricAlgebraMap f).toLinearMap.restrict (fun _ hx => symmetricAlgebraMap_mem f hx)

/-- The determinant of `1 - X f` after scalar extension to the power series ring. -/
noncomputable def symmetricTraceDenominator (f : W →ₗ[k] W) : PowerSeries k :=
  LinearMap.det (1 - (PowerSeries.X : PowerSeries k) • f.baseChange (PowerSeries k))

end RepTheorySurvey.Invariants

namespace Specs.RepTheorySurvey.Invariants.SymmetricPowerTrace

open _root_.RepTheorySurvey.Invariants

def degreeComparison : Prop :=
  ∀ {k W ι : Type*} [Field k] [AddCommGroup W] [Module k W]
    (b : Basis ι k W) (d : ℕ),
    Submodule.map (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv.toLinearMap
      (symmetricDegree k W d) = MvPolynomial.homogeneousSubmodule ι k d

def finiteDegree : Prop :=
  ∀ {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W] (d : ℕ),
    Module.Finite k (symmetricDegree k W d)

def mapOnGenerator : Prop :=
  ∀ {k W : Type*} [Field k] [AddCommGroup W] [Module k W] (f : W →ₗ[k] W) (w : W),
    symmetricAlgebraMap f (SymmetricAlgebra.ι k W w) = SymmetricAlgebra.ι k W (f w)

def mapOne : Prop :=
  ∀ {k W : Type*} [Field k] [AddCommGroup W] [Module k W] (d : ℕ),
    symmetricDegreeMap (k := k) (W := W) d 1 = 1

def mapMul : Prop :=
  ∀ {k W : Type*} [Field k] [AddCommGroup W] [Module k W] (d : ℕ) (f g : Module.End k W),
    symmetricDegreeMap d (f * g) = symmetricDegreeMap d f * symmetricDegreeMap d g

def constantCoeff : Prop :=
  ∀ {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (f : W →ₗ[k] W), PowerSeries.constantCoeff (symmetricTraceDenominator f) = 1

def traceIdentity : Prop :=
  ∀ {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [CharZero k] [Module.Finite k W]
    (g : W ≃ₗ[k] W), IsOfFinOrder g →
    PowerSeries.mk (fun d => LinearMap.trace k (symmetricDegree k W d)
      (symmetricDegreeMap d g.toLinearMap)) = (symmetricTraceDenominator g.toLinearMap)⁻¹

end Specs.RepTheorySurvey.Invariants.SymmetricPowerTrace
