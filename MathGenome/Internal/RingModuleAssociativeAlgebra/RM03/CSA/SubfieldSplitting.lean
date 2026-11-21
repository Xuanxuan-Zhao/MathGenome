import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.SubfieldSplitting
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Splitting by any subfield of degree equal to the degree of the division algebra. -/

namespace RM03.CSA

open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
variable {E : Type w} [Field E] [Algebra k E]

/-- Give `D` its right vector space structure over `E` via the inclusion `f`. -/
abbrev rightSubfieldModule (f : E →ₐ[k] D) : Module E D :=
  Specs.RM03.CSA.rightSubfieldModule f

theorem rightSubfield_smul (f : E →ₐ[k] D) :
    letI := rightSubfieldModule f
    ∀ (e : E) (z : D), e • z = z * f e :=
  fun _ _ => rfl

/-- Let the division algebra act on the left and the subfield on the right. -/
def subfieldTensorAction (f : E →ₐ[k] D) :
    letI := rightSubfieldModule f
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
    D ⊗[k] E →ₐ[E] Module.End E D :=
  Specs.RM03.CSA.subfieldTensorAction f

@[simp]
theorem subfieldTensorAction_tmul (f : E →ₐ[k] D) :
    letI := rightSubfieldModule f
    ∀ (a : D) (e : E) (z : D), subfieldTensorAction f (a ⊗ₜ[k] e) z = a * z * f e :=
  fun _ _ _ => rfl

/-- The dimension over the embedded field follows by the tower law. -/
theorem rightSubfield_dimension (f : E →ₐ[k] D) (hD : IsCentralDivision k D)
    (hE : Module.finrank k E = degree k D) :
    letI := rightSubfieldModule f
    FiniteDimensional E D ∧ Module.finrank E D = degree k D := by
  let := rightSubfieldModule f
  have := Specs.RM03.CSA.rightSubfieldTower f
  let : FiniteDimensional k D := hD.2
  have hFinite : FiniteDimensional E D := Module.Finite.of_restrictScalars_finite k E D
  have hCentral := isCentralSimple_of_isCentralDivision k D hD
  have hTower := Module.finrank_mul_finrank k E D
  rw [hE, finrank_eq_degree_sq hCentral, pow_two] at hTower
  exact ⟨hFinite, Nat.eq_of_mul_eq_mul_left (degree_pos hCentral) hTower⟩

/-- The left and right multiplication action is itself an algebra isomorphism. -/
theorem subfieldTensorAction_isomorphism (f : E →ₐ[k] D) (hD : IsCentralDivision k D)
    (hE : Module.finrank k E = degree k D) :
    letI := rightSubfieldModule f
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
    ∃ iso : D ⊗[k] E ≃ₐ[E] Module.End E D, iso.toAlgHom = subfieldTensorAction f := by
  let := rightSubfieldModule f
  let := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
  have hCentral := isCentralSimple_of_isCentralDivision k D hD
  have hBase := isCentralSimple_baseChange (L := E) hCentral
  have : IsSimpleRing (D ⊗[k] E) := isSimpleRing_tensor hCentral inferInstance
  have : FiniteDimensional E (BaseChange k E D) := hBase.2.2
  obtain ⟨hFinite, hDim⟩ := rightSubfield_dimension f hD hE
  let flip := baseChangeEquivTensor k E D
  let : FiniteDimensional E (D ⊗[k] E) := Module.Finite.equiv flip.toLinearEquiv
  let action := subfieldTensorAction f
  have hInj : Function.Injective action := action.toRingHom.injective
  have hRank : Module.finrank E (D ⊗[k] E) = Module.finrank E (D →ₗ[E] D) := by
    rw [← flip.toLinearEquiv.finrank_eq, finrank_baseChange hCentral, finrank_eq_degree_sq hCentral,
      Module.finrank_linearMap, hDim, pow_two]
  let linearEquiv := LinearEquiv.ofInjectiveOfFinrankEq action.toLinearMap hInj hRank
  exact ⟨AlgEquiv.ofBijective action ⟨hInj, linearEquiv.surjective⟩, rfl⟩

/-- A degree-sized subfield splits the division algebra into matrices of that size. -/
theorem subfield_splits (f : E →ₐ[k] D) (hD : IsCentralDivision k D)
    (hE : Module.finrank k E = degree k D) :
    Nonempty (BaseChange k E D ≃ₐ[E] Matrix (Fin (degree k D)) (Fin (degree k D)) E) := by
  let := rightSubfieldModule f
  let := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
  obtain ⟨hFinite, hDim⟩ := rightSubfield_dimension f hD hE
  obtain ⟨iso, _⟩ := subfieldTensorAction_isomorphism f hD hE
  let basis := Module.finBasisOfFinrankEq E D hDim
  exact ⟨((baseChangeEquivTensor k E D).trans iso).trans (LinearMap.toMatrixAlgEquiv basis)⟩

end RM03.CSA
