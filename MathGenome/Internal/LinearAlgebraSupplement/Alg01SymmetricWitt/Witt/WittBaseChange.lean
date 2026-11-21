import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.RationalIndex
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.WittBaseChange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Alg01SymmetricWitt.Witt.WittBaseChange

open scoped TensorProduct
open Coordinates (hyperbolicPlane hyperbolicSum)
open RationalIndex (rationalForm)
open Decomposition (IsWittIndex)

noncomputable section

/-- The field `ℚ(√2)` inside the reals. -/
abbrev sqrtTwoExtension := Specs.Alg01SymmetricWitt.Witt.WittBaseChange.sqrtTwoExtension

local notation "K" => (sqrtTwoExtension : Type)

abbrev sqrtTwo : K := Specs.Alg01SymmetricWitt.Witt.WittBaseChange.sqrtTwo

theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := by
  apply Subtype.ext
  exact Real.sq_sqrt (by norm_num)

abbrev coordinateBinaryForm : QuadraticForm K (K × K) :=
  Specs.Alg01SymmetricWitt.Witt.WittBaseChange.coordinateBinaryForm

abbrev coordinateForm : QuadraticForm K ((K × K) × (K × K)) :=
  Specs.Alg01SymmetricWitt.Witt.WittBaseChange.coordinateForm

private theorem coordinateBinaryForm_apply (u v : K) :
    coordinateBinaryForm (u, v) = u ^ 2 - 2 * v ^ 2 := by
  change u * u + (-2 : K) * (v * v) = _
  ring

theorem coordinateForm_apply (x y u v : K) :
    coordinateForm ((x, y), (u, v)) = x * y + u ^ 2 - 2 * v ^ 2 := by
  change x * y + coordinateBinaryForm (u, v) = _
  rw [coordinateBinaryForm_apply]
  ring

/-- Extend the two rational coordinates of each plane using the tensor product unit. -/
private def planeCoordinates : (K ⊗[ℚ] (ℚ × ℚ)) ≃ₗ[K] (K × K) :=
  let unit := TensorProduct.AlgebraTensorModule.rid ℚ K K
  (TensorProduct.prodRight ℚ K K ℚ ℚ).trans (unit.prodCongr unit)

/-- Extend the four rational coordinates by distributing over both planes. -/
private def tensorCoordinates : (K ⊗[ℚ] ((ℚ × ℚ) × (ℚ × ℚ))) ≃ₗ[K] ((K × K) × (K × K)) :=
  (TensorProduct.prodRight ℚ K K (ℚ × ℚ) (ℚ × ℚ)).trans
    (planeCoordinates.prodCongr planeCoordinates)

private theorem tensorCoordinates_tmul (a : K) (x y u v : ℚ) :
    tensorCoordinates (a ⊗ₜ[ℚ] ((x, y), (u, v))) =
      ((a * algebraMap ℚ K x, a * algebraMap ℚ K y),
        (a * algebraMap ℚ K u, a * algebraMap ℚ K v)) := by
  simp [tensorCoordinates, planeCoordinates, Algebra.smul_def, mul_comm]

/-- The canonical tensor-coordinate identification preserves the extended quadratic form. -/
theorem baseChangeCoordinates :
    ∃ e : (rationalForm.baseChange K).IsometryEquiv coordinateForm,
      ∀ (a : K) (x y u v : ℚ),
        e (a ⊗ₜ[ℚ] ((x, y), (u, v))) =
          ((a * algebraMap ℚ K x, a * algebraMap ℚ K y),
            (a * algebraMap ℚ K u, a * algebraMap ℚ K v)) := by
  have h :
      coordinateForm.comp tensorCoordinates.toLinearMap = rationalForm.baseChange K := by
    apply baseChange_ext
    rintro ⟨⟨x, y⟩, ⟨u, v⟩⟩
    change coordinateForm (tensorCoordinates (1 ⊗ₜ[ℚ] ((x, y), (u, v)))) = _
    rw [tensorCoordinates_tmul, QuadraticForm.baseChange_tmul, coordinateForm_apply,
      RationalIndex.rationalForm_apply]
    simp [Algebra.smul_def]
  exact ⟨{ toLinearEquiv := tensorCoordinates, map_app' := fun z =>
    congrArg (fun q : QuadraticForm K _ => q z) h }, tensorCoordinates_tmul⟩

theorem binaryPlaneSplits :
    ∃ e : coordinateBinaryForm.IsometryEquiv (hyperbolicPlane K),
      ∀ u v : K, e (u, v) = (u + sqrtTwo * v, u - sqrtTwo * v) := by
  have hα : sqrtTwo ≠ 0 := by
    intro h
    simpa [h] using sqrtTwo_sq
  have htwo : (2 : K) ≠ 0 := by norm_num
  let e : (K × K) ≃ₗ[K] (K × K) :=
    { toFun := fun z => (z.1 + sqrtTwo * z.2, z.1 - sqrtTwo * z.2)
      invFun := fun z => ((z.1 + z.2) / 2, (z.1 - z.2) / (2 * sqrtTwo))
      left_inv := by
        intro z
        apply Prod.ext <;> dsimp <;> field_simp <;> ring
      right_inv := by
        intro z
        apply Prod.ext <;> dsimp <;> field_simp <;> ring
      map_add' := by
        intro x y
        apply Prod.ext <;> dsimp <;> ring
      map_smul' := by
        intro a z
        apply Prod.ext <;>
          simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring }
  refine ⟨{ toLinearEquiv := e, map_app' := ?_ }, fun _ _ => rfl⟩
  rintro ⟨u, v⟩
  rw [Coordinates.hyperbolicPlane_apply, coordinateBinaryForm_apply]
  change (u + sqrtTwo * v) * (u - sqrtTwo * v) = u ^ 2 - 2 * v ^ 2
  calc
    _ = u ^ 2 - sqrtTwo ^ 2 * v ^ 2 := by ring
    _ = _ := by rw [sqrtTwo_sq]

theorem baseChangeHyperbolic :
    (rationalForm.baseChange K).Equivalent (hyperbolicSum K 2) := by
  obtain ⟨toCoordinates, _⟩ := baseChangeCoordinates
  obtain ⟨split, _⟩ := binaryPlaneSplits
  let toPlanes : (hyperbolicSum K 2).IsometryEquiv
      ((hyperbolicPlane K).prod (hyperbolicPlane K)) :=
    { toLinearEquiv := LinearEquiv.piFinTwo K (fun _ => K × K)
      map_app' := by
        intro z
        simp [Coordinates.hyperbolicSum_apply, Fin.sum_univ_two] }
  exact ⟨toCoordinates.trans
    (((QuadraticMap.IsometryEquiv.refl (hyperbolicPlane K)).prod split).trans toPlanes.symm)⟩

/-- The same rational form has index one over the rationals and two after base change. -/
theorem wittIndexComparison :
    IsWittIndex rationalForm 1 ∧ IsWittIndex (rationalForm.baseChange K) 2 := by
  refine ⟨RationalIndex.rationalForm_wittIndex, ?_⟩
  obtain ⟨e⟩ := baseChangeHyperbolic
  let : FiniteDimensional K (K ⊗[ℚ] ((ℚ × ℚ) × (ℚ × ℚ))) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let q := rationalForm.baseChange K
  let H := hyperbolicSum K 2
  have hH : H.Nondegenerate := (Coordinates.hyperbolicNondegenerate K).2 2
  have hq : q.Nondegenerate := by
    rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
    calc
      q.radical = H.radical.map e.symm.toLinearMap := Eq.symm e.symm.map_radical
      _ = ⊥ := by rw [hH.radical_eq_bot, Submodule.map_bot]
  let q₀ : QuadraticForm K (Fin 0 → K) := 0
  let withZero : (H.prod q₀).IsometryEquiv H :=
    { toLinearEquiv := LinearEquiv.prodUnique
      map_app' := fun z => by simp [q₀, QuadraticMap.prod_apply] }
  exact (Decomposition.isWittIndex_iff q q₀ 2 2 hq
    (Coordinates.anisotropic_of_subsingleton q₀) ⟨e.trans withZero.symm⟩).2 rfl

end

end Alg01SymmetricWitt.Witt.WittBaseChange
