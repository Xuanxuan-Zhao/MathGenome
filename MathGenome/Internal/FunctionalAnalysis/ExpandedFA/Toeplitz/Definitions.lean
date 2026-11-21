import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection

/-! Toeplitz and Hankel operators transported through the accepted Hardy
boundary isometry. No additional Hardy space or multiplier certificate is used. -/
noncomputable section
open MeasureTheory
open scoped Real ENNReal InnerProductSpace
set_option maxHeartbeats 800000

namespace ExpandedFA.Toeplitz.Definitions


abbrev H2 := Spec.H2
abbrev Circle := Spec.Circle
abbrev BoundaryL2 := Spec.BoundaryL2
abbrev BoundaryH2 := Spec.BoundaryH2
abbrev ScalarSymbol := Spec.ScalarSymbol
abbrev MatrixSymbol := Spec.MatrixSymbol
abbrev VectorH2 := Spec.VectorH2
abbrev VectorBoundaryL2 := Spec.VectorBoundaryL2
abbrev VectorBoundaryH2 := Spec.VectorBoundaryH2
abbrev symbolOfFunction := Spec.symbolOfFunction
abbrev boundedSymbolOfFunction := Spec.boundedSymbolOfFunction
abbrev continuousSymbol := Spec.continuousSymbol
abbrev continuousMatrixSymbol := @Spec.continuousMatrixSymbol
abbrev multiplication := Spec.multiplication
abbrev boundaryInclusion := Spec.boundaryInclusion
abbrev boundaryAnalysis := Spec.boundaryAnalysis
abbrev positiveProjection := Spec.positiveProjection
abbrev negativeProjection := Spec.negativeProjection
abbrev toeplitz := Spec.toeplitz
abbrev hankel := Spec.hankel
abbrev matrixMultiplication := @Spec.matrixMultiplication
abbrev matrixToeplitz := @Spec.matrixToeplitz
abbrev matrixHankel := @Spec.matrixHankel
abbrev matrixBoundary := Spec.matrixBoundary
abbrev matrixPositiveProjection := Spec.matrixPositiveProjection
abbrev matrixNegativeProjection := Spec.matrixNegativeProjection
abbrev NonvanishingLoop := Spec.NonvanishingLoop
abbrev winding := Spec.winding
abbrev coordinateLoop := Spec.coordinateLoop

theorem hardy_identification : Spec.HardyIdentification :=
  ⟨ExpandedFA.PartIV.HardyDisk.boundary_range, ExpandedFA.PartIV.HardyDisk.boundary_closed⟩

@[simp] theorem boundaryAnalysis_boundary (f : H2) : boundaryAnalysis (ExpandedFA.PartIV.HardyDisk.boundary f) = f := by
  have h := congrArg (fun A : H2 →L[ℂ] H2 => A f)
    ExpandedFA.PartIV.HardyDisk.boundary.adjoint_comp_self
  exact h

theorem positiveProjection_mem (g : BoundaryL2) : positiveProjection g ∈ BoundaryH2 := by
  have h : positiveProjection g ∈ LinearMap.range ExpandedFA.PartIV.HardyDisk.boundary.toLinearMap :=
    ⟨boundaryAnalysis g, rfl⟩
  have hr : LinearMap.range ExpandedFA.PartIV.HardyDisk.boundary.toLinearMap = BoundaryH2 :=
    ExpandedFA.PartIV.HardyDisk.boundary_range
  rw [hr] at h
  exact h

theorem negativeProjection_mem (g : BoundaryL2) :
    negativeProjection g ∈ BoundaryH2.orthogonal := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  obtain ⟨f, rfl⟩ := (show w ∈ LinearMap.range ExpandedFA.PartIV.HardyDisk.boundary.toLinearMap by
    rw [ExpandedFA.PartIV.HardyDisk.boundary_range]; exact hw)
  change ⟪ExpandedFA.PartIV.HardyDisk.boundary f, g - ExpandedFA.PartIV.HardyDisk.boundary (boundaryAnalysis g)⟫_ℂ = 0
  rw [inner_sub_right, ExpandedFA.PartIV.HardyDisk.boundary.inner_map_map]
  exact sub_eq_zero.mpr (boundaryInclusion.adjoint_inner_right f g).symm

theorem projection_characterization : Spec.ProjectionCharacterization := by
  intro g
  exact ⟨positiveProjection_mem g, negativeProjection_mem g,
    by change positiveProjection g + (g - positiveProjection g) = g; abel⟩

theorem native_projections : Spec.NativeProjections := by
  intro hc
  let : CompleteSpace BoundaryH2 := hc.completeSpace_coe
  have hp : positiveProjection = BoundaryH2.starProjection := by
    apply ContinuousLinearMap.ext
    intro g
    symm
    exact Submodule.eq_starProjection_of_mem_orthogonal (positiveProjection_mem g)
      (negativeProjection_mem g)
  refine ⟨hp, ?_⟩
  rw [Submodule.starProjection_orthogonal]
  exact congrArg (fun A => ContinuousLinearMap.id ℂ BoundaryL2 - A) hp

theorem multiplication_values : Spec.MultiplicationValues := by
  intro φ g
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder φ g

theorem function_symbol_values : Spec.FunctionSymbolValues := by
  intro φ hφ
  exact hφ.coeFn_toLp

theorem bounded_symbol_values : Spec.BoundedSymbolValues := by
  intro φ hφ C hb
  exact (memLp_top_of_bound hφ C hb).coeFn_toLp

theorem continuous_symbol_values : Spec.ContinuousSymbolValues := by
  intro φ
  exact ContinuousMap.coeFn_toLp _ φ

theorem scalar_compression : Spec.ScalarCompression := by
  intro φ f
  exact ⟨rfl, rfl, negativeProjection_mem _⟩

/-- The boundary-side compression, using the actual accepted unitary. -/
def boundaryToeplitz (φ : ScalarSymbol) : BoundaryH2 →L[ℂ] BoundaryH2 :=
  ExpandedFA.PartIV.HardyDisk.boundaryEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((toeplitz φ).comp ExpandedFA.PartIV.HardyDisk.boundaryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem boundaryToeplitz_values (φ : ScalarSymbol) (g : BoundaryH2) :
    (boundaryToeplitz φ g).val = positiveProjection (multiplication φ g.val) := by
  change ExpandedFA.PartIV.HardyDisk.boundary (toeplitz φ (ExpandedFA.PartIV.HardyDisk.boundaryEquiv.symm g)) = _
  rw [(scalar_compression φ (ExpandedFA.PartIV.HardyDisk.boundaryEquiv.symm g)).1]
  apply congrArg (fun w => positiveProjection (multiplication φ w))
  exact congrArg Subtype.val (ExpandedFA.PartIV.HardyDisk.boundaryEquiv.apply_symm_apply g)

theorem matrix_boundary_unitary : Spec.MatrixBoundaryUnitary := by
  intro d
  exact ⟨LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin d => ExpandedFA.PartIV.HardyDisk.boundaryEquiv),
    fun f i => rfl⟩

@[simp] theorem operatorMatrix_apply {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ)
    (A : Fin d → Fin d → E →L[ℂ] F) (f : PiLp 2 (fun _ : Fin d => E)) (i : Fin d) :
    Spec.operatorMatrix d A f i = ∑ j : Fin d, A i j (f j) := by
  simp [Spec.operatorMatrix]

@[simp] theorem coordinateOperator_apply {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ) (A : E →L[ℂ] F)
    (f : PiLp 2 (fun _ : Fin d => E)) (i : Fin d) :
    Spec.coordinateOperator d A f i = A (f i) := rfl

theorem matrix_multiplication_values : Spec.MatrixMultiplicationValues := by
  intro d Φ g i
  have he : matrixMultiplication Φ g i =
      ∑ j : Fin d, multiplication (Φ i j) (g j) :=
    operatorMatrix_apply (E := BoundaryL2) (F := BoundaryL2) d
      (fun i j => multiplication (Φ i j)) g i
  rw [he]
  have hsum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin d))
    (fun j => multiplication (Φ i j) (g j))
  filter_upwards [hsum, (Filter.eventually_all_finset Finset.univ).mpr
    (fun j _ => multiplication_values (Φ i j) (g j))] with t ht hmul
  rw [ht]
  exact Finset.sum_congr rfl (fun j hj => hmul j hj)

theorem matrix_compression : Spec.MatrixCompression := by
  intro d Φ f
  refine ⟨?_, ?_, ?_⟩
  · apply PiLp.ext
    intro i
    simp only [Spec.matrixBoundary, coordinateOperator_apply, Spec.matrixToeplitz,
      operatorMatrix_apply, Spec.matrixPositiveProjection, Spec.matrixMultiplication, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (scalar_compression (Φ i j) (f j)).1
  · apply PiLp.ext
    intro i
    simp only [Spec.matrixHankel, operatorMatrix_apply, Spec.matrixNegativeProjection,
      coordinateOperator_apply, Spec.matrixMultiplication, Spec.matrixBoundary, map_sum]
    rfl
  · intro i
    simp only [Spec.matrixHankel, operatorMatrix_apply]
    exact Submodule.sum_mem _ (fun j _ => (scalar_compression (Φ i j) (f j)).2.2)

theorem winding_lift : Spec.WindingLift := by
  intro φ a ha
  exact AddCircle.windingNumber_eq_div (Spec.phasePath φ) a (funext ha)

theorem phase_coordinate (t : Circle) :
    AddCircle.homeomorphCircle'.symm (Spec.loopPhase coordinateLoop t) = t := by
  apply AddCircle.homeomorphCircle'.injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  change (fourier (T := 2 * π) 1 t) / (‖fourier (T := 2 * π) 1 t‖ : ℂ) = _
  rw [fourier_one, Circle.norm_coe, Complex.ofReal_one, div_one]
  induction t using QuotientAddGroup.induction_on
  simp only [AddCircle.toCircle_apply_mk, AddCircle.homeomorphCircle'_apply_mk,
    div_self (by positivity : 2 * π ≠ (0 : ℝ)), one_mul]

theorem winding_coordinate : Spec.WindingCoordinate := by
  have h := winding_lift coordinateLoop
    (⟨fun t => (t : ℝ) * (2 * π), by fun_prop⟩ : C(unitInterval, ℝ)) (by
      intro t
      change (((t : ℝ) * (2 * π) : ℝ) : Circle) =
        AddCircle.homeomorphCircle'.symm (Spec.loopPhase coordinateLoop (Spec.angularTraversal t))
      rw [phase_coordinate]
      simp [Spec.angularTraversal, AddCircle.zsmulLoop])
  have hh : (winding coordinateLoop : ℝ) = 1 := by
    simpa using h
  exact_mod_cast hh

@[simp] theorem boundary_single (n : ℕ) (c : ℂ) :
    ExpandedFA.PartIV.HardyDisk.boundary (lp.single 2 n c) =
      c • fourierLp (T := 2 * π) 2 (n : ℤ) := by
  simp [ExpandedFA.PartIV.HardyDiskSpec.boundary,
    OrthogonalFamily.linearIsometry_apply_single, ExpandedFA.PartIV.HardyDiskSpec.modes]

theorem coordinate_multiplication_mode (n : ℕ) :
    multiplication (continuousSymbol (fourier (T := 2 * π) 1))
      (fourierLp (T := 2 * π) 2 (n : ℤ)) =
        fourierLp (T := 2 * π) 2 ((n : ℤ) + 1) := by
  apply Lp.ext
  filter_upwards [multiplication_values
      (continuousSymbol (fourier (T := 2 * π) 1)) (fourierLp (T := 2 * π) 2 (n : ℤ)),
    continuous_symbol_values (fourier (T := 2 * π) 1),
    coeFn_fourierLp (T := 2 * π) 2 (n : ℤ),
    coeFn_fourierLp (T := 2 * π) 2 ((n : ℤ) + 1)] with t hm hc hn hs
  rw [hm, hc, hn, hs, fourier_add, mul_comm]

theorem coordinate_multiplication_boundary (f : H2) :
    multiplication (continuousSymbol (fourier (T := 2 * π) 1))
      (ExpandedFA.PartIV.HardyDisk.boundary f) =
        ExpandedFA.PartIV.HardyDisk.boundary (ExpandedFA.PartIV.HardyDisk.shift f) := by
  have hm := (multiplication (continuousSymbol (fourier (T := 2 * π) 1))).hasSum
    (ExpandedFA.PartIV.HardyDisk.boundary_series f)
  simp only [map_smul, coordinate_multiplication_mode] at hm
  have he : (fun n : ℕ => boundaryInclusion
      (f n • lp.single 2 (n + 1) (1 : ℂ))) =
      (fun n : ℕ => f n • fourierLp (T := 2 * π) 2 ((n : ℤ) + 1)) := by
    funext n
    have h : boundaryInclusion (lp.single 2 (n + 1) (1 : ℂ)) =
        (1 : ℂ) • fourierLp (T := 2 * π) 2 ((n + 1 : ℕ) : ℤ) :=
      boundary_single (n + 1) 1
    rw [map_smul, h, one_smul, Nat.cast_add, Nat.cast_one]
  have hs' := boundaryInclusion.hasSum (ExpandedFA.PartIV.HardyDisk.shift_series f)
  rw [he] at hs'
  exact hm.unique hs'

theorem coordinate_toeplitz : Spec.CoordinateToeplitz := by
  apply ContinuousLinearMap.ext
  intro f
  change boundaryAnalysis (multiplication (continuousSymbol (fourier (T := 2 * π) 1))
    (ExpandedFA.PartIV.HardyDisk.boundary f)) = ExpandedFA.PartIV.HardyDisk.shift f
  rw [coordinate_multiplication_boundary, boundaryAnalysis_boundary]

end ExpandedFA.Toeplitz.Definitions
