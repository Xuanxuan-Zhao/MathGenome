import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.HankelCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Toeplitz.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal NNReal Topology InnerProductSpace
set_option maxHeartbeats 800000

namespace ExpandedFA.Toeplitz.HankelCompactness
open ExpandedFA.Toeplitz.Definitions

private theorem boundaryInclusion_norm : ‖boundaryInclusion‖ ≤ 1 :=
  ExpandedFA.PartIV.HardyDisk.boundary.norm_toContinuousLinearMap_le

private theorem boundaryAnalysis_norm : ‖boundaryAnalysis‖ ≤ 1 := by
  change ‖boundaryInclusion.adjoint‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact boundaryInclusion_norm

theorem multiplication_norm (φ : ScalarSymbol) : ‖multiplication φ‖ ≤ ‖φ‖ := by
  exact le_trans (((ContinuousLinearMap.mul ℂ ℂ).holderL Definitions.Spec.circleMeasure ∞ 2 2).le_opNorm φ)
    (by
      have h := (ContinuousLinearMap.mul ℂ ℂ).norm_holderL_le
        (μ := Definitions.Spec.circleMeasure) (p := ∞) (q := 2) (r := 2)
      have hm : ‖ContinuousLinearMap.mul ℂ ℂ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℂ ℂ
      calc
        _ ≤ 1 * ‖φ‖ := mul_le_mul_of_nonneg_right (h.trans hm) (norm_nonneg _)
        _ = _ := one_mul _)

theorem toeplitz_norm : Spec.ToeplitzNorm := by
  intro φ
  change ‖boundaryAnalysis.comp ((multiplication φ).comp boundaryInclusion)‖ ≤ ‖φ‖
  calc
    _ ≤ ‖boundaryAnalysis‖ * (‖multiplication φ‖ * ‖boundaryInclusion‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖φ‖ * 1) := by gcongr; exact boundaryAnalysis_norm; exact multiplication_norm φ; exact boundaryInclusion_norm
    _ = _ := by ring

theorem continuousSymbol_norm (φ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)) : ‖continuousSymbol φ‖ ≤ ‖φ‖ := by
  have h := (ContinuousMap.toLp (E := ℂ) ∞ Definitions.Spec.circleMeasure ℂ).le_opNorm φ
  have hb := ContinuousMap.toLp_norm_le (p := ∞) (E := ℂ) (𝕜 := ℂ) Definitions.Spec.circleMeasure
  have hb' : ‖ContinuousMap.toLp (E := ℂ) ∞ Definitions.Spec.circleMeasure ℂ‖ ≤ 1 := by simpa using hb
  exact h.trans (by simpa using mul_le_mul_of_nonneg_right hb' (norm_nonneg φ))

theorem continuous_toeplitz_norm : Spec.ContinuousToeplitzNorm := by
  intro φ
  exact (toeplitz_norm _).trans (continuousSymbol_norm φ)

@[simp] theorem negativeProjection_boundary (f : H2) :
    negativeProjection (ExpandedFA.PartIV.HardyDisk.boundary f) = 0 := by
  change ExpandedFA.PartIV.HardyDisk.boundary f -
    ExpandedFA.PartIV.HardyDisk.boundary (boundaryAnalysis (ExpandedFA.PartIV.HardyDisk.boundary f)) = 0
  rw [boundaryAnalysis_boundary, sub_self]

theorem negativeProjection_mode_nonneg (k : ℤ) (hk : 0 ≤ k) :
    negativeProjection (fourierLp (T := 2 * π) 2 k) = 0 := by
  have hb : ExpandedFA.PartIV.HardyDisk.boundary (lp.single 2 k.toNat (1 : ℂ)) =
      fourierLp (T := 2 * π) 2 k := by
    simpa only [one_smul, Int.toNat_of_nonneg hk] using boundary_single k.toNat 1
  rw [← hb, negativeProjection_boundary]

theorem mode_multiplication (m k : ℤ) :
    multiplication (continuousSymbol (fourier (T := 2 * π) m))
      (fourierLp (T := 2 * π) 2 k) = fourierLp (T := 2 * π) 2 (k + m) := by
  apply Lp.ext
  filter_upwards [multiplication_values
      (continuousSymbol (fourier (T := 2 * π) m)) (fourierLp (T := 2 * π) 2 k),
    continuous_symbol_values (fourier (T := 2 * π) m),
    coeFn_fourierLp (T := 2 * π) 2 k,
    coeFn_fourierLp (T := 2 * π) 2 (k + m)] with t hm hc hk hs
  rw [hm, hc, hk, hs, fourier_add, mul_comm]

/-- A monomial can cross the Hardy frequency boundary only at finitely many inputs. -/
theorem hankel_mode_finite_sum (m : ℤ) (f : H2) :
    hankel (continuousSymbol (fourier (T := 2 * π) m)) f =
      ∑ n ∈ Finset.range m.natAbs,
        f n • negativeProjection (fourierLp (T := 2 * π) 2 ((n : ℤ) + m)) := by
  have h := (negativeProjection.comp
    (multiplication (continuousSymbol (fourier (T := 2 * π) m)))).hasSum
      (ExpandedFA.PartIV.HardyDisk.boundary_series f)
  simp only [ContinuousLinearMap.comp_apply, map_smul, mode_multiplication] at h
  have hz : ∀ n ∉ Finset.range m.natAbs,
      f n • negativeProjection (fourierLp (T := 2 * π) 2 ((n : ℤ) + m)) = 0 := by
    intro n hn
    have hn' : m.natAbs ≤ n := by simpa using hn
    have hm := Int.le_natAbs (a := -m)
    rw [Int.natAbs_neg] at hm
    rw [negativeProjection_mode_nonneg _ (by omega), smul_zero]
  exact h.unique (hasSum_sum_of_ne_finset_zero hz)

private theorem compact_smulRight {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (a : E →L[ℂ] ℂ) (v : F) :
    IsCompactOperator (a.smulRight v) := by
  let b : ℂ →L[ℂ] F := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  exact (isCompactOperator_of_locallyCompactSpace_dom a).clm_comp b

private theorem compact_finset_sum {E F ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (s : Finset ι) (A : ι → E →L[ℂ] F) (h : ∀ i ∈ s, IsCompactOperator (A i)) :
    IsCompactOperator ((∑ i ∈ s, A i) : E →L[ℂ] F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] F))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem hankel_mode_compact (m : ℤ) :
    IsCompactOperator (hankel (continuousSymbol (fourier (T := 2 * π) m))) := by
  have he : hankel (continuousSymbol (fourier (T := 2 * π) m)) =
      ∑ n ∈ Finset.range m.natAbs,
        (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).smulRight
          (negativeProjection (fourierLp (T := 2 * π) 2 ((n : ℤ) + m))) := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [sum_apply, ContinuousLinearMap.smulRight_apply,
      lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply] using hankel_mode_finite_sum m f
  rw [he]
  exact compact_finset_sum _ _ (fun n _ => compact_smulRight _ _)

/-- The actual continuous linear dependence of the Hankel map on its symbol. -/
private def hankelSymbolMap : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ) →L[ℂ]
    H2 →L[ℂ] BoundaryL2 :=
  (ContinuousLinearMap.compL ℂ H2 BoundaryL2 BoundaryL2 negativeProjection).comp
    (((ContinuousLinearMap.compL ℂ H2 BoundaryL2 BoundaryL2).flip boundaryInclusion).comp
      (((ContinuousLinearMap.mul ℂ ℂ).holderL Definitions.Spec.circleMeasure ∞ 2 2).comp
        (ContinuousMap.toLp ∞ Definitions.Spec.circleMeasure ℂ)))

private theorem hankelSymbolMap_apply (φ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)) :
    hankelSymbolMap φ = hankel (continuousSymbol φ) := rfl

theorem hankel_compact : Spec.HankelCompact := by
  let M : Submodule ℂ C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ) :=
    { carrier := {φ | IsCompactOperator (hankelSymbolMap φ)}
      zero_mem' := by
        change IsCompactOperator (hankelSymbolMap 0)
        rw [map_zero]
        exact isCompactOperator_zero
      add_mem' := by
        intro φ ψ hφ hψ
        change IsCompactOperator (hankelSymbolMap (φ + ψ))
        rw [map_add]
        exact hφ.add hψ
      smul_mem' := by
        intro c φ hφ
        change IsCompactOperator (hankelSymbolMap (c • φ))
        rw [map_smul]
        exact hφ.smul c }
  have hclosed : IsClosed (M : Set C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)) :=
    isClosed_setOfPred_isCompactOperator.preimage hankelSymbolMap.continuous
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 2 * π))) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact hankel_mode_compact m
  have hclosure := Submodule.topologicalClosure_minimal _ hspan hclosed
  rw [span_fourier_closure_eq_top] at hclosure
  intro φ
  exact hclosure (Submodule.mem_top : φ ∈ (⊤ : Submodule ℂ C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)))

theorem multiplication_product (φ ψ : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)) :
    multiplication (continuousSymbol (φ * ψ)) =
      (multiplication (continuousSymbol φ)).comp (multiplication (continuousSymbol ψ)) := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  filter_upwards [multiplication_values (continuousSymbol (φ * ψ)) g,
    multiplication_values (continuousSymbol φ) (multiplication (continuousSymbol ψ) g),
    multiplication_values (continuousSymbol ψ) g,
    continuous_symbol_values φ, continuous_symbol_values ψ,
    continuous_symbol_values (φ * ψ)] with t hp ho hi hφ hψ hφψ
  simp only [ContinuousLinearMap.comp_apply]
  rw [hp, ho, hi, hφ, hψ, hφψ, ContinuousMap.mul_apply, mul_assoc]

theorem product_defect_formula : Spec.ProductDefectFormula := by
  intro φ ψ
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    neg_apply]
  change boundaryAnalysis (multiplication (continuousSymbol φ)
      (boundaryInclusion (boundaryAnalysis (multiplication (continuousSymbol ψ) (boundaryInclusion f))))) -
    boundaryAnalysis (multiplication (continuousSymbol (φ * ψ)) (boundaryInclusion f)) =
    -(boundaryAnalysis (multiplication (continuousSymbol φ)
      (multiplication (continuousSymbol ψ) (boundaryInclusion f) -
        boundaryInclusion (boundaryAnalysis (multiplication (continuousSymbol ψ) (boundaryInclusion f))))))
  rw [multiplication_product]
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem product_defect_compact : Spec.ProductDefectCompact := by
  intro φ ψ
  rw [product_defect_formula φ ψ]
  exact ((hankel_compact ψ).clm_comp
    (boundaryAnalysis.comp (multiplication (continuousSymbol φ)))).neg

private def matrixInsertion {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (d : ℕ) (i : Fin d) : F →L[ℂ] PiLp 2 (fun _ : Fin d => F) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin d => F) i)

theorem operatorMatrix_decomposition {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ)
    (A : Fin d → Fin d → E →L[ℂ] F) :
    Definitions.Spec.operatorMatrix d A = ∑ i : Fin d, ∑ j : Fin d,
      (matrixInsertion d i).comp ((A i j).comp (PiLp.proj (p := 2) (fun _ : Fin d => E) j)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro k
  simp only [operatorMatrix_apply, sum_apply, ContinuousLinearMap.comp_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  have hins (i : Fin d) (v : F) : matrixInsertion d i v k = if k = i then v else 0 := by
    simp [matrixInsertion, ContinuousLinearMap.single_apply]
  simp only [hins, PiLp.proj_apply]
  simp

/-- A finite matrix of compact maps between normed spaces is compact on their
finite Hilbert sums. The empty matrix is included. -/
theorem operatorMatrix_compact {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ)
    (A : Fin d → Fin d → E →L[ℂ] F) (hA : ∀ i j, IsCompactOperator (A i j)) :
    IsCompactOperator (Definitions.Spec.operatorMatrix d A) := by
  rw [operatorMatrix_decomposition]
  apply compact_finset_sum
  intro i _
  apply compact_finset_sum
  intro j _
  exact ((hA i j).comp_clm (PiLp.proj (p := 2) (fun _ : Fin d => E) j)).clm_comp
    (matrixInsertion d i)


theorem matrix_hankel_compact : Spec.MatrixHankelCompact := by
  intro d Φ
  exact operatorMatrix_compact d _ (fun i j => hankel_compact (Φ i j))

private def toeplitzSymbolMap : C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ) →L[ℂ]
    H2 →L[ℂ] H2 :=
  (ContinuousLinearMap.compL ℂ H2 BoundaryL2 H2 boundaryAnalysis).comp
    (((ContinuousLinearMap.compL ℂ H2 BoundaryL2 BoundaryL2).flip boundaryInclusion).comp
      (((ContinuousLinearMap.mul ℂ ℂ).holderL Definitions.Spec.circleMeasure ∞ 2 2).comp
        (ContinuousMap.toLp ∞ Definitions.Spec.circleMeasure ℂ)))

/-- The matrix product defect has entries summed in the order Φᵢₖ Ψₖⱼ. -/
theorem matrix_product_defect_compact : Spec.MatrixProductDefectCompact := by
  intro d Φ Ψ
  let A (i j : Fin d) : H2 →L[ℂ] H2 := ∑ k : Fin d,
    ((toeplitz (continuousSymbol (Φ i k))).comp (toeplitz (continuousSymbol (Ψ k j))) -
      toeplitz (continuousSymbol (Φ i k * Ψ k j)))
  have hA (i j : Fin d) : IsCompactOperator (A i j) :=
    compact_finset_sum _ _ (fun k _ => product_defect_compact (Φ i k) (Ψ k j))
  have he : (matrixToeplitz (continuousMatrixSymbol Φ)).comp
      (matrixToeplitz (continuousMatrixSymbol Ψ)) -
        matrixToeplitz (continuousMatrixSymbol (Φ * Ψ)) =
      Definitions.Spec.operatorMatrix d A := by
    apply ContinuousLinearMap.ext
    intro f
    apply PiLp.ext
    intro i
    simp only [sub_apply, ContinuousLinearMap.comp_apply, WithLp.ofLp_sub, Pi.sub_apply,
      Definitions.Spec.matrixToeplitz, operatorMatrix_apply,
      Definitions.Spec.continuousMatrixSymbol, Matrix.mul_apply]
    change (∑ k : Fin d, toeplitzSymbolMap (Φ i k)
      (∑ j : Fin d, toeplitzSymbolMap (Ψ k j) (f j))) -
      (∑ j : Fin d, toeplitzSymbolMap (∑ k : Fin d, Φ i k * Ψ k j) (f j)) =
      ∑ j : Fin d, (∑ k : Fin d,
        ((toeplitzSymbolMap (Φ i k)).comp (toeplitzSymbolMap (Ψ k j)) -
          toeplitzSymbolMap (Φ i k * Ψ k j))) (f j)
    simp only [map_sum, sum_apply, sub_apply, ContinuousLinearMap.comp_apply,
      Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [he]
  exact operatorMatrix_compact d A hA

/-- Continuous matrix loops are bounded in the Euclidean operator norm. -/
theorem pointwiseMatrix_continuous {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ)) :
    Continuous (Spec.pointwiseMatrix Φ) := by
  unfold Spec.pointwiseMatrix
  simp_rw [operatorMatrix_decomposition]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((ContinuousLinearMap.mul ℂ ℂ).continuous.comp (Φ i j).continuous).clm_comp_const
    (PiLp.proj (p := 2) (fun _ : Fin d => ℂ) j)).const_clm_comp (matrixInsertion d i)

private theorem l2_norm_sq_integral (g : BoundaryL2) :
    ‖g‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 ∂Definitions.Spec.circleMeasure := by
  calc
    ‖g‖ ^ 2 = Complex.re ⟪g, g⟫_ℂ := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) g
    _ = ∫ t, Complex.re ⟪g t, g t⟫_ℂ ∂Definitions.Spec.circleMeasure :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) g g)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun t =>
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (g t)).symm)

private theorem vectorL2_norm_sq_integral {d : ℕ} (g : VectorBoundaryL2 d) :
    ‖g‖ ^ 2 = ∫ t, ∑ i : Fin d, ‖g i t‖ ^ 2 ∂Definitions.Spec.circleMeasure := by
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => l2_norm_sq_integral (g i))
  · intro i _
    exact (Lp.memLp (g i)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

private theorem matrixMultiplication_bound {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) C(ExpandedFA.Toeplitz.Definitions.Spec.Circle, ℂ))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, ‖Spec.pointwiseMatrix Φ t‖ ≤ C)
    (g : VectorBoundaryL2 d) :
    ‖matrixMultiplication (continuousMatrixSymbol Φ) g‖ ≤ C * ‖g‖ := by
  let y := matrixMultiplication (continuousMatrixSymbol Φ) g
  have hy (i : Fin d) : ∀ᵐ t ∂Definitions.Spec.circleMeasure,
      y i t = ∑ j : Fin d, Φ i j t * g j t := by
    have hc : ∀ᵐ t ∂Definitions.Spec.circleMeasure,
        ∀ j ∈ (Finset.univ : Finset (Fin d)), continuousSymbol (Φ i j) t = Φ i j t :=
      (Filter.eventually_all_finset Finset.univ).mpr (fun j _ => continuous_symbol_values (Φ i j))
    filter_upwards [matrix_multiplication_values d (continuousMatrixSymbol Φ) g i, hc] with t ht hc
    exact ht.trans (Finset.sum_congr rfl (fun j hj => by rw [show
      continuousMatrixSymbol Φ i j t = Φ i j t from hc j hj]))
  have hpoint : ∀ᵐ t ∂Definitions.Spec.circleMeasure,
      (∑ i : Fin d, ‖y i t‖ ^ 2) ≤ C ^ 2 * ∑ i : Fin d, ‖g i t‖ ^ 2 := by
    filter_upwards [(Filter.eventually_all_finset Finset.univ).mpr (fun i _ => hy i)] with t ht
    let v : Spec.MatrixFiber d := WithLp.toLp 2 (fun i => g i t)
    let w : Spec.MatrixFiber d := WithLp.toLp 2 (fun i => y i t)
    have hw : w = Spec.pointwiseMatrix Φ t v := by
      apply PiLp.ext
      intro i
      exact (ht i (Finset.mem_univ i)).trans (by
        simp [Spec.pointwiseMatrix, operatorMatrix_apply, v])
    have hn : ‖w‖ ≤ C * ‖v‖ := hw ▸ (Spec.pointwiseMatrix Φ t).le_of_opNorm_le (hbound t) v
    have hs := pow_le_pow_left₀ (norm_nonneg w) hn 2
    simpa only [PiLp.norm_sq_eq_of_L2, mul_pow, v, w, PiLp.toLp_apply] using hs
  have hi := integral_mono_ae
    (integrable_finsetSum _ (fun i _ => (Lp.memLp (y i)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)))
    ((integrable_finsetSum _ (fun i _ => (Lp.memLp (g i)).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0))).const_mul (C ^ 2)) hpoint
  rw [integral_const_mul, ← vectorL2_norm_sq_integral y, ← vectorL2_norm_sq_integral g] at hi
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp (by
    simpa only [mul_pow] using hi)

private theorem coordinateOperator_bound {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ) (A : E →L[ℂ] F) (hA : ‖A‖ ≤ 1)
    (f : PiLp 2 (fun _ : Fin d => E)) :
    ‖Definitions.Spec.coordinateOperator d A f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, coordinateOperator_apply]
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simpa only [one_mul] using A.le_of_opNorm_le hA (f i)

theorem matrix_toeplitz_norm : Spec.MatrixToeplitzNorm := by
  intro d Φ
  have hb : BddAbove (Set.range (fun t => ‖Spec.pointwiseMatrix Φ t‖)) :=
    (isCompact_range (pointwiseMatrix_continuous Φ).norm).bddAbove
  have hC : 0 ≤ Spec.matrixSymbolNorm Φ :=
    (norm_nonneg (Spec.pointwiseMatrix Φ 0)).trans (le_ciSup hb 0)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have he : matrixToeplitz (continuousMatrixSymbol Φ) f =
      Definitions.Spec.coordinateOperator d boundaryAnalysis
        (matrixMultiplication (continuousMatrixSymbol Φ) (matrixBoundary d f)) := by
    apply PiLp.ext
    intro i
    simp only [Definitions.Spec.matrixToeplitz, operatorMatrix_apply,
      coordinateOperator_apply, Definitions.Spec.matrixMultiplication, map_sum,
      Definitions.Spec.matrixBoundary]
    rfl
  rw [he]
  calc
    _ ≤ ‖matrixMultiplication (continuousMatrixSymbol Φ) (matrixBoundary d f)‖ :=
      coordinateOperator_bound d boundaryAnalysis boundaryAnalysis_norm _
    _ ≤ Spec.matrixSymbolNorm Φ * ‖matrixBoundary d f‖ :=
      matrixMultiplication_bound Φ _ hC (fun t => le_ciSup hb t) _
    _ ≤ Spec.matrixSymbolNorm Φ * ‖f‖ := mul_le_mul_of_nonneg_left
      (coordinateOperator_bound d boundaryInclusion boundaryInclusion_norm f) hC

end ExpandedFA.Toeplitz.HankelCompactness
