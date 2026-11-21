import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff NNReal

noncomputable section
namespace ExpandedFA.Fourier
open LineDeriv

def schwartzSpace : Specs.ExpandedFA.Fourier.SchwartzFourierConvention.schwartzSpaceType :=
  fun 𝕜 _ d => Schwartz 𝕜 d

def temperedSpace : Specs.ExpandedFA.Fourier.SchwartzFourierConvention.temperedSpaceType :=
  fun 𝕜 _ d => Tempered 𝕜 d

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

@[simp] theorem inner_basisVector (x : Euclidean d) (i : Fin d) :
    inner ℝ x (basisVector i) = x i := by
  simp [basisVector, EuclideanSpace.inner_single_right]

@[simp] theorem norm_basisVector (i : Fin d) : ‖basisVector i‖ = 1 := by
  simp [basisVector, PiLp.norm_single]

lemma coordinate_growth (i : Fin d) :
    (fun x : Euclidean d => (x i : 𝕜)).HasTemperateGrowth := by
  have h : (fun x : Euclidean d => inner ℝ x (basisVector i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (basisVector i)).hasTemperateGrowth
  simpa [Function.comp_def] using (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth.comp h

lemma monomial_growth {k : ℕ} (a : Fin k → Fin d) :
    (fun x : Euclidean d => (monomial a x : 𝕜)).HasTemperateGrowth := by
  classical
  have hprod : ∀ t : Finset (Fin k),
      (fun x : Euclidean d => ∏ j ∈ t, (x (a j) : 𝕜)).HasTemperateGrowth := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      convert! (coordinate_growth (a i)).mul ih using 1
      ext x
      simp [Finset.prod_insert, hi]
  simpa [monomial, map_prod] using hprod Finset.univ

@[simp] theorem weightedPartial_apply (s : SchwartzIndex d) (f : Schwartz 𝕜 d)
    (x : Euclidean d) : weightedPartial 𝕜 s f x =
    (monomial s.weight x : 𝕜) *
      iteratedFDeriv ℝ s.order f x (fun j => basisVector (s.directions j)) := by
  simp [weightedPartial, monomial_growth, smul_eq_mul,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

theorem seminorm_formula :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.seminormFormulaType := by
  intro 𝕜 _ d s f C hC
  change SchwartzMap.seminorm 𝕜 0 0 (weightedPartial 𝕜 s f) ≤ C ↔ _
  constructor
  · intro h x
    simpa using (SchwartzMap.norm_le_seminorm 𝕜 (weightedPartial 𝕜 s f) x).trans h
  · intro h
    apply SchwartzMap.seminorm_le_bound 𝕜 0 0 _ hC
    intro x
    simpa [norm_iteratedFDeriv_zero] using h x

/-- Expansion of a vector in the Euclidean coordinate basis. -/
lemma basis_expansion (x : Euclidean d) : ∑ i, x i • basisVector i = x := by
  ext j
  simp [basisVector, Pi.single_apply]

/-- An operator norm is bounded by the sum of its values on coordinate tuples.
This estimate is valid for an empty basis and for multilinear degree zero. -/
lemma multilinear_coordinate_sum {n : ℕ} (A : (Euclidean d) [×n]→L[ℝ] 𝕜) :
    ‖A‖ ≤ ∑ b : Fin n → Fin d, ‖A (fun j => basisVector (b j))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  calc
    ‖A v‖ = ‖∑ b : Fin n → Fin d, A (fun j => v j (b j) • basisVector (b j))‖ := by
      congr 1
      calc
        A v = A (fun j => ∑ i, v j i • basisVector i) := by simp only [basis_expansion]
        _ = _ := A.toMultilinearMap.map_sum _
    _ ≤ ∑ b : Fin n → Fin d, ‖A (fun j => v j (b j) • basisVector (b j))‖ := norm_sum_le _ _
    _ = ∑ b : Fin n → Fin d, (∏ j, ‖v j (b j)‖) * ‖A (fun j => basisVector (b j))‖ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [A.map_smul_univ, norm_smul, norm_prod]
    _ ≤ ∑ b : Fin n → Fin d, (∏ j, ‖v j‖) * ‖A (fun j => basisVector (b j))‖ := by
      apply Finset.sum_le_sum
      intro b _
      gcongr with j
      exact PiLp.norm_apply_le (v j) (b j)
    _ = (∑ b : Fin n → Fin d, ‖A (fun j => basisVector (b j))‖) * ∏ j, ‖v j‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      ring

/-- Finite coordinate estimates imply the radial derivative estimate. -/
lemma radial_le_coordinate_sum {k n : ℕ} (x : Euclidean d)
    (A : (Euclidean d) [×n]→L[ℝ] 𝕜) :
    ‖x‖ ^ k * ‖A‖ ≤ ∑ a : Fin k → Fin d, ∑ b : Fin n → Fin d,
      ‖(monomial a x : 𝕜) * A (fun j => basisVector (b j))‖ := by
  have hx : ‖x‖ ≤ ∑ i, ‖x i‖ := by
    calc
      ‖x‖ = ‖∑ i, x i • basisVector i‖ := by rw [basis_expansion]
      _ ≤ ∑ i, ‖x i • basisVector i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul]
  calc
    ‖x‖ ^ k * ‖A‖ ≤ (∑ i, ‖x i‖) ^ k *
        (∑ b : Fin n → Fin d, ‖A (fun j => basisVector (b j))‖) := by
      gcongr
      exact multilinear_coordinate_sum A
    _ = _ := by
      rw [Fintype.sum_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [monomial, norm_mul, norm_prod]

/-- A finite rectangular collection of word seminorms controls a radial seminorm. -/
lemma radial_seminorm_bound (k n : ℕ) (f : Schwartz 𝕜 d) :
    SchwartzMap.seminorm 𝕜 k n f ≤
      ∑ a : Fin k → Fin d, ∑ b : Fin n → Fin d,
        coordinateSchwartzSeminorm 𝕜 ⟨k, n, a, b⟩ f := by
  apply SchwartzMap.seminorm_le_bound 𝕜 k n f
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)))
  intro x
  apply (radial_le_coordinate_sum x (iteratedFDeriv ℝ n f x)).trans
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have h := (seminorm_formula 𝕜 d ⟨k,n,a,b⟩ f _ (apply_nonneg _ _)).mp le_rfl x
  exact h

/-- The finite rectangle of coordinate words of fixed degrees. -/
noncomputable def wordIndices (d k n : ℕ) : Finset (SchwartzIndex d) := by
  classical
  exact Finset.univ.image (fun ab : (Fin k → Fin d) × (Fin n → Fin d) =>
    ⟨k, n, ab.1, ab.2⟩)

lemma mem_wordIndices (k n : ℕ) (a : Fin k → Fin d) (b : Fin n → Fin d) :
    (⟨k, n, a, b⟩ : SchwartzIndex d) ∈ wordIndices d k n := by
  classical
  exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_univ _, rfl⟩

theorem seminorm_topology :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.seminormTopologyType := by
  intro 𝕜 _ d
  classical
  have hp := schwartz_withSeminorms 𝕜 (Euclidean d) 𝕜
  apply hp.congr
  · intro s
    have hq : Continuous (coordinateSchwartzSeminorm 𝕜 s) :=
      (hp.continuous_seminorm (0,0)).comp (weightedPartial 𝕜 s).continuous
    obtain ⟨t, C, _, h⟩ := Seminorm.bound_of_continuous hp _ hq
    exact ⟨t, C, h⟩
  · rintro ⟨k,n⟩
    refine ⟨wordIndices d k n, (d : ℝ≥0) ^ (k+n), ?_⟩
    intro f
    apply (radial_seminorm_bound k n f).trans
    have hsum : (∑ a : Fin k → Fin d, ∑ b : Fin n → Fin d,
        coordinateSchwartzSeminorm 𝕜 ⟨k,n,a,b⟩ f) ≤
        ∑ _a : Fin k → Fin d, ∑ _b : Fin n → Fin d,
          (wordIndices d k n).sup (coordinateSchwartzSeminorm 𝕜) f := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact Finset.le_sup (f := coordinateSchwartzSeminorm 𝕜) (mem_wordIndices k n a b) f
    apply hsum.trans_eq
    simp [NNReal.smul_def, pow_add, mul_assoc]

theorem schwartz_characterization :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.schwartzCharacterizationType := by
  intro 𝕜 _ d f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.smooth ⊤, ?_⟩
    intro s
    refine ⟨coordinateSchwartzSeminorm 𝕜 s g, ?_⟩
    exact (seminorm_formula 𝕜 d s g _ (apply_nonneg _ _)).mp le_rfl
  · rintro ⟨hsmooth, hbounds⟩
    choose C hC using hbounds
    refine ⟨⟨f, hsmooth, ?_⟩, rfl⟩
    intro k n
    refine ⟨∑ a : Fin k → Fin d, ∑ b : Fin n → Fin d, C ⟨k,n,a,b⟩, ?_⟩
    intro x
    apply (radial_le_coordinate_sum x (iteratedFDeriv ℝ n f x)).trans
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    exact hC ⟨k,n,a,b⟩ x

def integral_fourier :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.integralFourierType := @integralFourier

def schwartz_fourier :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.schwartzFourierType := @schwartzFourier

def tempered_fourier :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.temperedFourierType := @temperedFourier

lemma integralFourier_eq_native (f : Euclidean d → ℂ) (ξ : Euclidean d) :
    integralFourier f ξ = 𝓕 f ξ := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  push_cast
  ring

theorem schwartz_integral :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.schwartzIntegralType := by
  intro d f ξ
  exact (integralFourier_eq_native f ξ).symm

theorem dual_pairing :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.dualPairingType := by
  intro d u φ
  rfl

theorem partial_pairing :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.partialPairingType := by
  intro d i u φ
  rfl

theorem coordinate_pairing :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.coordinatePairingType := by
  intro d i u φ
  refine ⟨?_, rfl⟩
  intro x
  exact SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth i) φ x

set_option backward.isDefEq.respectTransparency false in
lemma real_coordinateMultiply (i : Fin d) (φ : Schwartz ℂ d) :
    SchwartzMap.smulLeftCLM ℂ (fun x : Euclidean d => inner ℝ x (basisVector i)) φ =
      coordinateMultiply i φ := by
  have h : (fun x : Euclidean d => inner ℝ x (basisVector i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (basisVector i)).hasTemperateGrowth
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply h, coordinateMultiply,
    SchwartzMap.smulLeftCLM_apply_apply (coordinate_growth i)]
  simp only [inner_basisVector, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  rfl

lemma schwartz_partial_fourier (i : Fin d) (φ : Schwartz ℂ d) :
    LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) (schwartzFourier φ) =
      -(2 * (Real.pi : ℂ) * Complex.I) • schwartzFourier (coordinateMultiply i φ) := by
  simpa only [real_coordinateMultiply, map_smul, schwartzFourier,
    LineDeriv.lineDerivOpCLM_apply, FourierTransform.fourierCLM_apply,
    FourierTransform.fourier_smul] using
    SchwartzMap.lineDerivOp_fourier_eq φ (basisVector i)

lemma schwartz_fourier_partial (i : Fin d) (φ : Schwartz ℂ d) :
    schwartzFourier (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) φ) =
      (2 * (Real.pi : ℂ) * Complex.I) • coordinateMultiply i (schwartzFourier φ) := by
  simpa only [real_coordinateMultiply, schwartzFourier,
    LineDeriv.lineDerivOpCLM_apply, FourierTransform.fourierCLM_apply] using
    SchwartzMap.fourier_lineDerivOp_eq φ (basisVector i)

theorem fourier_partial :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.fourierPartialType := by
  intro d i u
  ext φ
  change -u (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) (schwartzFourier φ)) =
    (2 * (Real.pi : ℂ) * Complex.I) * u (schwartzFourier (coordinateMultiply i φ))
  rw [schwartz_partial_fourier, map_smul]
  simp [smul_eq_mul]

theorem fourier_coordinate :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.fourierCoordinateType := by
  intro d i u
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  ext φ
  change u (coordinateMultiply i (schwartzFourier φ)) =
    -(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * -u
      (schwartzFourier (LineDeriv.lineDerivOpCLM ℂ (Schwartz ℂ d) (basisVector i) φ))
  rw [schwartz_fourier_partial, map_smul]
  simp only [smul_eq_mul, neg_mul_neg]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem angular_normalization :
    Specs.ExpandedFA.Fourier.SchwartzFourierConvention.angularNormalizationType := by
  intro d f ξ
  unfold angularFourier integralFourier
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_smul_right]
  congr 2
  push_cast
  ring

end ExpandedFA.Fourier
