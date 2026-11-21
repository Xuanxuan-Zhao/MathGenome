import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.HouseholderReflector
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.DotProduct
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderPivotStep
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.HouseholderPivotStep
open MatrixDefinitions HouseholderDefinitions HouseholderPivotDefinitions
open Rounding

lemma squared_norm_error {d : ℕ} (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) (u : ℝ) (D : Set ℝ)
    (hm : Rounding.Specs.RelativeModelValue round u D) (hdu : (d : ℝ) * u < 1)
    (hs : DotSpecs.finiteSafe fused round D (⇑x) (⇑x)) :
    |squaredNorm fused round x - ‖x‖ ^ 2| ≤ gamma d u * ‖x‖ ^ 2 := by
  have h := (finite_sequential_dot_product fused round d (⇑x) (⇑x) u D hm hdu hs).2
  have ha (i : Fin d) : |x i * x i| = x i * x i := abs_of_nonneg (mul_self_nonneg _)
  rw [HouseholderReflector.norm_sq_dot]
  simpa only [squaredNorm, ha, dotProduct, gamma, _root_.Specs.NumAnalysis206.Rounding.gammaValue] using h

lemma norm_enclosure {q ν γ u δ : ℝ} (hν : 0 < ν) (_hu : 0 ≤ u)
    (hu1 : u < 1) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hq : |q - ν^2| ≤ γ * ν^2) (hδ : |δ| ≤ u) :
    0 < Real.sqrt q * (1+δ) ∧
    |Real.sqrt q * (1+δ) - ν| ≤
      max (1-(1-u)*Real.sqrt (1-γ)) ((1+u)*Real.sqrt (1+γ)-1) * ν := by
  have hqlo : (1-γ)*ν^2 ≤ q := by have := (abs_le.mp hq).1; linarith
  have hqhi : q ≤ (1+γ)*ν^2 := by have := (abs_le.mp hq).2; linarith
  have hqp : 0 < q := lt_of_lt_of_le (mul_pos (by linarith) (sq_pos_of_pos hν)) hqlo
  have hlo : Real.sqrt (1-γ) * ν ≤ Real.sqrt q := by
    have h := Real.sqrt_le_sqrt hqlo
    rwa [Real.sqrt_mul (by linarith : 0 ≤ 1-γ), Real.sqrt_sq (le_of_lt hν)] at h
  have hhi : Real.sqrt q ≤ Real.sqrt (1+γ) * ν := by
    have h := Real.sqrt_le_sqrt hqhi
    rwa [Real.sqrt_mul (by linarith : 0 ≤ 1+γ), Real.sqrt_sq (le_of_lt hν)] at h
  have hdlo : 1-u ≤ 1+δ := by have := (abs_le.mp hδ).1; linarith
  have hdhi : 1+δ ≤ 1+u := by have := (abs_le.mp hδ).2; linarith
  have hl := mul_le_mul hlo hdlo (by linarith) (Real.sqrt_nonneg q)
  have hh := mul_le_mul hhi hdhi (by linarith) (by positivity : 0 ≤ Real.sqrt (1+γ)*ν)
  refine ⟨mul_pos (Real.sqrt_pos.mpr hqp) (by linarith), abs_le.mpr ⟨?_, ?_⟩⟩
  · have h := mul_le_mul_of_nonneg_right (le_max_left
      (1-(1-u)*Real.sqrt (1-γ)) ((1+u)*Real.sqrt (1+γ)-1)) hν.le
    nlinarith [hl]
  · have h := mul_le_mul_of_nonneg_right (le_max_right
      (1-(1-u)*Real.sqrt (1-γ)) ((1+u)*Real.sqrt (1+γ)-1)) hν.le
    nlinarith [hh]

lemma computed_norm_bounds {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) (u : ℝ) (D : Set ℝ) (hx : x ≠ 0)
    (hm : Rounding.Specs.RelativeModelValue round u D) (hdu : (d : ℝ) * u < 1)
    (hg : gamma d u < 1) (hs : safe fused round D x) :
    0 < computedNorm fused round x ∧
    |computedNorm fused round x - ‖x‖| ≤ normError d u * ‖x‖ := by
  obtain ⟨δ, hδ, hδu⟩ := hm.2.2 _ hs.2.1
  rw [computedNorm, hδ]
  exact norm_enclosure (norm_pos_iff.mpr hx) hm.1 hm.2.1
    (gamma_nonneg ⟨hm.1, hm.2.1, hdu⟩) hg
    (squared_norm_error fused round x u D hm hdu hs.1) hδu

lemma norm_firstVector (d : ℕ) [NeZero d] : ‖firstVector d‖ = 1 := by
  simp [HouseholderDefinitions.firstVector, EuclideanSpace.single, PiLp.norm_single]

lemma abs_stable_difference (t ν : ℝ) (hν : 0 ≤ ν) :
    |t - (-signPlus t * ν)| = |t| + ν := by
  unfold signPlus
  split_ifs with h
  · simp only [neg_mul, one_mul, sub_neg_eq_add]
    rw [abs_of_nonneg h, abs_of_nonneg (add_nonneg h hν)]
  · rw [abs_of_neg (lt_of_not_ge h)]
    simp only [neg_neg, one_mul]
    rw [abs_of_nonpos (by linarith)]
    ring

lemma computed_alpha_error {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) :
    |computedAlpha fused round x - alpha x| = |computedNorm fused round x - ‖x‖| := by
  unfold computedAlpha alpha signPlus
  split_ifs <;> simp only [neg_neg, one_mul, neg_mul]
  · rw [show -computedNorm fused round x - -‖x‖ = -(computedNorm fused round x - ‖x‖) by ring, abs_neg]

lemma storedDirection_apply {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) (i : Fin d) :
    storedDirection fused round x i =
      if i = 0 then round (x 0 - computedAlpha fused round x) else x i := by
  by_cases hi : i = 0 <;>
    simp [storedDirection, HouseholderReflector.firstVector_apply, hi]

lemma storedDirection_first {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) :
    storedDirection fused round x 0 = round (x 0 - computedAlpha fused round x) := by
  simp [storedDirection, HouseholderReflector.firstVector_apply]

lemma stored_direction_bounds {d : ℕ} [NeZero d] (fused : Bool) (round : ℝ → ℝ)
    (x : Vec ℝ d) (u : ℝ) (D : Set ℝ)
    (hm : Rounding.Specs.RelativeModelValue round u D)
    (hs : safe fused round D x)
    (hn : 0 < computedNorm fused round x)
    (he : |computedNorm fused round x - ‖x‖| ≤ normError d u * ‖x‖) :
    storedDirection fused round x ≠ 0 ∧
    ‖storedDirection fused round x - direction x‖ ≤ directionError d u * ‖x‖ := by
  let z := x 0 - computedAlpha fused round x
  have hzabs : |z| = |x 0| + computedNorm fused round x :=
    abs_stable_difference _ _ hn.le
  have hz : z ≠ 0 := by
    have : 0 < |z| := by rw [hzabs]; linarith [abs_nonneg (x 0)]
    exact abs_pos.mp this
  obtain ⟨δ, hδ, hδu⟩ := hm.2.2 z hs.2.2
  have hround : round z ≠ 0 := by
    rw [hδ]
    exact mul_ne_zero hz (ne_of_gt (by have := (abs_le.mp hδu).1; linarith [hm.2.1]))
  refine ⟨?_, ?_⟩
  · intro hw
    apply hround
    simpa only [storedDirection_first, PiLp.zero_apply] using congrArg (fun w : Vec ℝ d => w 0) hw
  · have hv : storedDirection fused round x - direction x =
        (round z - x 0 + alpha x) • firstVector d := by
      unfold storedDirection direction
      module
    rw [hv, norm_smul, norm_firstVector, Real.norm_eq_abs, mul_one]
    have hsplit : round z - x 0 + alpha x = (round z - z) + (alpha x - computedAlpha fused round x) := by
      dsimp [z]; ring
    have hrounderr : |round z - z| ≤ u * (|x 0| + computedNorm fused round x) := by
      rw [hδ, show z * (1+δ)-z = z*δ by ring, abs_mul, hzabs]
      nlinarith [mul_le_mul_of_nonneg_left hδu (abs_nonneg z)]
    have halpha : |alpha x - computedAlpha fused round x| ≤ normError d u * ‖x‖ := by
      rw [abs_sub_comm, computed_alpha_error]
      exact he
    have hx0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    have hupper : computedNorm fused round x ≤ (1+normError d u)*‖x‖ := by
      have := (abs_le.mp he).2
      linarith
    calc
      |round z - x 0 + alpha x| ≤ |round z - z| + |alpha x - computedAlpha fused round x| := by
        rw [hsplit]; exact abs_add_le _ _
      _ ≤ directionError d u * ‖x‖ := by
        dsimp [directionError]
        nlinarith [mul_le_mul_of_nonneg_left hx0 hm.1,
          mul_le_mul_of_nonneg_left hupper hm.1]

lemma direction_norm_lower {d : ℕ} [NeZero d] (x : Vec ℝ d) : ‖x‖ ≤ ‖direction x‖ := by
  have h := PiLp.norm_apply_le (direction x) 0
  rw [Real.norm_eq_abs, HouseholderReflector.abs_direction_first] at h
  linarith [abs_nonneg (x 0)]

/-- Rescaling the normalization difference avoids dividing inequalities. -/
lemma normalized_difference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) (hv : v ≠ 0) (hw : w ≠ 0) {b : ℝ}
    (hb : ‖v-w‖ ≤ b*‖v‖) :
    ‖NormedSpace.normalize v - NormedSpace.normalize w‖ ≤ 2*b := by
  have hi : ‖v‖ • (NormedSpace.normalize v - NormedSpace.normalize w) =
      (v-w) + (‖w‖-‖v‖) • NormedSpace.normalize w := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  have hh : ‖v‖ * ‖NormedSpace.normalize v - NormedSpace.normalize w‖ ≤ 2*‖v-w‖ := by
    calc
      ‖v‖ * ‖NormedSpace.normalize v - NormedSpace.normalize w‖ =
          ‖‖v‖ • (NormedSpace.normalize v - NormedSpace.normalize w)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
      _ ≤ ‖v-w‖ + |‖w‖-‖v‖| := by
        rw [hi]
        simpa [norm_smul, NormedSpace.norm_normalize hw] using
          norm_add_le (v-w) ((‖w‖-‖v‖) • NormedSpace.normalize w)
      _ ≤ 2*‖v-w‖ := by
        have h := abs_norm_sub_norm_le w v
        rw [norm_sub_rev w v] at h
        linarith
  have hn := norm_pos_iff.mpr hv
  nlinarith

lemma reflector_normalized {d : ℕ} (v : Vec ℝ d) (hv : v ≠ 0) :
    reflector v = 1 - (2 : ℝ) • Matrix.vecMulVec
      (⇑(NormedSpace.normalize v)) (⇑(NormedSpace.normalize v)) := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold reflector
  rw [← HouseholderReflector.norm_sq_dot]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    NormedSpace.normalize, PiLp.smul_apply, smul_eq_mul]
  field_simp

lemma rankOne_matrix {d : ℕ} (p q : Vec ℝ d) :
    (Matrix.vecMulVec (⇑p) (⇑q)).toEuclideanLin.toContinuousLinearMap =
      InnerProductSpace.rankOne ℝ p q := by
  apply ContinuousLinearMap.coe_injective
  apply Matrix.toEuclideanLin.symm.injective
  simpa using (InnerProductSpace.symm_toEuclideanLin_rankOne p q).symm

lemma reflector_difference_map {d : ℕ} (v w : Vec ℝ d) (hv : v ≠ 0) (hw : w ≠ 0) :
    (reflector v - reflector w).toEuclideanLin.toContinuousLinearMap =
      (-2 : ℝ) • (InnerProductSpace.rankOne ℝ (NormedSpace.normalize v) (NormedSpace.normalize v) -
        InnerProductSpace.rankOne ℝ (NormedSpace.normalize w) (NormedSpace.normalize w)) := by
  rw [reflector_normalized v hv, reflector_normalized w hw]
  have hm : (1 - (2 : ℝ) • Matrix.vecMulVec (⇑(NormedSpace.normalize v)) (⇑(NormedSpace.normalize v))) -
      (1 - (2 : ℝ) • Matrix.vecMulVec (⇑(NormedSpace.normalize w)) (⇑(NormedSpace.normalize w))) =
      (-2 : ℝ) • (Matrix.vecMulVec (⇑(NormedSpace.normalize v)) (⇑(NormedSpace.normalize v)) -
        Matrix.vecMulVec (⇑(NormedSpace.normalize w)) (⇑(NormedSpace.normalize w))) := by module
  rw [hm]
  simp only [map_smul, map_sub, rankOne_matrix]

lemma reflector_perturbation {d : ℕ} (v w : Vec ℝ d) (hv : v ≠ 0) (hw : w ≠ 0)
    {b : ℝ} (hb : ‖v-w‖ ≤ b*‖v‖) :
    operatorNorm (reflector v - reflector w) ≤ 8*b := by
  let p := NormedSpace.normalize v
  let q := NormedSpace.normalize w
  have hp : ‖p‖ = 1 := NormedSpace.norm_normalize hv
  have hq : ‖q‖ = 1 := NormedSpace.norm_normalize hw
  have he : InnerProductSpace.rankOne ℝ p p - InnerProductSpace.rankOne ℝ q q =
      InnerProductSpace.rankOne ℝ (p-q) p + InnerProductSpace.rankOne ℝ q (p-q) := by
    simp only [map_sub, sub_apply]
    abel
  have hh : ‖InnerProductSpace.rankOne ℝ p p - InnerProductSpace.rankOne ℝ q q‖ ≤ 2*‖p-q‖ := by
    rw [he]
    simpa only [InnerProductSpace.norm_rankOne, hp, hq, mul_one, one_mul, two_mul] using
      norm_add_le (InnerProductSpace.rankOne ℝ (p-q) p) (InnerProductSpace.rankOne ℝ q (p-q))
  unfold operatorNorm
  rw [reflector_difference_map v w hv hw, norm_smul, Real.norm_eq_abs]
  norm_num
  have hd := normalized_difference_bound v w hv hw hb
  change ‖p-q‖ ≤ 2*b at hd
  change 2 * ‖InnerProductSpace.rankOne ℝ p p - InnerProductSpace.rankOne ℝ q q‖ ≤ 8*b
  linarith

/-- The complete nontrivial pivot step, including its Euclidean backward bound. -/
theorem pivot_step : Specs.NumAnalysis206.HouseholderPivotStep.pivotStep := by
  intro d _ fused round x u D hx hm hdu hg hs
  have hn := computed_norm_bounds fused round x u D hx hm hdu hg hs
  have hd := stored_direction_bounds fused round x u D hm hs hn.1 hn.2
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ha : 0 ≤ normError d u := by
    have := abs_nonneg (computedNorm fused round x - ‖x‖)
    nlinarith [hn.2]
  have hb : 0 ≤ directionError d u :=
    add_nonneg ha (mul_nonneg hm.1 (by linarith))
  have hv := HouseholderReflector.direction_ne_zero x hx
  have hdiff : ‖direction x - storedDirection fused round x‖ ≤
      directionError d u * ‖direction x‖ := by
    rw [norm_sub_rev]
    exact hd.2.trans (mul_le_mul_of_nonneg_left (direction_norm_lower x) hb)
  have hh := reflector_perturbation (direction x) (storedDirection fused round x) hv hd.1 hdiff
  refine ⟨hn.1, hn.2, hd.1, hd.2, HouseholderReflector.reflector_orthogonal _ hd.1, hh, ?_⟩
  have hmaps : (reflector (direction x)).toEuclideanLin x = alpha x • firstVector d := by
    apply PiLp.ext
    intro i
    exact congrFun (HouseholderReflector.reflector_maps x hx) i
  have hid : computedAlpha fused round x • firstVector d -
      (reflector (storedDirection fused round x)).toEuclideanLin x =
      (computedAlpha fused round x - alpha x) • firstVector d +
      (reflector (direction x) - reflector (storedDirection fused round x)).toEuclideanLin x := by
    rw [map_sub, LinearMap.sub_apply, hmaps, sub_smul]
    abel
  rw [hid]
  calc
    ‖(computedAlpha fused round x - alpha x) • firstVector d +
        (reflector (direction x) - reflector (storedDirection fused round x)).toEuclideanLin x‖ ≤
      ‖(computedAlpha fused round x - alpha x) • firstVector d‖ +
        ‖(reflector (direction x) - reflector (storedDirection fused round x)).toEuclideanLin x‖ :=
      norm_add_le _ _
    _ ≤ normError d u * ‖x‖ + (8 * directionError d u) * ‖x‖ := by
      apply add_le_add
      · simpa only [norm_smul, norm_firstVector, Real.norm_eq_abs, mul_one,
          computed_alpha_error] using hn.2
      · exact (MatrixData.operatorNorm_apply_le _ x).trans
          (mul_le_mul_of_nonneg_right hh (norm_nonneg x))
    _ = (normError d u + 8 * directionError d u) * ‖x‖ := by ring

end NumAnalysis206.HouseholderPivotStep
