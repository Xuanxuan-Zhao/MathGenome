import MathGenome.Internal.FourierSobolev.Specs.P102.U3.LittlewoodPaley
import MathGenome.Internal.FourierSobolev.P102.U3.Plancherel
import MathGenome.Internal.FourierSobolev.P102.U3.Mihlin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality

import MathGenome.Internal.FourierSobolev.P102.U3.LittlewoodPaleyUpper
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap ComplexInnerProductSpace

namespace P102.U3.LittlewoodPaley
open P102.Specs.U3 (Euclidean)
open P102.U3.Mihlin
open P102.U2.CZLpData (Exponent)

/-- A frequency-localized Schwartz pairing. -/
def frequencyTerm {d : ℕ} (χ : Euclidean d → ℝ)
    (f g : SchwartzMap (Euclidean d) ℂ) (j : ℤ) (ξ : Euclidean d) : ℂ :=
  (block χ j ξ : ℂ) * (𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ * star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ)


lemma frequencyTerm_continuous {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (f g : SchwartzMap (Euclidean d) ℂ) (j : ℤ) :
    Continuous (frequencyTerm χ f g j) := by
  have hb : Continuous (block χ j) :=
    (annulus_contDiff hχ).continuous.comp (by fun_prop)
  exact ((Complex.continuous_ofReal.comp hb).mul (𝓕 f : SchwartzMap (Euclidean d) ℂ).continuous).mul
    (𝓕 g : SchwartzMap (Euclidean d) ℂ).continuous.star

lemma frequencyTerm_sum_norm_le {d : ℕ} {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (f g : SchwartzMap (Euclidean d) ℂ)
    (J : Finset ℤ) (ξ : Euclidean d) :
    ∑ j ∈ J, ‖frequencyTerm χ f g j ξ‖ ≤
      2 * ‖(𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ * star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ)‖ := by
  simp only [frequencyTerm, mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    ← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    (∑ j ∈ J, |block χ j ξ|) =
        ∑ j ∈ J.filter (fun j => block χ j ξ ≠ 0), |block χ j ξ| := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hn
      have hz : block χ j ξ = 0 := by simpa [hj] using hn
      simp [hz]
    _ ≤ ∑ j ∈ J.filter (fun j => block χ j ξ ≠ 0), (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => block_abs_le_one hχ j ξ)
    _ = ((J.filter (fun j => block χ j ξ ≠ 0)).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast block_overlap hχ ξ J

/-- The frequency-side series can be integrated as an unordered sum; bounded
overlap supplies an integrable majorant for its sum of absolute values. -/
lemma frequency_reconstruction {d : ℕ} (hd : 1 ≤ d) {χ : Euclidean d → ℝ}
    (hχ : IsCutoff χ) (hpart : IsPartition χ)
    (f g : SchwartzMap (Euclidean d) ℂ) :
    HasSum (fun j : ℤ => ∫ ξ, frequencyTerm χ f g j ξ)
      (∫ ξ, (𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ * star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ)) := by
  have hb : Integrable (fun ξ => 2 * ‖(𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ * star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ)‖) volume :=
    (((𝓕 f : SchwartzMap (Euclidean d) ℂ).memLp 2 volume).integrable_mul ((𝓕 g : SchwartzMap (Euclidean d) ℂ).memLp 2 volume).star).norm.const_mul 2
  have hsum (ξ : Euclidean d) : Summable (fun j => ‖frequencyTerm χ f g j ξ‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) (fun J =>
      frequencyTerm_sum_norm_le hχ f g J ξ)
  have hbound : Integrable (fun ξ => ∑' j, ‖frequencyTerm χ f g j ξ‖) volume := by
    apply hb.mono'
      ((Measurable.tsum (fun j => (frequencyTerm_continuous hχ f g j).measurable.norm)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      exact Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
        (fun J => frequencyTerm_sum_norm_le hχ f g J ξ)
  apply hasSum_integral_of_dominated_convergence (μ := volume)
    (F := frequencyTerm χ f g) (f := fun ξ : Euclidean d => (𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ *
      star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ))
    (fun j ξ => ‖frequencyTerm χ f g j ξ‖)
    (fun j => (frequencyTerm_continuous hχ f g j).aestronglyMeasurable)
    (fun _ => Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall hsum) hbound
  filter_upwards [ae_ne_zero d hd] with ξ hξ
  have h : HasSum (fun j : ℤ => (block χ j ξ : ℂ)) (1 : ℂ) :=
    Complex.ofRealCLM.hasSum (hpart.2.1 ξ hξ)
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, frequencyTerm, one_mul]
    using (h.mul_right ((𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ)).mul_right (star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ))

/-- Plancherel written with the manuscript's convention f conjugate(g). -/
lemma integral_pair_eq_fourier {d : ℕ} (f g : Lp (α := Euclidean d) ℂ 2 volume) :
    (∫ x, f x * star (g x)) =
      ∫ ξ, (𝓕 f : Lp (α := Euclidean d) ℂ 2 volume) ξ *
        star ((𝓕 g : Lp (α := Euclidean d) ℂ 2 volume) ξ) := by
  have h := Lp.inner_fourier_eq g f
  simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply, mul_comm] using h.symm

lemma schwartz_integral_pair_eq_fourier {d : ℕ}
    (f g : SchwartzMap (Euclidean d) ℂ) :
    (∫ x, f x * star (g x)) = ∫ ξ, (𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ * star ((𝓕 g : SchwartzMap (Euclidean d) ℂ) ξ) := by
  calc
    _ = ∫ x, f.toLp 2 volume x * star (g.toLp 2 volume x) := by
      apply integral_congr_ae
      filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
      rw [hx, hy]
    _ = _ := integral_pair_eq_fourier _ _
    _ = _ := by
      rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
      apply integral_congr_ae
      filter_upwards [(𝓕 f : SchwartzMap (Euclidean d) ℂ).coeFn_toLp 2 volume, (𝓕 g : SchwartzMap (Euclidean d) ℂ).coeFn_toLp 2 volume] with ξ hx hy
      rw [hx, hy]

/-- On Schwartz inputs the Lᵖ extension has precisely the canonical L²
multiplier representative. No choice of pointwise representatives is used. -/
lemma schwartz_projection_L2 {d : ℕ} {η : Euclidean d → ℝ}
    (p : Exponent) (j : ℤ) (hP : HasLpSymbol p (symbol η j) (projection p η j))
    (f : SchwartzMap (Euclidean d) ℂ) :
    ∃ u : Lp (α := Euclidean d) ℂ 2 volume,
      (projection p η j (f.toLp p.val volume) : Euclidean d → ℂ) =ᵐ[volume] u ∧
      (𝓕 u : Lp (α := Euclidean d) ℂ 2 volume) =ᵐ[volume]
        fun ξ => symbol η j ξ * (𝓕 f : SchwartzMap (Euclidean d) ℂ) ξ := by
  obtain ⟨T, hT, hA⟩ := hP
  refine ⟨T (f.toLp 2 volume), hA f (f.memLp _ _) (f.memLp _ _), ?_⟩
  have h := hT (f.toLp 2 volume)
  rw [SchwartzMap.toLp_fourier_eq] at h
  filter_upwards [h, (𝓕 f : SchwartzMap (Euclidean d) ℂ).coeFn_toLp 2 volume] with ξ hx hy
  rw [hx, hy]

lemma pairingTerm_eq_frequency {d : ℕ} {χ : Euclidean d → ℝ}
    (hone : ∀ ξ ∈ tsupport (annulus χ), enlargedCutoff χ ξ = 1)
    (p q : Exponent) (f g : SchwartzMap (Euclidean d) ℂ) (j : ℤ)
    (hP : HasLpSymbol p (symbol (annulus χ) j) (projection p (annulus χ) j))
    (hQ : HasLpSymbol q (symbol (enlargedCutoff χ) j) (projection q (enlargedCutoff χ) j)) :
    pairingTerm p q χ f g j = ∫ ξ, frequencyTerm χ f g j ξ := by
  obtain ⟨u, hu, hFu⟩ := schwartz_projection_L2 p j hP f
  obtain ⟨v, hv, hFv⟩ := schwartz_projection_L2 q j hQ g
  unfold pairingTerm
  calc
    _ = ∫ x, u x * star (v x) := by
      apply integral_congr_ae
      filter_upwards [hu, hv] with x hx hy
      rw [hx, hy]
    _ = _ := integral_pair_eq_fourier u v
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hFu, hFv] with ξ hx hy
      rw [hx, hy]
      by_cases hz : annulus χ (scale (-j) • ξ) = 0
      · simp only [symbol, frequencyTerm, block, hz, Complex.ofReal_zero, zero_mul]
      · have htilde := hone (scale (-j) • ξ) (subset_tsupport _ hz)
        simp only [symbol, htilde, Complex.ofReal_one, one_mul, frequencyTerm, block]


/-- Conditional draft of the original reconstruction target. The five explicit
premises are the frozen upper-stage obligations, in contract order. -/
theorem reconstruction_conditional
    (hcutoff : P102.Specs.U3.LittlewoodPaleyUpper.cutoffType)
    (_hupper_theorem : P102.Specs.U3.LittlewoodPaleyUpper.theoremType)
    (hprojections : P102.Specs.U3.LittlewoodPaleyUpper.projectionsType)
    (_hsigned : P102.Specs.U3.LittlewoodPaleyUpper.signedType)
    (_hupper : P102.Specs.U3.LittlewoodPaleyUpper.upperType) :
    P102.Specs.U3.LittlewoodPaley.reconstructionType := by
  intro d hd χ hχ hpart p q f g
  obtain ⟨hη, _, hθ, _, hone⟩ := hcutoff d χ hχ
  have heq : pairingTerm p q χ f g = fun j => ∫ ξ, frequencyTerm χ f g j ξ := by
    funext j
    exact pairingTerm_eq_frequency hone p q f g j
      (hprojections d hd _ hη p j) (hprojections d hd _ hθ q j)
  have h := frequency_reconstruction hd hχ hpart f g
  rw [← schwartz_integral_pair_eq_fourier f g, ← heq] at h
  exact ⟨h.summable.norm, h⟩

/-- The norm used in the lower estimate; finiteness will always be supplied
by `UpperBound`, before taking this real value. -/
def squareNorm {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (f : Lp (α := Euclidean d) ℂ p.val volume) : ℝ :=
  (eLpNorm (infiniteSquare p η f) p.val volume).toReal

lemma finiteSquare_nonneg {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) :
    0 ≤ finiteSquare p η J f x := Real.sqrt_nonneg _

lemma finiteSquare_le_infinite {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) (x : Euclidean d) :
    ENNReal.ofReal (finiteSquare p η J f x) ≤ infiniteSquare p η f x := by
  unfold finiteSquare infiniteSquare
  rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num)]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  exact ENNReal.sum_le_tsum J

lemma finiteSquare_norm_le {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    {C : ℝ≥0} (hU : UpperBound p η C)
    (J : Finset ℤ) (f : Lp (α := Euclidean d) ℂ p.val volume) :
    (eLpNorm (finiteSquare p η J f) p.val volume).toReal ≤ squareNorm p η f := by
  apply ENNReal.toReal_mono (ne_top_of_le_ne_top (by finiteness) (hU f).2.2.2.2)
  calc
    _ ≤ eLpNorm (fun x => (infiniteSquare p η f x).toReal) p.val volume := by
      apply eLpNorm_mono_ae ((hU f).1 J).1.aestronglyMeasurable
      filter_upwards [(hU f).2.2.1] with x hx
      rw [Real.norm_of_nonneg (finiteSquare_nonneg _ _ _ _ _),
        Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.ofReal_le_iff_le_toReal hx.ne).mp (finiteSquare_le_infinite _ _ _ _ _)
    _ = _ := by
      apply eLpNorm_congr_enorm_ae (hU f).2.2.2.1.aestronglyMeasurable
        (hU f).2.1.aestronglyMeasurable
      filter_upwards [(hU f).2.2.1] with x hx
      simp only [Real.enorm_toReal hx.ne, enorm_eq_self]

lemma squareNorm_le {d : ℕ} (p : Exponent) (η : Euclidean d → ℝ)
    {C : ℝ≥0} (hU : UpperBound p η C)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    squareNorm p η f ≤ (C : ℝ) * ‖f‖ := by
  have h := ENNReal.toReal_mono (by finiteness) ((hU f).2.2.2.2)
  simpa only [squareNorm, ENNReal.toReal_mul, ENNReal.coe_toReal, enorm,
    ENNReal.coe_toReal, coe_nnnorm] using h

lemma finite_pairing_sum_le {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ) {C D : ℝ≥0}
    (hU : UpperBound p η C) (hV : UpperBound q θ D)
    (f : Lp (α := Euclidean d) ℂ p.val volume)
    (g : Lp (α := Euclidean d) ℂ q.val volume) (J : Finset ℤ) :
    ∑ j ∈ J, ‖∫ x, projection p η j f x * star (projection q θ j g x)‖ ≤
      squareNorm p η f * ((D : ℝ) * ‖g‖) := by
  have hprod j : Integrable (fun x => projection p η j f x * star (projection q θ j g x)) volume :=
    (Lp.memLp _).integrable_mul (Lp.memLp _).star
  have hsq := (((hU f).1 J).1).integrable_mul (((hV g).1 J).1)
  calc
    _ ≤ ∑ j ∈ J, ∫ x, ‖projection p η j f x * star (projection q θ j g x)‖ :=
      Finset.sum_le_sum (fun _ _ => norm_integral_le_integral_norm _)
    _ = ∫ x, ∑ j ∈ J, ‖projection p η j f x * star (projection q θ j g x)‖ :=
      (integral_finsetSum _ (fun j _ => (hprod j).norm)).symm
    _ ≤ ∫ x, finiteSquare p η J f x * finiteSquare q θ J g x := by
      apply integral_mono (integrable_finsetSum _ fun j _ => (hprod j).norm) hsq
      intro x
      simpa only [Pi.mul_apply, norm_mul, norm_star, finiteSquare] using
        Real.sum_mul_le_sqrt_mul_sqrt J
          (fun j => ‖projection p η j f x‖) (fun j => ‖projection q θ j g x‖)
    _ ≤ (eLpNorm (finiteSquare p η J f) p.val volume).toReal *
        (eLpNorm (finiteSquare q θ J g) q.val volume).toReal := by
      let a := (((hU f).1 J).1).toLp (finiteSquare p η J f)
      let b := (((hV g).1 J).1).toLp (finiteSquare q θ J g)
      have he : (∫ x, a x * b x) = ∫ x, finiteSquare p η J f x * finiteSquare q θ J g x := by
        apply integral_congr_ae
        filter_upwards [(((hU f).1 J).1).coeFn_toLp, (((hV g).1 J).1).coeFn_toLp] with x hx hy
        rw [hx, hy]
      have hn := ExpandedFA.FunctionSpaces.lp_pairing_apply_bound volume p.val q.val b a
      rw [(ExpandedFA.FunctionSpaces.lp_pairing_integral volume p.val q.val b a).2, he] at hn
      rw [Real.norm_of_nonneg (integral_nonneg fun _ =>
        mul_nonneg (finiteSquare_nonneg _ _ _ _ _) (finiteSquare_nonneg _ _ _ _ _))] at hn
      simpa only [a, b, Lp.norm_toLp, mul_comm] using hn
    _ ≤ squareNorm p η f * ((D : ℝ) * ‖g‖) := by
      apply mul_le_mul (finiteSquare_norm_le p η hU J f)
        ((finiteSquare_norm_le q θ hV J g).trans (squareNorm_le q θ hV g))
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg


open ExpandedFA.FunctionSpaces

/-- The scalar-linear pairing at a single scale. Conjugation is placed in
its fixed second input, leaving a genuine continuous linear map in f. -/
def scalePairing {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ)
    (g : Lp (α := Euclidean d) ℂ q.val volume) (j : ℤ) :
    Lp (α := Euclidean d) ℂ p.val volume →L[ℂ] ℂ :=
  (lpIntegralPairing volume p.val q.val (star (projection q θ j g))).comp (projection p η j)

lemma scalePairing_apply {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ)
    (g : Lp (α := Euclidean d) ℂ q.val volume) (j : ℤ)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    scalePairing p q η θ g j f = ∫ x, projection p η j f x * star (projection q θ j g x) := by
  change lpIntegralPairing volume p.val q.val (star (projection q θ j g))
    (projection p η j f) = _
  calc
    _ = ∫ x, projection p η j f x * (star (projection q θ j g)) x :=
      (lp_pairing_integral volume p.val q.val _ _).2
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_star (projection q θ j g)] with x hx
      rw [hx]
      rfl

lemma scalePairing_summable_norm {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ) {C D : ℝ≥0}
    (hU : UpperBound p η C) (hV : UpperBound q θ D)
    (g : Lp (α := Euclidean d) ℂ q.val volume)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    Summable (fun j : ℤ => ‖scalePairing p q η θ g j f‖) := by
  apply summable_of_sum_le (fun _ => norm_nonneg _)
  intro J
  simp_rw [scalePairing_apply]
  exact finite_pairing_sum_le p q η θ hU hV f g J

lemma norm_scalePairing_tsum_le {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ) {C D : ℝ≥0}
    (hU : UpperBound p η C) (hV : UpperBound q θ D)
    (g : Lp (α := Euclidean d) ℂ q.val volume)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    ‖∑' j : ℤ, scalePairing p q η θ g j f‖ ≤ squareNorm p η f * ((D : ℝ) * ‖g‖) := by
  apply (norm_tsum_le_tsum_norm (scalePairing_summable_norm p q η θ hU hV g f)).trans
  apply Real.tsum_le_of_sum_le (fun _ => norm_nonneg _)
  intro J
  simp_rw [scalePairing_apply]
  exact finite_pairing_sum_le p q η θ hU hV f g J

/-- Absolute summation defines a bounded functional, thanks to the two upper
bounds. This will extend the Schwartz reconstruction identity by density. -/
def pairingSeries {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ) {C D : ℝ≥0}
    (hU : UpperBound p η C) (hV : UpperBound q θ D)
    (g : Lp (α := Euclidean d) ℂ q.val volume) :
    Lp (α := Euclidean d) ℂ p.val volume →L[ℂ] ℂ :=
  ({ toFun := fun f => ∑' j : ℤ, scalePairing p q η θ g j f
     map_add' := fun f h => by
       simp only [map_add]
       exact (scalePairing_summable_norm p q η θ hU hV g f).of_norm.tsum_add
         (scalePairing_summable_norm p q η θ hU hV g h).of_norm
     map_smul' := fun c f => by
       simp only [map_smul, RingHom.id_apply]
       exact (scalePairing_summable_norm p q η θ hU hV g f).of_norm.tsum_const_smul c } : _ →ₗ[ℂ] ℂ).mkContinuous
    ((C : ℝ) * (D : ℝ) * ‖g‖) (fun f => by
      calc
        _ ≤ squareNorm p η f * ((D : ℝ) * ‖g‖) :=
          norm_scalePairing_tsum_le p q η θ hU hV g f
        _ ≤ ((C : ℝ) * ‖f‖) * ((D : ℝ) * ‖g‖) :=
          mul_le_mul_of_nonneg_right (squareNorm_le p η hU f)
            (mul_nonneg D.coe_nonneg (norm_nonneg _))
        _ = _ := by ring)

lemma pairingSeries_apply {d : ℕ} (p q : Exponent) [p.val.HolderConjugate q.val]
    (η θ : Euclidean d → ℝ) {C D : ℝ≥0}
    (hU : UpperBound p η C) (hV : UpperBound q θ D)
    (g : Lp (α := Euclidean d) ℂ q.val volume)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    pairingSeries p q η θ hU hV g f = ∑' j : ℤ, scalePairing p q η θ g j f := rfl


lemma starLp_norm {d : ℕ} (p : Exponent)
    (f : Lp (α := Euclidean d) ℂ p.val volume) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f), eLpNorm_star]

lemma starLp_isometry {d : ℕ} (p : Exponent) :
    Isometry (star : Lp (α := Euclidean d) ℂ p.val volume → Lp ℂ p.val volume) := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  rw [Lp.dist_def, Lp.dist_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with x hx hy
  simp only [Pi.sub_apply, hx, hy, Pi.star_apply, ← star_sub, norm_star]


lemma pairingSeries_eq_integral {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) (hpart : IsPartition χ)
    (hR : P102.Specs.U3.LittlewoodPaley.reconstructionType)
    (p q : Exponent) [p.val.HolderConjugate q.val] {C D : ℝ≥0}
    (hU : UpperBound p (annulus χ) C) (hV : UpperBound q (enlargedCutoff χ) D)
    (g : SchwartzMap (Euclidean d) ℂ) :
    pairingSeries p q (annulus χ) (enlargedCutoff χ) hU hV (g.toLp q.val volume) =
      lpIntegralPairing volume p.val q.val (star (g.toLp q.val volume)) := by
  let L := pairingSeries p q (annulus χ) (enlargedCutoff χ) hU hV (g.toLp q.val volume)
  let K := lpIntegralPairing volume p.val q.val (star (g.toLp q.val volume))
  have heq : (L : Lp ℂ p.val volume → ℂ) ∘ SchwartzMap.toLpCLM ℝ ℂ p.val volume =
      (K : Lp ℂ p.val volume → ℂ) ∘ SchwartzMap.toLpCLM ℝ ℂ p.val volume := by
    funext f
    change L (f.toLp p.val volume) = K (f.toLp p.val volume)
    have hK : K (f.toLp p.val volume) = ∫ x, f x * star (g x) := by
      calc
        _ = ∫ x, f.toLp p.val volume x * (star (g.toLp q.val volume)) x :=
          (lp_pairing_integral volume p.val q.val _ _).2
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_star (g.toLp q.val volume),
            f.coeFn_toLp p.val volume, g.coeFn_toLp q.val volume] with x hs hf hg
          simp only [hs, Pi.star_apply, hf, hg]
    rw [hK]
    change (∑' j : ℤ, scalePairing p q (annulus χ) (enlargedCutoff χ)
      (g.toLp q.val volume) j (f.toLp p.val volume)) = _
    simp_rw [scalePairing_apply]
    exact (hR d hd χ hχ hpart p q f g).2.tsum_eq
  have h := (SchwartzMap.denseRange_toLpCLM (E := Euclidean d) (F := ℂ)
    (μ := volume) (p := p.val) p.lt_top.ne).equalizer L.continuous K.continuous heq
  exact DFunLike.coe_injective h

/-- Duality uses the upper estimate only for the enlarged family at p'.
Reconstruction first extends in f by the bounded series functional, then the
Schwartz testing estimate extends in g by density. -/
lemma lower_norm_of_reconstruction {d : ℕ} (hd : 1 ≤ d)
    {χ : Euclidean d → ℝ} (hχ : IsCutoff χ) (hpart : IsPartition χ)
    (hR : P102.Specs.U3.LittlewoodPaley.reconstructionType)
    (p q : Exponent) [p.val.HolderConjugate q.val] {C D : ℝ≥0}
    (hU : UpperBound p (annulus χ) C) (hV : UpperBound q (enlargedCutoff χ) D)
    (f : Lp (α := Euclidean d) ℂ p.val volume) :
    ‖f‖ ≤ (D : ℝ) * squareNorm p (annulus χ) f := by
  haveI : q.val.HolderConjugate p.val := ENNReal.HolderConjugate.symm
  have htests (g : SchwartzMap (Euclidean d) ℂ) :
      ‖lpIntegralPairing volume p.val q.val (star (g.toLp q.val volume)) f‖ ≤
        squareNorm p (annulus χ) f * ((D : ℝ) * ‖g.toLp q.val volume‖) := by
    rw [← pairingSeries_eq_integral hd hχ hpart hR p q hU hV g]
    exact norm_scalePairing_tsum_le p q (annulus χ) (enlargedCutoff χ) hU hV _ f
  have hall (g : Lp (α := Euclidean d) ℂ q.val volume) :
      ‖lpIntegralPairing volume p.val q.val (star g) f‖ ≤
        squareNorm p (annulus χ) f * ((D : ℝ) * ‖g‖) := by
    refine (SchwartzMap.denseRange_toLpCLM (E := Euclidean d) (F := ℂ)
      (μ := volume) (p := q.val) q.lt_top.ne).induction_on
      (p := fun g => ‖lpIntegralPairing volume p.val q.val (star g) f‖ ≤
        squareNorm p (annulus χ) f * ((D : ℝ) * ‖g‖)) g ?_ ?_
    · apply isClosed_le
      · exact ((ContinuousLinearMap.apply ℂ ℂ f).continuous.comp
          ((lpIntegralPairing (𝕜 := ℂ) volume p.val q.val).continuous.comp
            (starLp_isometry q).continuous)).norm
      · exact continuous_const.mul (continuous_const.mul continuous_norm)
    · exact htests
  have hbil (g : Lp (α := Euclidean d) ℂ q.val volume) :
      ‖lpIntegralPairing volume q.val p.val f g‖ ≤
        ((D : ℝ) * squareNorm p (annulus χ) f) * ‖g‖ := by
    have h := hall (star g)
    rw [star_star, starLp_norm] at h
    have heq : lpIntegralPairing volume p.val q.val g f =
        lpIntegralPairing volume q.val p.val f g := by
      calc
        _ = ∫ x, f x * g x := (lp_pairing_integral volume p.val q.val g f).2
        _ = ∫ x, g x * f x := by simp only [mul_comm]
        _ = _ := (lp_pairing_integral volume q.val p.val f g).2.symm
    rw [heq] at h
    convert h using 1 <;> ring
  have hn := ContinuousLinearMap.opNorm_le_bound
    (lpIntegralPairing (𝕜 := ℂ) volume q.val p.val f)
    (mul_nonneg D.coe_nonneg ENNReal.toReal_nonneg) hbil
  have he := lp_pairing_exact_norm volume q.val p.val q.lt_top.ne (Or.inr q.one_lt) f
  change ‖lpIntegralPairing volume q.val p.val f‖ = ‖f‖ at he
  rwa [he] at hn

/-- The full strict conjugate exponent stays inside the shared exponent type. -/
def dualExponent (p : Exponent) : Exponent :=
  ⟨ENNReal.conjExponent p.val,
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p.val (ENNReal.conjExponent p.val)).mp p.lt_top,
    (ENNReal.HolderConjugate.lt_top_iff_one_lt (ENNReal.conjExponent p.val) p.val).mpr p.one_lt⟩


/-- Conditional derivation of the original two-sided theorem. This is a draft:
its five premise types are the exact frozen upper-stage obligations. -/
theorem littlewood_paley_conditional
    (hcutoff : P102.Specs.U3.LittlewoodPaleyUpper.cutoffType)
    (hupper_theorem : P102.Specs.U3.LittlewoodPaleyUpper.theoremType)
    (hprojections : P102.Specs.U3.LittlewoodPaleyUpper.projectionsType)
    (hsigned : P102.Specs.U3.LittlewoodPaleyUpper.signedType)
    (hupper : P102.Specs.U3.LittlewoodPaleyUpper.upperType) :
    P102.Specs.U3.LittlewoodPaley.theoremType := by
  have hR := reconstruction_conditional hcutoff hupper_theorem hprojections hsigned hupper
  intro d hd χ hχ hpart p
  obtain ⟨hη, _, hθ, _, _⟩ := hcutoff d χ hχ
  obtain ⟨C, hC, hU⟩ := hupper d hd _ hη p
  let q := dualExponent p
  haveI : p.val.HolderConjugate q.val := by
    change p.val.HolderConjugate (ENNReal.conjExponent p.val)
    infer_instance
  obtain ⟨D, hD, hV⟩ := hupper d hd _ hθ q
  let c : ℝ≥0 := min C D⁻¹
  have hc : 0 < c := lt_min hC (inv_pos.mpr hD)
  refine ⟨c, C, hc, min_le_left _ _, hU, ?_⟩
  intro f
  have hlow := lower_norm_of_reconstruction hd hχ hpart hR p q hU hV f
  have hD' : 0 < (D : ℝ) := hD
  have hsmall : (c : ℝ) ≤ (D : ℝ)⁻¹ := by exact_mod_cast min_le_right C D⁻¹
  have hreal : (c : ℝ) * ‖f‖ ≤ squareNorm p (annulus χ) f := by
    calc
      _ ≤ (D : ℝ)⁻¹ * ‖f‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ ≤ (D : ℝ)⁻¹ * ((D : ℝ) * squareNorm p (annulus χ) f) :=
        mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr D.coe_nonneg)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hD'.ne', one_mul]
  have hfin : eLpNorm (infiniteSquare p (annulus χ) f) p.val volume ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) (hU f).2.2.2.2
  apply (ENNReal.toReal_le_toReal (by finiteness) hfin).mp
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm, squareNorm] using hreal

end P102.U3.LittlewoodPaley

theorem _root_.«P102».«U3».«LittlewoodPaley».«littlewood_paley» : _root_.«P102».«Specs».«U3».«LittlewoodPaley».«theoremType» :=
  @_root_.«P102».«U3».«LittlewoodPaley».«littlewood_paley_conditional» (@_root_.«P102».«U3».«LittlewoodPaley».«cutoff_construction») (@_root_.«P102».«U3».«LittlewoodPaley».«littlewood_paley_upper») (@_root_.«P102».«U3».«LittlewoodPaley».«projections») (@_root_.«P102».«U3».«LittlewoodPaley».«signed_control») (@_root_.«P102».«U3».«LittlewoodPaley».«upper_bound»)
theorem _root_.«P102».«U3».«LittlewoodPaley».«reconstruction» : _root_.«P102».«Specs».«U3».«LittlewoodPaley».«reconstructionType» :=
  @_root_.«P102».«U3».«LittlewoodPaley».«reconstruction_conditional» (@_root_.«P102».«U3».«LittlewoodPaley».«cutoff_construction») (@_root_.«P102».«U3».«LittlewoodPaley».«littlewood_paley_upper») (@_root_.«P102».«U3».«LittlewoodPaley».«projections») (@_root_.«P102».«U3».«LittlewoodPaley».«signed_control») (@_root_.«P102».«U3».«LittlewoodPaley».«upper_bound»)
