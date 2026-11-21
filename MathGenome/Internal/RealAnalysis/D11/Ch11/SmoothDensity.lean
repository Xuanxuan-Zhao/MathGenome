import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.SmoothDensity
import MathGenome.Internal.RealAnalysis.D11.Ch11.SmoothMollifier
import MathGenome.Internal.RealAnalysis.D11.Ch11.CcDensityEuclidean
import MathGenome.Internal.RealAnalysis.D11.Ch11.ApproximateIdentityLp
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace D11.Ch11.SmoothDensity
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch03.LebesgueMeasures

/-- A smooth Urysohn function on a relatively compact neighborhood of K.
Shrinking the neighborhood first controls the *topological* support. -/
theorem smooth_cutoff : Specs.D11.Ch11.SmoothDensity.smooth_cutoff := by
  intro d _ K U hK hU hKU
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨ψ, hψ, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (Metric.isOpen_thickening (E := K) (δ := δ)) hK.isClosed
      (Metric.self_subset_thickening hδ K)
  have hts : tsupport ψ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hsupp]
    exact Metric.closure_thickening_subset_cthickening δ K
  exact ⟨ψ, hψ,
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hδU, fun x => hrange (mem_range_self x),
    fun x hx => (hone x).mp hx⟩

/-- Apply the explicit normalized mollifier to a Cc approximant and then
pass its finite-p convergence to the ordinary quotient norm. -/
theorem smooth_density : Specs.D11.Ch11.SmoothDensity.smooth_density := by
  intro d _ 𝕜 _ _ _ p _ hp
  letI : MeasurableSpace (Point d) := lebesgueSpace_value d
  letI : OpensMeasurableSpace (Point d) := ⟨borel_le_lebesgue d⟩
  letI : Measure.Regular (lebesgue_value d) := by
    change @Measure.Regular _ (lebesgueSpace d) _ (lebesgue d)
    infer_instance
  intro f ε hε
  obtain ⟨g, hg, herr⟩ := CcDensityEuclidean.cc_density d 𝕜 p hp f
    (ε / 2) (half_pos hε)
  let φ : Point d → 𝕜 := fun x => (SmoothMollifier.mollifier d x : 𝕜)
  have hφsmooth : ContDiff ℝ ∞ φ := by
    simpa only [Function.comp_def, RCLike.ofRealCLM_apply] using
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp
        (SmoothMollifier.mollifier_smooth (d := d))
  have hφcompact : HasCompactSupport φ :=
    (SmoothMollifier.mollifier_compact (d := d)).comp_left
      (g := fun r : ℝ => (r : 𝕜)) (by simp)
  have hφ1 : MemLp φ 1 (lebesgue_value d) :=
    hφsmooth.continuous.memLp_of_hasCompactSupport hφcompact
  have hφint : (∫ x, φ x ∂lebesgue_value d) = 1 := by
    change (∫ x, (SmoothMollifier.mollifier d x : 𝕜) ∂lebesgue_value d) = 1
    rw [integral_ofReal, (SmoothMollifier.mollifier_properties d).2.2.2.2.2]
    simp
  obtain ⟨hmem, hlim⟩ := ApproximateIdentityLp.approximate_identity_lp d 𝕜 p hp
    φ g hφsmooth.continuous.measurable g.continuous.measurable hφ1 hg
  have hlim' : Tendsto (fun t : ℝ => eLpNorm
      (Specs.D11.Ch11.ConvolutionBound.convolution_value d g
        (ApproximateIdentityLp.scaledKernel d φ t) - (g : Point d → 𝕜))
        p (lebesgue_value d)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [hφint, one_smul] using hlim
  have hevent := hlim'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hε)))
  obtain ⟨t, ht, hterr⟩ :=
    (Filter.Eventually.and
      (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Ioi 0) hevent).exists
  let c := Specs.D11.Ch11.ConvolutionBound.convolution_value d g
    (ApproximateIdentityLp.scaledKernel d φ t)
  have hc : MemLp c p (lebesgue_value d) := (hmem t ht).2
  have hscaled : ApproximateIdentityLp.scaledKernel d φ t =
      fun x => (SmoothMollifier.scaledMollifier d t x : 𝕜) := by
    funext x
    simp only [ApproximateIdentityLp.scaledKernel,
      Specs.D11.Ch11.ApproximateIdentityLp.scaledKernel_value,
      SmoothMollifier.scaledMollifier,
      Specs.D11.Ch11.SmoothMollifier.scaledMollifier_value, φ,
      RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul]
  have hreg := SmoothMollifier.regularization d 𝕜 g g.continuous g.hasCompactSupport t ht
  have hcsmooth : ContDiff ℝ ∞ c := by
    dsimp only [c]
    rw [hscaled]
    exact hreg.1
  have hccompact : HasCompactSupport c := by
    dsimp only [c]
    rw [hscaled]
    exact hreg.2.1
  refine ⟨c, hcsmooth, hccompact, hc, ?_⟩
  have hnorm : ‖hc.toLp c - hg.toLp g‖ < ε / 2 := by
    rw [← MemLp.toLp_sub hc hg, Lp.norm_toLp]
    exact ((ENNReal.toReal_lt_toReal (ne_top_of_lt hterr)
      ENNReal.ofReal_ne_top).mpr hterr).trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  calc
    ‖f - hc.toLp c‖ ≤ ‖f - hg.toLp g‖ + ‖hg.toLp g - hc.toLp c‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add herr (by rwa [norm_sub_rev])
    _ = ε := add_halves ε

end D11.Ch11.SmoothDensity
