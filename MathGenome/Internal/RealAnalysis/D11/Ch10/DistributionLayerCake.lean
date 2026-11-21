import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.DistributionLayerCake
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Distribution functions and layer cake (paper.tex:3501–3521).
The scalar integral is nonnegative and extended-valued, so no integrability
hypothesis is needed. Mathlib's real-power layer-cake theorem applies to
arbitrary measures: its general layer-cake proof explicitly handles infinite
level masses and constructs a sigma-finite restriction only in the remaining
case. We do not apply product interchange on the original arbitrary space.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch10.DistributionLayerCake

def distribution {X : Type u} {K : Type v} [MeasurableSpace X] [Norm K]
    (μ : Measure X) (f : X → K) (t : ℝ) : ℝ≥0∞ := μ {x | t < ‖f x‖}

theorem decreasing : Specs.D11.Ch10.DistributionLayerCake.decreasing := by
  intro X K _ _ _ _ μ f _hf s t hst
  exact measure_mono (fun _ hx => hst.trans_lt hx)

theorem right_continuous : Specs.D11.Ch10.DistributionLayerCake.right_continuous := by
  intro X K _ _ _ _ μ f hf t _ht
  change ContinuousWithinAt (distribution μ f) (Ici t) t
  obtain ⟨s, hsanti, hst, hslim⟩ := exists_seq_strictAnti_tendsto t
  have hunion : (⋃ n, {x | s n < ‖f x‖}) = {x | t < ‖f x‖} := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, hx⟩
      exact (hst n).trans hx
    · intro hx
      obtain ⟨n, hn⟩ := ((tendsto_order.mp hslim).2 _ hx).exists
      exact mem_iUnion.mpr ⟨n, hn⟩
  have hm : Monotone (fun n => {x | s n < ‖f x‖}) := by
    intro i j hij x hx
    exact (hsanti.antitone hij).trans_lt hx
  have hsup : (⨆ n, distribution μ f (s n)) = distribution μ f t := by
    simpa only [distribution, hunion] using (hm.measure_iUnion (μ := μ)).symm
  apply tendsto_order.mpr
  constructor
  · intro a ha
    rw [← hsup] at ha
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp ha
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (hst n))] with r hr
    exact hn.trans_le (decreasing μ f hf hr.le)
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (decreasing μ f hf hr).trans_lt hb

theorem layer_cake : Specs.D11.Ch10.DistributionLayerCake.layer_cake := by
  intro X K _ _ _ _ μ f hf p hp
  change D11.Ch05.NonnegativeIntegral.nonnegativeIntegral μ _ =
    ENNReal.ofReal p * D11.Ch05.NonnegativeIntegral.nonnegativeIntegral _ _
  simp only [D11.Ch05.NonnegativeIntegral.integral_eq_lintegral]
  simpa only [Specs.D11.Ch10.DistributionLayerCake.distribution_value, mul_comm]
    using lintegral_rpow_eq_lintegral_meas_lt_mul μ
      (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hf.norm.aemeasurable hp

end D11.Ch10.DistributionLayerCake
