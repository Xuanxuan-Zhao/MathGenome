import MathGenome.Internal.LinearPDE.P201Specs.Common.TimeTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTripleTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
open MeasureTheory
open scoped Topology ENNReal
universe u v

namespace P201.Common.TimeTrace
open ExpandedFA.Evolution
open HilbertTripleSpec HilbertTripleTraceSpec
open P201Specs.Common.TimeTrace (productCurve TimeTraceTheorem)

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Averaging the energy identity retains the actual L²(H) norm. -/
theorem curve_sq_bound (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T) (f : TraceCurve H T)
    (hf : Represents j T u f)
    (he : ∀ s t : Set.Icc 0 T, ‖f t‖ ^ 2 - ‖f s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, g r (u r)) (t : Set.Icc 0 T) :
    ‖f t‖ ^ 2 ≤ T⁻¹ * ‖j.embedding.compLp u‖ ^ 2 + 2 * ‖g‖ * ‖u‖ := by
  let μ := timeMeasure T
  let C : ℝ := 2 * ‖g‖ * ‖u‖
  have hμ : (μ Set.univ).toReal = T := by
    simp [μ, timeMeasure, timeMeasureValue, Real.volume_Ioo, hT.le]
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hui : Integrable (fun r => ‖j.embedding (u r)‖ ^ 2) μ :=
    (j.embedding.comp_memLp u).integrable_norm_pow (by norm_num)
  have hpoint : ∀ᵐ r ∂μ, ‖f t‖ ^ 2 ≤ ‖j.embedding (u r)‖ ^ 2 + C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hf] with r hr hfr
    let s : Set.Icc 0 T := ⟨r, Set.Ioo_subset_Icc_self hr⟩
    have hsr : f s = j.embedding (u r) := by
      simpa only [s, extendCurve, dite_eq_left (Set.Ioo_subset_Icc_self hr)] using hfr
    have hid := he s t
    rw [hsr] at hid
    have hb := triple_pairing_interval_bound T u g s t
    have hl := le_abs_self (∫ r in s.val..t.val, g r (u r))
    rw [Real.norm_eq_abs] at hb
    dsimp only [C]
    linarith
  have havg := integral_mono_ae (integrable_const (‖f t‖ ^ 2))
    (hui.add (integrable_const C)) hpoint
  have hnorm : (∫ r, ‖j.embedding (u r)‖ ^ 2 ∂μ) = ‖j.embedding.compLp u‖ ^ 2 := by
    rw [← timeLp_integral_norm_sq T (j.embedding.compLp u)]
    exact integral_congr_ae
      ((j.embedding.coeFn_compLp' u).fun_comp (fun x => ‖x‖ ^ 2)).symm
  have hmain : T * ‖f t‖ ^ 2 ≤ ‖j.embedding.compLp u‖ ^ 2 + T * C := by
    simp only [Pi.add_apply] at havg
    rw [integral_add hui (integrable_const C), integral_const, integral_const] at havg
    simp only [measureReal_def, hμ, smul_eq_mul] at havg
    rw [hnorm] at havg
    linarith
  apply (mul_le_mul_iff_right₀ hT).mp
  calc
    T * ‖f t‖ ^ 2 ≤ ‖j.embedding.compLp u‖ ^ 2 + T * C := hmain
    _ = T * (T⁻¹ * ‖j.embedding.compLp u‖ ^ 2 + 2 * ‖g‖ * ‖u‖) := by
      dsimp only [C]
      field_simp [hT.ne']


/-- Addition preserves the distributional Bochner derivative. -/
theorem derivative_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (a b c d : ℝ → E)
    (ha : HasTimeDerivative T a c) (hb : HasTimeDerivative T b d) :
    HasTimeDerivative T (a + b) (c + d) := by
  refine ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ?_⟩
  intro φ hφ
  have hia := hasTimeDerivative_test_integrable T a c ha φ hφ
  have hib := hasTimeDerivative_test_integrable T b d hb φ hφ
  simp only [timeMeasure] at hia hib
  simp only [Pi.add_apply, smul_add]
  rw [integral_add hia.1 hib.1, integral_add hia.2 hib.2,
    ha.2.2 φ hφ, hb.2.2 φ hφ, neg_add]

/-- Addition of the original two L² classes stays in the energy graph. -/
def energyAdd (j : HilbertTriple V H) (T : ℝ) (z w : EnergySpace j T) :
    EnergySpace j T := by
  refine ⟨(z.val.1 + w.val.1, z.val.2 + w.val.2), ?_⟩
  have hd := derivative_add T _ _ _ _ z.property w.property
  apply (hasTimeDerivative_congr T _ _ _ _ ?_
    (Lp.coeFn_add z.val.2 w.val.2).symm).mp hd
  filter_upwards [Lp.coeFn_add z.val.1 w.val.1] with t ht
  simp only [Pi.add_apply, ht, map_add]

/-- Representation commutes with addition, including the two endpoints. -/
theorem represents_add (j : HilbertTriple V H) (T : ℝ)
    (u v : TimeLp V 2 T) (f g : TraceCurve H T)
    (hf : Represents j T u f) (hg : Represents j T v g) :
    Represents j T (u + v) (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add u v,
    ae_restrict_mem measurableSet_Ioo] with r hfr hgr huv hr
  have hrcc := Set.Ioo_subset_Icc_self hr
  simp only [extendCurve, dite_eq_left hrcc] at hfr hgr ⊢
  simp only [ContinuousMap.add_apply, huv, Pi.add_apply, map_add, hfr, hgr]

/-- Polarization of the energy identity gives the full endpoint product formula. -/
theorem trace_product_identity (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (trace : EnergySpace j T → TraceCurve H T)
    (hr : ∀ z, Represents j T z.val.1 (trace z))
    (he : ∀ z (s t : Set.Icc 0 T), ‖trace z t‖ ^ 2 - ‖trace z s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, z.val.2 r (z.val.1 r))
    (z w : EnergySpace j T) (s t : Set.Icc 0 T) :
    productCurve (trace z) (trace w) t - productCurve (trace z) (trace w) s =
      ∫ r in s.val..t.val, z.val.2 r (w.val.1 r) + w.val.2 r (z.val.1 r) := by
  let zw := energyAdd j T z w
  have hsum : trace zw = trace z + trace w :=
    triple_representative_unique j T hT zw.val.1 _ _ (hr zw)
      (represents_add j T _ _ _ _ (hr z) (hr w))
  have hpair : (fun r => zw.val.2 r (zw.val.1 r)) =ᵐ[timeMeasure T]
      fun r => z.val.2 r (z.val.1 r) + w.val.2 r (w.val.1 r) +
        (z.val.2 r (w.val.1 r) + w.val.2 r (z.val.1 r)) := by
    filter_upwards [Lp.coeFn_add z.val.1 w.val.1, Lp.coeFn_add z.val.2 w.val.2]
      with r hu hg
    calc
      zw.val.2 r (zw.val.1 r) = (z.val.2 r + w.val.2 r) (z.val.1 r + w.val.1 r) :=
        congrArg₂ (fun (g : StrongDual ℝ V) (v : V) => g v) hg hu
      _ = _ := by
        rw [add_apply, map_add, map_add]
        ring
  have hz := he z s t
  have hw := he w s t
  have hzw := he zw s t
  rw [hsum] at hzw
  simp only [ContinuousMap.add_apply, norm_add_sq_real] at hzw
  have hiz : IntervalIntegrable (fun r => z.val.2 r (z.val.1 r)) volume s.val t.val :=
    triple_pairing_intervalIntegrable T z.val.1 z.val.2 s t
  have hiw : IntervalIntegrable (fun r => w.val.2 r (w.val.1 r)) volume s.val t.val :=
    triple_pairing_intervalIntegrable T w.val.1 w.val.2 s t
  have hic : IntervalIntegrable
      (fun r => z.val.2 r (w.val.1 r) + w.val.2 r (z.val.1 r)) volume s.val t.val :=
    (triple_pairing_intervalIntegrable T w.val.1 z.val.2 s t).add
      (triple_pairing_intervalIntegrable T z.val.1 w.val.2 s t)
  rw [time_integral_congr_ae T hpair s t,
    intervalIntegral.integral_add (hiz.add hiw) hic,
    intervalIntegral.integral_add hiz hiw] at hzw
  simp only [productCurve, extendCurve_apply]
  linarith


/-- An integrable increment density gives absolute continuity and its
classical derivative almost everywhere, without assumptions outside [0,T]. -/
theorem regularity_of_integral_increments (T : ℝ) (hT : 0 < T) (p d : ℝ → ℝ)
    (hd : Integrable d (timeMeasure T))
    (hp : ∀ s t : Set.Icc 0 T, p t - p s = ∫ r in s.val..t.val, d r) :
    AbsolutelyContinuousOnInterval p 0 T ∧
      (∀ᵐ r ∂timeMeasure T, HasDerivAt p (d r) r) := by
  let zero : Set.Icc 0 T := ⟨0, le_rfl, hT.le⟩
  have hii : IntervalIntegrable d volume 0 T := by
    have hcc : IntegrableOn d (Set.Icc 0 T) := by
      simpa only [IntegrableOn, timeMeasure, timeMeasureValue,
        restrict_Ioo_eq_restrict_Icc] using hd
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hcc
  have hz : (0 : ℝ) ∈ Set.uIcc 0 T := by simp [hT.le]
  let F := fun x => p 0 + ∫ r in 0..x, d r
  have heq : Set.EqOn F p (Set.Icc 0 T) := by
    intro x hx
    have hh := hp zero ⟨x, hx⟩
    dsimp only [zero, Subtype.coe_mk] at hh
    dsimp only [F]
    linarith
  have hac : AbsolutelyContinuousOnInterval F 0 T :=
    ((LipschitzWith.const (p 0)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hii.absolutelyContinuousOnInterval_intervalIntegral hz)
  refine ⟨hac.congr (by simpa only [Set.uIcc_of_le hT.le] using heq), ?_⟩
  filter_upwards [ae_restrict_of_ae hii.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioo] with r hr hri
  have hder : HasDerivAt F (d r) r :=
    (hr (by simpa only [Set.uIcc_of_le hT.le] using Set.Ioo_subset_Icc_self hri)
      0 hz).const_add (p 0)
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hri.1 hri.2] with x hx
  exact (heq (Set.Ioo_subset_Icc_self hx)).symm

/-- C06: the continuous trace, endpoint energy identity, sharp estimate, and
absolutely continuous product rule for arbitrary real Hilbert triples. -/
theorem time_trace : TimeTraceTheorem.{u,v} := by
  intro V H _ _ _ _ _ _ j T hT
  obtain ⟨trace, hr, hu, hc, he⟩ := hilbertTriple_trace j T hT
  refine ⟨trace, hr, hu, hc, he, ?_, ?_⟩
  · intro z
    let A := T⁻¹ * ‖j.embedding.compLp z.val.1‖ ^ 2 + 2 * ‖z.val.2‖ * ‖z.val.1‖
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hb : ‖trace z‖ ≤ Real.sqrt A := by
      apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg A)).mpr
      intro t
      have ht := curve_sq_bound j T hT z.val.1 z.val.2 (trace z) (hr z)
        (fun s t => (he z s t).2) t
      nlinarith [Real.sq_sqrt hA, norm_nonneg (trace z t), Real.sqrt_nonneg A]
    nlinarith [Real.sq_sqrt hA, norm_nonneg (trace z)]
  · intro z w
    let d := fun r => z.val.2 r (w.val.1 r) + w.val.2 r (z.val.1 r)
    have hd : Integrable d (timeMeasure T) :=
      (triple_pairing_integrable T w.val.1 z.val.2).add
        (triple_pairing_integrable T z.val.1 w.val.2)
    have hp := trace_product_identity j T hT trace hr
      (fun z s t => (he z s t).2) z w
    obtain ⟨hac, hder⟩ := regularity_of_integral_increments T hT _ d hd hp
    exact ⟨hd, hac, hder, hp⟩

end P201.Common.TimeTrace
