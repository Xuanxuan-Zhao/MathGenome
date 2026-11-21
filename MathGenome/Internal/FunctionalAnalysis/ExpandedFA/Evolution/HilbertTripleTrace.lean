import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTripleTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HilbertTriple
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
universe u v

namespace ExpandedFA.Evolution
open HilbertTripleTraceSpec

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

@[simp] theorem extendCurve_apply {T : ℝ} (f : TraceCurve H T)
    (t : Set.Icc 0 T) : extendCurve f t = f t := by
  simp [extendCurve, t.property]

theorem extendCurve_continuousOn {T : ℝ} (f : TraceCurve H T) :
    ContinuousOn (extendCurve f) (Set.Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Set.Icc 0 T).domRestrict (extendCurve f) = f := by
    funext t
    exact extendCurve_apply f t
  rw [heq]
  exact f.continuous

/-- The dual evaluation is a bounded bilinear map, so Hölder (2,2,1)
proves genuine integrability without assuming the energy identity. -/
theorem triple_pairing_integrable : PairingIntegrable (V := V) := by
  intro T u g
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.id ℝ (StrongDual ℝ V)).memLp_of_bilin 1
      (Lp.memLp g) (Lp.memLp u))

/-- Equality a.e. on (0,T) propagates to both endpoints by continuity. -/
theorem triple_representative_unique : RepresentativeUniqueness (V := V) (H := H) := by
  intro j T hT u f g hf hg
  have hopen : Set.EqOn (extendCurve f) (extendCurve g) (Set.Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq (hf.trans hg.symm) isOpen_Ioo
      ((extendCurve_continuousOn f).mono Set.Ioo_subset_Icc_self)
      ((extendCurve_continuousOn g).mono Set.Ioo_subset_Icc_self)
  have hclosed : Set.EqOn (extendCurve f) (extendCurve g) (Set.Icc 0 T) := by
    apply hopen.of_subset_closure (extendCurve_continuousOn f)
      (extendCurve_continuousOn g) Set.Ioo_subset_Icc_self
    rw [closure_Ioo (ne_of_lt hT)]
  ext t
  simpa only [extendCurve_apply] using hclosed t.property

/-- Cauchy–Schwarz for the actual dual energy density. The estimate remains
valid when V is the zero space. -/
theorem triple_pairing_L1_bound (T : ℝ) (u : TimeLp V 2 T)
    (g : TimeLp (StrongDual ℝ V) 2 T) :
    (∫ t, ‖g t (u t)‖ ∂timeMeasure T) ≤ ‖g‖ * ‖u‖ := by
  let B := ContinuousLinearMap.id ℝ (StrongDual ℝ V)
  calc
    (∫ t, ‖g t (u t)‖ ∂timeMeasure T) = ‖B.holder 1 g u‖ := by
      rw [L1.norm_eq_integral_norm]
      exact integral_congr_ae ((B.coeFn_holder (r := 1) g u).fun_comp norm).symm
    _ ≤ ‖B‖ * ‖g‖ * ‖u‖ := B.norm_holder_apply_apply_le g u
    _ ≤ 1 * ‖g‖ * ‖u‖ := by
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = ‖g‖ * ‖u‖ := by ring

/-- Endpoint intervals have no extra integrability requirement: Lebesgue
measure gives the endpoints mass zero. -/
theorem triple_pairing_intervalIntegrable (T : ℝ) (u : TimeLp V 2 T)
    (g : TimeLp (StrongDual ℝ V) 2 T) (s t : Set.Icc 0 T) :
    IntervalIntegrable (energyDensity T u g) volume s.val t.val := by
  have hi : IntegrableOn (energyDensity T u g) (Set.Icc 0 T) := by
    have h := triple_pairing_integrable T u g
    simpa only [IntegrableOn, HilbertTripleSpec.timeMeasureValue,
      restrict_Ioo_eq_restrict_Icc] using h
  rw [intervalIntegrable_iff']
  exact hi.mono_set (Set.uIcc_subset_Icc s.property t.property)

/-- The energy identity for a C¹ V-valued trajectory, before taking limits. -/
theorem smooth_triple_energy_identity (j : HilbertTriple V H) (F : ℝ → V)
    (hF : ContDiff ℝ 1 F) (s t : ℝ) :
    ‖j.embedding (F t)‖ ^ 2 - ‖j.embedding (F s)‖ ^ 2 =
      2 * ∫ r in s..t, intoDual j (deriv F r) (F r) := by
  have hFc : Continuous F := hF.continuous
  have hdc : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hc : Continuous (fun r => intoDual j (deriv F r) (F r)) :=
    (((intoDual j).continuous.comp hdc).clm_apply hFc)
  have hd (r : ℝ) : HasDerivAt (fun x => ‖j.embedding (F x)‖ ^ 2)
      (2 * intoDual j (deriv F r) (F r)) r := by
    have h := (j.embedding.hasFDerivAt.comp_hasDerivAt r
      ((hF.differentiable (by norm_num)) r).hasDerivAt).norm_sq
    simpa only [intoDual_apply, Function.comp_apply,
      real_inner_comm (j.embedding (F r)) (j.embedding (deriv F r))] using h
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hd r) ((continuous_const.mul hc).intervalIntegrable s t)
  rw [intervalIntegral.integral_const_mul] at heq
  exact heq.symm

/-- Continuity of evaluation for an arbitrary bounded bilinear map. Keeping
this separate avoids unfolding the Hölder construction while taking limits. -/
theorem bilinear_tendsto {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (e : E) (f : F) (en : ℕ → E) (fn : ℕ → F)
    (he : Filter.Tendsto en Filter.atTop (𝓝 e))
    (hf : Filter.Tendsto fn Filter.atTop (𝓝 f)) :
    Filter.Tendsto (fun n => B (en n) (fn n)) Filter.atTop (𝓝 (B e f)) := by
  have hprod : Filter.Tendsto (fun n => (en n, fn n)) Filter.atTop (𝓝 (e, f)) :=
    he.prodMk_nhds hf
  exact (B.continuous₂.tendsto (e, f)).comp hprod

/-- Strong L² convergence in both factors implies L¹ convergence of the
energy densities. This supplies the energy-identity limit without requiring
pointwise convergence of the derivatives. -/
theorem triple_pairing_L1_tendsto (T : ℝ)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T)
    (un : ℕ → TimeLp V 2 T) (gn : ℕ → TimeLp (StrongDual ℝ V) 2 T)
    (hu : Filter.Tendsto un Filter.atTop (𝓝 u))
    (hg : Filter.Tendsto gn Filter.atTop (𝓝 g)) :
    Filter.Tendsto (fun n => ∫ t, ‖gn n t (un n t) - g t (u t)‖ ∂timeMeasure T)
      Filter.atTop (𝓝 0) := by
  let B := ContinuousLinearMap.id ℝ (StrongDual ℝ V)
  let P := B.holderL (timeMeasure T) 2 2 1
  have hP : Filter.Tendsto (fun n => P (gn n) (un n)) Filter.atTop (𝓝 (P g u)) :=
    bilinear_tendsto P g u gn un hg hu
  have heq (n : ℕ) : (∫ t, ‖gn n t (un n t) - g t (u t)‖ ∂timeMeasure T) =
      ‖P (gn n) (un n) - P g u‖ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (P (gn n) (un n)) (P g u),
      B.coeFn_holder (r := 1) (gn n) (un n), B.coeFn_holder (r := 1) g u]
      with t ht hn h0
    rw [ht]
    change _ = ‖(B.holder 1 (gn n) (un n)) t - (B.holder 1 g u) t‖
    rw [hn, h0]
    rfl
  simpa only [heq, sub_self, norm_zero] using (hP.sub_const (P g u)).norm


/-- Cauchy–Schwarz also controls every oriented subinterval integral. -/
theorem triple_pairing_interval_bound (T : ℝ) (u : TimeLp V 2 T)
    (g : TimeLp (StrongDual ℝ V) 2 T) (s t : Set.Icc 0 T) :
    ‖∫ r in s.val..t.val, g r (u r)‖ ≤ ‖g‖ * ‖u‖ := by
  have hi : IntegrableOn (fun r => g r (u r)) (Set.Icc 0 T) := by
    change Integrable (fun r => g r (u r)) (volume.restrict (Set.Icc 0 T))
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact triple_pairing_integrable T u g
  calc
    ‖∫ r in s.val..t.val, g r (u r)‖ ≤
        ∫ r in Set.uIoc s.val t.val, ‖g r (u r)‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ r in Set.Icc 0 T, ‖g r (u r)‖ :=
      setIntegral_mono_set hi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun _ hr =>
          Set.uIcc_subset_Icc s.property t.property (Set.uIoc_subset_uIcc hr))
    _ = ∫ r, ‖g r (u r)‖ ∂timeMeasure T := by
      simp only [timeMeasure, HilbertTripleSpec.timeMeasureValue,
        restrict_Ioo_eq_restrict_Icc]
    _ ≤ ‖g‖ * ‖u‖ := triple_pairing_L1_bound T u g

/-- L² norm identity for the existing classes, with their original norm. -/
theorem timeLp_integral_norm_sq (T : ℝ) (u : TimeLp H 2 T) :
    (∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, timeMeasure]

/-- Quantitative trace estimate from a representative and its energy identity.
The hypotheses here are explicitly proof inputs; this lemma does not assert
that a general energy-space element already has such a representative. -/
theorem triple_curve_sq_bound_of_energy (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T) (f : TraceCurve H T)
    (hf : Represents j T u f)
    (he : ∀ s t : Set.Icc 0 T, ‖f t‖ ^ 2 - ‖f s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, g r (u r)) (t : Set.Icc 0 T) :
    ‖f t‖ ^ 2 ≤ T⁻¹ * ‖j.embedding‖ ^ 2 * ‖u‖ ^ 2 + 2 * ‖g‖ * ‖u‖ := by
  let μ := timeMeasure T
  let C : ℝ := 2 * ‖g‖ * ‖u‖
  have hμ : (μ Set.univ).toReal = T := by
    simp [μ, timeMeasure, HilbertTripleSpec.timeMeasureValue, Real.volume_Ioo, hT.le]
  let : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hu : MemLp (fun r => j.embedding (u r)) 2 μ :=
    j.embedding.comp_memLp u
  have hui : Integrable (fun r => ‖j.embedding (u r)‖ ^ 2) μ :=
    hu.integrable_norm_pow (by norm_num)
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
  have hnorm : (∫ r, ‖j.embedding (u r)‖ ^ 2 ∂μ) ≤
      ‖j.embedding‖ ^ 2 * ‖u‖ ^ 2 := by
    calc
      (∫ r, ‖j.embedding (u r)‖ ^ 2 ∂μ) = ‖j.embedding.compLp u‖ ^ 2 := by
        rw [← timeLp_integral_norm_sq T (j.embedding.compLp u)]
        exact integral_congr_ae (Filter.EventuallyEq.fun_comp (j.embedding.coeFn_compLp' u) (fun x => ‖x‖ ^ 2)).symm
      _ ≤ (‖j.embedding‖ * ‖u‖) ^ 2 := by
        gcongr
        exact j.embedding.norm_compLp_le u
      _ = ‖j.embedding‖ ^ 2 * ‖u‖ ^ 2 := mul_pow _ _ _
  have hmain : T * ‖f t‖ ^ 2 ≤ ‖j.embedding‖ ^ 2 * ‖u‖ ^ 2 + T * C := by
    simp only [Pi.add_apply] at havg
    rw [integral_add hui (integrable_const C), integral_const, integral_const] at havg
    simp only [MeasureTheory.measureReal_def, hμ, smul_eq_mul] at havg
    linarith
  apply (mul_le_mul_iff_right₀ hT).mp
  calc
    T * ‖f t‖ ^ 2 ≤ ‖j.embedding‖ ^ 2 * ‖u‖ ^ 2 + T * C := hmain
    _ = T * (T⁻¹ * ‖j.embedding‖ ^ 2 * ‖u‖ ^ 2 + 2 * ‖g‖ * ‖u‖) := by
      dsimp only [C]
      field_simp [hT.ne']

/-- Supremum-norm version of the energy estimate. The constant depends only
on the time interval and the norm of the original embedding. -/
theorem triple_curve_norm_bound_of_energy (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T) (f : TraceCurve H T)
    (hf : Represents j T u f)
    (he : ∀ s t : Set.Icc 0 T, ‖f t‖ ^ 2 - ‖f s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, g r (u r)) :
    ‖f‖ ≤ Real.sqrt (T⁻¹ * ‖j.embedding‖ ^ 2 + 1) * (‖u‖ + ‖g‖) := by
  let A : ℝ := T⁻¹ * ‖j.embedding‖ ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ Real.sqrt (A + 1) * (‖u‖ + ‖g‖) := by positivity
  apply (ContinuousMap.norm_le f hK).mpr
  intro t
  have hb := triple_curve_sq_bound_of_energy j T hT u g f hf he t
  have hsq : ‖f t‖ ^ 2 ≤ (Real.sqrt (A + 1) * (‖u‖ + ‖g‖)) ^ 2 := by
    calc
      ‖f t‖ ^ 2 ≤ A * ‖u‖ ^ 2 + 2 * ‖g‖ * ‖u‖ := by
        simpa only [A, mul_assoc] using hb
      _ ≤ (A + 1) * (‖u‖ + ‖g‖) ^ 2 := by
        nlinarith [mul_nonneg hA (sq_nonneg ‖g‖),
          mul_nonneg hA (mul_nonneg (norm_nonneg u) (norm_nonneg g)),
          sq_nonneg ‖g‖, sq_nonneg ‖u‖]
      _ = (Real.sqrt (A + 1) * (‖u‖ + ‖g‖)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact (sq_le_sq₀ (norm_nonneg _) hK).mp hsq

/-- A time-L¹ estimate that is uniform in both endpoints. -/
theorem norm_intervalIntegral_le_timeIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : ℝ) (h : ℝ → E) (hh : Integrable h (timeMeasure T))
    (s t : Set.Icc 0 T) :
    ‖∫ r in s.val..t.val, h r‖ ≤ ∫ r, ‖h r‖ ∂timeMeasure T := by
  have hi : IntegrableOn h (Set.Icc 0 T) := by
    change Integrable h (volume.restrict (Set.Icc 0 T))
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hh
  calc
    ‖∫ r in s.val..t.val, h r‖ ≤ ∫ r in Set.uIoc s.val t.val, ‖h r‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ r in Set.Icc 0 T, ‖h r‖ :=
      setIntegral_mono_set hi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun _ hr =>
          Set.uIcc_subset_Icc s.property t.property (Set.uIoc_subset_uIcc hr))
    _ = ∫ r, ‖h r‖ ∂timeMeasure T := by
      simp only [timeMeasure, HilbertTripleSpec.timeMeasureValue,
        restrict_Ioo_eq_restrict_Icc]

/-- The energy integral converges for every pair of endpoints. -/
theorem triple_pairing_interval_tendsto (T : ℝ)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T)
    (un : ℕ → TimeLp V 2 T) (gn : ℕ → TimeLp (StrongDual ℝ V) 2 T)
    (hu : Filter.Tendsto un Filter.atTop (𝓝 u))
    (hg : Filter.Tendsto gn Filter.atTop (𝓝 g)) (s t : Set.Icc 0 T) :
    Filter.Tendsto (fun n => ∫ r in s.val..t.val, gn n r (un n r)) Filter.atTop
      (𝓝 (∫ r in s.val..t.val, g r (u r))) := by
  have hbound (n : ℕ) :
      ‖(∫ r in s.val..t.val, gn n r (un n r)) - (∫ r in s.val..t.val, g r (u r))‖ ≤
        ∫ r, ‖gn n r (un n r) - g r (u r)‖ ∂timeMeasure T := by
    have hsub := intervalIntegral.integral_sub
      (triple_pairing_intervalIntegrable T (un n) (gn n) s t)
      (triple_pairing_intervalIntegrable T u g s t)
    change (∫ r in s.val..t.val, gn n r (un n r) - g r (u r)) =
      (∫ r in s.val..t.val, gn n r (un n r)) - (∫ r in s.val..t.val, g r (u r)) at hsub
    rw [← hsub]
    exact norm_intervalIntegral_le_timeIntegral T _
      ((triple_pairing_integrable T (un n) (gn n)).sub
        (triple_pairing_integrable T u g)) s t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hbound
    (triple_pairing_L1_tendsto T u g un gn hu hg)

/-- Passing the energy identity through a uniform H limit and strong L² limits.
This is a limit lemma: constructing the approximants and their uniform limit
remains a separate obligation. -/
theorem triple_energy_identity_of_limits (T : ℝ)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T)
    (un : ℕ → TimeLp V 2 T) (gn : ℕ → TimeLp (StrongDual ℝ V) 2 T)
    (hu : Filter.Tendsto un Filter.atTop (𝓝 u))
    (hg : Filter.Tendsto gn Filter.atTop (𝓝 g))
    (f : TraceCurve H T) (fn : ℕ → TraceCurve H T)
    (hf : Filter.Tendsto fn Filter.atTop (𝓝 f))
    (he : ∀ n (s t : Set.Icc 0 T), ‖fn n t‖ ^ 2 - ‖fn n s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, gn n r (un n r)) (s t : Set.Icc 0 T) :
    ‖f t‖ ^ 2 - ‖f s‖ ^ 2 = 2 * ∫ r in s.val..t.val, g r (u r) := by
  have hft : Filter.Tendsto (fun n => fn n t) Filter.atTop (𝓝 (f t)) :=
    (continuous_eval_const t).tendsto f |>.comp hf
  have hfs : Filter.Tendsto (fun n => fn n s) Filter.atTop (𝓝 (f s)) :=
    (continuous_eval_const s).tendsto f |>.comp hf
  have hl := (hft.norm.pow 2).sub (hfs.norm.pow 2)
  have hr := Filter.Tendsto.const_mul 2 (triple_pairing_interval_tendsto T u g un gn hu hg s t)
  exact tendsto_nhds_unique hl (by simpa only [he] using hr)

/-- Identifying a uniform H limit with the original V-valued L² class uses
an a.e.-convergent subsequence, not a separability assumption on V or H. -/
theorem triple_represents_of_limits (j : HilbertTriple V H) (T : ℝ)
    (u : TimeLp V 2 T) (un : ℕ → TimeLp V 2 T)
    (hu : Filter.Tendsto un Filter.atTop (𝓝 u))
    (f : TraceCurve H T) (fn : ℕ → TraceCurve H T)
    (hf : Filter.Tendsto fn Filter.atTop (𝓝 f))
    (hrep : ∀ n, Represents j T (un n) (fn n)) : Represents j T u f := by
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have hAll : ∀ᵐ r ∂timeMeasure T, ∀ n,
      extendCurve (fn n) r = j.embedding (un n r) := ae_all_iff.mpr hrep
  filter_upwards [hlim, hAll, ae_restrict_mem measurableSet_Ioo] with r hr ha hri
  let x : Set.Icc 0 T := ⟨r, Set.Ioo_subset_Icc_self hri⟩
  have hfn : Filter.Tendsto (fun n => fn (ns n) x) Filter.atTop (𝓝 (f x)) :=
    ((continuous_eval_const x).tendsto f).comp (hf.comp hns.tendsto_atTop)
  have hJU : Filter.Tendsto (fun n => j.embedding (un (ns n) r)) Filter.atTop
      (𝓝 (j.embedding (u r))) := (j.embedding.continuous.tendsto (u r)).comp hr
  have hfJ : Filter.Tendsto (fun n => j.embedding (un (ns n) r)) Filter.atTop
      (𝓝 (f x)) := hfn.congr' (Filter.Eventually.of_forall fun n => by
        simpa only [extendCurve, dite_eq_left (Set.Ioo_subset_Icc_self hri), x] using ha (ns n))
  have heq := tendsto_nhds_unique hfJ hJU
  simpa only [extendCurve, dite_eq_left (Set.Ioo_subset_Icc_self hri), x] using heq

/-- A uniform estimate on differences transfers the two L² Cauchy properties
to a genuine continuous H-valued limit. -/
theorem triple_trace_limit_of_approximants (j : HilbertTriple V H) (T : ℝ)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T)
    (un : ℕ → TimeLp V 2 T) (gn : ℕ → TimeLp (StrongDual ℝ V) 2 T)
    (hu : Filter.Tendsto un Filter.atTop (𝓝 u))
    (hg : Filter.Tendsto gn Filter.atTop (𝓝 g)) (fn : ℕ → TraceCurve H T)
    (hrep : ∀ n, Represents j T (un n) (fn n))
    (he : ∀ n (s t : Set.Icc 0 T), ‖fn n t‖ ^ 2 - ‖fn n s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, gn n r (un n r))
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ m n, ‖fn m - fn n‖ ≤ K * (‖un m - un n‖ + ‖gn m - gn n‖)) :
    ∃ f : TraceCurve H T, Represents j T u f ∧
      (∀ s t : Set.Icc 0 T, ‖f t‖ ^ 2 - ‖f s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, g r (u r)) ∧ Filter.Tendsto fn Filter.atTop (𝓝 f) := by
  have hc : CauchySeq fn := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    let δ := ε / (2 * (K + 1))
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    obtain ⟨Nu, hNu⟩ := Metric.cauchySeq_iff.mp hu.cauchySeq δ hδ
    obtain ⟨Ng, hNg⟩ := Metric.cauchySeq_iff.mp hg.cauchySeq δ hδ
    refine ⟨max Nu Ng, ?_⟩
    intro m hm n hn
    have hdu := hNu m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn)
    have hdg := hNg m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)
    calc
      dist (fn m) (fn n) ≤ K * (dist (un m) (un n) + dist (gn m) (gn n)) := by
        simpa only [dist_eq_norm] using hb m n
      _ ≤ (K + 1) * (dist (un m) (un n) + dist (gn m) (gn n)) := by
        gcongr
        linarith
      _ < (K + 1) * (δ + δ) :=
        mul_lt_mul_of_pos_left (add_lt_add hdu hdg) (by linarith)
      _ = ε := by
        dsimp only [δ]
        field_simp [show K + 1 ≠ 0 by linarith]
        ring
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨f, triple_represents_of_limits j T u un hu f fn hf hrep,
    triple_energy_identity_of_limits T u g un gn hu hg f fn hf he, hf⟩


lemma lp_two_norm_eq_sqrt_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} (f : Lp E 2 μ) :
    ‖f‖ = Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂μ) := by
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (Lp.memLp f)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- A uniformly bounded pointwise strongly convergent sequence of operators
converges strongly on L². This uses domination by the original Bochner norm. -/
theorem compLp_two_tendsto_of_strong {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure α} (An : ℕ → E →L[ℝ] F) (A : E →L[ℝ] F)
    (C : ℝ) (hbound : ∀ n x, ‖An n x‖ ≤ C * ‖x‖)
    (hlim : ∀ x, Filter.Tendsto (fun n => An n x) Filter.atTop (𝓝 (A x))) (f : Lp E 2 μ) :
    Filter.Tendsto (fun n => (An n).compLp f) Filter.atTop (𝓝 (A.compLp f)) := by
  let v (n : ℕ) := (An n).compLp f - A.compLp f
  have heq (n : ℕ) :
      (∫ t, ‖v n t‖ ^ 2 ∂μ) = ∫ t, ‖An n (f t) - A (f t)‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((An n).compLp f) (A.compLp f),
      (An n).coeFn_compLp' f, A.coeFn_compLp' f] with t ht hn ha
    simp only [v, ht, hn, ha, Pi.sub_apply]
  have hint : Integrable (fun t => (C + ‖A‖) ^ 2 * ‖f t‖ ^ 2) μ :=
    ((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul _
  have hc := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n t => ‖An n (f t) - A (f t)‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun t => (C + ‖A‖) ^ 2 * ‖f t‖ ^ 2)
    (fun n => ((((An n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).sub
      (A.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))).norm.pow 2))
    hint (fun n => Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb : ‖An n (f t) - A (f t)‖ ≤ (C + ‖A‖) * ‖f t‖ := by
        calc
          _ ≤ ‖An n (f t)‖ + ‖A (f t)‖ := norm_sub_le _ _
          _ ≤ C * ‖f t‖ + ‖A‖ * ‖f t‖ := add_le_add (hbound n _) (A.le_opNorm _)
          _ = _ := by ring
      calc
        _ ≤ ((C + ‖A‖) * ‖f t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb _
        _ = _ := mul_pow _ _ _)
    (Filter.Eventually.of_forall fun t => by
      simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        ((hlim (f t)).sub_const (A (f t))).norm.pow 2)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp
    (by simpa only [integral_zero] using hc)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, ← heq, ← lp_two_norm_eq_sqrt_integral, Real.sqrt_zero, v] using hsqrt



/-- Bounded linear maps preserve the actual Banach-valued weak derivative. -/
theorem hasTimeDerivative_map {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (T : ℝ) (u g : ℝ → E) (hd : HasTimeDerivative T u g) :
    HasTimeDerivative T (fun t => L (u t)) (fun t => L (g t)) := by
  refine ⟨L.locallyIntegrableOn_comp hd.1, L.locallyIntegrableOn_comp hd.2.1, ?_⟩
  intro φ hφ
  have hi := hasTimeDerivative_test_integrable T u g hd φ hφ
  have he := congrArg L (hd.2.2 φ hφ)
  change L (∫ t, deriv φ t • u t ∂timeMeasure T) =
    L (-(∫ t, φ t • g t ∂timeMeasure T)) at he
  rw [← L.integral_comp_comm hi.1, map_neg, ← L.integral_comp_comm hi.2] at he
  simpa only [map_smul, timeMeasure] using he

/-- L² graph data in the Banach derivative space can be regularized by a
bounded linear map into V without presupposing a Hilbert-valued trace. -/
theorem triple_regularized_derivative
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (T : ℝ) (z : EnergySpace j T)
    (R : StrongDual ℝ V →L[ℝ] V) :
    HasTimeDerivative T
      ((R.comp (intoDual j)).compLp z.val.1 : ℝ → V)
      (R.compLp z.val.2 : ℝ → V) := by
  have hd : HasTimeDerivative T (fun t => intoDual j (z.val.1 t)) z.val.2 := z.property
  have hmap := hasTimeDerivative_map R T _ _ hd
  apply (hasTimeDerivative_congr T
    (fun t => R (intoDual j (z.val.1 t)))
    ((R.comp (intoDual j)).compLp z.val.1 : ℝ → V)
    (fun t => R (z.val.2 t)) (R.compLp z.val.2 : ℝ → V) _ _).mp hmap
  · exact ((R.comp (intoDual j)).coeFn_compLp' z.val.1).symm
  · exact (R.coeFn_compLp' z.val.2).symm



lemma compLp_comp_eq {α E F G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : F →L[ℝ] G) (M : E →L[ℝ] F) (f : Lp E p μ) :
    L.compLp (M.compLp f) = (L.comp M).compLp f := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp' (M.compLp f), M.coeFn_compLp' f,
    (L.comp M).coeFn_compLp' f] with t hL hM hLM
  simp only [hL, hM, hLM, ContinuousLinearMap.comp_apply]

lemma compLp_id_eq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp E p μ) :
    (ContinuousLinearMap.id ℝ E).compLp f = f := by
  apply Lp.ext
  exact (ContinuousLinearMap.id ℝ E).coeFn_compLp' f

lemma compLp_two_tendsto_id_of_strong {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} (An : ℕ → E →L[ℝ] E)
    (hbound : ∀ n x, ‖An n x‖ ≤ ‖x‖)
    (hlim : ∀ x, Filter.Tendsto (fun n => An n x) Filter.atTop (𝓝 x)) (f : Lp E 2 μ) :
    Filter.Tendsto (fun n => (An n).compLp f) Filter.atTop (𝓝 f) := by
  have hc := compLp_two_tendsto_of_strong An (ContinuousLinearMap.id ℝ E) 1
    (fun n x => by simpa only [one_mul] using hbound n x) hlim f
  simpa only [compLp_id_eq] using hc


/-- Banach-valued integration by parts for an integrable primitive. Duality
is applied to the integral equality, so this uses no countable family of
functionals or separability assumption on the range space. -/
theorem integral_test_smul_primitive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : LocallyIntegrable g volume) (c : ℝ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    (∫ t, deriv φ t • (∫ r in c..t, g r)) = -(∫ t, φ t • g t) := by
  have hi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hP : Continuous (fun t => ∫ r in c..t, g r) :=
    intervalIntegral.continuous_primitive hi c
  have hleft : Integrable (fun t => deriv φ t • (∫ r in c..t, g r)) :=
    ((hφ.continuous_deriv (by simp)).smul hP).integrable_of_hasCompactSupport
      hcφ.deriv.smul_right
  have hright : Integrable (fun t => φ t • g t) :=
    hg.integrable_smul_left_of_hasCompactSupport hφ.continuous hcφ
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hLg : LocallyIntegrable (fun t => L (g t)) volume :=
    fun x => L.integrableAtFilter_comp (hg x)
  have hscalar := Sobolev.OneDimensional.integral_test_mul_primitive hLg c hφ hcφ
  rw [← L.integral_comp_comm hleft, map_neg, ← L.integral_comp_comm hright]
  simp only [map_smul, smul_eq_mul]
  have hcomm (t : ℝ) : L (∫ r in c..t, g r) = ∫ r in c..t, L (g r) :=
    (L.intervalIntegral_comp_comm (hi c t)).symm
  simp_rw [hcomm]
  linarith

/-- The weak derivative determines a Banach-valued primitive up to a constant
on the entire open interval. Zero extension is used before invoking the
upstream fundamental lemma, so arbitrary values outside the interval cannot
create a hidden local-integrability hypothesis. -/
theorem hasTimeDerivative_ae_eq_primitive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (u g : ℝ → E) (hu : Integrable u (timeMeasure T))
    (hg : Integrable g (timeMeasure T)) (hd : HasTimeDerivative T u g) :
    ∃ c : E, u =ᵐ[timeMeasure T]
      fun t => c + ∫ r in 0..t, (Set.Ioo 0 T).indicator g r := by
  let U := (Set.Ioo 0 T).indicator u
  let G := (Set.Ioo 0 T).indicator g
  have hU : Integrable U volume := (integrable_indicator_iff measurableSet_Ioo).mpr hu
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hi (a b : ℝ) : IntervalIntegrable G volume a b := hG.intervalIntegrable
  let P : ℝ → E := fun t => ∫ r in 0..t, G r
  have hP : Continuous P := intervalIntegral.continuous_primitive hi 0
  have hzero (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ Set.Ioo 0 T) :
      (∫ t, deriv φ t • (U - P) t) = 0 := by
    have hder := hd.2.2 φ ⟨hφ, hcφ, hsφ⟩
    have hext : (∫ t, deriv φ t • U t) = -(∫ t, φ t • G t) := by
      simpa only [U, G, ← Set.indicator_smul_apply,
        integral_indicator measurableSet_Ioo, HilbertTripleSpec.timeMeasureValue] using hder
    have hprim : (∫ t, deriv φ t • P t) = -(∫ t, φ t • G t) :=
      integral_test_smul_primitive hG.locallyIntegrable 0 hφ hcφ
    have h1 : Integrable (fun t => deriv φ t • U t) :=
      hU.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hcφ.deriv
    have h2 : Integrable (fun t => deriv φ t • P t) :=
      hP.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hcφ.deriv
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub h1 h2, hext, hprim, sub_self]
  obtain ⟨c, hc⟩ := Sobolev.OneDimensional.ae_eq_const_of_integral_deriv_eq_zero
    isOpen_Ioo (Set.ordConnected_Ioo) (hU.locallyIntegrable.sub hP.locallyIntegrable) hzero
  refine ⟨c, ?_⟩
  filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with t ht hti
  change U t - P t = c at ht
  have hUt : U t = u t := Set.indicator_of_mem hti u
  rw [hUt] at ht
  exact sub_eq_iff_eq_add.mp ht


def tripleGram (j : HilbertTriple V H) : V →L[ℝ] V :=
  j.embedding.adjoint.comp j.embedding

@[simp] theorem tripleGram_inner (j : HilbertTriple V H) (x y : V) :
    inner ℝ (tripleGram j x) y = inner ℝ (j.embedding x) (j.embedding y) := by
  exact j.embedding.adjoint_inner_left y (j.embedding x)

@[simp] theorem tripleGram_toDual (j : HilbertTriple V H) (x : V) :
    (InnerProductSpace.toDual ℝ V) (tripleGram j x) = intoDual j x := rfl

def tripleResolventBilin (j : HilbertTriple V H) (n : ℕ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (show V →L[ℝ] StrongDual ℝ V from
    (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap) +
    (n + 1 : ℝ) • intoDual j

@[simp] theorem tripleResolventBilin_apply (j : HilbertTriple V H) (n : ℕ) (x y : V) :
    tripleResolventBilin j n x y =
      inner ℝ x y + (n + 1 : ℝ) * inner ℝ (j.embedding x) (j.embedding y) := by
  simp [tripleResolventBilin]

theorem tripleResolventBilin_coercive (j : HilbertTriple V H) (n : ℕ) :
    IsCoercive (tripleResolventBilin j n) := by
  refine ⟨1, zero_lt_one, fun x => ?_⟩
  rw [tripleResolventBilin_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  have : 0 ≤ (n + 1 : ℝ) * ‖j.embedding x‖ ^ 2 := by positivity
  nlinarith

def tripleResolventEquiv (j : HilbertTriple V H) (n : ℕ) : V ≃L[ℝ] V :=
  (tripleResolventBilin_coercive j n).continuousLinearEquivOfBilin

def tripleResolvent (j : HilbertTriple V H) (n : ℕ) : V →L[ℝ] V :=
  (tripleResolventEquiv j n).symm.toContinuousLinearMap

@[simp] theorem tripleResolventEquiv_apply (j : HilbertTriple V H) (n : ℕ) (x : V) :
    tripleResolventEquiv j n x = x + (n + 1 : ℝ) • tripleGram j x := by
  apply ext_inner_right ℝ
  intro y
  change inner ℝ ((tripleResolventBilin_coercive j n).continuousLinearEquivOfBilin x) y = _
  rw [IsCoercive.continuousLinearEquivOfBilin_apply, tripleResolventBilin_apply,
    inner_add_left, real_inner_smul_left, tripleGram_inner]

theorem tripleResolvent_equation (j : HilbertTriple V H) (n : ℕ) (x : V) :
    tripleResolvent j n x + (n + 1 : ℝ) • tripleGram j (tripleResolvent j n x) = x := by
  rw [← tripleResolventEquiv_apply]
  exact (tripleResolventEquiv j n).apply_symm_apply x

theorem tripleResolvent_energy (j : HilbertTriple V H) (n : ℕ) (x : V) :
    ‖tripleResolvent j n x‖ ^ 2 +
      (n + 1 : ℝ) * ‖j.embedding (tripleResolvent j n x)‖ ^ 2 =
        inner ℝ x (tripleResolvent j n x) := by
  have he := congrArg (fun v => inner ℝ v (tripleResolvent j n x))
    (tripleResolvent_equation j n x)
  simpa only [inner_add_left, real_inner_smul_left, tripleGram_inner,
    real_inner_self_eq_norm_sq] using he

theorem tripleResolvent_contract (j : HilbertTriple V H) (n : ℕ) (x : V) :
    ‖tripleResolvent j n x‖ ≤ ‖x‖ := by
  have he := tripleResolvent_energy j n x
  have hi := real_inner_le_norm x (tripleResolvent j n x)
  have hn : 0 ≤ (n + 1 : ℝ) * ‖j.embedding (tripleResolvent j n x)‖ ^ 2 := by positivity
  have hx := norm_nonneg x
  have hs := norm_nonneg (tripleResolvent j n x)
  nlinarith

def tripleRegularize (j : HilbertTriple V H) (n : ℕ) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - tripleResolvent j n

theorem tripleRegularize_contract (j : HilbertTriple V H) (n : ℕ) (x : V) :
    ‖tripleRegularize j n x‖ ≤ ‖x‖ := by
  have he := tripleResolvent_energy j n x
  have hn : 0 ≤ (n + 1 : ℝ) * ‖j.embedding (tripleResolvent j n x)‖ ^ 2 := by positivity
  have hn2 := norm_sub_sq_real x (tripleResolvent j n x)
  change ‖x - tripleResolvent j n x‖ ≤ ‖x‖
  have hx := norm_nonneg x
  have hs := norm_nonneg (x - tripleResolvent j n x)
  nlinarith

theorem tripleResolvent_regularize (j : HilbertTriple V H) (n : ℕ) (x : V) :
    (n + 1 : ℝ) • tripleResolvent j n (tripleGram j x) = tripleRegularize j n x := by
  have he := congrArg (tripleResolvent j n) (tripleResolventEquiv_apply j n x)
  simp only [map_add, map_smul] at he
  have he' : tripleResolvent j n x + (n + 1 : ℝ) •
      tripleResolvent j n (tripleGram j x) = x := by
    simpa only [tripleResolvent, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using he.symm
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans he')

def tripleRiesz : V ≃L[ℝ] StrongDual ℝ V :=
  (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv

@[simp] theorem tripleRiesz_apply (x : V) :
    tripleRiesz (V := V) x = (InnerProductSpace.toDual ℝ V) x := rfl

@[simp] theorem tripleRiesz_norm (x : V) : ‖tripleRiesz (V := V) x‖ = ‖x‖ :=
  (InnerProductSpace.toDual ℝ V).norm_map x

@[simp] theorem tripleRiesz_symm_norm (x : StrongDual ℝ V) :
    ‖tripleRiesz.symm x‖ = ‖x‖ :=
  (InnerProductSpace.toDual ℝ V).symm.norm_map x

def tripleRegularizeDerivative (j : HilbertTriple V H) (n : ℕ) :
    StrongDual ℝ V →L[ℝ] V :=
  (n + 1 : ℝ) • (tripleResolvent j n).comp tripleRiesz.symm.toContinuousLinearMap

def tripleRegularizeDual (j : HilbertTriple V H) (n : ℕ) :
    StrongDual ℝ V →L[ℝ] StrongDual ℝ V :=
  tripleRiesz.toContinuousLinearMap.comp
    ((tripleRegularize j n).comp tripleRiesz.symm.toContinuousLinearMap)

theorem tripleRegularizeDerivative_intoDual (j : HilbertTriple V H) (n : ℕ) (x : V) :
    tripleRegularizeDerivative j n (intoDual j x) = tripleRegularize j n x := by
  change (n + 1 : ℝ) • tripleResolvent j n
    (tripleRiesz.symm (intoDual j x)) = _
  have hr : tripleRiesz.symm (intoDual j x) = tripleGram j x := by
    rw [← tripleGram_toDual]
    exact tripleRiesz.symm_apply_apply _
  rw [hr]
  exact tripleResolvent_regularize j n x

theorem tripleRegularizeDual_intoDual (j : HilbertTriple V H) (n : ℕ)
    (f : StrongDual ℝ V) :
    intoDual j (tripleRegularizeDerivative j n f) = tripleRegularizeDual j n f := by
  let y : V := tripleRiesz.symm f
  change intoDual j ((n + 1 : ℝ) • tripleResolvent j n y) =
    tripleRiesz (tripleRegularize j n y)
  rw [map_smul, ← tripleGram_toDual]
  rw [← tripleRiesz_apply, ← map_smul]
  congr 1
  exact eq_sub_iff_add_eq.mpr
    ((add_comm _ _).trans (tripleResolvent_equation j n y))

theorem tripleRegularizeDual_contract (j : HilbertTriple V H) (n : ℕ)
    (f : StrongDual ℝ V) : ‖tripleRegularizeDual j n f‖ ≤ ‖f‖ := by
  change ‖tripleRiesz (tripleRegularize j n (tripleRiesz.symm f))‖ ≤ ‖f‖
  rw [tripleRiesz_norm]
  simpa only [tripleRiesz_symm_norm] using
    tripleRegularize_contract j n (tripleRiesz.symm f)

theorem tripleGram_denseRange (j : HilbertTriple V H) : DenseRange (tripleGram j) := by
  have hd := tripleRiesz.symm.surjective.denseRange.comp
    (intoDual_injective_denseRange j).2 tripleRiesz.symm.continuous
  convert hd using 1
  ext x
  change tripleGram j x = tripleRiesz.symm (intoDual j x)
  rw [← tripleGram_toDual]
  exact (tripleRiesz.symm_apply_apply _).symm

theorem tripleResolvent_gram_bound (j : HilbertTriple V H) (n : ℕ) (x : V) :
    ‖tripleResolvent j n (tripleGram j x)‖ ≤ (n + 1 : ℝ)⁻¹ * ‖x‖ := by
  have he := congrArg norm (tripleResolvent_regularize j n x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < n + 1)] at he
  have hc := tripleRegularize_contract j n x
  have hn : (0 : ℝ) < n + 1 := by positivity
  apply (mul_le_mul_iff_right₀ hn).mp
  rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  nlinarith

theorem tripleResolvent_gram_tendsto (j : HilbertTriple V H) (x : V) :
    Filter.Tendsto (fun n => tripleResolvent j n (tripleGram j x))
      Filter.atTop (𝓝 0) := by
  have ha : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hz := (tendsto_inv_atTop_zero.comp ha).mul_const ‖x‖
  rw [zero_mul] at hz
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (tripleResolvent_gram_bound j · x) hz

theorem tripleResolvent_tendsto (j : HilbertTriple V H) (x : V) :
    Filter.Tendsto (fun n => tripleResolvent j n x) Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy⟩ := (tripleGram_denseRange j).exists_dist_lt x (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tripleResolvent_gram_tendsto j y)
    (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hcontract : dist (tripleResolvent j n x)
      (tripleResolvent j n (tripleGram j y)) ≤ dist x (tripleGram j y) := by
    simpa only [dist_eq_norm, ← map_sub] using
      tripleResolvent_contract j n (x - tripleGram j y)
  calc
    dist (tripleResolvent j n x) 0 ≤
        dist (tripleResolvent j n x) (tripleResolvent j n (tripleGram j y)) +
          dist (tripleResolvent j n (tripleGram j y)) 0 := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hy) (hN n hn)
    _ = ε := add_halves ε

theorem tripleRegularize_tendsto (j : HilbertTriple V H) (x : V) :
    Filter.Tendsto (fun n => tripleRegularize j n x) Filter.atTop (𝓝 x) := by
  simpa only [tripleRegularize, sub_apply,
    ContinuousLinearMap.id_apply, sub_zero] using
    tendsto_const_nhds.sub (tripleResolvent_tendsto j x)

theorem tripleRegularizeDual_tendsto (j : HilbertTriple V H) (f : StrongDual ℝ V) :
    Filter.Tendsto (fun n => tripleRegularizeDual j n f) Filter.atTop (𝓝 f) := by
  have he := tripleRiesz.continuous.continuousAt.tendsto.comp
    (tripleRegularize_tendsto j (tripleRiesz.symm f))
  simpa only [tripleRegularizeDual, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, Function.comp_def,
    ContinuousLinearEquiv.apply_symm_apply] using he

theorem tripleRegularizeDerivative_comp_intoDual (j : HilbertTriple V H) (n : ℕ) :
    (tripleRegularizeDerivative j n).comp (intoDual j) = tripleRegularize j n := by
  ext x
  exact tripleRegularizeDerivative_intoDual j n x

theorem intoDual_comp_tripleRegularizeDerivative (j : HilbertTriple V H) (n : ℕ) :
    (intoDual j).comp (tripleRegularizeDerivative j n) = tripleRegularizeDual j n := by
  apply ContinuousLinearMap.ext
  intro f
  exact tripleRegularizeDual_intoDual j n f

theorem tripleSpatialRegularizers (j : HilbertTriple V H) :
    ∃ R : ℕ → StrongDual ℝ V →L[ℝ] V,
      (∀ n x, ‖R n (intoDual j x)‖ ≤ ‖x‖) ∧
      (∀ n f, ‖intoDual j (R n f)‖ ≤ ‖f‖) ∧
      (∀ x, Filter.Tendsto (fun n => R n (intoDual j x)) Filter.atTop (𝓝 x)) ∧
      (∀ f, Filter.Tendsto (fun n => intoDual j (R n f)) Filter.atTop (𝓝 f)) := by
  refine ⟨tripleRegularizeDerivative j, ?_, ?_, ?_, ?_⟩
  · intro n x
    rw [tripleRegularizeDerivative_intoDual]
    exact tripleRegularize_contract j n x
  · intro n f
    rw [tripleRegularizeDual_intoDual]
    exact tripleRegularizeDual_contract j n f
  · intro x
    simpa only [tripleRegularizeDerivative_intoDual] using tripleRegularize_tendsto j x
  · intro f
    simpa only [tripleRegularizeDual_intoDual] using tripleRegularizeDual_tendsto j f


/-- Continuous representative in the Banach derivative space; the increment
identity includes all endpoint times. -/
theorem hasTimeDerivative_continuous_primitive {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (u g : ℝ → E) (hu : Integrable u (timeMeasure T))
    (hg : Integrable g (timeMeasure T)) (hd : HasTimeDerivative T u g) :
    ∃ P : ℝ → E, Continuous P ∧ u =ᵐ[timeMeasure T] P ∧
      ∀ s t : Set.Icc 0 T,
        P t - P s = ∫ r in s.val..t.val, g r := by
  obtain ⟨c, hc⟩ := hasTimeDerivative_ae_eq_primitive T u g hu hg hd
  let G := (Set.Ioo 0 T).indicator g
  have hG : Integrable G volume := (integrable_indicator_iff measurableSet_Ioo).mpr hg
  have hi (a b : ℝ) : IntervalIntegrable G volume a b := hG.intervalIntegrable
  let P : ℝ → E := fun t => c + ∫ r in 0..t, G r
  refine ⟨P, continuous_const.add (intervalIntegral.continuous_primitive hi 0), hc, ?_⟩
  intro s t
  have hdifference : P t - P s = ∫ r in s.val..t.val, G r := by
    dsimp [P]
    rw [add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 s)]
  rw [hdifference]
  apply intervalIntegral.integral_congr_ae_restrict
  have heq : G =ᵐ[volume.restrict (Set.Icc 0 T)] g := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Set.indicator_of_mem hr g
  exact ae_restrict_of_ae_restrict_of_subset
    (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc s.property t.property)) heq



/-- The image of a smooth V-valued curve on the actual closed interval. -/
def smoothTripleCurve (j : HilbertTriple V H) (T : ℝ) (F : ℝ → V)
    (hF : ContDiff ℝ 1 F) : TraceCurve H T :=
  ⟨fun t => j.embedding (F t),
    j.embedding.continuous.comp (hF.continuous.comp continuous_subtype_val)⟩

/-- A.e. agreement on the full time interval can be used on every oriented
subinterval, including those that meet either endpoint. -/
theorem time_integral_congr_ae {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : ℝ) {a b : ℝ → E}
    (hab : a =ᵐ[timeMeasure T] b) (s t : Set.Icc 0 T) :
    (∫ r in s.val..t.val, a r) = ∫ r in s.val..t.val, b r := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hcc : a =ᵐ[volume.restrict (Set.Icc 0 T)] b := by
    simpa only [timeMeasure, HilbertTripleSpec.timeMeasureValue,
      restrict_Ioo_eq_restrict_Icc] using hab
  exact hcc.filter_mono (ae_mono (Measure.restrict_mono_set _
    (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc s.property t.property))))

/-- Actual L² classes agreeing with a smooth graph have its endpoint energy
identity; the selected representatives of L² need not agree pointwise. -/
theorem smooth_triple_energy_identity_of_ae (j : HilbertTriple V H) (T : ℝ)
    (F : ℝ → V) (hF : ContDiff ℝ 1 F)
    (u : TimeLp V 2 T) (g : TimeLp (StrongDual ℝ V) 2 T)
    (hu : (u : ℝ → V) =ᵐ[timeMeasure T] F)
    (hg : (g : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
      fun r => intoDual j (deriv F r)) (s t : Set.Icc 0 T) :
    ‖smoothTripleCurve j T F hF t‖ ^ 2 - ‖smoothTripleCurve j T F hF s‖ ^ 2 =
      2 * ∫ r in s.val..t.val, g r (u r) := by
  have hpair : (fun r => g r (u r)) =ᵐ[timeMeasure T]
      (fun r => intoDual j (deriv F r) (F r)) := by
    filter_upwards [hu, hg] with r hr hgr
    rw [hr, hgr]
  rw [time_integral_congr_ae T hpair s t]
  exact smooth_triple_energy_identity j F hF s.val t.val

theorem smoothTripleCurve_represents (j : HilbertTriple V H) (T : ℝ)
    (F : ℝ → V) (hF : ContDiff ℝ 1 F) (u : TimeLp V 2 T)
    (hu : (u : ℝ → V) =ᵐ[timeMeasure T] F) :
    Represents j T u (smoothTripleCurve j T F hF) := by
  filter_upwards [hu, ae_restrict_mem measurableSet_Ioo] with r hr hri
  simp only [extendCurve, dite_eq_left (Set.Ioo_subset_Icc_self hri),
    smoothTripleCurve, ContinuousMap.coe_mk, hr]

/-- Subtraction respects representation of the original L² classes. -/
theorem triple_represents_sub (j : HilbertTriple V H) (T : ℝ)
    (u v : TimeLp V 2 T) (f h : TraceCurve H T)
    (hf : Represents j T u f) (hh : Represents j T v h) :
    Represents j T (u - v) (f - h) := by
  filter_upwards [hf, hh, Lp.coeFn_sub u v,
    ae_restrict_mem measurableSet_Ioo] with r hfr hhr huv hr
  have hrcc := Set.Ioo_subset_Icc_self hr
  simp only [extendCurve, dite_eq_left hrcc] at hfr hhr ⊢
  simp only [ContinuousMap.sub_apply, huv, Pi.sub_apply, map_sub, hfr, hhr]

/-- The difference of two smooth graph representatives is again the smooth
graph of their difference. This is the estimate needed for Cauchy completion. -/
theorem smooth_triple_difference_energy (j : HilbertTriple V H) (T : ℝ)
    (F G : ℝ → V) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (u v : TimeLp V 2 T) (g h : TimeLp (StrongDual ℝ V) 2 T)
    (hu : (u : ℝ → V) =ᵐ[timeMeasure T] F)
    (hv : (v : ℝ → V) =ᵐ[timeMeasure T] G)
    (hg : (g : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
      fun r => intoDual j (deriv F r))
    (hh : (h : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
      fun r => intoDual j (deriv G r)) (s t : Set.Icc 0 T) :
    ‖(smoothTripleCurve j T F hF - smoothTripleCurve j T G hG) t‖ ^ 2 -
      ‖(smoothTripleCurve j T F hF - smoothTripleCurve j T G hG) s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, (g - h) r ((u - v) r) := by
  have huv : ((u - v : TimeLp V 2 T) : ℝ → V) =ᵐ[timeMeasure T] F - G := by
    filter_upwards [Lp.coeFn_sub u v, hu, hv] with r huv hr hvr
    simp only [huv, hr, hvr, Pi.sub_apply]
  have hgh : ((g - h : TimeLp (StrongDual ℝ V) 2 T) : ℝ → StrongDual ℝ V)
      =ᵐ[timeMeasure T] fun r => intoDual j (deriv (F - G) r) := by
    filter_upwards [Lp.coeFn_sub g h, hg, hh] with r hgh hgr hhr
    simp only [hgh, Pi.sub_apply, hgr, hhr,
      deriv_sub (hF.differentiable (by norm_num) r) (hG.differentiable (by norm_num) r),
      map_sub]
  have he := smooth_triple_energy_identity_of_ae j T (F - G) (hF.sub hG)
    (u - v) (g - h) huv hgh s t
  simpa only [smoothTripleCurve, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
    Pi.sub_apply, map_sub] using he

theorem smooth_triple_difference_bound (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (F G : ℝ → V) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (u v : TimeLp V 2 T) (g h : TimeLp (StrongDual ℝ V) 2 T)
    (hu : (u : ℝ → V) =ᵐ[timeMeasure T] F)
    (hv : (v : ℝ → V) =ᵐ[timeMeasure T] G)
    (hg : (g : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
      fun r => intoDual j (deriv F r))
    (hh : (h : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
      fun r => intoDual j (deriv G r)) :
    ‖smoothTripleCurve j T F hF - smoothTripleCurve j T G hG‖ ≤
      Real.sqrt (T⁻¹ * ‖j.embedding‖ ^ 2 + 1) * (‖u - v‖ + ‖g - h‖) := by
  exact triple_curve_norm_bound_of_energy j T hT (u - v) (g - h) _
    (triple_represents_sub j T u v _ _
      (smoothTripleCurve_represents j T F hF u hu)
      (smoothTripleCurve_represents j T G hG v hv))
    (smooth_triple_difference_energy j T F G hF hG u v g h hu hv hg hh)

section BanachSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma continuous_primitive_contDiff_one {k : ℝ → E} (hk : Continuous k) (c : E) :
    ContDiff ℝ 1 (fun t => c + ∫ r in 0..t, k r) ∧
    ∀ t, deriv (fun t => c + ∫ r in 0..t, k r) t = k t := by
  have hd (t : ℝ) : HasDerivAt (fun t => c + ∫ r in 0..t, k r) (k t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 0 t)
      (hk.stronglyMeasurableAtFilter volume (𝓝 t)) hk.continuousAt).const_add c
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun t => (hd t).differentiableAt, ?_⟩,
    fun t => (hd t).deriv⟩
  simpa only [funext fun t => (hd t).deriv] using hk

lemma exists_continuous_timeLp_approx (T : ℝ) (g : TimeLp E 2 T) :
    ∃ (k : ℕ → (ℝ →ᵇ E)) (v : ℕ → TimeLp E 2 T),
      (∀ n, (v n : ℝ → E) =ᵐ[timeMeasure T] k n) ∧
      Filter.Tendsto v Filter.atTop (𝓝 g) := by
  classical
  let : IsFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let : IsFiniteMeasure (timeMeasure T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  letI : (timeMeasure T).WeaklyRegular := by
    exact Measure.WeaklyRegular.restrict_of_measure_ne_top (by simp)
  have hd := BoundedContinuousFunction.toLp_denseRange E (timeMeasure T) ℝ
    (p := 2) (by norm_num)
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (hd g)
  choose k hk using hv
  refine ⟨k, v, ?_, hlim⟩
  intro n
  rw [← hk n]
  exact BoundedContinuousFunction.coeFn_toLp _ _ _ _

lemma timeLp_integral_norm_bound (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TimeLp E 2 T,
      (∫ t, ‖g t‖ ∂timeMeasure T) ≤ C * ‖g‖ := by
  let : IsFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let : IsFiniteMeasure (timeMeasure T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let one : TimeLp ℝ 2 T := Lp.const 2 (timeMeasure T) 1
  let B : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨‖one‖, norm_nonneg _, fun g => ?_⟩
  calc
    (∫ t, ‖g t‖ ∂timeMeasure T) = ‖B.holder 1 one g‖ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [B.coeFn_holder (r := 1) one g,
        Lp.coeFn_const (p := 2) (μ := timeMeasure T) (c := (1 : ℝ))]
        with t ht ho
      change one t = 1 at ho
      simp only [B, ContinuousLinearMap.lsmul_apply] at ht
      rw [ht, ho, one_smul]
    _ ≤ ‖B‖ * ‖one‖ * ‖g‖ := B.norm_holder_apply_apply_le one g
    _ ≤ ‖one‖ * ‖g‖ := by
      have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
      nlinarith [norm_nonneg one, norm_nonneg g,
        mul_nonneg (sub_nonneg.mpr hB) (mul_nonneg (norm_nonneg one) (norm_nonneg g))]

lemma timeLp_intervalIntegrable (T : ℝ) (q : TimeLp E 2 T) (s t : Set.Icc 0 T) :
    IntervalIntegrable q volume s.val t.val := by
  let : IsFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let : IsFiniteMeasure (timeMeasure T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have hq : IntegrableOn q (Set.Icc 0 T) := by
    change Integrable q (volume.restrict (Set.Icc 0 T))
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact (Lp.memLp q).integrable (by norm_num)
  exact (hq.mono_set (Set.uIcc_subset_Icc s.property t.property)).intervalIntegrable

lemma timeSobolev_smooth_graph_dense (T : ℝ) (hT : 0 < T)
    (u d : TimeLp E 2 T) (hd : HasTimeDerivative T u d) :
    ∃ (F : ℕ → ℝ → E) (un dn : ℕ → TimeLp E 2 T),
      (∀ n, ContDiff ℝ 1 (F n)) ∧
      (∀ n, (un n : ℝ → E) =ᵐ[timeMeasure T] F n) ∧
      (∀ n, (dn n : ℝ → E) =ᵐ[timeMeasure T] deriv (F n)) ∧
      Filter.Tendsto un Filter.atTop (𝓝 u) ∧
      Filter.Tendsto dn Filter.atTop (𝓝 d) := by
  classical
  let : IsFiniteMeasure (HilbertTripleSpec.timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  let : IsFiniteMeasure (timeMeasure T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨c, hc⟩ := hasTimeDerivative_ae_eq_primitive T u d
    ((Lp.memLp u).integrable (by norm_num))
    ((Lp.memLp d).integrable (by norm_num)) hd
  obtain ⟨k, dn, hdn, hlim⟩ := exists_continuous_timeLp_approx T d
  let F (n : ℕ) (t : ℝ) : E := c + ∫ r in 0..t, k n r
  have hF (n : ℕ) := (continuous_primitive_contDiff_one (k n).continuous c).1
  have hder (n : ℕ) := (continuous_primitive_contDiff_one (k n).continuous c).2
  have hmem (n : ℕ) : MemLp (F n) 2 (timeMeasure T) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hF n).continuous.continuousOn
    apply MemLp.of_bound (hF n).continuous.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hC t (Set.Ioo_subset_Icc_self ht)
  let un (n : ℕ) : TimeLp E 2 T := (hmem n).toLp (F n)
  have hun (n : ℕ) : (un n : ℝ → E) =ᵐ[timeMeasure T] F n := (hmem n).coeFn_toLp
  refine ⟨F, un, dn, hF, hun, ?_, ?_, hlim⟩
  · intro n
    simpa only [F, funext fun t => hder n t] using hdn n
  obtain ⟨C, hC, hCB⟩ := timeLp_integral_norm_bound (E := E) T
  let zero : Set.Icc 0 T := ⟨0, le_rfl, hT.le⟩
  have hbound (n : ℕ) : ‖un n - u‖ ≤
      ((measureUnivNNReal (timeMeasure T) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹)) *
        (C * ‖dn n - d‖) := by
    apply Lp.norm_le_of_ae_bound (mul_nonneg hC (norm_nonneg _))
    filter_upwards [hun n, hc, Lp.coeFn_sub (un n) u,
      ae_restrict_mem measurableSet_Ioo] with t hfn hcu hs ht
    let tt : Set.Icc 0 T := ⟨t, Set.Ioo_subset_Icc_self ht⟩
    have hki : (∫ r in 0..t, k n r) = ∫ r in 0..t, dn n r :=
      time_integral_congr_ae T (hdn n).symm zero tt
    have hdi : (∫ r in 0..t, (Set.Ioo 0 T).indicator (d : ℝ → E) r) =
        ∫ r in 0..t, d r := by
      apply time_integral_congr_ae T _ zero tt
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact Set.indicator_of_mem hr _
    have hint : (∫ r in 0..t, dn n r) - (∫ r in 0..t, d r) =
        ∫ r in 0..t, (dn n - d) r := by
      rw [← intervalIntegral.integral_sub
        (timeLp_intervalIntegrable T (dn n) zero tt)
        (timeLp_intervalIntegrable T d zero tt)]
      exact time_integral_congr_ae T (Lp.coeFn_sub (dn n) d).symm zero tt
    rw [hs]
    change ‖un n t - u t‖ ≤ _
    rw [hfn, hcu]
    change ‖(c + ∫ r in 0..t, k n r) -
      (c + ∫ r in 0..t, (Set.Ioo 0 T).indicator (d : ℝ → E) r)‖ ≤ _
    rw [add_sub_add_left_eq_sub, hki, hdi, hint]
    exact (norm_intervalIntegral_le_timeIntegral T (dn n - d)
      ((Lp.memLp _).integrable (by norm_num)) zero tt).trans (hCB _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa using (((tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul C).const_mul
      ((measureUnivNNReal (timeMeasure T) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹)))

end BanachSmoothing

/-- The smooth graph density property. No representative or energy
identity is included among its hypotheses or conclusion. The smooth curves
must approximate both original components in their original L² norms. -/
def SmoothTripleGraphDense (j : HilbertTriple V H) (T : ℝ) : Prop :=
  ∀ z : EnergySpace j T,
    ∃ (F : ℕ → ℝ → V) (un : ℕ → TimeLp V 2 T)
      (gn : ℕ → TimeLp (StrongDual ℝ V) 2 T),
      (∀ n, ContDiff ℝ 1 (F n)) ∧
      (∀ n, (un n : ℝ → V) =ᵐ[timeMeasure T] F n) ∧
      (∀ n, (gn n : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
        fun r => intoDual j (deriv (F n) r)) ∧
      Filter.Tendsto un Filter.atTop (𝓝 z.val.1) ∧
      Filter.Tendsto gn Filter.atTop (𝓝 z.val.2)

/-- Smooth V-valued curves are dense in the original L²(V), L²(V′) graph.
Spatial resolvents first give a V-valued weak derivative; approximation of
that derivative by continuous functions and diagonal selection finish the proof. -/
theorem smooth_triple_graph_dense (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T) :
    SmoothTripleGraphDense j T := by
  classical
  obtain ⟨R, hPbound, hQbound, hPlim, hQlim⟩ := tripleSpatialRegularizers j
  let P (n : ℕ) := (R n).comp (intoDual j)
  let Q (n : ℕ) := (intoDual j).comp (R n)
  intro z
  let vn (n : ℕ) : TimeLp V 2 T := (P n).compLp z.val.1
  let dn (n : ℕ) : TimeLp V 2 T := (R n).compLp z.val.2
  let qn (n : ℕ) : TimeLp (StrongDual ℝ V) 2 T := (Q n).compLp z.val.2
  have hvlim : Filter.Tendsto vn Filter.atTop (𝓝 z.val.1) :=
    compLp_two_tendsto_id_of_strong P hPbound hPlim z.val.1
  have hqlim : Filter.Tendsto qn Filter.atTop (𝓝 z.val.2) :=
    compLp_two_tendsto_id_of_strong Q hQbound hQlim z.val.2
  have hder (n : ℕ) : HasTimeDerivative T (vn n) (dn n) :=
    triple_regularized_derivative j T z (R n)
  choose F un dd hF hun hdd huc hdc using
    fun n => timeSobolev_smooth_graph_dense T hT (vn n) (dn n) (hder n)
  let gn (n k : ℕ) : TimeLp (StrongDual ℝ V) 2 T := (intoDual j).compLp (dd n k)
  have hgn (n k : ℕ) : (gn n k : ℝ → StrongDual ℝ V) =ᵐ[timeMeasure T]
      fun r => intoDual j (deriv (F n k) r) := by
    filter_upwards [(intoDual j).coeFn_compLp' (dd n k), hdd n k] with r hr hd
    rw [hr, hd]
  have hgc (n : ℕ) : Filter.Tendsto (gn n) Filter.atTop (𝓝 (qn n)) := by
    have hc := ((intoDual j).compLpL 2 (timeMeasure T)).continuous.tendsto (dn n)
      |>.comp (hdc n)
    change Filter.Tendsto (gn n) Filter.atTop (𝓝 ((intoDual j).compLp (dn n))) at hc
    have heq : (intoDual j).compLp (dn n) = qn n :=
      compLp_comp_eq (intoDual j) (R n) z.val.2
    rw [heq] at hc
    exact hc
  let ε (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have he (n : ℕ) : ∃ k,
      ‖un n k - vn n‖ < ε n ∧ ‖gn n k - qn n‖ < ε n := by
    obtain ⟨Nu, hNu⟩ := Metric.tendsto_atTop.mp (huc n) (ε n) (hε n)
    obtain ⟨Ng, hNg⟩ := Metric.tendsto_atTop.mp (hgc n) (ε n) (hε n)
    exact ⟨max Nu Ng, by simpa only [dist_eq_norm] using hNu _ (le_max_left _ _),
      by simpa only [dist_eq_norm] using hNg _ (le_max_right _ _)⟩
  choose k hk1 hk2 using he
  have he0 : Filter.Tendsto ε Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu0 : Filter.Tendsto (fun n => un n (k n) - vn n) Filter.atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hk1 n).le) he0
  have hg0 : Filter.Tendsto (fun n => gn n (k n) - qn n) Filter.atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hk2 n).le) he0
  refine ⟨fun n => F n (k n), fun n => un n (k n), fun n => gn n (k n),
    fun n => hF n (k n), fun n => hun n (k n), fun n => hgn n (k n), ?_, ?_⟩
  · simpa only [sub_add_cancel, zero_add] using hu0.add hvlim
  · simpa only [sub_add_cancel, zero_add] using hg0.add hqlim


/-- Completion and the trace bound, conditional only on the explicitly stated
smooth graph density assertion. In particular, the difference estimate is
proved using differences of approximants, rather than inferred from the two
individual energy identities. -/
theorem hilbertTriple_trace_of_smooth_graph_dense
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (hdense : SmoothTripleGraphDense j T) :
    ∃ trace : EnergySpace j T → TraceCurve H T,
      (∀ z, Represents j T z.val.1 (trace z)) ∧
      (∀ z (f : TraceCurve H T), Represents j T z.val.1 f → f = trace z) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ z w,
        ‖trace z - trace w‖ ≤ C * (‖z.val.1 - w.val.1‖ + ‖z.val.2 - w.val.2‖)) ∧
      (∀ z (s t : Set.Icc 0 T),
        IntervalIntegrable (energyDensity T z.val.1 z.val.2) volume s.val t.val ∧
        ‖trace z t‖ ^ 2 - ‖trace z s‖ ^ 2 =
          2 * ∫ r in s.val..t.val, energyDensity T z.val.1 z.val.2 r) := by
  classical
  choose F un gn hF hun hgn huc hgc using hdense
  let fn (z : EnergySpace j T) (n : ℕ) := smoothTripleCurve j T (F z n) (hF z n)
  let K : ℝ := Real.sqrt (T⁻¹ * ‖j.embedding‖ ^ 2 + 1)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hrep (z : EnergySpace j T) (n : ℕ) : Represents j T (un z n) (fn z n) :=
    smoothTripleCurve_represents j T (F z n) (hF z n) (un z n) (hun z n)
  have he (z : EnergySpace j T) (n : ℕ) (s t : Set.Icc 0 T) :
      ‖fn z n t‖ ^ 2 - ‖fn z n s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, gn z n r (un z n r) :=
    smooth_triple_energy_identity_of_ae j T (F z n) (hF z n)
      (un z n) (gn z n) (hun z n) (hgn z n) s t
  have hb (z w : EnergySpace j T) (m n : ℕ) :
      ‖fn z m - fn w n‖ ≤ K * (‖un z m - un w n‖ + ‖gn z m - gn w n‖) :=
    smooth_triple_difference_bound j T hT (F z m) (F w n) (hF z m) (hF w n)
      (un z m) (un w n) (gn z m) (gn w n) (hun z m) (hun w n) (hgn z m) (hgn w n)
  have hlim (z : EnergySpace j T) := triple_trace_limit_of_approximants j T
    z.val.1 z.val.2 (un z) (gn z) (huc z) (hgc z) (fn z) (hrep z) (he z)
      K hK (hb z z)
  choose trace htrace henergy hconv using hlim
  refine ⟨trace, htrace, ?_, ⟨K, hK, ?_⟩, ?_⟩
  · intro z f hf
    exact triple_representative_unique j T hT z.val.1 f (trace z) hf (htrace z)
  · intro z w
    have hed (s t : Set.Icc 0 T) :
        ‖(trace z - trace w) t‖ ^ 2 - ‖(trace z - trace w) s‖ ^ 2 =
          2 * ∫ r in s.val..t.val, (z.val.2 - w.val.2) r ((z.val.1 - w.val.1) r) := by
      apply triple_energy_identity_of_limits T (z.val.1 - w.val.1) (z.val.2 - w.val.2)
        (fun n => un z n - un w n) (fun n => gn z n - gn w n)
        ((huc z).sub (huc w)) ((hgc z).sub (hgc w))
        (trace z - trace w) (fun n => fn z n - fn w n) ((hconv z).sub (hconv w))
      intro n
      exact smooth_triple_difference_energy j T (F z n) (F w n) (hF z n) (hF w n)
        (un z n) (un w n) (gn z n) (gn w n) (hun z n) (hun w n) (hgn z n) (hgn w n)
    exact triple_curve_norm_bound_of_energy j T hT (z.val.1 - w.val.1) (z.val.2 - w.val.2)
      (trace z - trace w)
      (triple_represents_sub j T _ _ _ _ (htrace z) (htrace w)) hed
  · intro z s t
    exact ⟨triple_pairing_intervalIntegrable T z.val.1 z.val.2 s t, henergy z s t⟩

/-- The positive-time Hilbert-triple trace theorem, with endpoint energy
identity, uniqueness and continuity for the two original L² norms. -/
theorem hilbertTriple_trace : TraceTheorem (V := V) (H := H) := by
  intro j T hT
  exact hilbertTriple_trace_of_smooth_graph_dense j T hT
    (smooth_triple_graph_dense j T hT)

end ExpandedFA.Evolution
