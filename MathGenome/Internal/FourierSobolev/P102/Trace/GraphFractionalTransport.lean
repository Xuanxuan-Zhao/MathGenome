import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.GraphFractionalTransport
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.P102.U4.GraphArea
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

namespace P102.Trace.MeasuredFractional
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {E : Type*} [NormedAddCommGroup E]
variable {m : ℕ} {μ : Measure X} {s : ℝ} {p : ℝ≥0∞}
local instance : DecidableEq X := Classical.decEq X

theorem metricEnergy_congr {g h : X → E} (hgh : g =ᵐ[μ] h) :
    metricEnergy m μ s p g = metricEnergy m μ s p h := by
  apply lintegral_congr_ae
  filter_upwards [hgh] with x hx
  apply lintegral_congr_ae
  filter_upwards [hgh] with y hy
  simp only [hx, hy]

theorem metricSeminorm_congr {g h : X → E} (hgh : g =ᵐ[μ] h) :
    metricSeminorm m μ s p g = metricSeminorm m μ s p h := by
  unfold metricSeminorm
  rw [metricEnergy_congr hgh]

theorem metricNorm_congr {g h : X → E} (hgh : g =ᵐ[μ] h) :
    metricNorm m μ s p g = metricNorm m μ s p h := by
  unfold metricNorm
  rw [metricSeminorm_congr hgh, eLpNorm_congr_ae hgh]

theorem metricKernel_measurable [BorelSpace X] [SecondCountableTopology X] :
    Measurable (metricKernel (X := X) m s p) := by
  unfold metricKernel
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
  fun_prop

/-- Fatou's lemma makes integrals of lower semicontinuous sections lower
semicontinuous on any first countable parameter space. -/
theorem lowerSemicontinuous_lintegral_sections
    {A Y : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    [MeasurableSpace Y] (ν : Measure Y) {f : A → Y → ℝ≥0∞}
    (hf : ∀ x, AEMeasurable (f x) ν)
    (hls : ∀ y, LowerSemicontinuous (fun x => f x y)) :
    LowerSemicontinuous (fun x => ∫⁻ y, f x y ∂ν) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro x
  exact (lintegral_mono fun y => (hls y).le_liminf x).trans
    (lintegral_liminf_le' hf)

theorem metricKernel_lowerSemicontinuous_left (y : X) :
    LowerSemicontinuous (fun x => metricKernel m s p (x, y)) := by
  intro x a ha
  by_cases hxy : x = y
  · simp [metricKernel, hxy] at ha
  · have hx : ∀ᶠ z in 𝓝 x, z ≠ y :=
      isClosed_singleton.isOpen_compl.mem_nhds hxy
    have hc : ContinuousAt (fun z =>
        (ENNReal.ofReal (dist z y) ^ ((m : ℝ) + s * p.toReal))⁻¹) x := by
      exact continuous_inv.continuousAt.comp
        (ENNReal.continuous_rpow_const.continuousAt.comp
          (ENNReal.continuous_ofReal.continuousAt.comp (continuousAt_id.dist continuousAt_const)))
    have ha' : a < (ENNReal.ofReal (dist x y) ^ ((m : ℝ) + s * p.toReal))⁻¹ := by
      simpa [metricKernel, hxy] using ha
    filter_upwards [hx, hc.lowerSemicontinuousAt a ha'] with z hz haz
    simpa [metricKernel, hz] using haz

theorem metricKernel_symm (x y : X) :
    metricKernel m s p (x, y) = metricKernel m s p (y, x) := by
  simp only [metricKernel, dist_comm, eq_comm]

theorem metricKernel_lowerSemicontinuous_right (x : X) :
    LowerSemicontinuous (fun y => metricKernel m s p (x, y)) := by
  simpa only [metricKernel_symm x] using
    (metricKernel_lowerSemicontinuous_left (m := m) (s := s) (p := p) x)

theorem metricKernel_ne_top (x y : X) : metricKernel m s p (x, y) ≠ ∞ := by
  unfold metricKernel
  split_ifs with hxy
  · exact ENNReal.zero_ne_top
  · exact ENNReal.inv_ne_top.mpr
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (dist_pos.mpr hxy))
        ENNReal.ofReal_ne_top).ne'

theorem metricSection_measurable [BorelSpace X] :
    Measurable (fun x => μ.withDensity (fun y => metricKernel m s p (x, y))) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [withDensity_apply _ hA]
  exact (lowerSemicontinuous_lintegral_sections (μ.restrict A)
    (fun x => (metricKernel_lowerSemicontinuous_right x).measurable.aemeasurable)
    metricKernel_lowerSemicontinuous_left).measurable

theorem metricCappedSection_measurable [BorelSpace X] (c : ℝ≥0∞) :
    Measurable (fun x => μ.withDensity (fun y => min (metricKernel m s p (x, y)) c)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [withDensity_apply _ hA]
  exact (lowerSemicontinuous_lintegral_sections (μ.restrict A)
    (fun x => ((metricKernel_lowerSemicontinuous_right x).inf
      continuous_const.lowerSemicontinuous).measurable.aemeasurable)
    (fun y => (metricKernel_lowerSemicontinuous_left y).inf
      continuous_const.lowerSemicontinuous)).measurable

theorem metricTransition_apply [BorelSpace X] (x : X) :
    metricTransition m μ s p x = μ.withDensity (fun y => metricKernel m s p (x, y)) := by
  rw [metricTransition, dite_eq_left metricSection_measurable]
  rfl

section SectionDensity
open ProbabilityTheory
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem cappedDensityLayer_measurable (ν : Measure B) [IsFiniteMeasure ν]
    (f : A → B → ℝ≥0∞) (hf : ∀ a, Measurable (f a))
    (hcap : ∀ n : ℕ, Measurable (fun a => ν.withDensity (fun b => min (f a b) n)))
    (n : ℕ) : Measurable (fun a => ν.withDensity
      (fun b => min (f a b) (n+1) - min (f a b) n)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have heq (a : A) : ν.withDensity (fun b => min (f a b) (n+1) - min (f a b) n) s =
      ν.withDensity (fun b => min (f a b) (n+1)) s -
      ν.withDensity (fun b => min (f a b) n) s := by
    simp only [withDensity_apply _ hs]
    apply lintegral_sub ((hf a).min measurable_const)
    · refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun b => min_le_right _ _) ?_)
      simp only [lintegral_const]
      exact ENNReal.mul_lt_top (by simp) (measure_lt_top (ν.restrict s) Set.univ)
    · exact ae_of_all _ fun b => min_le_min_left _ (by norm_cast; omega)
  have heqfun := funext heq
  rw [heqfun]
  have h1 : Measurable (fun a => ν.withDensity (fun b => min (f a b) (n+1)) s) := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (Measure.measurable_coe hs).comp (hcap (n+1))
  have h2 : Measurable (fun a => ν.withDensity (fun b => min (f a b) n) s) :=
    (Measure.measurable_coe hs).comp (hcap n)
  exact h1.sub h2

theorem ennreal_eq_tsum_cap_layers (r : ℝ≥0∞) (hr : r ≠ ∞) :
    r = ∑' n : ℕ, (min r (n+1) - min r n) := by
  have h_le : ∀ n : ℕ, ⌈r.toReal⌉₊ ≤ n → r ≤ n := by
    intro n hn
    have : r.toReal ≤ n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le hr _] at this
    · simpa using this
    · exact n.cast_nonneg
  rw [ENNReal.tsum_eq_liminf_sum_nat]
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (min r (i+1) - min r i) = min r n := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
      rw [Finset.sum_range_succ, hn]
      simp
  simp_rw [hsum]
  refine (Filter.Tendsto.liminf_eq ?_).symm
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨⌈r.toReal⌉₊, fun n hn => (min_eq_left (h_le n hn)).symm⟩

/-- A section density kernel is s-finite, assuming measurable capped kernels for finite measures. -/
theorem sectionDensity_sfinite (μ : Measure B) [SFinite μ]
    (f : A → B → ℝ≥0∞) (hf : ∀ a, Measurable (f a))
    (hft : ∀ a b, f a b ≠ ∞)
    (hcap : ∀ (ν : Measure B) [IsFiniteMeasure ν], ∀ n : ℕ,
      Measurable (fun a => ν.withDensity (fun b => min (f a b) n)))
    (k : Kernel A B) (hk : ∀ a, k a = μ.withDensity (f a)) :
    IsSFiniteKernel k := by
  let fs : ℕ → A → B → ℝ≥0∞ := fun n a b => min (f a b) (n+1) - min (f a b) n
  let ks : ℕ → ℕ → Kernel A B := fun i n =>
    ⟨fun a => (sfiniteSeq μ i).withDensity (fs n a),
      cappedDensityLayer_measurable (sfiniteSeq μ i) f hf (hcap (sfiniteSeq μ i)) n⟩
  have hks : ∀ i n, IsFiniteKernel (ks i n) := by
    intro i n
    refine ⟨⟨(n+1) * sfiniteSeq μ i Set.univ,
      ENNReal.mul_lt_top (by simp) (measure_lt_top _ _), fun a => ?_⟩⟩
    change (sfiniteSeq μ i).withDensity (fs n a) Set.univ ≤ _
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    calc
      ∫⁻ b, fs n a b ∂sfiniteSeq μ i ≤ ∫⁻ _ : B, (n+1 : ℝ≥0∞) ∂sfiniteSeq μ i := by
        apply lintegral_mono
        intro b
        exact tsub_le_self.trans (min_le_right _ _)
      _ = _ := lintegral_const _
  have hk_sum : k = Kernel.sum (fun i => Kernel.sum (ks i)) := by
    ext a s hs
    rw [hk a, ← sum_sfiniteSeq μ, withDensity_sum]
    simp only [Measure.sum_apply _ hs, Kernel.sum_apply' _ _ hs]
    congr 1 with i
    have hfeq : f a = ∑' n, fs n a := by
      funext b
      rw [Pi.tsum_apply]
      · exact ennreal_eq_tsum_cap_layers (f a b) (hft a b)
      · exact Pi.summable.mpr fun _ => ENNReal.summable
    rw [hfeq, withDensity_tsum (fun n => show Measurable (fs n a) from
      ((hf a).min measurable_const).sub ((hf a).min measurable_const)),
      Measure.sum_apply _ hs]
    rfl
  rw [hk_sum]
  have : ∀ i n, IsFiniteKernel (ks i n) := hks
  infer_instance

end SectionDensity

instance metricTransition_isSFiniteKernel [BorelSpace X] [SFinite μ] :
    ProbabilityTheory.IsSFiniteKernel (metricTransition m μ s p) := by
  apply sectionDensity_sfinite μ (fun x y => metricKernel m s p (x, y))
    (fun x => (metricKernel_lowerSemicontinuous_right x).measurable)
    (fun x y => metricKernel_ne_top x y)
    (fun ν _ n => metricCappedSection_measurable (μ := ν) n)
  exact metricTransition_apply

theorem metricPairMeasure_absolutelyContinuous [BorelSpace X] [SFinite μ] :
    metricPairMeasure m μ s p ≪ μ.prod μ := by
  rw [metricPairMeasure, ← Measure.compProd_const]
  apply Measure.AbsolutelyContinuous.compProd_right
  exact Eventually.of_forall fun x => by
    rw [metricTransition_apply, ProbabilityTheory.Kernel.const_apply]
    exact withDensity_absolutelyContinuous _ _

/-- The a.e. version of the iterated-integral formula, with no countability
assumption on the measurable spaces. -/
theorem lintegral_compProd_ae {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {ν : Measure A} [SFinite ν] {κ : ProbabilityTheory.Kernel A B}
    [ProbabilityTheory.IsSFiniteKernel κ] {f : A × B → ℝ≥0∞}
    (hf : AEMeasurable f (ν.compProd κ)) :
    ∫⁻ z, f z ∂ν.compProd κ = ∫⁻ x, ∫⁻ y, f (x, y) ∂κ x ∂ν := by
  rw [Measure.compProd, ProbabilityTheory.Kernel.lintegral_compProd₀ _ _ _ hf]
  simp

omit [MetricSpace X] in
theorem metricIncrement_aestronglyMeasurable_prod [SigmaFinite μ] {g : X → E}
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (metricIncrement g) (μ.prod μ) :=
  (hg.comp_quasiMeasurePreserving quasiMeasurePreserving_fst).sub
    (hg.comp_quasiMeasurePreserving quasiMeasurePreserving_snd)

theorem metricIncrement_aestronglyMeasurable [BorelSpace X] [SigmaFinite μ] {g : X → E}
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (metricIncrement g) (metricPairMeasure m μ s p) :=
  (metricIncrement_aestronglyMeasurable_prod hg).mono_ac
    metricPairMeasure_absolutelyContinuous

/-- Equality with the actual iterated integral, before taking roots. The
section-measure construction avoids joint measurability of the distance. -/
theorem integral_metricIncrement_eq_energy [BorelSpace X] [SigmaFinite μ]
    {g : X → E} (hg : AEStronglyMeasurable g μ) :
    (∫⁻ z, ‖metricIncrement g z‖ₑ ^ p.toReal ∂metricPairMeasure m μ s p) =
      metricEnergy m μ s p g := by
  rw [metricPairMeasure, lintegral_compProd_ae
    ((metricIncrement_aestronglyMeasurable hg).enorm.pow_const _)]
  apply lintegral_congr
  intro x
  simp only [metricIncrement]
  have hw : AEMeasurable (fun y => ‖g x - g y‖ₑ ^ p.toReal) μ := by
    simpa only [Pi.sub_apply] using
      (((aestronglyMeasurable_const (b := g x)).sub hg).enorm.pow_const p.toReal)
  rw [metricTransition_apply, lintegral_withDensity_eq_lintegral_mul₀
    (metricKernel_lowerSemicontinuous_right (m := m) (s := s) (p := p) x).measurable.aemeasurable
    hw]
  apply lintegral_congr
  intro y
  simp only [Pi.mul_apply, metricKernel, metricIncrement]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

theorem eLpNorm_metricIncrement_eq_seminorm [BorelSpace X] [SigmaFinite μ]
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) {g : X → E}
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (metricIncrement g) p (metricPairMeasure m μ s p) =
      metricSeminorm m μ s p g := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
    (metricIncrement_aestronglyMeasurable hg), integral_metricIncrement_eq_energy hg]
  rfl

theorem metricSeminorm_add_le [BorelSpace X] [SigmaFinite μ] (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g h : X → E} (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    metricSeminorm m μ s p (g + h) ≤
      metricSeminorm m μ s p g + metricSeminorm m μ s p h := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [← eLpNorm_metricIncrement_eq_seminorm hp0 hpt (hg.add hh),
    ← eLpNorm_metricIncrement_eq_seminorm hp0 hpt hg,
    ← eLpNorm_metricIncrement_eq_seminorm hp0 hpt hh]
  have hi : metricIncrement (g + h) = metricIncrement g + metricIncrement h := by
    funext z
    simp [metricIncrement, sub_add_sub_comm]
  rw [hi]
  exact eLpNorm_add_le hp

theorem metricNorm_add_le [BorelSpace X] [SigmaFinite μ] (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g h : X → E} (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    metricNorm m μ s p (g + h) ≤ metricNorm m μ s p g + metricNorm m μ s p h := by
  have ha := eLpNorm_add_le (f := g) (g := h) (μ := μ) hp
  have hb := metricSeminorm_add_le (m := m) (s := s) hp hpt hg hh
  simpa only [metricNorm, add_add_add_comm] using add_le_add ha hb

@[simp] theorem metricNorm_zero (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    metricNorm m μ s p (0 : X → E) = 0 := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  simp [metricNorm, metricSeminorm, metricEnergy, ENNReal.zero_rpow_of_pos hp,
    hp]

theorem metricNorm_sum_le [BorelSpace X] [SigmaFinite μ] (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {ι : Type*} (t : Finset ι) (g : ι → X → E)
    (hg : ∀ i ∈ t, MemLp (g i) p μ) :
    metricNorm m μ s p (∑ i ∈ t, g i) ≤ ∑ i ∈ t, metricNorm m μ s p (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [metricNorm_zero (zero_lt_one.trans_le hp).ne' hpt]
  | @insert i t hit ih =>
    rw [Finset.sum_insert hit, Finset.sum_insert hit]
    have hsum : AEStronglyMeasurable (∑ j ∈ t, g j) μ := by
      exact
        (memLp_finsetSum' t fun j hj => hg j (Finset.mem_insert_of_mem hj)).aestronglyMeasurable
    exact (metricNorm_add_le hp hpt (g := g i) (h := ∑ j ∈ t, g j)
      (hg i (Finset.mem_insert_self _ _)).aestronglyMeasurable hsum).trans
      (add_le_add_right (ih fun j hj => hg j (Finset.mem_insert_of_mem hj)) _)

theorem metricEnergy_euclidean {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (G : Set (P102.Fractional.Domain d)) (s : ℝ) (p : ℝ≥0∞)
    (g : P102.Fractional.Domain d → 𝕜) :
    metricEnergy d (volume.restrict G) s p g = P102.Fractional.energy G s p g := by
  simp only [metricEnergy, P102.Fractional.energy, P102.Fractional.domainMeasure, dist_eq_norm]

/-- Raw energies are monotone in their measure, with no measurability premise
on the representative or the integrand. -/
theorem metricEnergy_mono_measure {ν : Measure X} (hμν : μ ≤ ν) (g : X → E) :
    metricEnergy m μ s p g ≤ metricEnergy m ν s p g := by
  apply lintegral_mono' hμν
  intro x
  exact lintegral_mono' hμν (fun _ => le_rfl)

theorem metricEnergy_smul_measure (c : ℝ≥0∞) (hc : c ≠ ∞) (g : X → E) :
    metricEnergy m (c • μ) s p g = c * c * metricEnergy m μ s p g := by
  unfold metricEnergy
  simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' c _ hc]
  rw [mul_assoc]

/-- A measurable embedding transports arbitrary nonnegative integrands, so this
formula deliberately imposes no Borel representative assumption on g. -/
theorem metricEnergy_map {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) (g : Y → E) :
    metricEnergy m (Measure.map f μ) s p g =
      ∫⁻ x, ∫⁻ y, if x = y then 0 else
        ‖g (f x) - g (f y)‖ₑ ^ p.toReal /
          ENNReal.ofReal (dist (f x) (f y)) ^ ((m : ℝ) + s * p.toReal) ∂μ ∂μ := by
  simp only [metricEnergy, hf.lintegral_map, hf.injective.eq_iff]

private theorem div_le_mul_div {a b d C : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCt : C ≠ ∞) (hd : d ≤ C * b) : a / b ≤ C * (a / d) := by
  calc
    a / b = C * (a / (C * b)) := by
      simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hC0) (Or.inl hCt)]
      calc
        a * b⁻¹ = 1 * (a * b⁻¹) := (one_mul _).symm
        _ = (C * C⁻¹) * (a * b⁻¹) := by rw [ENNReal.mul_inv_cancel hC0 hCt]
        _ = C * (a * (C⁻¹ * b⁻¹)) := by ac_rfl
    _ ≤ C * (a / d) := mul_le_mul' le_rfl (ENNReal.div_le_div_left hd a)

/-- Local distance distortion, independently of the particular graph model. -/
theorem metricEnergy_map_distance_bounds {Y : Type*} [MetricSpace Y] [MeasurableSpace Y]
    {f : X → Y} (hf : MeasurableEmbedding f) (K : ℝ≥0) (hK : 0 < K)
    (hq : 0 ≤ (m : ℝ) + s * p.toReal)
    (hd : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ K * dist x y) (g : Y → E) :
    metricEnergy m (Measure.map f μ) s p g ≤ metricEnergy m μ s p (g ∘ f) ∧
    metricEnergy m μ s p (g ∘ f) ≤
      ((K : ℝ≥0∞) ^ ((m : ℝ) + s * p.toReal)) *
        metricEnergy m (Measure.map f μ) s p g := by
  let q : ℝ := (m : ℝ) + s * p.toReal
  let D : ℝ≥0∞ := (K : ℝ≥0∞) ^ q
  have hD0 : D ≠ 0 := (ENNReal.rpow_pos (by exact_mod_cast hK) ENNReal.coe_ne_top).ne'
  have hDt : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq ENNReal.coe_ne_top
  rw [metricEnergy_map hf]
  constructor
  · apply lintegral_mono_ae
    filter_upwards [hd] with x hx
    apply lintegral_mono_ae
    filter_upwards [hx] with y hy
    dsimp [Function.comp_def]
    split_ifs
    · exact le_rfl
    · exact ENNReal.div_le_div_left
        (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hy.1) hq) _
  · have hinner : ∀ᵐ x ∂μ,
        (∫⁻ y, if x = y then 0 else ‖g (f x) - g (f y)‖ₑ ^ p.toReal /
          ENNReal.ofReal (dist x y) ^ q ∂μ) ≤
        D * (∫⁻ y, if x = y then 0 else ‖g (f x) - g (f y)‖ₑ ^ p.toReal /
          ENNReal.ofReal (dist (f x) (f y)) ^ q ∂μ) := by
      filter_upwards [hd] with x hx
      rw [← lintegral_const_mul' D _ hDt]
      apply lintegral_mono_ae
      filter_upwards [hx] with y hy
      split_ifs
      · simp
      · apply div_le_mul_div hD0 hDt
        calc
          ENNReal.ofReal (dist (f x) (f y)) ^ q ≤
              ENNReal.ofReal ((K : ℝ) * dist x y) ^ q :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hy.2) hq
          _ = D * ENNReal.ofReal (dist x y) ^ q := by
            rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
              ENNReal.mul_rpow_of_nonneg _ _ hq]
    calc
      metricEnergy m μ s p (g ∘ f) ≤ ∫⁻ x, D * (∫⁻ y,
          if x = y then 0 else ‖g (f x) - g (f y)‖ₑ ^ p.toReal /
            ENNReal.ofReal (dist (f x) (f y)) ^ q ∂μ) ∂μ := lintegral_mono_ae hinner
      _ = _ := lintegral_const_mul' D _ hDt

universe u v

/-- Formula verification for the canonical definition shared through Specs. -/
theorem metricEnergy_definition : Expected.MetricEnergyDefinition.{u, v} := rfl

/-- Formula verification for the canonical definition shared through Specs. -/
theorem metricSeminorm_definition : Expected.MetricSeminormDefinition.{u, v} := rfl

/-- Formula verification for the canonical definition shared through Specs. -/
theorem metricNorm_definition : Expected.MetricNormDefinition.{u, v} := rfl

theorem energy_congr : Expected.EnergyCongr.{u, v} := by
  intro X _ _ E _ m μ s p g h hgh
  exact metricEnergy_congr hgh

theorem weighted_increment_identification : Expected.WeightedIncrementIdentification.{u, v} := by
  intro X _ _ _ E _ m μ _ s p hp0 hpt g hg
  exact eLpNorm_metricIncrement_eq_seminorm hp0 hpt hg

theorem norm_triangle : Expected.NormTriangle.{u, v} := by
  intro X _ _ _ E _ m μ _ s p hp hpt g h hg hh
  exact metricNorm_add_le hp hpt hg.aestronglyMeasurable hh.aestronglyMeasurable

theorem norm_finite_sum : Expected.NormFiniteSum.{u, v} := by
  intro X _ _ _ E _ m μ _ s p hp hpt ι t g hg
  exact metricNorm_sum_le hp hpt t g hg

theorem euclidean_energy : Expected.EuclideanEnergy.{v} := by
  intro d 𝕜 _ G s p g
  exact metricEnergy_euclidean G s p g

end P102.Trace.MeasuredFractional

namespace P102.Trace.GraphFractionalTransport
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open MeasuredFractional

/-- The Borel extension changes no values on the base. Graph distortion gives
both inequalities directly, without selecting a classical gradient. -/
theorem pushforward_comparison : Expected.PushforwardComparison := by
  intro m B hB γ L hL e
  let U : TopologicalSpace.Opens (Space m) := ⟨B, hB⟩
  let f : Space m → Ambient m := e ∘ GraphArea.borelParam U γ
  have hf : MeasurableEmbedding f :=
    e.toHomeomorph.measurableEmbedding.comp (GraphArea.borelParam_embedding U γ hL.continuousOn)
  have heq : EqOn f (graphMap e γ) B := by
    intro x hx
    exact congrArg e (GraphArea.borelParam_eq U γ hx)
  obtain ⟨_, _, harea⟩ := graph_geometry_in_frame m B γ L hL e
  refine ⟨f, hf, heq, ?_, ?_⟩
  · apply Measure.le_iff.mpr
    intro S hS
    have himg : graphMap e γ '' (f ⁻¹' S ∩ B) = S ∩ (graphMap e γ '' B) := by
      ext z
      constructor
      · rintro ⟨x, ⟨hxS, hxB⟩, rfl⟩
        exact ⟨by simpa only [mem_preimage, heq hxB] using hxS, ⟨x, hxB, rfl⟩⟩
      · rintro ⟨hzS, x, hxB, rfl⟩
        exact ⟨x, ⟨by simpa only [mem_preimage, heq hxB] using hzS, hxB⟩, rfl⟩
    rw [Measure.map_apply hf.measurable hS, Measure.restrict_apply (hf.measurable hS)]
    rw [graphMeasure, Measure.restrict_apply hS, ← himg]
    exact (harea _ inter_subset_right).1
  · apply Measure.le_iff.mpr
    intro S hS
    have himg : graphMap e γ '' (f ⁻¹' S ∩ B) = S ∩ (graphMap e γ '' B) := by
      ext z
      constructor
      · rintro ⟨x, ⟨hxS, hxB⟩, rfl⟩
        exact ⟨by simpa only [mem_preimage, heq hxB] using hxS, ⟨x, hxB, rfl⟩⟩
      · rintro ⟨hzS, x, hxB, rfl⟩
        exact ⟨x, ⟨by simpa only [mem_preimage, heq hxB] using hzS, hxB⟩, rfl⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf.measurable hS,
      Measure.restrict_apply (hf.measurable hS)]
    rw [graphMeasure, Measure.restrict_apply hS, ← himg]
    exact (harea _ inter_subset_right).2

/-- The two geometric inequalities imply equality of null sets. -/
theorem graphMap_ae_iff {m : ℕ} {B : Set (Space m)} (hB : IsOpen B)
    {γ : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L γ B)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (q : Ambient m → Prop) :
    (∀ᵐ z ∂graphMeasure e γ B, q z) ↔
      ∀ᵐ x ∂volume.restrict B, q (graphMap e γ x) := by
  obtain ⟨f, hf, heq, hlow, hupp⟩ := pushforward_comparison m B hB γ L hL e
  have hac₁ := Measure.absolutelyContinuous_of_le hlow
  have hac₂ := Measure.absolutelyContinuous_of_le_smul hupp
  have heqae : f =ᵐ[volume.restrict B] graphMap e γ :=
    (ae_restrict_iff' hB.measurableSet).mpr (Eventually.of_forall fun x hx => heq hx)
  have hm : (∀ᵐ z ∂graphMeasure e γ B, q z) ↔ ∀ᵐ z ∂Measure.map f (volume.restrict B), q z :=
    ⟨fun h => hac₁.ae_le h, fun h => hac₂.ae_le h⟩
  rw [hm, hf.ae_map_iff]
  exact eventually_congr (heqae.mono fun x hx => by rw [hx])

theorem graphMap_aestronglyMeasurable_iff {m : ℕ} {B : Set (Space m)} (hB : IsOpen B)
    {γ : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L γ B)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {E : Type*} [NormedAddCommGroup E]
    (g : Ambient m → E) :
    AEStronglyMeasurable g (graphMeasure e γ B) ↔
      AEStronglyMeasurable (g ∘ graphMap e γ) (volume.restrict B) := by
  obtain ⟨f, hf, heq, hlow, hupp⟩ := pushforward_comparison m B hB γ L hL e
  have hac₁ := Measure.absolutelyContinuous_of_le hlow
  have hac₂ := Measure.absolutelyContinuous_of_le_smul hupp
  have heqae : g ∘ f =ᵐ[volume.restrict B] g ∘ graphMap e γ :=
    (ae_restrict_iff' hB.measurableSet).mpr (Eventually.of_forall fun x hx => congrArg g (heq hx))
  have hm : AEStronglyMeasurable g (graphMeasure e γ B) ↔
      AEStronglyMeasurable g (Measure.map f (volume.restrict B)) :=
    ⟨fun h => h.mono_ac hac₁, fun h => h.mono_ac hac₂⟩
  rw [hm, hf.aestronglyMeasurable_map_iff]
  exact aestronglyMeasurable_congr heqae

theorem representative_transport : Expected.RepresentativeTransport := by
  intro m c R _ γ L hL e E _ g h
  exact ⟨graphMap_ae_iff Metric.isOpen_ball hL e (fun z => g z = h z),
    graphMap_aestronglyMeasurable_iff Metric.isOpen_ball hL e g⟩

/-- Pointwise representatives need not be measurable: the two integrals are
compared using inequalities of measures and the embedding's raw lintegral API. -/
theorem graph_lintegral_comparison {m : ℕ} {B : Set (Space m)} (hB : IsOpen B)
    {γ : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L γ B)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (w : Ambient m → ℝ≥0∞) :
    (∫⁻ x in B, w (graphMap e γ x)) ≤ ∫⁻ z, w z ∂graphMeasure e γ B ∧
    (∫⁻ z, w z ∂graphMeasure e γ B) ≤
      (graphConstant L : ℝ≥0∞) ^ m * ∫⁻ x in B, w (graphMap e γ x) := by
  obtain ⟨f, hf, heq, hlow, hupp⟩ := pushforward_comparison m B hB γ L hL e
  have heqint : (∫⁻ x in B, w (f x)) = ∫⁻ x in B, w (graphMap e γ x) := by
    apply setLIntegral_congr_fun hB.measurableSet
    intro x hx
    exact congrArg w (heq hx)
  have hmap : (∫⁻ z, w z ∂Measure.map f (volume.restrict B)) =
      ∫⁻ x in B, w (graphMap e γ x) := (hf.lintegral_map w).trans heqint
  constructor
  · rw [← hmap]
    exact lintegral_mono' hlow (fun _ => le_rfl)
  · calc
      (∫⁻ z, w z ∂graphMeasure e γ B) ≤
          ∫⁻ z, w z ∂((graphConstant L : ℝ≥0∞) ^ m) •
            Measure.map f (volume.restrict B) := lintegral_mono' hupp (fun _ => le_rfl)
      _ = _ := by rw [lintegral_smul_measure, smul_eq_mul, hmap]

/-- Norm comparison applies to all raw functions, including the convention that
the eLpNorm of a non-a.e.-strongly-measurable function is infinite. -/
theorem graph_eLpNorm_comparison {m : ℕ} {B : Set (Space m)} (hB : IsOpen B)
    {γ : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L γ B)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (g : Ambient m → E) :
    eLpNorm (g ∘ graphMap e γ) p (volume.restrict B) ≤ eLpNorm g p (graphMeasure e γ B) ∧
    eLpNorm g p (graphMeasure e γ B) ≤
      ((graphConstant L : ℝ≥0∞) ^ m) ^ (1 / p).toReal *
        eLpNorm (g ∘ graphMap e γ) p (volume.restrict B) := by
  obtain ⟨f, hf, heq, hlow, hupp⟩ := pushforward_comparison m B hB γ L hL e
  have heqae : g ∘ f =ᵐ[volume.restrict B] g ∘ graphMap e γ :=
    (ae_restrict_iff' hB.measurableSet).mpr (Eventually.of_forall fun x hx => congrArg g (heq hx))
  have hmap : eLpNorm g p (Measure.map f (volume.restrict B)) =
      eLpNorm (g ∘ graphMap e γ) p (volume.restrict B) :=
    hf.eLpNorm_map_measure.trans (eLpNorm_congr_ae heqae)
  constructor
  · rw [← hmap]
    exact eLpNorm_mono_measure g hlow
  · simpa only [hmap, smul_eq_mul] using eLpNorm_le_of_measure_le_smul (f := g) (p := p) hupp

theorem graph_memLp_iff {m : ℕ} {B : Set (Space m)} (hB : IsOpen B)
    {γ : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L γ B)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (g : Ambient m → E) :
    MemLp g p (graphMeasure e γ B) ↔ MemLp (g ∘ graphMap e γ) p (volume.restrict B) := by
  obtain ⟨f, hf, heq, hlow, hupp⟩ := pushforward_comparison m B hB γ L hL e
  have heqae : g ∘ f =ᵐ[volume.restrict B] g ∘ graphMap e γ :=
    (ae_restrict_iff' hB.measurableSet).mpr (Eventually.of_forall fun x hx => congrArg g (heq hx))
  have hm : MemLp g p (graphMeasure e γ B) ↔ MemLp g p (Measure.map f (volume.restrict B)) :=
    ⟨fun h => h.mono_measure hlow,
      fun h => h.of_measure_le_smul (by finiteness) hupp⟩
  rw [hm, hf.memLp_map_measure_iff]
  exact memLp_congr_ae heqae

private theorem graphConstant_pos (L : ℝ≥0) : 0 < graphConstant L := by
  unfold graphConstant
  positivity

/-- Both energies here are the actual diagonal-zero double integrals.
The forward energy constant is K^(m+sp); the reverse is K^(2m). -/
theorem graph_energy_comparison {m : ℕ} {B : Set (Space m)} (hB : IsOpen B)
    {γ : Space m → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L γ B)
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) {E : Type*} [NormedAddCommGroup E]
    (s : ℝ) (p : ℝ≥0∞) (hq : 0 ≤ (m : ℝ) + s * p.toReal) (g : Ambient m → E) :
    metricEnergy m (volume.restrict B) s p (g ∘ graphMap e γ) ≤
      (graphConstant L : ℝ≥0∞) ^ ((m : ℝ) + s * p.toReal) *
        metricEnergy m (graphMeasure e γ B) s p g ∧
    metricEnergy m (graphMeasure e γ B) s p g ≤
      ((graphConstant L : ℝ≥0∞) ^ m * (graphConstant L : ℝ≥0∞) ^ m) *
        metricEnergy m (volume.restrict B) s p (g ∘ graphMap e γ) := by
  obtain ⟨f, hf, heq, hlow, hupp⟩ := pushforward_comparison m B hB γ L hL e
  obtain ⟨hLip, hdist, _⟩ := graph_geometry_in_frame m B γ L hL e
  have hd : ∀ᵐ x ∂volume.restrict B, ∀ᵐ y ∂volume.restrict B,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ graphConstant L * dist x y := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    filter_upwards [ae_restrict_mem hB.measurableSet] with y hy
    rw [heq hx, heq hy]
    exact ⟨hdist x hx y hy, hLip.dist_le_mul x hx y hy⟩
  have heqae : g ∘ f =ᵐ[volume.restrict B] g ∘ graphMap e γ :=
    (ae_restrict_iff' hB.measurableSet).mpr (Eventually.of_forall fun x hx => congrArg g (heq hx))
  have hbase := metricEnergy_congr (m := m) (s := s) (p := p) heqae
  obtain ⟨hmapped, hbase_le⟩ := metricEnergy_map_distance_bounds hf (graphConstant L)
    (graphConstant_pos L) hq hd g
  rw [hbase] at hmapped hbase_le
  constructor
  · exact hbase_le.trans (mul_le_mul' le_rfl (metricEnergy_mono_measure hlow g))
  · calc
      metricEnergy m (graphMeasure e γ B) s p g ≤
          metricEnergy m (((graphConstant L : ℝ≥0∞) ^ m) • Measure.map f (volume.restrict B)) s p g :=
        metricEnergy_mono_measure hupp g
      _ = ((graphConstant L : ℝ≥0∞) ^ m * (graphConstant L : ℝ≥0∞) ^ m) *
          metricEnergy m (Measure.map f (volume.restrict B)) s p g :=
        metricEnergy_smul_measure _ (by finiteness) g
      _ ≤ _ := mul_le_mul' le_rfl hmapped

private theorem root_le_mul_root {a b : ℝ≥0∞} (c : ℝ≥0) (r : ℝ) (hr : 0 ≤ r)
    (h : a ≤ (c : ℝ≥0∞) * b) : a ^ r ≤ (c ^ r : ℝ≥0) * b ^ r := by
  calc
    a ^ r ≤ ((c : ℝ≥0∞) * b) ^ r := ENNReal.rpow_le_rpow h hr
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hr,
      ENNReal.coe_rpow_of_nonneg c hr]

/-- All eight estimates, with one positive finite uniform constant.
The exponents and the constants are chosen before the base ball and frame. -/
theorem local_graph_comparison : Expected.LocalGraphComparison := by
  intro m _ s hs _ p hp hpt L
  let K := graphConstant L
  let A : ℝ≥0 := K ^ m
  let q : ℝ := (m : ℝ) + s * p.toReal
  let r : ℝ := 1 / p.toReal
  have hq : 0 ≤ q := add_nonneg (Nat.cast_nonneg _) (mul_nonneg hs.le ENNReal.toReal_nonneg)
  have hr : 0 ≤ r := one_div_nonneg.mpr ENNReal.toReal_nonneg
  let N : ℝ≥0 := A ^ r
  let D : ℝ≥0 := K ^ q
  let AA : ℝ≥0 := A * A
  let R₁ : ℝ≥0 := D ^ r
  let R₂ : ℝ≥0 := AA ^ r
  let C : ℝ≥0 := max 1 (max A (max N (max D (max AA (max R₁ R₂)))))
  have h1C : (1 : ℝ≥0) ≤ C := le_max_left _ _
  have hAC : A ≤ C := by simp [C, le_max_iff]
  have hNC : N ≤ C := by simp [C, le_max_iff]
  have hDC : D ≤ C := by simp [C, le_max_iff]
  have hAAC : AA ≤ C := by simp [C, le_max_iff]
  have hR₁C : R₁ ≤ C := by simp [C, le_max_iff]
  have hR₂C : R₂ ≤ C := by simp [C, le_max_iff]
  have h1C' : (1 : ℝ≥0∞) ≤ C := by exact_mod_cast h1C
  have hAC' : (A : ℝ≥0∞) ≤ C := by exact_mod_cast hAC
  have hNC' : (N : ℝ≥0∞) ≤ C := by exact_mod_cast hNC
  have hDC' : (D : ℝ≥0∞) ≤ C := by exact_mod_cast hDC
  have hAAC' : (AA : ℝ≥0∞) ≤ C := by exact_mod_cast hAAC
  have hR₁C' : (R₁ : ℝ≥0∞) ≤ C := by exact_mod_cast hR₁C
  have hR₂C' : (R₂ : ℝ≥0∞) ≤ C := by exact_mod_cast hR₂C
  refine ⟨C, zero_lt_one.trans_le h1C, ?_⟩
  intro c R _ γ hL e 𝕜 _ g
  let μb : Measure (Space m) := volume.restrict (Metric.ball c R)
  let ν := graphMeasure e γ (Metric.ball c R)
  let u := g ∘ graphMap e γ
  have hmass := graph_lintegral_comparison Metric.isOpen_ball hL e (fun z => ‖g z‖ₑ ^ p.toReal)
  change lpMass μb p u ≤ lpMass ν p g ∧
    lpMass ν p g ≤ (K : ℝ≥0∞) ^ m * lpMass μb p u at hmass
  have hnorm := graph_eLpNorm_comparison Metric.isOpen_ball hL e p g
  have hN : ((K : ℝ≥0∞) ^ m) ^ (1 / p).toReal = (N : ℝ≥0∞) := by
    simp only [N, A, ENNReal.coe_rpow_of_nonneg _ hr, ENNReal.coe_pow,
      ENNReal.toReal_div, ENNReal.toReal_one, r]
  change eLpNorm u p μb ≤ eLpNorm g p ν ∧
    eLpNorm g p ν ≤ ((K : ℝ≥0∞) ^ m) ^ (1 / p).toReal * eLpNorm u p μb at hnorm
  rw [hN] at hnorm
  have henergy := graph_energy_comparison Metric.isOpen_ball hL e s p hq g
  have hD : (K : ℝ≥0∞) ^ q = (D : ℝ≥0∞) :=
    (ENNReal.coe_rpow_of_nonneg K hq).symm
  have hAA : (K : ℝ≥0∞) ^ m * (K : ℝ≥0∞) ^ m = (AA : ℝ≥0∞) := by
    simp only [AA, A, ENNReal.coe_mul, ENNReal.coe_pow]
  change metricEnergy m μb s p u ≤ (K : ℝ≥0∞) ^ q * metricEnergy m ν s p g ∧
    metricEnergy m ν s p g ≤ ((K : ℝ≥0∞) ^ m * (K : ℝ≥0∞) ^ m) *
      metricEnergy m μb s p u at henergy
  rw [hD, hAA] at henergy
  have hsemi₁ := root_le_mul_root D r hr henergy.1
  have hsemi₂ := root_le_mul_root AA r hr henergy.2
  change metricSeminorm m μb s p u ≤ (R₁ : ℝ≥0∞) * metricSeminorm m ν s p g at hsemi₁
  change metricSeminorm m ν s p g ≤ (R₂ : ℝ≥0∞) * metricSeminorm m μb s p u at hsemi₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, graph_memLp_iff Metric.isOpen_ball hL e p g⟩
  · exact hmass.1.trans (by simpa only [one_mul] using mul_le_mul' h1C' (le_refl (lpMass ν p g)))
  · exact hmass.2.trans (mul_le_mul' (by simpa only [A, ENNReal.coe_pow] using hAC') le_rfl)
  · exact hnorm.1.trans (by simpa only [one_mul] using mul_le_mul' h1C' (le_refl (eLpNorm g p ν)))
  · exact hnorm.2.trans (mul_le_mul' hNC' le_rfl)
  · exact henergy.1.trans (mul_le_mul' hDC' le_rfl)
  · exact henergy.2.trans (mul_le_mul' hAAC' le_rfl)
  · exact hsemi₁.trans (mul_le_mul' hR₁C' le_rfl)
  · exact hsemi₂.trans (mul_le_mul' hR₂C' le_rfl)

end P102.Trace.GraphFractionalTransport

/- Mathlib proof attribution
Adapted portion near line 143:
The layer-sum argument for change of density, adapted to the graph gauge.

Upstream: Mathlib/Probability/Kernel/WithDensity.lean (around line 196)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
