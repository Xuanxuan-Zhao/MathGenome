import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MultiplierKernelsAndRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MultiplierTranspose

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u
namespace ExpandedFA.Multiplication
open FunctionSpaces Unbounded FunctionSpaces.ScalarLpIntegralPairingSpec

/-- Kernel membership is the raw product equation, with no extra domain assumption. -/
theorem mem_multiplier_kernel_iff {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    (μ : Measure Ω) (r : ℝ≥0∞) (a : Ω → 𝕜) (f : Lp 𝕜 r μ) :
    f ∈ (maximalMultiplier μ r a).ker ↔ ∀ᵐ x ∂μ, a x * f x = 0 := by
  have hgraph : f ∈ (maximalMultiplier μ r a).ker ↔
      (f, 0) ∈ (maximalMultiplier μ r a).graph := by
    rw [LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨g, rfl, hg⟩; exact ⟨g, rfl, hg⟩
    · rintro ⟨g, rfl, hg⟩; exact ⟨g, rfl, hg⟩
  rw [hgraph, mem_maximalMultiplier_graph_iff]
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_zero 𝕜 r μ] with x hx hz
    exact hx.symm.trans hz
  · intro h
    filter_upwards [h, Lp.coeFn_zero 𝕜 r μ] with x hx hz
    exact hz.trans hx.symm

theorem multiplier_kernel : MultiplierKernelsAndRangeSpec.Kernel := by
  intro Ω 𝕜 _ _ μ r a
  ext f
  rw [mem_multiplier_kernel_iff]
  change (∀ᵐ x ∂μ, a x * f x = 0) ↔ ∀ᵐ x ∂μ, x ∉ zeroSet a → f x = 0
  constructor
  · intro h
    exact h.mono fun x hx ha => (mul_eq_zero.mp hx).resolve_left ha
  · intro h
    exact h.mono fun x hx => by
      by_cases ha : a x = 0
      · simp [ha]
      · simp [hx ha]

/-- Annihilator of a supported Lp space, under the fixed bilinear pairing. -/
theorem supportedLp_annihilator {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω]
    [RCLike 𝕜] (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp1 : 1 < p) (hp : p ≠ ∞)
    (E : Set Ω) (hE : MeasurableSet E) (g : Lp 𝕜 q μ) :
    (∀ f ∈ supportedLp μ p E, IntegralPairingValue μ p q g f = 0) ↔
      g ∈ supportedLp μ q Eᶜ := by
  constructor
  · intro h
    let hg := (Lp.memLp g).indicator hE.nullMeasurableSet
    have hzero : (hg.toLp _ : Ω → 𝕜) =ᵐ[μ] (0 : Lp 𝕜 q μ) := by
      apply (lp_density_ae_unique μ p q hp (Or.inr hp1) _ _).mp
      intro f
      let hf := (Lp.memLp f).indicator hE.nullMeasurableSet
      have hfs : hf.toLp _ ∈ supportedLp μ p E := by
        filter_upwards [hf.coeFn_toLp] with x hx hnot
        simp [hx, hnot]
      calc
        (∫ x, f x * hg.toLp _ x ∂μ) = ∫ x, hf.toLp _ x * g x ∂μ := by
          apply integral_congr_ae
          filter_upwards [hg.coeFn_toLp, hf.coeFn_toLp] with x hx hy
          rw [hx, hy]
          by_cases hxE : x ∈ E <;> simp [hxE]
        _ = 0 := by rw [← (lp_pairing_integral μ p q g (hf.toLp _)).2]; exact h _ hfs
        _ = ∫ x, f x * (0 : Lp 𝕜 q μ) x ∂μ := by
          symm
          convert integral_zero Ω 𝕜 using 1
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_zero 𝕜 q μ] with x hx
          change (0 : Lp 𝕜 q μ) x = (0 : 𝕜) at hx
          rw [hx, mul_zero]
    filter_upwards [hg.coeFn_toLp, hzero, Lp.coeFn_zero 𝕜 q μ] with x hx hy hz hnot
    have hxE : x ∈ E := by simpa only [Set.mem_compl_iff, not_not] using hnot
    change (0 : Lp 𝕜 q μ) x = (0 : 𝕜) at hz
    rw [hx, hz, Set.indicator_of_mem hxE] at hy
    exact hy
  · intro hg f hf
    rw [(lp_pairing_integral μ p q g f).2]
    apply integral_eq_zero_of_ae
    filter_upwards [hf, hg] with x hfx hgx
    by_cases hx : x ∈ E
    · simp [hgx (by simpa using hx)]
    · simp [hfx hx]

theorem multiplier_kernel_annihilator : MultiplierKernelsAndRangeSpec.KernelAnnihilator.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha
  rw [multiplier_kernel μ p a]
  ext g
  exact supportedLp_annihilator μ p q hp1 hp (zeroSet a) (ha (measurableSet_singleton 0)) g

/-- The actual Banach transpose kernel, transported by the dual identification. -/
theorem mem_multiplier_transpose_kernel_iff {Ω : Type u} {𝕜 : Type}
    [MeasurableSpace Ω] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp1 : 1 < p) (hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a) (g : Lp 𝕜 q μ) :
    IntegralPairingValue μ p q g ∈ (banachAdjoint (maximalMultiplier μ p a)).ker ↔
      g ∈ supportedLp μ q (zeroSet a) := by
  have hzero : IntegralPairingValue (𝕜 := 𝕜) μ p q 0 = 0 := map_zero _
  have hgraph : IntegralPairingValue μ p q g ∈
      (banachAdjoint (maximalMultiplier μ p a)).ker ↔
      (IntegralPairingValue μ p q g, IntegralPairingValue μ p q 0) ∈
        (banachAdjoint (maximalMultiplier μ p a)).graph := by
    rw [hzero, LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨v, hv, hval⟩; exact ⟨v, hv.symm, hval⟩
    · rintro ⟨v, hv, hval⟩; exact ⟨v, hv.symm, hval⟩
  rw [hgraph, multiplier_banach_graph μ p q hp1 hp a ha,
    mem_maximalMultiplier_graph_iff]
  rw [← multiplier_kernel μ q a, mem_multiplier_kernel_iff]
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_zero 𝕜 q μ] with x hx hz
    exact hx.symm.trans hz
  · intro h
    filter_upwards [h, Lp.coeFn_zero 𝕜 q μ] with x hx hz
    exact hz.trans hx.symm

theorem multiplier_transpose_kernel : MultiplierKernelsAndRangeSpec.TransposeKernel.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha
  ext g
  exact mem_multiplier_transpose_kernel_iff μ p q hp1 hp a ha g

theorem multiplier_transpose_kernel_preannihilator :
    MultiplierKernelsAndRangeSpec.TransposeKernelPreannihilator.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha
  have hq : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp (lt_top_iff_ne_top.mpr hp)
  ext f
  change (∀ g : Lp 𝕜 q μ, _ → _) ↔ _
  simp_rw [mem_multiplier_transpose_kernel_iff μ p q hp1 hp a ha]
  have hcomm (g : Lp 𝕜 q μ) : IntegralPairingValue μ p q g f = IntegralPairingValue μ q p f g := by
    rw [(lp_pairing_integral μ p q g f).2, (lp_pairing_integral μ q p f g).2]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  simp_rw [hcomm]
  exact supportedLp_annihilator μ q p hq1 hq (zeroSet a) (ha (measurableSet_singleton 0)) f

theorem multiplier_range_closure : MultiplierKernelsAndRangeSpec.RangeClosure.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha
  rw [banachAdjoint_range_closure _ (maximalLpMultiplier_denselyDefined μ p hp a ha)]
  rw [← multiplier_transpose_kernel_preannihilator μ p q hp1 hp a ha]
  ext f
  constructor
  · intro h g hg; exact h _ hg
  · intro h L hL
    obtain ⟨g, rfl⟩ := (lp_pairing_arbitrary_isometric_bijective (𝕜 := 𝕜) μ p q hp1 hp).2.2 L
    exact h g hL

/-- Solve the multiplier equation by the masked quotient. -/
theorem multiplier_exact_range : MultiplierKernelsAndRangeSpec.ExactRange := by
  intro Ω 𝕜 _ _ _ _ μ p a ha
  ext h
  constructor
  · rintro ⟨f, rfl⟩
    have heq := maximalLpMultiplier_apply μ p a f
    constructor
    · filter_upwards [heq] with x hx hz
      simp only [zeroSet, Set.mem_ofPred_eq] at hz
      change (maximalMultiplier μ p a f) x = 0
      rw [hx, hz, zero_mul]
    · have hZ : MeasurableSet (zeroSet a)ᶜ := (ha (measurableSet_singleton 0)).compl
      apply ((Lp.memLp (f : Lp 𝕜 p μ)).indicator hZ.nullMeasurableSet).ae_eq
      filter_upwards [heq] with x hx
      by_cases hz : a x = 0
      · simp [zeroSet, hz]
      · simp [zeroSet, hz, hx, mul_div_cancel_left₀ _ hz]
  · rintro ⟨hzero, hquot⟩
    let f : Lp 𝕜 p μ := hquot.toLp _
    have heq : (h : Ω → 𝕜) =ᵐ[μ] fun x => a x * f x := by
      filter_upwards [hzero, hquot.coeFn_toLp] with x hx hf
      rw [hf]
      by_cases hz : a x = 0
      · simp [zeroSet, hz, hx hz]
      · simp [zeroSet, hz, mul_div_cancel₀ _ hz]
    exact LinearPMap.mem_range_iff.mpr
      ⟨f, (mem_maximalMultiplier_graph_iff μ p a f h).mpr heq⟩

end ExpandedFA.Multiplication
