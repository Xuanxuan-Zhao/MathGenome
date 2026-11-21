import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MultiplierTranspose
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MaximalLpMultiplier
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate
universe u
namespace ExpandedFA.Multiplication
open FunctionSpaces Unbounded
open FunctionSpaces.ScalarLpIntegralPairingSpec

section Localization
variable {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

/-- Multiplication localized to a measurable set on which the symbol is bounded. -/
theorem memLp_indicator_mul (r : ℝ≥0∞) (a : Ω → 𝕜) (ha : Measurable a)
    (E : Set Ω) (hE : MeasurableSet E) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ E, ‖a x‖ ≤ C) (f : Lp 𝕜 r μ) :
    MemLp (E.indicator (fun x => a x * f x)) r μ := by
  apply (Lp.memLp f).of_le_mul (c := C)
    ((ha.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).indicator hE)
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem hx]
    change ‖a x * f x‖ ≤ C * ‖f x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact mul_nonneg hC (norm_nonneg _)

/-- Integral tests on the maximal domain determine the full raw product a*g.
Only bounded-symbol truncations enter the duality uniqueness theorem. -/
theorem multiplier_integral_tests_iff (hp1 : 1 < p) (hp : p ≠ ∞)
    (a : Ω → 𝕜) (ha : Measurable a) (g h : Lp 𝕜 q μ) :
    (∀ f : (maximalMultiplier μ p a).domain,
      (∫ x, (maximalMultiplier μ p a f) x * g x ∂μ) =
        ∫ x, (f : Lp 𝕜 p μ) x * h x ∂μ) ↔
    (h : Ω → 𝕜) =ᵐ[μ] fun x => a x * g x := by
  constructor
  · intro htest
    let E : ℕ → Set Ω := fun n => {x | ‖a x‖ ≤ (n : ℝ)}
    have hE (n) : MeasurableSet (E n) := ha.norm measurableSet_Iic
    have hlocal (n) : ∀ᵐ x ∂μ, x ∈ E n → h x = a x * g x := by
      let hu := (Lp.memLp h).indicator (hE n).nullMeasurableSet
      let hv := memLp_indicator_mul μ q a ha (E n) (hE n) n (Nat.cast_nonneg n)
        (fun _ hx => hx) g
      have heq : (hu.toLp _ : Ω → 𝕜) =ᵐ[μ] (hv.toLp _ : Ω → 𝕜) := by
        apply (lp_density_ae_unique μ p q hp (Or.inr hp1) _ _).mp
        intro f
        let hf := (Lp.memLp f).indicator (hE n).nullMeasurableSet
        let fn : Lp 𝕜 p μ := hf.toLp _
        have hfn : fn ∈ (maximalMultiplier μ p a).domain := by
          apply (memLp_indicator_mul μ p a ha (E n) (hE n) n
            (Nat.cast_nonneg n) (fun _ hx => hx) f).ae_eq
          filter_upwards [hf.coeFn_toLp] with x hx
          change (E n).indicator (fun x => a x * f x) x = a x * fn x
          rw [hx]
          by_cases hxE : x ∈ E n <;> simp [hxE]
        calc
          (∫ x, f x * hu.toLp _ x ∂μ) = ∫ x, fn x * h x ∂μ := by
            apply integral_congr_ae
            filter_upwards [hu.coeFn_toLp, hf.coeFn_toLp] with x hx hy
            rw [hx, hy]
            by_cases hxE : x ∈ E n <;> simp [hxE]
          _ = ∫ x, (maximalMultiplier μ p a ⟨fn, hfn⟩) x * g x ∂μ :=
            (htest ⟨fn, hfn⟩).symm
          _ = ∫ x, f x * hv.toLp _ x ∂μ := by
            apply integral_congr_ae
            filter_upwards [maximalLpMultiplier_apply μ p a ⟨fn, hfn⟩,
              hf.coeFn_toLp, hv.coeFn_toLp] with x hx hy hz
            rw [hx, hy, hz]
            by_cases hxE : x ∈ E n <;> simp [hxE, mul_left_comm, mul_comm, mul_assoc]
      filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp, heq] with x hx hy hz hxE
      simpa only [hx, hy, Set.indicator_of_mem hxE] using hz
    have hall := ae_all_iff.mpr hlocal
    filter_upwards [hall] with x hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖a x‖
    exact hx n hn
  · intro heq f
    apply integral_congr_ae
    filter_upwards [heq, maximalLpMultiplier_apply μ p a f] with x hx hy
    rw [hx, hy, mul_assoc, mul_left_comm (a x)]

end Localization

/-- Under the bilinear isometric dual identification the entire transpose graph
is precisely the graph of multiplication by the same symbol. -/
theorem multiplier_banach_graph : MultiplierTransposeSpec.BanachGraph.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha g h
  have hd := maximalLpMultiplier_denselyDefined μ p hp a ha
  rw [banachAdjoint_graph (maximalMultiplier μ p a) hd,
    mem_maximalMultiplier_graph_iff]
  change (∀ f : (maximalMultiplier μ p a).domain,
    IntegralPairingValue μ p q h (f : Lp 𝕜 p μ) =
      IntegralPairingValue μ p q g (maximalMultiplier μ p a f)) ↔ _
  simp_rw [(lp_pairing_integral μ p q _ _).2]
  exact (forall_congr' fun f => eq_comm).trans
    (multiplier_integral_tests_iff μ p q hp1 hp a ha g h)

theorem multiplier_banach_domain : MultiplierTransposeSpec.BanachDomain.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha g
  rw [mem_banachAdjoint_domain_iff]
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨h, hh⟩ :=
      (lp_pairing_arbitrary_isometric_bijective μ p q hp1 hp).2.2 L
    have hgraph : (IntegralPairingValue μ p q g, IntegralPairingValue μ p q h) ∈
        (banachAdjoint (maximalMultiplier μ p a)).graph := by
      rw [banachAdjoint_graph _ (maximalLpMultiplier_denselyDefined μ p hp a ha)]
      intro f
      exact (congrArg (fun L => L (f : Lp 𝕜 p μ)) hh).trans (hL f)
    have hmul := (multiplier_banach_graph μ p q hp1 hp a ha g h).mp hgraph
    obtain ⟨f, hf, _⟩ := (maximalMultiplier μ q a).mem_graph_iff.mp hmul
    have hf' : (f : Lp 𝕜 q μ) = g := hf
    rw [← hf']
    exact f.2
  · intro hg
    refine ⟨IntegralPairingValue μ p q (hg.toLp _), ?_⟩
    intro f
    rw [(lp_pairing_integral μ p q _ _).2, (lp_pairing_integral μ p q _ _).2]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, maximalLpMultiplier_apply μ p a f] with x hx hy
    rw [hx, hy]
    exact (mul_left_comm ((f : Lp 𝕜 p μ) x) (a x) (g x)).trans
      (mul_assoc (a x) ((f : Lp 𝕜 p μ) x) (g x)).symm

theorem multiplier_banach_apply : MultiplierTransposeSpec.BanachApply.{u} := by
  intro Ω 𝕜 _ _ _ _ μ p q _ _ _ hp1 hp a ha g hg
  have hgraph := (multiplier_banach_graph μ p q hp1 hp a ha
    (g : Lp 𝕜 q μ) (maximalMultiplier μ q a g)).mpr
    ((maximalMultiplier μ q a).mem_graph g)
  obtain ⟨v, hv, heq⟩ := (banachAdjoint (maximalMultiplier μ p a)).mem_graph_iff.mp hgraph
  have hv' : v = ⟨IntegralPairingValue μ p q (g : Lp 𝕜 q μ), hg⟩ := Subtype.ext hv
  rw [hv'] at heq
  exact heq


/-- The L² inner product as the bilinear integral paired with a conjugated class. -/
theorem l2_inner_eq_integral_star {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (g f : Lp ℂ 2 μ) :
    inner ℂ g f = ∫ x, f x * (star g : Lp ℂ 2 μ) x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  simp only [RCLike.inner_apply, hx, Pi.star_apply, starRingEnd_apply]

/-- The Hilbert adjoint identity is equivalent to multiplication by the conjugate
symbol, including the converse maximal-domain assertion. -/
theorem multiplier_hilbert_tests_iff {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (a : Ω → ℂ) (ha : Measurable a) (g h : Lp ℂ 2 μ) :
    (∀ f : (maximalMultiplier μ 2 a).domain,
      inner ℂ (maximalMultiplier μ 2 a f) g = inner ℂ (f : Lp ℂ 2 μ) h) ↔
    (h : Ω → ℂ) =ᵐ[μ] fun x => conj (a x) * g x := by
  constructor
  · intro htest
    have hstar := (multiplier_integral_tests_iff μ 2 2 (by norm_num) (by norm_num)
      a ha (star g) (star h)).mp (by
        intro f
        rw [← l2_inner_eq_integral_star, ← l2_inner_eq_integral_star]
        calc
          inner ℂ g (maximalMultiplier μ 2 a f) =
              conj (inner ℂ (maximalMultiplier μ 2 a f) g) :=
            (inner_conj_symm _ _).symm
          _ = conj (inner ℂ (f : Lp ℂ 2 μ) h) := congrArg conj (htest f)
          _ = inner ℂ h (f : Lp ℂ 2 μ) := inner_conj_symm _ _)
    filter_upwards [hstar, Lp.coeFn_star h, Lp.coeFn_star g] with x hx hh hg
    rw [hh, hg] at hx
    have hc := congrArg star hx
    simpa only [Pi.star_apply, star_mul, star_star, starRingEnd_apply, mul_comm] using hc
  · intro heq f
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq, maximalLpMultiplier_apply μ 2 a f] with x hx hy
    simp only [RCLike.inner_apply, hx, hy, map_mul]
    ac_rfl

theorem multiplier_hilbert_adjoint : MultiplierTransposeSpec.HilbertAdjoint.{u} := by
  intro Ω _ μ a ha
  have hd := maximalLpMultiplier_denselyDefined μ 2 (by norm_num) a ha
  apply LinearPMap.eq_of_eq_graph
  ext z
  rcases z with ⟨g, h⟩
  change (g, h) ∈ (hilbertAdjoint (maximalMultiplier μ 2 a)).graph ↔ _
  rw [mem_hilbertAdjoint_graph_iff (maximalMultiplier μ 2 a) hd,
    mem_maximalMultiplier_graph_iff]
  exact multiplier_hilbert_tests_iff μ a ha g h

theorem multiplier_real_selfAdjoint : MultiplierTransposeSpec.RealSelfAdjoint.{u} := by
  intro Ω _ μ a ha hre
  apply LinearPMap.isSelfAdjoint_def.mpr
  change HilbertAdjointSpec.adjointValue (maximalMultiplier μ 2 a) = _
  rw [multiplier_hilbert_adjoint μ a ha]
  apply maximalLpMultiplier_congr μ 2
  exact hre.mono fun x hx => Complex.conj_eq_iff_im.mpr hx

end ExpandedFA.Multiplication
