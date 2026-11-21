import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ConstrainedLp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.LocallyConvex.HahnBanach

open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace ExpandedFA.PartIV.ConstrainedLp
open ExpandedFA.FunctionSpaces

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (p q : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

-- The weighted L1 norm supplies a continuous seminorm for Hahn–Banach.
def weightedSeminorm (k : Lp ℝ q μ) : Seminorm ℝ (Lp ℝ p μ) :=
  (normSeminorm ℝ (Lp ℝ 1 μ)).comp
    (((ContinuousLinearMap.mul ℝ ℝ).holderL μ p q 1).flip k).toLinearMap

lemma weightedSeminorm_eq (k : Lp ℝ q μ) (hk : ∀ᵐ x ∂μ, 0 ≤ k x)
    (u : Lp ℝ p μ) :
    weightedSeminorm μ p q k u = ∫ x, k x * |u x| ∂μ := by
  change ‖(ContinuousLinearMap.mul ℝ ℝ).holder 1 u k‖ = _
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) u k, hk] with x hx hxk
  simp only [ContinuousLinearMap.mul_apply', Real.norm_eq_abs] at hx ⊢
  rw [hx, abs_mul, abs_of_nonneg hxk, mul_comm]

lemma continuous_weightedSeminorm (k : Lp ℝ q μ) :
    Continuous (weightedSeminorm μ p q k) :=
  (((ContinuousLinearMap.mul ℝ ℝ).holderL μ p q 1).flip k).continuous.norm



omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
lemma box_bound (k g : Lp ℝ q μ) (u : Lp ℝ p μ)
    (hg : ∀ᵐ x ∂μ, |g x| ≤ k x) :
    (∫ x, u x * g x ∂μ) ≤ ∫ x, k x * |u x| ∂μ := by
  apply integral_mono_ae ((Lp.memLp u).integrable_mul (Lp.memLp g))
    ((Lp.memLp k).integrable_mul (by simpa only [Real.norm_eq_abs] using (Lp.memLp u).norm))
  filter_upwards [hg] with x hx
  calc
    u x * g x ≤ |u x * g x| := le_abs_self _
    _ = |u x| * |g x| := abs_mul _ _
    _ ≤ |u x| * k x := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = k x * |u x| := mul_comm _ _

theorem interval_support : Spec.IntervalSupport.{u} := by
  intro Ω _ μ p q _ _ _ _ _ k hk u
  refine ⟨fun g hg => box_bound μ p q k g u hg, ?_⟩
  let s : Set Ω := {x | 0 ≤ u x}
  have hs : MeasurableSet s := measurableSet_le measurable_const (Lp.stronglyMeasurable u).measurable
  let g : Ω → ℝ := s.piecewise k (fun x => -k x)
  have hgm : AEStronglyMeasurable g μ :=
    ((Lp.stronglyMeasurable k).piecewise hs (Lp.stronglyMeasurable k).neg).aestronglyMeasurable
  have hgn (x : Ω) : |g x| = |k x| := by
    simp only [g, Set.piecewise]
    split_ifs <;> simp
  have hg : MemLp g q μ := (Lp.memLp k).of_le hgm (by
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, hgn]
    exact le_rfl)
  refine ⟨hg.toLp g, ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp, hk] with x hx hxk
    rw [hx, hgn, abs_of_nonneg hxk]
  · apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
    simp only [g, s, Set.piecewise, Set.mem_ofPred_eq]
    split_ifs with hu
    · rw [abs_of_nonneg hu, mul_comm]
    · rw [abs_of_neg (lt_of_not_ge hu)]
      ring

lemma vanishes_on_kernel_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (J H : E →ₗ[ℝ] ℝ) :
    (∀ u, J u = 0 → H u = 0) ↔ ∃ c : ℝ, H = c • J := by
  constructor
  · intro h
    by_cases hJ : ∀ u, J u = 0
    · refine ⟨0, ?_⟩
      ext u
      simpa using h u (hJ u)
    · push Not at hJ
      obtain ⟨v, hv⟩ := hJ
      refine ⟨H v / J v, ?_⟩
      ext u
      have hz : J (u - (J u / J v) • v) = 0 := by
        simp [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
      have hh := h _ hz
      simp only [map_sub, map_smul, smul_eq_mul] at hh ⊢
      have : H u = (J u / J v) * H v := sub_eq_zero.mp hh
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [this]
      ring
  · rintro ⟨c, rfl⟩ u hu
    simp [hu]

theorem kernel_annihilator : Spec.KernelAnnihilator.{u} := by
  intro Ω _ μ p q _ _ _ hp hpfin j h
  let B := lpIntegralPairing (𝕜 := ℝ) μ p q
  have hi := (lp_pairing_arbitrary_isometric_bijective (𝕜 := ℝ) μ p q hp hpfin).2.1
  have hv := vanishes_on_kernel_iff (B j).toLinearMap (B h).toLinearMap
  constructor
  · intro hh
    obtain ⟨c, hc⟩ := hv.mp (by
      intro u hu
      exact ((lp_pairing_integral μ p q h u).2).trans
        (hh u (((lp_pairing_integral μ p q j u).2).symm.trans hu)))
    refine ⟨c, hi ?_⟩
    rw [map_smul]
    ext u
    exact congrArg (fun L : Lp ℝ p μ →ₗ[ℝ] ℝ => L u) hc
  · rintro ⟨c, rfl⟩ u hu
    rw [← (lp_pairing_integral μ p q (c • j) u).2, map_smul]
    change c * (B j) u = 0
    rw [show (B j) u = 0 from ((lp_pairing_integral μ p q j u).2).trans hu]
    simp



omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Positive-part power tests detect order on ordinary Lq on any measure.
The test is supported where the density is positive, so no semifiniteness
assumption is necessary. -/
lemma nonpos_of_nonpos_tests (hp : 1 < p) (hpfin : p ≠ ∞)
    (h : Ω → ℝ) (hh : MemLp h q μ)
    (ht : ∀ u : Lp ℝ p μ, (∀ᵐ x ∂μ, 0 ≤ u x) →
      (∫ x, u x * h x ∂μ) ≤ 0) : ∀ᵐ x ∂μ, h x ≤ 0 := by
  have hqfin : q ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp.ne'
  have hq1 : q ≠ 1 := fun hq => hpfin ((ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mpr hq)
  obtain ⟨hr, he⟩ := D11.Ch20.PairingNormFiniteQ.conjugate_power_exponent p q hqfin hq1
  let a : Ω → ℝ := fun x => max (h x) 0
  have ha : MemLp a q μ := hh.pos_part
  let v : Ω → ℝ := fun x => ‖a x‖ ^ (q.toReal - 1)
  have hvm : AEStronglyMeasurable v μ :=
    (Real.continuous_rpow_const hr.le).comp_aestronglyMeasurable ha.aestronglyMeasurable.norm
  have hv : MemLp v p μ := by
    rw [memLp_iff, show eLpNorm v p μ = eLpNorm a q μ ^ (q.toReal - 1) by
      change eLpNorm (fun x => ‖a x‖ ^ (q.toReal - 1)) p μ = _
      rw [eLpNorm_norm_rpow _ ha.aestronglyMeasurable hr, he]]
    exact ENNReal.rpow_lt_top_of_nonneg hr.le ha.eLpNorm_ne_top
  have hv0 (x : Ω) : 0 ≤ v x := Real.rpow_nonneg (norm_nonneg _) _
  have hit : (∫ x, v x * h x ∂μ) ≤ 0 := by
    have ht' := ht (hv.toLp v) (by
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx]
      exact hv0 x)
    have heq : (∫ x, (hv.toLp v) x * h x ∂μ) = ∫ x, v x * h x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx]
    exact heq ▸ ht'
  have hn : ∀ x, 0 ≤ v x * h x := by
    intro x
    by_cases hx : h x ≤ 0
    · simp [v, a, max_eq_right hx, Real.zero_rpow hr.ne']
    · exact mul_nonneg (hv0 x) (le_of_not_ge hx)
  have hz : ∀ᵐ x ∂μ, v x * h x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hn)
      (hv.integrable_mul hh)).mp (le_antisymm hit (integral_nonneg hn))
  filter_upwards [hz] with x hx
  by_contra hn
  have hpos : 0 < h x := lt_of_not_ge hn
  have hvpos : 0 < v x := by
    dsimp [v, a]
    rw [max_eq_left hpos.le, abs_of_pos hpos]
    exact Real.rpow_pos_of_pos hpos _
  exact (ne_of_gt (mul_pos hvpos hpos)) hx



lemma box_of_dominated (hp : 1 < p) (hpfin : p ≠ ∞)
    (g k : Lp ℝ q μ) (hk : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hd : ∀ u : Lp ℝ p μ,
      |lpIntegralPairing μ p q g u| ≤ weightedSeminorm μ p q k u) :
    ∀ᵐ x ∂μ, |g x| ≤ k x := by
  have hweight (u : Lp ℝ p μ) (hu : ∀ᵐ x ∂μ, 0 ≤ u x) :
      weightedSeminorm μ p q k u = ∫ x, u x * k x ∂μ := by
    rw [weightedSeminorm_eq μ p q k hk]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [abs_of_nonneg hx, mul_comm]
  have hupper : ∀ᵐ x ∂μ, g x - k x ≤ 0 := by
    apply nonpos_of_nonpos_tests μ p q hp hpfin _ ((Lp.memLp g).sub (Lp.memLp k))
    intro u hu
    have hd' := (le_abs_self _).trans (hd u)
    rw [hweight u hu] at hd'
    have hgI := (Lp.memLp u).integrable_mul (Lp.memLp g)
    have hkI := (Lp.memLp u).integrable_mul (Lp.memLp k)
    change (∫ x, u x * (g x - k x) ∂μ) ≤ 0
    simp_rw [mul_sub]
    rw [integral_sub (f := fun x => u x * g x) (g := fun x => u x * k x) hgI hkI]
    exact sub_nonpos.mpr (((lp_pairing_integral μ p q g u).2).symm.trans_le hd')
  have hlower : ∀ᵐ x ∂μ, -g x - k x ≤ 0 := by
    apply nonpos_of_nonpos_tests μ p q hp hpfin _ ((Lp.memLp g).neg.sub (Lp.memLp k))
    intro u hu
    have hd' := (neg_le_abs _).trans (hd u)
    rw [hweight u hu] at hd'
    have hgI := (Lp.memLp u).integrable_mul (Lp.memLp g)
    have hkI := (Lp.memLp u).integrable_mul (Lp.memLp k)
    change (∫ x, u x * (-g x - k x) ∂μ) ≤ 0
    simp_rw [mul_sub, mul_neg]
    rw [integral_sub (f := fun x => -(u x * g x)) (g := fun x => u x * k x) hgI.neg hkI,
      integral_neg]
    have heq := (lp_pairing_integral μ p q g u).2
    exact sub_nonpos.mpr ((congrArg Neg.neg heq).symm.trans_le hd')
  filter_upwards [hupper, hlower] with x hx hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩



/-- The constrained support inequality, including the zero constraint.
A dominated extension supplies g; the remaining functional is a multiple of j.
Only interior scalar Lp duality is used, with no hypothesis on the measure. -/
theorem constrained_equivalence : Spec.ConstrainedEquivalence.{u} := by
  intro Ω _ μ p q _ _ _ hp hpfin f j k hk
  let B := lpIntegralPairing (𝕜 := ℝ) μ p q
  have pair (g : Lp ℝ q μ) (u : Lp ℝ p μ) :
      B g u = ∫ x, u x * g x ∂μ := (lp_pairing_integral μ p q g u).2
  constructor
  · intro h
    let M : Submodule ℝ (Lp ℝ p μ) := (B j).ker
    let F : M →ₗ[ℝ] ℝ := (B f).toLinearMap.comp M.subtype
    have hF (u : M) : F u ≤ weightedSeminorm μ p q k u := by
      have hu : (∫ x, u.val x * j x ∂μ) = 0 := (pair j u).symm.trans u.property
      exact (pair f u).trans_le ((h u hu).trans_eq (weightedSeminorm_eq μ p q k hk u).symm)
    obtain ⟨G, hG, hbd⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm_real
      M F (continuous_weightedSeminorm μ p q k) hF
    obtain ⟨g, hg, _⟩ := lp_duality_arbitrary_measure (𝕜 := ℝ) μ p q hp hpfin G
    have hBg : B g = G := by
      ext u
      exact (pair g u).trans ((hg.1 u).2.symm)
    have hgbox : ∀ᵐ x ∂μ, |g x| ≤ k x :=
      box_of_dominated μ p q hp hpfin g k hk (fun u => by
        change |B g u| ≤ _
        rw [hBg]
        exact hbd u)
    have hker : ∀ u : Lp ℝ p μ, (∫ x, u x * j x ∂μ) = 0 →
        (∫ x, u x * (f - g) x ∂μ) = 0 := by
      intro u hu
      have hum : u ∈ M := (pair j u).trans hu
      have hext : G u = B f u := hG ⟨u, hum⟩
      calc
        (∫ x, u x * (f - g) x ∂μ) = B (f - g) u := (pair (f - g) u).symm
        _ = B f u - B g u := by rw [map_sub, _root_.sub_apply]
        _ = 0 := by rw [hBg, hext, sub_self]
    obtain ⟨c, hc⟩ := (kernel_annihilator μ p q hp hpfin j (f - g)).mp hker
    exact ⟨c, g, sub_eq_iff_eq_add.mp hc, hgbox⟩
  · rintro ⟨c, g, rfl, hg⟩ u hu
    have hju : B j u = 0 := (pair j u).trans hu
    calc
      (∫ x, u x * (c • j + g) x ∂μ) = B (c • j + g) u := (pair _ u).symm
      _ = c * B j u + B g u := by
        simp only [map_add, map_smul, _root_.add_apply,
          _root_.smul_apply, smul_eq_mul]
      _ = B g u := by rw [hju, mul_zero, zero_add]
      _ ≤ ∫ x, k x * |u x| ∂μ := (pair g u).trans_le (box_bound μ p q k g u hg)

end ExpandedFA.PartIV.ConstrainedLp
