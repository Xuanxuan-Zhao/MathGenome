import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.LpMultiplierSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.SemifiniteMultiplierBounds

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ExpandedFA.Multiplication
open Unbounded
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translating a maximal multiplier retains precisely its maximal domain. -/
theorem shifted_multiplier_domain (a : Ω → ℂ) (z : ℂ) :
    (maximalMultiplier μ p (fun x => z - a x)).domain =
      (maximalMultiplier μ p a).domain := by
  ext f
  change MemLp (fun x => (z - a x) * f x) p μ ↔ MemLp (fun x => a x * f x) p μ
  constructor <;> intro hf
  · convert ((Lp.memLp f).const_smul z).sub hf using 1
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · convert ((Lp.memLp f).const_smul z).sub hf using 1
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The translated operator is multiplication by z-a, including its domain. -/
theorem shifted_multiplier (a : Ω → ℂ) (z : ℂ) :
    OperatorDomainsSpec.shiftValue z (maximalMultiplier μ p a) =
      maximalMultiplier μ p (fun x => z - a x) := by
  apply LinearPMap.dExt
  · exact (shifted_multiplier_domain a z).symm
  · intro f g hfg
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (z • (f : Lp ℂ p μ)) (maximalMultiplier μ p a f),
      Lp.coeFn_smul z (f : Lp ℂ p μ), maximalLpMultiplier_apply μ p a f,
      maximalLpMultiplier_apply μ p (fun x => z - a x) g] with x hsub hsm ha hb
    change (z • (f : Lp ℂ p μ) - maximalMultiplier μ p a f) x = _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsm
    rw [hsub, hsm, ha, hb, ← hfg]
    ring

/-- Outside the essential range is exactly an a.e. positive separation. -/
theorem not_mem_essentialRange_iff (a : Ω → ℂ) (z : ℂ) :
    z ∉ multiplierEssentialRange μ a ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂μ, c ≤ ‖z - a x‖ := by
  classical
  change (¬ ∀ ε : ℝ, 0 < ε → 0 < μ {x | ‖a x - z‖ < ε}) ↔ _
  simp only [not_forall, not_lt]
  constructor
  · rintro ⟨c, hc0, hc⟩
    have hzero : μ {x | ‖a x - z‖ < c} = 0 := le_antisymm hc bot_le
    refine ⟨c, hc0, ?_⟩
    have h : ∀ᵐ x ∂μ, ¬ ‖a x - z‖ < c := ae_iff.mpr (by simpa only [not_not] using hzero)
    filter_upwards [h] with x hx
    simpa only [not_lt, norm_sub_rev] using hx
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c, hc, le_of_eq ?_⟩
    have h : ∀ᵐ x ∂μ, ¬ ‖a x - z‖ < c := by
      filter_upwards [hbound] with x hx
      simpa only [not_lt, norm_sub_rev] using hx
    simpa only [not_not] using ae_iff.mp h

/-- The essential range is closed without measure qualifications. -/
theorem multiplier_essentialRange_closed : LpMultiplierSpectrumSpec.EssentialRangeClosed := by
  intro Ω _ μ a
  apply isOpen_compl_iff.mp
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨c, hc, hb⟩ := (not_mem_essentialRange_iff a z).mp hz
  refine ⟨c / 2, by linarith, ?_⟩
  intro w hw
  apply (not_mem_essentialRange_iff a w).mpr
  refine ⟨c / 2, by linarith, ?_⟩
  have hw' : ‖z - w‖ < c / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
  filter_upwards [hb] with x hx
  have htri := norm_add_le (z - w) (w - a x)
  rw [sub_add_sub_cancel] at htri
  linarith

/-- Evaluation of the shifted multiplier on the shared underlying vector. -/
theorem shifted_multiplier_apply (a : Ω → ℂ) (z : ℂ)
    (f : (maximalMultiplier μ p a).domain)
    (g : (maximalMultiplier μ p (fun x => z - a x)).domain)
    (hfg : (f : Lp ℂ p μ) = g) :
    z • (f : Lp ℂ p μ) - maximalMultiplier μ p a f =
      maximalMultiplier μ p (fun x => z - a x) g :=
  (LinearPMap.dExt_iff.mp (shifted_multiplier a z)).2 hfg

/-- Resolvent existence is equivalent to surjectivity of the translated symbol.
The reverse implication uses the semifinite lower-bound theorem, which also
ensures injectivity and an ambient bounded inverse. -/
theorem resolvent_iff_shifted_surjective (hμ : Semifinite μ)
    (hp1 : 1 < p) (hp : p ≠ ∞) (a : Ω → ℂ) (ha : Measurable a) (z : ℂ) :
    Nonempty (ResolventInverse (maximalMultiplier μ p a) z) ↔
      Function.Surjective (maximalMultiplier μ p (fun x => z - a x)).toFun := by
  have hd := shifted_multiplier_domain (μ := μ) (p := p) a z
  constructor
  · rintro ⟨R⟩ y
    let g : (maximalMultiplier μ p (fun x => z - a x)).domain :=
      ⟨R.inverse y, by rw [hd]; exact R.mem_domain y⟩
    refine ⟨g, ?_⟩
    change maximalMultiplier μ p (fun x => z - a x) g = y
    rw [← shifted_multiplier_apply a z ⟨R.inverse y, R.mem_domain y⟩ g rfl]
    exact R.right_inverse y
  · intro hs
    obtain ⟨_, B, hrep, hB, hright, hleft⟩ :=
      semifinite_multiplier_bounded_inverse μ hμ p hp1 hp (fun x => z - a x)
        (measurable_const.sub ha) hs
    have hmem : ∀ y, B y ∈ (maximalMultiplier μ p a).domain := by
      intro y
      rw [← hd]
      exact hB y
    refine ⟨⟨B, hmem, ?_, ?_⟩⟩
    · intro y
      rw [shifted_multiplier_apply a z ⟨B y, hmem y⟩ ⟨B y, hB y⟩ rfl]
      exact hright y
    · intro f
      let g : (maximalMultiplier μ p (fun x => z - a x)).domain :=
        ⟨f, by rw [hd]; exact f.2⟩
      rw [shifted_multiplier_apply a z f g rfl]
      exact hleft g

theorem multiplier_spectrum : LpMultiplierSpectrumSpec.SpectrumFormula := by
  intro Ω _ μ hμ p _ hp1 hp a ha
  ext z
  change (¬ Nonempty (ResolventInverse (maximalMultiplier μ p a) z)) ↔ _
  rw [resolvent_iff_shifted_surjective hμ hp1 hp a ha z,
    semifinite_multiplier_surjective μ hμ p hp1 hp (fun x => z - a x)
      (measurable_const.sub ha), ← not_mem_essentialRange_iff a z]
  exact not_not

/-- Every resolvent inverse has the reciprocal symbol as its representative. -/
theorem multiplier_resolvent : LpMultiplierSpectrumSpec.ResolventFormula := by
  intro Ω _ μ hμ p _ hp1 hp a ha z hz
  have hsep := (not_mem_essentialRange_iff a z).mp hz
  have hs := (semifinite_multiplier_surjective μ hμ p hp1 hp (fun x => z - a x)
    (measurable_const.sub ha)).mpr hsep
  have hR := (resolvent_iff_shifted_surjective hμ hp1 hp a ha z).mpr hs
  obtain ⟨_, B, hBrep, hB, hright, hleft⟩ :=
    semifinite_multiplier_bounded_inverse μ hμ p hp1 hp (fun x => z - a x)
      (measurable_const.sub ha) hs
  have heq : OperatorDomainsSpec.resolventValue z (maximalMultiplier μ p a) = B := by
    let R : ResolventInverse (maximalMultiplier μ p a) z := hR.some
    have hresolve : OperatorDomainsSpec.resolventValue z (maximalMultiplier μ p a) =
        R.inverse := by simp [OperatorDomainsSpec.resolventValue, hR, R]
    rw [hresolve]
    apply ContinuousLinearMap.ext
    intro y
    have hg : R.inverse y ∈ (maximalMultiplier μ p (fun x => z - a x)).domain := by
      rw [shifted_multiplier_domain a z]; exact R.mem_domain y
    have h := hleft ⟨R.inverse y, hg⟩
    rw [← shifted_multiplier_apply a z ⟨R.inverse y, R.mem_domain y⟩
      ⟨R.inverse y, hg⟩ rfl, R.right_inverse y] at h
    exact h.symm
  rw [heq]
  refine ⟨?_, ?_⟩
  · intro f
    exact (hBrep f).trans (Eventually.of_forall fun x => by
      simp only [div_eq_mul_inv, mul_comm])
  · have hi := (reciprocal_memLp_top_iff (fun x => z - a x)
      (measurable_const.sub ha)).mpr
        ⟨hsep.choose, hsep.choose_spec.1, hsep.choose_spec.2.mono fun _ hx _ => hx⟩
    have hd := full_domain_of_memLp_top (p := p) (fun x => (z - a x)⁻¹)
      (measurable_const.sub ha).inv hi
    obtain ⟨T, hT, hnorm⟩ := semifinite_multiplier_norm μ hμ p hp1 hp
      (fun x => (z - a x)⁻¹) (measurable_const.sub ha).inv hd
    have hBT : B = T := by
      apply ContinuousLinearMap.ext
      intro f
      apply Lp.ext
      exact (hBrep f).trans (hT f).symm
    rw [hBT, hnorm]

theorem multiplier_eigenspace : LpMultiplierSpectrumSpec.EigenspaceFormula := by
  intro Ω _ μ p _ a z
  unfold multiplierEigenspace
  rw [shifted_multiplier, multiplier_kernel]
  congr 1
  ext x
  simp only [zeroSet, Set.mem_ofPred_eq, sub_eq_zero, eq_comm]

/-- A supported Lp space detects positive measure under semifiniteness. -/
theorem supportedLp_has_nonzero_iff (hμ : Semifinite μ) (hp : p ≠ ∞)
    (E : Set Ω) (hE : MeasurableSet E) :
    (∃ f : Lp ℂ p μ, f ∈ supportedLp μ p E ∧ f ≠ 0) ↔ 0 < μ E := by
  constructor
  · rintro ⟨f, hf, hne⟩
    by_contra hpos
    have hzero : μ E = 0 := le_antisymm (not_lt.mp hpos) bot_le
    have hnot : ∀ᵐ x ∂μ, x ∉ E := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hzero
    apply hne
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hf, hnot] with x hx hnx
    exact hx hnx
  · intro hpos
    obtain ⟨F, hFE, hF, hF0, hFtop⟩ := hμ E hE hpos
    let f : Lp ℂ p μ := indicatorConstLp p hF hFtop.ne 1
    refine ⟨f, ?_, ?_⟩
    · filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hF)
        (hμs := hFtop.ne) (c := (1 : ℂ))] with x hx hnE
      change f x = F.indicator (fun _ => (1 : ℂ)) x at hx
      rw [hx, Set.indicator_of_notMem (fun hxF => hnE (hFE hxF))]
    · exact norm_pos_iff.mp (indicator_norm_pos hp hF hF0 hFtop)

theorem multiplier_eigenvalue : LpMultiplierSpectrumSpec.EigenvalueFormula := by
  intro Ω _ μ hμ p _ _hp1 hp a ha z
  rw [← supportedLp_has_nonzero_iff hμ hp {x | a x = z}
    (measurableSet_eq_fun ha measurable_const), ← multiplier_eigenspace μ p a z]
  constructor
  · rintro ⟨f, hne, heq⟩
    refine ⟨f, ?_, hne⟩
    apply LinearPMap.mem_ker_iff.mpr
    refine ⟨f, rfl, ?_⟩
    change z • (f : Lp ℂ p μ) - maximalMultiplier μ p a f = 0
    rw [heq, sub_self]
  · rintro ⟨f, hf, hne⟩
    obtain ⟨g, hgf, hg⟩ := LinearPMap.mem_ker_iff.mp hf
    refine ⟨g, ?_, ?_⟩
    · simpa only [hgf] using hne
    · change z • (g : Lp ℂ p μ) - maximalMultiplier μ p a g = 0 at hg
      exact (sub_eq_zero.mp hg).symm

/-- Real and imaginary parts preserve Lp membership, and together characterize it. -/
theorem memLp_complex_iff_parts (f : Ω → ℂ) :
    MemLp f p μ ↔ MemLp (fun x => (f x).re) p μ ∧
      MemLp (fun x => (f x).im) p μ := by
  constructor
  · intro hf
    exact ⟨Complex.reCLM.comp_memLp' hf, Complex.imCLM.comp_memLp' hf⟩
  · rintro ⟨hr, hi⟩
    have h := (Complex.ofRealCLM.comp_memLp' hr).add
      ((Complex.ofRealCLM.comp_memLp' hi).const_smul Complex.I)
    convert h using 1
    ext x
    simpa only [Pi.add_apply, Pi.smul_apply, Function.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, mul_comm] using (Complex.re_add_im (f x)).symm

theorem lp_ambient_complexification : LpMultiplierSpectrumSpec.AmbientComplexification := by
  intro Ω _ μ p _
  constructor
  · intro f
    filter_upwards [Complex.reCLM.coeFn_compLp f, Complex.imCLM.coeFn_compLp f] with x hr hi
    rw [hr, hi]
    simpa only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using
      (Complex.re_add_im (f x)).symm
  · intro u v
    let f : Lp ℂ p μ := Complex.ofRealCLM.compLp u + Complex.I • Complex.ofRealCLM.compLp v
    have hrep : (f : Ω → ℂ) =ᵐ[μ] fun x => (u x : ℂ) + Complex.I * (v x : ℂ) := by
      filter_upwards [Lp.coeFn_add (Complex.ofRealCLM.compLp u)
        (Complex.I • Complex.ofRealCLM.compLp v),
        Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLp v),
        Complex.ofRealCLM.coeFn_compLp u, Complex.ofRealCLM.coeFn_compLp v] with x hadd hsm hu hv
      change (Complex.ofRealCLM.compLp u + Complex.I • Complex.ofRealCLM.compLp v) x = _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsm
      rw [hadd, hsm, hu, hv]
      rfl
    refine ⟨f, hrep, ?_, ?_⟩
    · apply Lp.ext
      filter_upwards [Complex.reCLM.coeFn_compLp f, hrep] with x hr hx
      rw [hr, hx]
      simp
    · apply Lp.ext
      filter_upwards [Complex.imCLM.coeFn_compLp f, hrep] with x hi hx
      rw [hi, hx]
      simp

theorem multiplier_real_complexification : LpMultiplierSpectrumSpec.RealComplexification := by
  intro Ω _ μ p _ a
  constructor
  · intro f
    constructor
    · intro hf
      let u := Complex.reCLM.compLp f
      let v := Complex.imCLM.compLp f
      have hu : u ∈ (maximalMultiplier μ p a).domain := by
        apply (Complex.reCLM.comp_memLp' hf).ae_eq
        filter_upwards [Complex.reCLM.coeFn_compLp f] with x hx
        change ((a x : ℂ) * f x).re = a x * u x
        rw [hx]
        simp
      have hv : v ∈ (maximalMultiplier μ p a).domain := by
        apply (Complex.imCLM.comp_memLp' hf).ae_eq
        filter_upwards [Complex.imCLM.coeFn_compLp f] with x hx
        change ((a x : ℂ) * f x).im = a x * v x
        rw [hx]
        simp
      refine ⟨⟨u, hu⟩, ⟨v, hv⟩, ?_⟩
      filter_upwards [Complex.reCLM.coeFn_compLp f, Complex.imCLM.coeFn_compLp f] with x hr hi
      rw [hr, hi]
      simpa only [Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using
        (Complex.re_add_im (f x)).symm
    · rintro ⟨u, v, hrep⟩
      have hu := Complex.ofRealCLM.comp_memLp' u.2
      have hv := Complex.ofRealCLM.comp_memLp' v.2
      apply (hu.add (hv.const_smul Complex.I)).ae_eq
      filter_upwards [hrep] with x hx
      change ((a x * (u : Lp ℝ p μ) x : ℝ) : ℂ) +
        Complex.I * ((a x * (v : Lp ℝ p μ) x : ℝ) : ℂ) = (a x : ℂ) * f x
      rw [hx, Complex.ofReal_mul, Complex.ofReal_mul]
      ring
  · intro f u v hrep
    filter_upwards [maximalLpMultiplier_apply μ p (fun x => (a x : ℂ)) f,
      maximalLpMultiplier_apply μ p a u, maximalLpMultiplier_apply μ p a v,
      hrep] with x hf hu hv hx
    rw [hf, hu, hv, hx, Complex.ofReal_mul, Complex.ofReal_mul]
    ring

theorem multiplier_real_spectrum : LpMultiplierSpectrumSpec.RealSpectrumFormula := by
  intro Ω _ μ hμ p _ hp1 hp a ha
  exact multiplier_spectrum μ hμ p hp1 hp (fun x => (a x : ℂ))
    (Complex.measurable_ofReal.comp ha)

end ExpandedFA.Multiplication
