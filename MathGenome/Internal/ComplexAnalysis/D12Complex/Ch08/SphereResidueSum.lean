import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.SphereResidueSum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.InfinityResidue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology

noncomputable section
open Set Metric Filter
open scoped Topology BigOperators ENNReal

namespace D12Complex.SphereResidueSum

lemma regularAt_differentiableAt {f : ℂ → ℂ} {a : ℂ} (h : RegularAt f a) :
    DifferentiableAt ℂ f a := by
  obtain ⟨r, hr, hf⟩ := h
  exact hf.2 a (mem_ball_self hr)

lemma regularAt_isolated {f : ℂ → ℂ} {a : ℂ} (h : RegularAt f a) :
    IsolatedSingularityAt f a := by
  obtain ⟨r, hr, hf⟩ := h
  refine ⟨r, hr, ?_, ?_⟩
  · change IsOpen ({z : ℂ | 0 < ‖z-a‖} ∩ {z : ℂ | ‖z-a‖ < r})
    exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) continuous_const)
  · intro z hz
    exact hf.2 z (mem_ball_iff_norm.mpr hz.2)

lemma pole_not_continuousAt {f : ℂ → ℂ} {a : ℂ} (h : PoleAt f a) :
    ¬ ContinuousAt f a := by
  rintro hf
  obtain ⟨m, hm, _, r, hr, g, hg, hga, heq⟩ := h
  have hgcont : ContinuousAt g a := (hg.2 a (mem_ball_self hr)).continuousAt
  have hprod : Tendsto (fun z => (z-a)^m * f z) (𝓝[≠] a) (𝓝 0) := by
    have hh : Tendsto (fun z : ℂ => (z-a)^m * f z) (𝓝 a) (𝓝 ((a-a)^m * f a)) :=
      (((continuousAt_id.sub (continuousAt_const (y := a))).pow m).mul hf).tendsto
    simpa [zero_pow (by omega : m ≠ 0)] using hh.mono_left nhdsWithin_le_nhds
  have hevent : (fun z => (z-a)^m * f z) =ᶠ[𝓝[≠] a] g := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin] with z hz hza
    have hn : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [heq z ⟨norm_pos_iff.mpr hn, mem_ball_iff_norm.mp hz⟩]
    simp [hn]
  exact hga (tendsto_nhds_unique (hprod.congr' hevent)
    (hgcont.tendsto.mono_left nhdsWithin_le_nhds)).symm

lemma pole_not_regularAt {f : ℂ → ℂ} {a : ℂ} (h : PoleAt f a) : ¬ RegularAt f a :=
  fun hr => pole_not_continuousAt h (regularAt_differentiableAt hr).continuousAt

/-- The local data exclude nonregular points on a whole punctured neighborhood. -/
lemma isolated_eventually_differentiable {f : ℂ → ℂ} {a : ℂ}
    (h : IsolatedSingularityAt f a) : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ f z := by
  obtain ⟨r, hr, hf⟩ := h
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin] with z hz hza
  exact hf.2 z ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), mem_ball_iff_norm.mp hz⟩

/-- Inversion of the differential coefficient recovers the finite-chart function
by multiplication by the nonvanishing Jacobian inverse. -/
lemma isolated_at_infinity {f : ℂ → ℂ}
    (h : IsolatedSingularityAt (InfinityResidue.pullbackCoefficient f) 0) :
    IsolatedSingularityAtInfinity f := by
  obtain ⟨r, hr, hg⟩ := h
  refine ⟨r, hr, hg.1, ?_⟩
  intro w hw
  have hw0 : w ≠ 0 := by simpa only [sub_zero, norm_pos_iff] using hw.1
  have heq : reciprocalPullback f =ᶠ[𝓝 w]
      (fun z => -InfinityResidue.pullbackCoefficient f z * z ^ (2 : ℕ)) := by
    filter_upwards [eventually_ne_nhds hw0] with z hz
    simp [InfinityResidue.pullbackCoefficient, zpow_neg, hz]
  exact (((hg.2 w hw).neg.mul (differentiableAt_id.pow 2))).congr_of_eventuallyEq heq

lemma meromorphic_isolated {f : ℂ → ℂ} (h : MeromorphicDifferential f) :
    (∀ a, IsolatedSingularityAt f a) ∧ IsolatedSingularityAtInfinity f := by
  constructor
  · intro a
    rcases h.1 a with hr | ⟨m, _, hi, _⟩
    · exact regularAt_isolated hr
    · exact hi
  · apply isolated_at_infinity
    rcases h.2 with hr | ⟨m, _, hi, _⟩
    · exact hr.1
    · exact hi

/-- Entirely local singularities form a closed discrete set. -/
lemma nonregular_closed_discrete {f : ℂ → ℂ} (hf : ∀ a, IsolatedSingularityAt f a) :
    IsClosed {a | ¬DifferentiableAt ℂ f a} ∧ IsDiscrete {a | ¬DifferentiableAt ℂ f a} := by
  apply isClosed_and_discrete_iff.mpr
  intro a
  rw [Filter.disjoint_principal_right]
  filter_upwards [isolated_eventually_differentiable (hf a)] with z hz
  exact fun hn => hn hz

lemma finite_nonregular {f : ℂ → ℂ} (hf : ∀ a, IsolatedSingularityAt f a)
    (hi : IsolatedSingularityAtInfinity f) : {a | ¬DifferentiableAt ℂ f a}.Finite := by
  obtain ⟨R, hR, hext⟩ := (isolatedSingularityAtInfinity_iff_exterior f).mp hi
  obtain ⟨hc, hd⟩ := nonregular_closed_discrete hf
  have hb : {a | ¬DifferentiableAt ℂ f a} ⊆ closedBall 0 R := by
    intro a ha
    by_contra hball
    have hn : R < ‖a‖ := by simpa [mem_closedBall, dist_zero_right] using hball
    exact ha (hext.2 a hn)
  exact ((isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hc hb).finite hd

lemma poles_eq_nonregular {f : ℂ → ℂ} (hf : MeromorphicDifferential f) :
    {a | PoleAt f a} = {a | ¬DifferentiableAt ℂ f a} := by
  ext a
  constructor
  · intro hp hd
    exact pole_not_continuousAt hp hd.continuousAt
  · intro hn
    rcases hf.1 a with hr | hp
    · exact (hn (regularAt_differentiableAt hr)).elim
    · exact hp

lemma finite_finite_poles {f : ℂ → ℂ} (hf : MeromorphicDifferential f) :
    {a | PoleAt f a}.Finite := by
  rw [poles_eq_nonregular hf]
  exact finite_nonregular (meromorphic_isolated hf).1 (meromorphic_isolated hf).2

end D12Complex.SphereResidueSum

namespace D12Complex.SphereResidueSum

lemma residue_zero_of_removable {f : ℂ → ℂ} {a : ℂ}
    (hf : RemovableSingularityAt f a) : Residue.residue f a = 0 := by
  obtain ⟨⟨R, hR, hhol⟩, r, hr, g, hg, heq⟩ := hf
  let t := min R r / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htR : t < R := by dsimp [t]; linarith [min_le_left R r]
  have htr : t < r := by dsimp [t]; linarith [min_le_right R r]
  have hh : HolomorphicOn (Laurent.annulus a 0 (ENNReal.ofReal R)) f := by
    refine ⟨?_, ?_⟩
    · change IsOpen ({z : ℂ | 0 < ‖z-a‖} ∩
        {z : ℂ | (‖z-a‖₊ : ℝ≥0∞) < ENNReal.ofReal R})
      exact (isOpen_lt continuous_const (by fun_prop)).inter
        (isOpen_lt (by fun_prop) continuous_const)
    · intro z hz
      apply hhol.2 z
      refine ⟨hz.1, ?_⟩
      have hz' : (‖z-a‖₊ : ℝ≥0∞) < ENNReal.ofReal R := hz.2
      rw [← ENNReal.ofReal_coe_nnreal] at hz'
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mp hz'
  rw [Residue.residue_eq_circleIntegral f a (ENNReal.ofReal R) hh t ht
    ((ENNReal.ofReal_lt_ofReal_iff hR).mpr htR)]
  have hcongr : circleIntegral f a t = circleIntegral g a t := by
    apply circleIntegral.integral_congr ht.le
    intro z hz
    apply heq z
    have hz' : ‖z-a‖ = t := mem_sphere_iff_norm.mp hz
    exact ⟨by simpa [hz'] using ht, by simpa [hz'] using htr⟩
  rw [hcongr]
  have hz : circleIntegral g a t = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable ht.le
      (s := (∅ : Set ℂ)) countable_empty
    · intro z hz
      exact (hg.2 z ((closedBall_subset_ball htr) hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact hg.2 z ((ball_subset_ball htr.le) hz.1)
  rw [hz, mul_zero]

lemma residue_zero_of_regular {f : ℂ → ℂ} {a : ℂ} (hf : RegularAt f a) :
    Residue.residue f a = 0 := by
  obtain ⟨r, hr, hg⟩ := hf
  exact residue_zero_of_removable ⟨regularAt_isolated ⟨r, hr, hg⟩,
    r, hr, f, hg, fun _ _ => rfl⟩

theorem poles_finite : Specs.D12Complex.Ch08.SphereResidueSum.poles_finite_type := by
  intro f hf
  apply ((finite_finite_poles hf).image sphereFinite).union
  exact (finite_singleton sphereInfty).subset (fun _ h => h.1)

theorem residue_zero_off_poles :
    Specs.D12Complex.Ch08.SphereResidueSum.residue_zero_off_poles_type := by
  intro f hf p hp
  induction p using OnePoint.rec with
  | infty =>
    have hn : ¬ PoleAt (InfinityResidue.pullbackCoefficient f) 0 := by
      intro h
      exact hp (Or.inr ⟨rfl, h⟩)
    exact residue_zero_of_removable (hf.2.resolve_right hn)
  | coe a =>
    have hn : ¬ PoleAt f a := by
      intro h
      exact hp (Or.inl ⟨a, h, rfl⟩)
    exact residue_zero_of_regular ((hf.1 a).resolve_right hn)

private def positiveCircle (r : ℝ) : IntegralCycle :=
  ⟨Finsupp.single (DiskCauchyFormula.circlePath 0 r) 1, by
    intro γ hγ
    have he : γ = DiskCauchyFormula.circlePath 0 r := by
      simpa using hγ
    subst γ
    exact DiskCauchyFormula.circlePath_closed 0 r⟩

private lemma positiveCircle_trace (r : ℝ) (hr : 0 ≤ r) :
    (positiveCircle r).trace = sphere 0 r := by
  classical
  ext z
  simp [positiveCircle, IntegralCycle.trace, IntegralCycle.chain, IntegralChain.trace,
    DiskCauchyFormula.circlePath_trace 0 r hr]

private lemma positiveCircle_integral (r : ℝ) (f : ℂ → ℂ) :
    (positiveCircle r).integral f = (DiskCauchyFormula.circlePath 0 r).integral f := by
  classical
  simp [positiveCircle, IntegralCycle.integral, IntegralCycle.chain, IntegralChain.integral]

private lemma positiveCircle_index {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : ‖a‖ < r) :
    (positiveCircle r).index a = 1 := by
  have hat : a ∉ (positiveCircle r).trace := by
    rw [positiveCircle_trace r hr.le]
    simpa only [mem_sphere_iff_norm, sub_zero] using ne_of_lt ha
  rw [IntegralCycle.index_eq_integral _ _ hat, positiveCircle_integral]
  simp only [one_div]
  rw [DiskCauchyFormula.circle_integral_sub_inv 0 a r hr (by simpa using ha)]
  exact inv_mul_cancel₀ (by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

/-- A large circle encloses exactly all finite poles. Its Laurent coefficient
is the negative of the differential residue at infinity. -/
theorem finite_residue_sum :
    Specs.D12Complex.Ch08.SphereResidueSum.finite_residue_sum_type := by
  classical
  intro f hf
  let A : Set ℂ := {a | PoleAt f a}
  have hA : A.Finite := finite_finite_poles hf
  obtain ⟨R, hR, hext⟩ := (isolatedSingularityAtInfinity_iff_exterior f).mp
    (meromorphic_isolated hf).2
  obtain ⟨r, hRr, hAr⟩ := hA.isBounded.subset_ball_lt R 0
  have hr : 0 < r := hR.trans hRr
  have hhol : HolomorphicOn (univ \ A) f := by
    refine ⟨isOpen_univ.sdiff hA.isClosed, ?_⟩
    intro a ha
    exact regularAt_differentiableAt ((hf.1 a).resolve_right ha.2)
  have havoid : Disjoint (positiveCircle r).trace A := by
    apply Set.disjoint_left.mpr
    intro a ha ht
    have hh := hAr ht
    rw [positiveCircle_trace r hr.le] at ha
    exact (ne_of_lt (mem_ball.mp hh)) (mem_sphere.mp ha)
  obtain ⟨s, hs, hsum⟩ := ResidueCycle.residue_theorem univ A f (positiveCircle r)
    isOpen_univ (subset_univ _) (hA.isClosed.preimage continuous_subtype_val)
    hA.isDiscrete hhol (subset_univ _) havoid (fun w hw => (hw (mem_univ w)).elim)
  have hsA : ∀ a, a ∈ s ↔ PoleAt f a := by
    intro a
    rw [hs]
    constructor
    · exact fun h => h.1
    · intro ha
      refine ⟨ha, ?_⟩
      rw [positiveCircle_index hr (by simpa using hAr ha)]
      exact one_ne_zero
  have heach : (∑ a ∈ s, (positiveCircle r).index a * Residue.residue f a) =
      ∑ a ∈ s, Residue.residue f a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [positiveCircle_index hr (by simpa using hAr ((hsA a).mp ha)), one_mul]
  rw [heach, positiveCircle_integral] at hsum
  have hcont : ContinuousOn f (sphere 0 r) := by
    intro z hz
    exact (hext.2 z (by
      have hn : ‖z‖ = r := by simpa using mem_sphere.mp hz
      change R < ‖z‖
      rwa [hn])).continuousAt.continuousWithinAt
  rw [DiskCauchyFormula.integral_eq_circleIntegral 0 r f hr.le hcont] at hsum
  have hAnn : HolomorphicOn (Laurent.annulus 0 R ⊤) f := by
    convert hext using 1
    ext z
    simp [Laurent.annulus, exterior]
  obtain ⟨c, hc, hcoeff, _⟩ := Laurent.laurent_exists 0 R ⊤ f hR.le
    ENNReal.ofReal_lt_top hAnn
  have hinf := InfinityResidue.residueAtInfinity_eq_neg_laurentCoefficient f R c hR.le
    (Laurent.convergent_of_hasLaurentSeriesOn hc)
  have hc1 := hcoeff r hRr ENNReal.ofReal_lt_top (-1)
  rw [Residue.coefficientIntegral_neg_one, hsum] at hc1
  have hc2 : c (-1) = ∑ a ∈ s, Residue.residue f a := by
    rw [hc1, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨s, hsA, ?_⟩
  rw [hinf, hc2, add_neg_cancel]

theorem total_residue_zero :
    Specs.D12Complex.Ch08.SphereResidueSum.total_residue_zero_type := by
  classical
  intro f hf
  obtain ⟨s, hs, hsum⟩ := finite_residue_sum f hf
  let t := s.image sphereFinite
  have hinfty : sphereInfty ∉ t := by
    simp [t, sphereFinite, sphereInfty]
  have ht : ∑ p ∈ t, residueOnSphere f p = ∑ a ∈ s, Residue.residue f a := by
    rw [Finset.sum_image]
    · rfl
    · exact fun a _ b _ hab => sphereFinite_injective hab
  by_cases hp : PoleAt (InfinityResidue.pullbackCoefficient f) 0
  · refine ⟨insert sphereInfty t, ?_, ?_⟩
    · intro p
      simp only [Finset.mem_insert, Finset.mem_image, t, poleSet, mem_union,
        mem_image, mem_ofPred_eq]
      constructor
      · rintro (rfl | ⟨a, ha, rfl⟩)
        · exact Or.inr ⟨rfl, hp⟩
        · exact Or.inl ⟨a, (hs a).mp ha, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨rfl, _⟩)
        · exact Or.inr ⟨a, (hs a).mpr ha, rfl⟩
        · exact Or.inl rfl
    · rw [Finset.sum_insert hinfty, ht]
      simpa [residueOnSphere, sphereInfty, add_comm] using hsum
  · have hz : InfinityResidue.residueAtInfinity f = 0 :=
      residue_zero_of_removable (hf.2.resolve_right hp)
    refine ⟨t, ?_, ?_⟩
    · intro p
      simp only [t, Finset.mem_image, poleSet, mem_union, mem_image, mem_ofPred_eq]
      simp only [hp, and_false, or_false]
      constructor <;> rintro ⟨a, ha, rfl⟩
      · exact ⟨a, (hs a).mp ha, rfl⟩
      · exact ⟨a, (hs a).mpr ha, rfl⟩
    · rw [ht]
      simpa [hz] using hsum

end D12Complex.SphereResidueSum

namespace D12Complex.SphereResidueSum.Definitions
abbrev RegularAt : Specs.D12Complex.Ch08.SphereResidueSum.RegularAt_type :=
  D12Complex.SphereResidueSum.RegularAt
abbrev MeromorphicDifferential :
    Specs.D12Complex.Ch08.SphereResidueSum.MeromorphicDifferential_type :=
  D12Complex.SphereResidueSum.MeromorphicDifferential
abbrev poleSet : Specs.D12Complex.Ch08.SphereResidueSum.poleSet_type :=
  D12Complex.SphereResidueSum.poleSet
abbrev residueOnSphere : Specs.D12Complex.Ch08.SphereResidueSum.residueOnSphere_type :=
  D12Complex.SphereResidueSum.residueOnSphere
end D12Complex.SphereResidueSum.Definitions
