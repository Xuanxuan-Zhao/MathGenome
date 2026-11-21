import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.Residue
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.FiniteCycleCauchy

noncomputable section
open Set Metric Filter
open scoped Topology BigOperators ENNReal

namespace D12Complex.ResidueCycle

/-- The filled trace of a cycle: its trace and every nonzero-index point. -/
def filledTrace (Γ : IntegralCycle) : Set ℂ :=
  Γ.trace ∪ Function.support Γ.index

theorem filledTrace_isCompact (Γ : IntegralCycle) : IsCompact (filledTrace Γ) := by
  apply isCompact_iff_isClosed_bounded.mpr
  constructor
  · rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hat : a ∉ Γ.trace := fun h => ha (Or.inl h)
    have hz : Γ.index a = 0 := by
      by_contra h
      exact ha (Or.inr h)
    filter_upwards [IndexProperties.cycle_index_locally_constant Γ a hat] with b hb
    rintro (ht | hi)
    · exact hb.1 ht
    · exact hi (hb.2.trans hz)
  · exact (PiecewiseC1Length.chain_trace_compact Γ.chain).isBounded.union
      (IndexProperties.cycle_index_bounded_support Γ)

theorem filledTrace_subset (Ω : Set ℂ) (Γ : IntegralCycle)
    (hΓ : Γ.trace ⊆ Ω) (hzero : ∀ w, w ∉ Ω → Γ.index w = 0) :
    filledTrace Γ ⊆ Ω := by
  rintro a (ha | ha)
  · exact hΓ ha
  · by_contra h
    exact ha (hzero a h)

/-- Relative closedness suffices for compact intersection inside Ω. -/
theorem compact_inter_relativelyClosed {Ω A K : Set ℂ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hA : IsClosed ((Subtype.val : Ω → ℂ) ⁻¹' A)) :
    IsCompact (K ∩ A) := by
  obtain ⟨C, hC, he⟩ := isClosed_induced_iff.mp hA
  have heq : K ∩ A = K ∩ C := by
    ext a
    constructor
    · rintro ⟨ha, haA⟩
      exact ⟨ha, show (⟨a, hKΩ ha⟩ : Ω) ∈ Subtype.val ⁻¹' C from
        he.symm ▸ haA⟩
    · rintro ⟨ha, haC⟩
      exact ⟨ha, show (⟨a, hKΩ ha⟩ : Ω) ∈ Subtype.val ⁻¹' A from
        he ▸ haC⟩
  rw [heq]
  exact hK.inter_right hC

theorem finite_nonzero_indices :
    Specs.D12Complex.Ch08.ResidueCycle.finite_nonzero_indices_type := by
  intro Ω A Γ _ _ hclosed hdis hΓ _ hzero
  have hK := compact_inter_relativelyClosed (filledTrace_isCompact Γ)
    (filledTrace_subset Ω Γ hΓ hzero) hclosed
  exact (hK.finite (hdis.mono inter_subset_right)).subset (by
    rintro a ⟨ha, hi⟩
    exact ⟨Or.inr hi, ha⟩)

/-- Linearity in the chain holds for every integrand, since it only sums
already defined path integrals. No integrability assumption is needed here. -/
def chainIntegralHom (f : ℂ → ℂ) : IntegralChain →+ ℂ :=
  Finsupp.liftAddHom fun γ =>
    { toFun := fun m : ℤ => (m : ℂ) * γ.integral f
      map_zero' := by simp
      map_add' := by intros; simp [add_mul] }

theorem chainIntegralHom_apply (f : ℂ → ℂ) (Γ : IntegralChain) :
    chainIntegralHom f Γ = Γ.integral f := by
  simp [chainIntegralHom, Finsupp.liftAddHom_apply, IntegralChain.integral]

theorem integral_sub_sum_single {ι : Type*} (Γ : IntegralChain) (s : Finset ι)
    (p : ι → PiecewiseC1Path) (n : ι → ℤ) (f : ℂ → ℂ) :
    (Γ - ∑ a ∈ s, Finsupp.single (p a) (n a)).integral f =
      Γ.integral f - ∑ a ∈ s, (n a : ℂ) * (p a).integral f := by
  simp only [← chainIntegralHom_apply, map_sub, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp [chainIntegralHom]

/-- Cancellation may remove paths from the active trace; every remaining path
comes from the original cycle or one of the correcting circles. -/
theorem support_sub_sum_single {ι : Type*} (Γ : IntegralChain) (s : Finset ι)
    (p : ι → PiecewiseC1Path) (n : ι → ℤ) (γ : PiecewiseC1Path)
    (hγ : γ ∈ (Γ - ∑ a ∈ s, Finsupp.single (p a) (n a)).support) :
    γ ∈ Γ.support ∨ ∃ a ∈ s, γ = p a := by
  classical
  by_contra h
  have hΓ : Γ γ = 0 := by
    simpa only [Finsupp.mem_support_iff, not_not] using
      (show γ ∉ Γ.support from fun hγ => h (Or.inl hγ))
  have hp : ∀ a ∈ s, p a ≠ γ := by
    intro a ha he
    exact h (Or.inr ⟨a, ha, he.symm⟩)
  have hz : (Γ - ∑ a ∈ s, Finsupp.single (p a) (n a)) γ = 0 := by
    simp only [Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, hΓ,
      zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero (fun a ha => ite_eq_right (hp a ha))
  exact Finsupp.mem_support_iff.mp hγ hz

theorem exists_isolating_radius (Ω A : Set ℂ) (hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω)
    (hdis : IsDiscrete A) (a : ℂ) (ha : a ∈ A) :
    ∃ r : ℝ, 0 < r ∧ closedBall a (2*r) ⊆ Ω ∧
      ∀ b ∈ A, b ≠ a → 2*r < dist b a := by
  obtain ⟨V, hV, he⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdis a ha
  have haV : a ∈ V := (show a ∈ V ∩ A from he.symm ▸ mem_singleton a).1
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((hΩ.inter hV).mem_nhds ⟨hAΩ ha, haV⟩)
  refine ⟨δ/4, by positivity, ?_, ?_⟩
  · exact ((closedBall_subset_ball (by linarith) :
      closedBall a (2*(δ/4)) ⊆ ball a δ).trans hsub).trans inter_subset_left
  · intro b hb hba
    by_contra h
    have hbV : b ∈ V := (hsub (show b ∈ ball a δ from
      (mem_ball.mpr (lt_of_le_of_lt (le_of_not_gt h) (by linarith))))).2
    exact hba (mem_singleton_iff.mp (he ▸ (show b ∈ V ∩ A from ⟨hbV, hb⟩)))

theorem annulus_subset_punctured {Ω A : Set ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hball : closedBall a (2*r) ⊆ Ω)
    (hsep : ∀ b ∈ A, b ≠ a → 2*r < dist b a) :
    Laurent.annulus a 0 (ENNReal.ofReal (2*r)) ⊆ Ω \ A := by
  intro z hz
  have hz0 : 0 < ‖z-a‖ := hz.1
  have hzr : ‖z-a‖ < 2*r := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp
    (by
      change ENNReal.ofReal (‖z-a‖₊ : ℝ) < _
      rw [ENNReal.ofReal_coe_nnreal]
      exact hz.2)
  have hne : z ≠ a := by simpa only [sub_ne_zero] using (norm_pos_iff.mp hz0)
  have hd : dist z a < 2*r := by simpa only [dist_eq_norm] using hzr
  exact ⟨hball (mem_closedBall.mpr hd.le), fun hzA =>
    (not_lt_of_ge hd.le) (hsep z hzA hne)⟩

theorem sphere_subset_punctured {Ω A : Set ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall a (2*r) ⊆ Ω)
    (hsep : ∀ b ∈ A, b ≠ a → 2*r < dist b a) :
    sphere a r ⊆ Ω \ A := by
  apply Subset.trans _ (annulus_subset_punctured hr hball hsep)
  intro z hz
  have hn : ‖z-a‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
  constructor
  · simpa only [hn] using hr
  · rw [← ENNReal.ofReal_coe_nnreal, show (‖z-a‖₊ : ℝ) = ‖z-a‖ from rfl, hn]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)

theorem circle_integral_residue {Ω A : Set ℂ} {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hf : HolomorphicOn (Ω \ A) f) (hr : 0 < r)
    (hball : closedBall a (2*r) ⊆ Ω)
    (hsep : ∀ b ∈ A, b ≠ a → 2*r < dist b a) :
    (DiskCauchyFormula.circlePath a r).integral f =
      (2 * Real.pi * Complex.I : ℂ) * Residue.residue f a := by
  have hsub := annulus_subset_punctured hr hball hsep
  have hhol : HolomorphicOn (Laurent.annulus a 0 (ENNReal.ofReal (2*r))) f :=
    ⟨by
      change IsOpen ({z : ℂ | 0 < ‖z-a‖} ∩
        {z : ℂ | (‖z-a‖₊ : ℝ≥0∞) < ENNReal.ofReal (2*r)})
      exact (isOpen_lt continuous_const (by fun_prop)).inter
        (isOpen_lt (by fun_prop) continuous_const), fun z hz => hf.2 z (hsub hz)⟩
  have he := Residue.residue_eq_circleIntegral f a (ENNReal.ofReal (2*r)) hhol
    r hr (ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith))
  rw [DiskCauchyFormula.integral_eq_circleIntegral a r f hr.le (by
    intro z hz
    exact (hf.2 z (sphere_subset_punctured hr hball hsep hz)).continuousAt.continuousWithinAt)]
  rw [he, ← mul_assoc, mul_inv_cancel₀ (by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero), one_mul]

/-- Each correcting circle contributes one at its center and zero at every
other excluded point. This calculation concerns actual path integrals. -/
theorem circle_integral_reciprocal {Ω A : Set ℂ} {a w : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall a (2*r) ⊆ Ω)
    (hsep : ∀ b ∈ A, b ≠ a → 2*r < dist b a)
    (hw : w ∉ Ω \ A) :
    (DiskCauchyFormula.circlePath a r).integral (fun z => 1 / (z-w)) =
      if w = a then (2 * Real.pi * Complex.I : ℂ) else 0 := by
  classical
  by_cases hwa : w = a
  · subst w
    simp only [ite_true, one_div]
    exact DiskCauchyFormula.circle_integral_sub_inv a a r hr (by simpa using hr)
  · rw [ite_eq_right hwa]
    have hd : r < dist w a := by
      by_cases hwΩ : w ∈ Ω
      · have hwA : w ∈ A := by
          by_contra hwA
          exact hw ⟨hwΩ, hwA⟩
        linarith [hsep w hwA hwa]
      · have hd' : 2*r < dist w a := lt_of_not_ge (fun h => hwΩ (hball h))
        linarith
    have hcont : ContinuousOn (fun z : ℂ => 1 / (z-w)) (sphere a r) := by
      apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      intro z hz
      apply sub_ne_zero.mpr
      intro he
      change z = w at he
      subst z
      exact (ne_of_gt hd) (mem_sphere.mp hz)
    rw [DiskCauchyFormula.integral_eq_circleIntegral a r _ hr.le hcont]
    simpa only [one_div, dist_eq_norm] using
      Laurent.circleIntegral_sub_inv_of_exterior a w r hr.le
        (by simpa only [dist_eq_norm] using hd)

theorem residue_theorem : Specs.D12Complex.Ch08.ResidueCycle.residue_theorem_type := by
  classical
  intro Ω A f Γ hΩ hAΩ hclosed hdis hf hΓ havoid hzero
  have hfinite := finite_nonzero_indices Ω A Γ hΩ hAΩ hclosed hdis hΓ havoid hzero
  let s := hfinite.toFinset
  have hs : ∀ a, a ∈ s ↔ a ∈ A ∧ Γ.index a ≠ 0 := by
    intro a
    exact hfinite.mem_toFinset
  have hat : ∀ a ∈ A, a ∉ Γ.trace := fun a ha ht => Set.disjoint_left.mp havoid ht ha
  have hex : ∀ a : ℂ, ∃ r : ℝ, a ∈ A → 0 < r ∧
      closedBall a (2*r) ⊆ Ω ∧ ∀ b ∈ A, b ≠ a → 2*r < dist b a := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨r, hr⟩ := exists_isolating_radius Ω A hΩ hAΩ hdis a ha
      exact ⟨r, fun _ => hr⟩
    · exact ⟨1, fun h => (ha h).elim⟩
  choose r hr using hex
  have hnex : ∀ a : ℂ, ∃ n : ℤ, a ∈ A → Γ.index a = (n : ℂ) := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨n, hn⟩ := IndexProperties.cycle_index_integer Γ a (hat a ha)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose n hn using hnex
  let p : ℂ → PiecewiseC1Path := fun a => DiskCauchyFormula.circlePath a (r a)
  let Δchain : IntegralChain := Γ.chain - ∑ a ∈ s, Finsupp.single (p a) (n a)
  have hpaths : ∀ γ ∈ Δchain.support, γ ∈ Γ.chain.support ∨ ∃ a ∈ s, γ = p a :=
    support_sub_sum_single Γ.chain s p n
  have hΔcycle : Δchain.IsCycle := by
    intro γ hγ
    rcases hpaths γ hγ with h | ⟨a, _, rfl⟩
    · exact Γ.property γ h
    · exact DiskCauchyFormula.circlePath_closed a (r a)
  let Δ : IntegralCycle := ⟨Δchain, hΔcycle⟩
  have hΔtrace : Δ.trace ⊆ Ω \ A := by
    rintro z ⟨γ, hγ, hz⟩
    rcases hpaths γ hγ with h | ⟨a, ha, rfl⟩
    · have hzΓ : z ∈ Γ.trace := ⟨γ, h, hz⟩
      exact ⟨hΓ hzΓ, fun hzA => Set.disjoint_left.mp havoid hzΓ hzA⟩
    · have haA := ((hs a).mp ha).1
      have hp : (p a).trace = sphere a (r a) :=
        DiskCauchyFormula.circlePath_trace a (r a) (hr a haA).1.le
      exact sphere_subset_punctured (hr a haA).1 (hr a haA).2.1 (hr a haA).2.2 (hp ▸ hz)
  have hΔzero : ∀ w, w ∉ Ω \ A → Δ.index w = 0 := by
    intro w hw
    have hwt : w ∉ Δ.trace := fun ht => hw (hΔtrace ht)
    rw [Δ.index_eq_integral w hwt]
    change (2 * Real.pi * Complex.I : ℂ)⁻¹ * Δchain.integral (fun z => 1 / (z-w)) = 0
    rw [integral_sub_sum_single]
    have hcircles : ∀ a ∈ s, (p a).integral (fun z => 1 / (z-w)) =
        if w = a then (2 * Real.pi * Complex.I : ℂ) else 0 := by
      intro a ha
      have haA := ((hs a).mp ha).1
      exact circle_integral_reciprocal (hr a haA).1 (hr a haA).2.1 (hr a haA).2.2 hw
    rw [mul_sub, Finset.mul_sum]
    have hsum : ∑ a ∈ s, (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ((n a : ℂ) * (p a).integral (fun z => 1 / (z-w))) = Γ.index w := by
      have heach : ∀ a ∈ s, (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ((n a : ℂ) * (p a).integral (fun z => 1 / (z-w))) =
          if w = a then Γ.index w else 0 := by
        intro a ha
        rw [hcircles a ha]
        split_ifs with he
        · subst w
          rw [hn a ((hs a).mp ha).1]
          field_simp
        · simp
      rw [Finset.sum_congr rfl heach]
      by_cases hwS : w ∈ s
      · simp [hwS]
      · have hzi : Γ.index w = 0 := by
          by_cases hwA : w ∈ A
          · by_contra hzi
            exact hwS ((hs w).mpr ⟨hwA, hzi⟩)
          · exact hzero w (fun hwΩ => hw ⟨hwΩ, hwA⟩)
        simp [hzi]
    rw [hsum]
    have hΓwt : w ∉ Γ.trace := fun ht => hw ⟨hΓ ht,
      fun hwA => Set.disjoint_left.mp havoid ht hwA⟩
    change ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Γ.integral (fun z => 1 / (z-w))) -
      Γ.index w = 0
    rw [← Γ.index_eq_integral w hΓwt]
    exact sub_self _
  have hCauchy := FiniteCycleCauchy.cycle_cauchy_theorem (Ω \ A) f Δ hf hΔtrace hΔzero
  change Δchain.integral f = 0 at hCauchy
  rw [integral_sub_sum_single, sub_eq_zero] at hCauchy
  refine ⟨s, hs, hCauchy.trans ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have haA := ((hs a).mp ha).1
  rw [show (p a).integral f = (2 * Real.pi * Complex.I : ℂ) * Residue.residue f a from
    circle_integral_residue hf (hr a haA).1 (hr a haA).2.1 (hr a haA).2.2,
    hn a haA]
  ring

end D12Complex.ResidueCycle
