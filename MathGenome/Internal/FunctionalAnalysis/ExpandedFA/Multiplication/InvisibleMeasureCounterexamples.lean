import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MaximalLpMultiplier
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.InvisibleMeasureCounterexamples

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ExpandedFA.Multiplication

theorem infiniteCounting_apply : InvisibleMeasureCounterexamplesSpec.MeasureLaw := by
  intro Ω _ s
  classical
  by_cases hs : s = ∅
  · simp [hs]
  · simp [infiniteCounting, Measure.smul_apply, hs,
      ENNReal.top_mul (Measure.count_eq_zero_iff.not.mpr hs)]

theorem finiteLp_infiniteCounting_eq_zero :
    InvisibleMeasureCounterexamplesSpec.FiniteLpZero := by
  intro Ω 𝕜 _ _ p hp₀ hp f
  have hfin := (Lp.memLp f).eLpNorm_lt_top
  have hpos : 0 < (1 / p).toReal := by
    simpa only [one_div, ENNReal.toReal_inv] using
      inv_pos.mpr (ENNReal.toReal_pos hp₀ hp)
  change eLpNorm (⇑f) p ((∞ : ℝ≥0∞) • Measure.count) < ∞ at hfin
  rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top hp₀ hp,
    ENNReal.top_rpow_of_pos hpos, smul_eq_mul] at hfin
  have hz : eLpNorm (⇑f) p Measure.count = 0 := by
    by_contra h
    rw [ENNReal.top_mul h] at hfin
    exact (lt_irrefl ∞) hfin
  have hf : (⇑f) =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp₀).mp hz
  apply Lp.ext
  have ha : (⇑f) =ᵐ[infiniteCounting Ω] (0 : Ω → 𝕜) := Measure.ae_smul_measure hf ∞
  exact ha.trans (Lp.coeFn_zero 𝕜 p (infiniteCounting Ω)).symm

theorem zeroSpace_multiplier : InvisibleMeasureCounterexamplesSpec.ZeroSpaceOperator := by
  intro Ω 𝕜 _ _ μ p _ h a
  let _ := h
  have hdom : (maximalMultiplier μ p a).domain = ⊤ :=
    Submodule.eq_top_iff'.mpr fun f => by
      rw [Subsingleton.elim f 0]
      exact (maximalMultiplier μ p a).domain.zero_mem
  refine ⟨hdom, ?_, (fun f => Subsingleton.elim _ _), ?_⟩
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · apply Set.eq_univ_of_forall
    intro z
    exact ⟨{ inverse := 0
             mem_domain := fun y => by simp
             right_inverse := fun y => Subsingleton.elim _ _
             left_inverse := fun x => Subsingleton.elim _ _ }⟩

theorem zeroSpace_multiplier_spectrum : InvisibleMeasureCounterexamplesSpec.ZeroSpaceSpectrum := by
  intro Ω _ μ p _ h a
  unfold multiplierSpectrum
  rw [(zeroSpace_multiplier μ p h a).2.2.2, Set.compl_univ]

theorem point_zero_counterexample : InvisibleMeasureCounterexamplesSpec.PointZeroCounterexample := by
  intro 𝕜 _ p hp₁ hp
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp₁.out).ne'
  have hs : Subsingleton (Lp 𝕜 p (infiniteCounting Unit)) :=
    ⟨fun f g => (finiteLp_infiniteCounting_eq_zero p hp₀ hp f).trans
      (finiteLp_infiniteCounting_eq_zero p hp₀ hp g).symm⟩
  refine ⟨(zeroSpace_multiplier _ p hs (fun _ => (0 : 𝕜))).2.1, ?_⟩
  rintro ⟨c, hc, h⟩
  have h' := Measure.ae_count_iff.mp
    ((Measure.ae_ennreal_smul_measure_iff ENNReal.top_ne_zero).mp h) ()
  exact (not_le_of_gt hc) (by simpa using h')

theorem point_one_essentialRange : InvisibleMeasureCounterexamplesSpec.PointOneEssentialRange := by
  ext z
  constructor
  · intro hz
    by_contra h
    have hd : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
    have he := hz ‖(1 : ℂ) - z‖ hd
    simp at he
  · intro hz
    have hz' : z = 1 := Set.mem_singleton_iff.mp hz
    subst z
    intro ε hε
    simp [hε, infiniteCounting]

theorem point_spectrum_resolvent : InvisibleMeasureCounterexamplesSpec.PointSpectrumResolvent := by
  intro p hp₁ hp a
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp₁.out).ne'
  have hs : Subsingleton (Lp ℂ p (infiniteCounting Unit)) :=
    ⟨fun f g => (finiteLp_infiniteCounting_eq_zero p hp₀ hp f).trans
      (finiteLp_infiniteCounting_eq_zero p hp₀ hp g).symm⟩
  exact ⟨zeroSpace_multiplier_spectrum _ p hs a, (zeroSpace_multiplier _ p hs a).2.2.2⟩

theorem nat_fullDomain_unbounded : InvisibleMeasureCounterexamplesSpec.NatFullDomainUnbounded := by
  intro 𝕜 _ _ _ p hp₁ hp
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp₁.out).ne'
  have hs : Subsingleton (Lp 𝕜 p (infiniteCounting ℕ)) :=
    ⟨fun f g => (finiteLp_infiniteCounting_eq_zero p hp₀ hp f).trans
      (finiteLp_infiniteCounting_eq_zero p hp₀ hp g).symm⟩
  have hunbounded : ¬ ∃ C : ℝ, ∀ᵐ (n : ℕ) ∂infiniteCounting ℕ, ‖(n : 𝕜)‖ ≤ C := by
    rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have h := Measure.ae_count_iff.mp
      ((Measure.ae_ennreal_smul_measure_iff ENNReal.top_ne_zero).mp hC) n
    rw [RCLike.norm_natCast] at h
    exact (not_le_of_gt hn) h
  refine ⟨measurable_of_countable _, (zeroSpace_multiplier _ p hs _).1, hunbounded, ?_⟩
  intro h
  have hbound := ae_le_eLpNormEssSup (f := fun n : ℕ => (n : 𝕜))
    (μ := infiniteCounting ℕ)
  have hfin : eLpNormEssSup (fun n : ℕ => (n : 𝕜)) (infiniteCounting ℕ) ≠ ∞ := by
    simpa [eLpNorm_exponent_top h.aestronglyMeasurable] using h.eLpNorm_lt_top.ne
  apply hunbounded
  refine ⟨(eLpNormEssSup (fun n : ℕ => (n : 𝕜)) (infiniteCounting ℕ)).toReal, ?_⟩
  filter_upwards [hbound] with n hn
  exact (ENNReal.toReal_mono hfin hn)

end ExpandedFA.Multiplication
