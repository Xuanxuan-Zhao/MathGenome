import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealNormalEssentialSpectrum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RealFredholmComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RealEssentialWeylFormula
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.EssentialWeylSpectra
import Mathlib.Analysis.CStarAlgebra.Spectrum

noncomputable section
namespace ExpandedFA.Fredholm.RealNormalEssentialSpectrum
universe u
open TraceIdeals.RealComplexification
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Failure of Fredholmness is preserved for each real shift. -/
theorem essentialSpectrum_complexification : Spec.EssentialComplexification.{u} := by
  intro H _ _ _ T
  ext r
  exact (RealFredholmComplexification.shift_comparison H T r).2.1

/-- The complex classification transfers with the actual real kernel. -/
theorem normal_essentialSpectrum_description : Spec.NormalEssentialDescription.{u} := by
  intro H _ _ _ N hN
  have hNC := (RealFredholmComplexification.normality H N).mp hN
  rw [essentialSpectrum_complexification N]
  have hdesc := ExpandedFA.Fredholm.normal_essentialSpectrum_description (operator N) hNC
  ext r
  change ((r : ℂ) ∈ essentialSpectrum (operator N)) ↔ _
  rw [hdesc]
  have hk := RealFredholmComplexification.kernel_finite_iff (N - r • 1)
  have hshift : operator (N - r • 1) = operator N - (r : ℂ) • 1 :=
    RealFredholmComplexification.operator_shift N r
  rw [hshift] at hk
  exact and_congr_right fun _ => or_congr Iff.rfl (and_congr_right fun _ => not_congr hk.symm)

/-- Index zero descends through the Fredholm index bridge. -/
theorem normal_weylSpectrum_eq_essentialSpectrum : Spec.NormalWeylEssential.{u} := by
  intro H _ _ _ N hN
  change realWeylSpectrum N = realEssentialSpectrum N
  rw [realWeylSpectrum_eq]
  have he : {r : ℝ | ∃ h : IsFredholm (N - r • 1),
      fredholmIndex (N - r • 1) h ≠ 0} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro h
    have hs := RealFredholmComplexification.shift_comparison H N r
    have hC : IsFredholm (operator N - (r : ℂ) • 1) := by
      exact Classical.byContradiction fun hn => (hs.2.1.mpr hn) h
    have hnC := (RealFredholmComplexification.normality H N).mp hN
    have hz := normal_fredholmIndex_zero _ (normal_sub_scalar _ hnC (r : ℂ)) hC
    exact fun hne => hne ((hs.2.2 h hC).trans hz)
  rw [he, Set.union_empty]

lemma operator_selfAdjoint (N : H →L[ℝ] H) (hN : IsSelfAdjoint N) :
    IsSelfAdjoint (operator N) := by
  change (operator N).adjoint = operator N
  rw [operator_adjoint]
  exact congrArg operator hN

/-- Self-adjointness makes the whole complex spectrum the real spectral image. -/
theorem selfAdjoint_spectrum : Spec.SelfAdjointSpectrum.{u} := by
  intro H _ _ _ N hN
  have hNC := operator_selfAdjoint N hN
  refine ⟨fun w hw => hNC.mem_spectrum_eq_re hw, ?_⟩
  ext w
  constructor
  · intro hw
    refine ⟨w.re, ?_, (hNC.mem_spectrum_eq_re hw).symm⟩
    apply (RealFredholmComplexification.spectrum_comparison H N w.re).mpr
    rwa [← hNC.mem_spectrum_eq_re hw]
  · rintro ⟨r, hr, rfl⟩
    exact (RealFredholmComplexification.spectrum_comparison H N r).mp hr

/-- Real inclusion is an isometry, and self-adjointness puts every spectral
point in its range. Thus no approaching complex spectral points are lost. -/
lemma selfAdjoint_nonisolation_iff (N : H →L[ℝ] H) (hN : IsSelfAdjoint N) (r : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ w ∈ spectrum ℂ (operator N),
      w ≠ (r : ℂ) ∧ dist w (r : ℂ) < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ s ∈ spectrum ℝ N, s ≠ r ∧ dist s r < ε) := by
  constructor
  · intro h ε hε
    obtain ⟨w, hw, hne, hd⟩ := h ε hε
    have hr := (selfAdjoint_spectrum N hN).1 w hw
    refine ⟨w.re, ?_, ?_, ?_⟩
    · exact (RealFredholmComplexification.spectrum_comparison H N w.re).mpr (hr ▸ hw)
    · intro he
      exact hne (hr.trans (congrArg Complex.ofReal he))
    · rw [← Complex.isometry_ofReal.dist_eq w.re r, ← hr]
      exact hd
  · intro h ε hε
    obtain ⟨s, hs, hne, hd⟩ := h ε hε
    refine ⟨(s : ℂ), (RealFredholmComplexification.spectrum_comparison H N s).mp hs,
      ?_, ?_⟩
    · exact fun he => hne (Complex.ofReal_injective he)
    · simpa only [Complex.isometry_ofReal.dist_eq] using hd

lemma selfAdjoint_isolation_iff (N : H →L[ℝ] H) (hN : IsSelfAdjoint N) (r : ℝ) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ spectrum ℂ (operator N),
      dist w (r : ℂ) < ε → w = (r : ℂ)) ↔
    (∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ spectrum ℝ N, dist s r < ε → s = r) := by
  constructor
  · rintro ⟨ε, hε, hgap⟩
    refine ⟨ε, hε, fun s hs hd => ?_⟩
    apply Complex.ofReal_injective
    apply hgap _ ((RealFredholmComplexification.spectrum_comparison H N s).mp hs)
    simpa only [Complex.isometry_ofReal.dist_eq] using hd
  · rintro ⟨ε, hε, hgap⟩
    refine ⟨ε, hε, fun w hw hd => ?_⟩
    have hr := (selfAdjoint_spectrum N hN).1 w hw
    have hs := (RealFredholmComplexification.spectrum_comparison H N w.re).mpr (hr ▸ hw)
    have hd' : dist w.re r < ε := by
      rw [← Complex.isometry_ofReal.dist_eq w.re r, ← hr]
      exact hd
    exact hr.trans (congrArg Complex.ofReal (hgap w.re hs hd'))

/-- The intrinsic real description is valid for self-adjoint operators. -/
theorem selfAdjoint_essentialSpectrum_description : Spec.SelfAdjointEssentialDescription.{u} := by
  intro H _ _ _ N hN
  rw [normal_essentialSpectrum_description N hN.isStarNormal]
  ext r
  exact and_congr (RealFredholmComplexification.spectrum_comparison H N r).symm
    (or_congr (selfAdjoint_nonisolation_iff N hN r)
      (and_congr (selfAdjoint_isolation_iff N hN r) Iff.rfl))

/-- All corrected real and unchanged complex conclusions, on the same canonical
operator algebras and complexification, without a real nonemptiness assertion. -/
theorem essential_weyl_theorem : Spec.EssentialWeylTheorem.{u} := by
  refine ⟨mem_realEssentialSpectrum, mem_realWeylSpectrum, realWeylSpectrum_eq,
    realEssentialSpectrum_add_compact, realWeylSpectrum_add_compact,
    realEssentialSpectrum_eq_calkin, realEssentialSpectrum_isCompact,
    essentialSpectrum_complexification, normal_weylSpectrum_eq_essentialSpectrum,
    normal_essentialSpectrum_description, selfAdjoint_spectrum,
    selfAdjoint_essentialSpectrum_description, weylSpectrum_formula,
    essentialSpectrum_add_compact, weylSpectrum_add_compact,
    essentialSpectrum_eq_calkinSpectrum, essentialSpectrum_nonempty_compact,
    ExpandedFA.Fredholm.normal_weylSpectrum_eq_essentialSpectrum,
    ExpandedFA.Fredholm.normal_essentialSpectrum_description⟩

end ExpandedFA.Fredholm.RealNormalEssentialSpectrum
