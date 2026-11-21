import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealEssentialWeylFormula
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RealEssentialSpectraDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.IndexStability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.AtkinsonCalkin
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-! The intrinsic real Weyl formula and compact-perturbation laws from
`fa2:p2:essential-spectrum`. The finite-rank correction is constructed in the
original real operator algebra. All conclusions include the zero and finite
dimensional cases, and impose no separability assumption. -/

noncomputable section
namespace ExpandedFA.Fredholm
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Atkinson's theorem in the actual real Calkin quotient. -/
theorem realEssentialSpectrum_eq_calkin (T : H →L[ℝ] H) :
    realEssentialSpectrum T = spectrum ℝ (calkinProjection ℝ H T) := by
  ext z
  rw [mem_realEssentialSpectrum, spectrum.mem_iff]
  have hf : IsFredholm (T - z • (1 : H →L[ℝ] H)) ↔
      IsUnit (calkinProjection ℝ H (T - z • (1 : H →L[ℝ] H))) := atkinson_calkin _
  rw [hf]
  have heq : calkinProjection ℝ H (T - z • (1 : H →L[ℝ] H)) =
      -(algebraMap ℝ (Calkin ℝ H) z - calkinProjection ℝ H T) := by
    simp [map_sub, map_smul, Algebra.algebraMap_eq_smul_one]
  rw [heq, IsUnit.neg_iff]

/-- The intrinsic real set is compact, possibly empty. -/
theorem realEssentialSpectrum_isCompact (T : H →L[ℝ] H) :
    IsCompact (realEssentialSpectrum T) := by
  rw [realEssentialSpectrum_eq_calkin]
  exact spectrum.isCompact _

/-- Compact perturbations preserve failure of Fredholmness over ℝ. -/
theorem realEssentialSpectrum_add_compact (T K : H →L[ℝ] H)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    realEssentialSpectrum (T + K) = realEssentialSpectrum T := by
  ext z
  simp only [mem_realEssentialSpectrum]
  have heq : T + K - z • (1 : H →L[ℝ] H) =
      (T - z • (1 : H →L[ℝ] H)) + K := by abel
  rw [heq, isFredholm_add_compact_iff _ _ hK]

/-- Translating all real compact perturbations leaves their intersection unchanged. -/
theorem realWeylSpectrum_add_compact (T K : H →L[ℝ] H)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) :
    realWeylSpectrum (T + K) = realWeylSpectrum T := by
  have hnK : Compactness.IsCompactLinearMap (-K).toLinearMap := by
    simpa using Compactness.compact_smul (-1 : ℝ) K.toLinearMap hK
  ext z
  simp only [mem_realWeylSpectrum]
  constructor
  · intro h L hL
    have hLK := Compactness.compact_add _ _ hL hnK
    have heq : T + K + (L + -K) = T + L := by abel
    simpa only [heq] using h (L + -K) hLK
  · intro h L hL
    have hKL := Compactness.compact_add _ _ hK hL
    simpa only [add_assoc] using h (K + L) hKL

/-- An index-zero real Fredholm operator can be repaired on its finite-dimensional
kernel. The correction and inverse are constructed over ℝ on the original space. -/
theorem real_finite_rank_correction (T : H →L[ℝ] H) (hT : IsFredholm T)
    (hz : fredholmIndex T hT = 0) :
    ∃ F : H →L[ℝ] H, FiniteDimensional ℝ F.range ∧ IsUnit (T + F) := by
  obtain ⟨p⟩ := hT.to_native.nonempty_fredholmPackage
  let := p.decDom.finite_X₀
  let := p.decCodom.finite_X₀
  have hd : Module.finrank ℝ p.decDom.X₀ = Module.finrank ℝ p.decCodom.X₀ := by
    have hq := (Submodule.quotientEquivOfIsCompl p.decCodom.X₁ p.decCodom.X₀
      p.decCodom.isTopCompl.isCompl).finrank_eq
    change (Module.finrank ℝ T.ker : ℤ) - Module.finrank ℝ (H ⧸ T.range) = 0 at hz
    rw [p.ker_eq, p.range_eq, hq] at hz
    omega
  let e₀ : p.decDom.X₀ ≃L[ℝ] p.decCodom.X₀ := ContinuousLinearEquiv.ofFinrankEq hd
  let d := p.decDom.X₁.prodEquivOfIsTopCompl p.decDom.X₀ p.decDom.isTopCompl
  let c := p.decCodom.X₁.prodEquivOfIsTopCompl p.decCodom.X₀ p.decCodom.isTopCompl
  let U : H ≃L[ℝ] H := d.symm.trans ((p.equiv.prodCongr e₀).trans c)
  let F : H →L[ℝ] H := p.decCodom.X₀.subtypeL.comp
    (e₀.toContinuousLinearMap.comp
      (p.decDom.X₀.projectionOntoL p.decDom.X₁ p.decDom.isTopCompl.symm))
  have hF : FiniteDimensional ℝ F.range := by
    apply Submodule.finiteDimensional_of_le
      (S₂ := p.decCodom.X₀)
    rintro y ⟨x, rfl⟩
    exact (e₀ (p.decDom.X₀.projectionOntoL p.decDom.X₁ p.decDom.isTopCompl.symm x)).property
  have hU : T + F = U.toContinuousLinearMap := by
    ext x
    change T x + F x = U x
    rw [p.eq_equiv]
    simp [U, d, c, F, Submodule.prodEquivOfIsTopCompl_symm_apply,
      Submodule.prodEquivOfIsTopCompl_apply]
  refine ⟨F, hF, ?_⟩
  rw [hU]
  exact ⟨U.toUnit, rfl⟩

/-- A unit in the real operator algebra is Fredholm with index zero. -/
theorem real_fredholm_index_zero_of_isUnit (A : H →L[ℝ] H) (hA : IsUnit A) :
    ∃ h : IsFredholm A, fredholmIndex A h = 0 := by
  obtain ⟨a, rfl⟩ := hA
  have h : IsFredholm (a : H →L[ℝ] H) :=
    isFredholm_of_native (ContinuousLinearEquiv.ofUnit a).isFredholm
  refine ⟨h, ?_⟩
  rw [fredholmIndex_eq_native]
  exact LinearMap.index_of_bijective (ContinuousLinearEquiv.ofUnit a).bijective

/-- No real compact perturbation can turn a non-Fredholm or nonzero-index
operator into a unit. -/
theorem real_index_zero_of_isUnit_add_compact (A K : H →L[ℝ] H)
    (hK : Compactness.IsCompactLinearMap K.toLinearMap) (hunit : IsUnit (A + K)) :
    ∃ h : IsFredholm A, fredholmIndex A h = 0 := by
  obtain ⟨hAK, hz⟩ := real_fredholm_index_zero_of_isUnit (A + K) hunit
  have hA := (isFredholm_add_compact_iff A K hK).mp hAK
  exact ⟨hA, (fredholmIndex_add_compact A K hK hA hAK).symm.trans hz⟩

/-- The resolvent test with the source's `T - z I` sign convention. -/
private theorem real_mem_spectrum_iff (T : H →L[ℝ] H) (z : ℝ) :
    z ∈ spectrum ℝ T ↔ ¬ IsUnit (T - z • (1 : H →L[ℝ] H)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  rw [← neg_sub (T : H →L[ℝ] H), IsUnit.neg_iff]

/-- The real Weyl formula, without separability or a complex structure. -/
theorem realWeylSpectrum_eq (T : H →L[ℝ] H) :
    realWeylSpectrum T = realEssentialSpectrum T ∪
      {z | ∃ h : IsFredholm (T - z • (1 : H →L[ℝ] H)),
        fredholmIndex (T - z • (1 : H →L[ℝ] H)) h ≠ 0} := by
  classical
  ext z
  let A := T - z • (1 : H →L[ℝ] H)
  have heq (K : H →L[ℝ] H) : T + K - z • (1 : H →L[ℝ] H) = A + K := by
    dsimp [A]
    abel
  change (z ∈ realWeylSpectrum T) ↔ (¬ IsFredholm A) ∨
    (∃ h : IsFredholm A, fredholmIndex A h ≠ 0)
  constructor
  · intro hz
    by_cases hA : IsFredholm A
    · right
      refine ⟨hA, ?_⟩
      intro hzero
      obtain ⟨F, hF, hunit⟩ := real_finite_rank_correction A hA hzero
      let := hF
      have hs := (mem_realWeylSpectrum T z).mp hz F (compact_of_finiteDimensional_range F)
      rw [real_mem_spectrum_iff, heq] at hs
      exact hs hunit
    · exact Or.inl hA
  · intro hz
    apply (mem_realWeylSpectrum T z).mpr
    intro K hK
    rw [real_mem_spectrum_iff, heq]
    intro hunit
    obtain ⟨hA, hzero⟩ := real_index_zero_of_isUnit_add_compact A K hK hunit
    rcases hz with hn | ⟨_, hi⟩
    · exact hn hA
    · exact hi hzero

end ExpandedFA.Fredholm
