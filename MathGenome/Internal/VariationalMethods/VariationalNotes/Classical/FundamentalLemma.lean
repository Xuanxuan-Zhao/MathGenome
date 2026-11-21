import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.FundamentalLemma

open MeasureTheory Set Filter
open scoped ContDiff

namespace VariationalNotes.Classical

/-- A locally integrable scalar function annihilating all smooth tests vanishes a.e.
Only the restriction to the open interval is used. -/
theorem fundamentalLemmaAE :
  ∀ (a b : ℝ), a < b → ∀ (h : ℝ → ℝ),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, h t * φ t = 0) →
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t = 0 := by
  intro a b _hab h hh htest
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hh
  intro φ hφ hc hs
  have hz : ∀ t, t ∉ Ioo a b → h t * φ t = 0 := by
    intro t ht
    have hzero : φ t = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => ht (hs hmem))
    simp [hzero]
  simpa only [smul_eq_mul, mul_comm] using
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm.trans (htest φ hφ hc hs)

/-- Continuity upgrades the almost-everywhere conclusion to every interior point. -/
theorem fundamentalLemmaContinuous :
  ∀ (a b : ℝ), a < b → ∀ (h : ℝ → ℝ),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, h t * φ t = 0) →
    ContinuousOn h (Ioo a b) → ∀ t ∈ Ioo a b, h t = 0 := by
  intro a b hab h hh htest hcont
  exact Measure.eqOn_open_of_ae_eq (fundamentalLemmaAE a b hab h hh htest)
    isOpen_Ioo hcont continuousOn_const

/-- The Euclidean vector version, with vector tests and the Euclidean pairing.
Testing along each coordinate axis reduces it to the scalar fundamental lemma. -/
theorem fundamentalLemmaVectorAE :
  ∀ (m : ℕ) (a b : ℝ), a < b → ∀ (h : ℝ → EuclideanSpace ℝ (Fin m)),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → EuclideanSpace ℝ (Fin m), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, inner ℝ (h t) (φ t) = 0) →
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t = 0 := by
  intro m a b hab h hh htest
  have hcoord : ∀ i : Fin m, ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t i = 0 := by
    intro i
    apply fundamentalLemmaAE a b hab (fun t => h t i)
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).locallyIntegrableOn_comp hh
    intro φ hφ hc hs
    let e : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
    have hv : ContDiff ℝ ∞ (fun t => φ t • e) := hφ.smul contDiff_const
    have hvc : HasCompactSupport (fun t => φ t • e) := hc.smul_right
    have hvs : tsupport (fun t => φ t • e) ⊆ Ioo a b :=
      (tsupport_smul_subset_left φ (fun _ => e)).trans hs
    have ht := htest (fun t => φ t • e) hv hvc hvs
    simpa [e, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm] using ht
  filter_upwards [ae_all_iff.mpr hcoord] with t ht
  ext i
  exact ht i

/-- The pointwise Euclidean vector conclusion for continuous functions. -/
theorem fundamentalLemmaVectorContinuous :
  ∀ (m : ℕ) (a b : ℝ), a < b → ∀ (h : ℝ → EuclideanSpace ℝ (Fin m)),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → EuclideanSpace ℝ (Fin m), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, inner ℝ (h t) (φ t) = 0) →
    ContinuousOn h (Ioo a b) → ∀ t ∈ Ioo a b, h t = 0 := by
  intro m a b hab h hh htest hcont
  exact Measure.eqOn_open_of_ae_eq (fundamentalLemmaVectorAE m a b hab h hh htest)
    isOpen_Ioo hcont continuousOn_const

end VariationalNotes.Classical
