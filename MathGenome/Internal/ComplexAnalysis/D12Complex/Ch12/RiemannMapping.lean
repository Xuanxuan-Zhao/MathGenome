import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.RiemannMapping
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.ExtremalOnto
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.SimplyConnectedCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.DiskAutomorphisms
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential

/-! Riemann mapping in the original weak holomorphy scope. Homotopy-Cauchy
supplies logarithms, whose half exponentials supply the square roots used
by the extremal construction. Disk automorphism rigidity proves uniqueness
of the normalized map on its domain. -/

noncomputable section
open Metric Set
open scoped Topology

namespace D12Complex.RiemannMapping

/-- Square roots constructed from the actual simply-connected logarithm
theorem, with exactly its topological and nonvanishing hypotheses. -/
lemma square_root_of_logarithm (Ω : Set ℂ) (hΩ : IsDomain Ω)
    (hsc : IsSimplyConnected Ω) (f : ℂ → ℂ) (hf : HolomorphicOn Ω f)
    (hne : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, HolomorphicOn Ω g ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  obtain ⟨L, hL, hexp⟩ := SimplyConnectedCalculus.exists_logarithm Ω f hΩ hsc hf hne
  refine ⟨fun z => E (L z / 2), ⟨hL.1, ?_⟩, ?_⟩
  · intro z hz
    exact (Exponential.hasDerivAt_E (L z / 2)).differentiableAt.comp z
      ((hL.2 z hz).div_const 2)
  · intro z hz
    calc
      E (L z / 2) ^ 2 = E (L z / 2 + L z / 2) := by
        rw [pow_two, Exponential.E_add]
      _ = E (L z) := by congr 1; ring
      _ = f z := hexp z hz

lemma normalized_pair (Ω : Set ℂ) (hΩ : IsDomain Ω)
    (hsc : IsSimplyConnected Ω) (hproper : Ω ≠ Set.univ) (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) :
    ∃ F G : ℂ → ℂ, BiholomorphicPair Ω (Metric.ball 0 1) F G ∧ F z₀ = 0 ∧
      ∃ t : ℝ, 0 < t ∧ deriv F z₀ = (t : ℂ) := by
  exact ExtremalOnto.normalized_biholomorphism Ω hΩ hproper
    (square_root_of_logarithm Ω hΩ hsc) z₀ hz₀

/-- Positive real basepoint derivatives remove the rotation ambiguity. -/
lemma normalized_pair_unique {Ω : Set ℂ} {z₀ : ℂ} {F Finv G Ginv : ℂ → ℂ}
    (hz₀ : z₀ ∈ Ω)
    (hF : BiholomorphicPair Ω (ball 0 1) F Finv)
    (hG : BiholomorphicPair Ω (ball 0 1) G Ginv)
    (hFzero : F z₀ = 0) (hGzero : G z₀ = 0)
    (hFpos : ∃ t : ℝ, 0 < t ∧ deriv F z₀ = (t : ℂ))
    (hGpos : ∃ t : ℝ, 0 < t ∧ deriv G z₀ = (t : ℂ)) :
    EqOn F G Ω := by
  rcases hF with ⟨hFhol, hFinvhol, hFm, hFinvm, hFl, hFr⟩
  rcases hG with ⟨hGhol, hGinvhol, hGm, hGinvm, hGl, hGr⟩
  have hpair : BiholomorphicPair (ball 0 1) (ball 0 1)
      (F ∘ Ginv) (G ∘ Finv) := by
    refine ⟨⟨isOpen_ball, fun z hz =>
        (hFhol.2 _ (hGinvm hz)).comp z (hGinvhol.2 z hz)⟩,
      ⟨isOpen_ball, fun z hz =>
        (hGhol.2 _ (hFinvm hz)).comp z (hFinvhol.2 z hz)⟩,
      hFm.comp hGinvm, hGm.comp hFinvm, ?_, ?_⟩
    · intro w hw
      simp only [Function.comp_apply, hFl (hGinvm hw), hGr hw]
    · intro w hw
      simp only [Function.comp_apply, hGl (hFinvm hw), hFr hw]
  have hGinvzero : Ginv 0 = z₀ := by simpa only [hGzero] using hGl hz₀
  have hzero : (F ∘ Ginv) 0 = 0 := by simp only [Function.comp_apply, hGinvzero, hFzero]
  obtain ⟨c, hc, hrotation⟩ := DiskAutomorphisms.rotation_of_pair_fix_zero hpair hzero
  have hfactor : EqOn F (fun z => c * G z) Ω := by
    intro z hz
    simpa only [Function.comp_apply, hGl hz] using hrotation (hGm hz)
  have hlocal : F =ᶠ[𝓝 z₀] (fun z => c * G z) := by
    filter_upwards [hFhol.1.mem_nhds hz₀] with z hz
    exact hfactor hz
  have hd : deriv F z₀ = c * deriv G z₀ :=
    (((hGhol.2 z₀ hz₀).hasDerivAt.const_mul c).congr_of_eventuallyEq hlocal).deriv
  obtain ⟨t, ht, htd⟩ := hFpos
  obtain ⟨s, hs, hsd⟩ := hGpos
  rw [htd, hsd] at hd
  have hts : t = s := by
    have hnorm := congrArg norm hd
    simpa [norm_mul, hc, abs_of_pos ht, abs_of_pos hs] using hnorm
  subst t
  have hc_one : c = 1 := by
    apply mul_right_cancel₀ (by exact_mod_cast (ne_of_gt hs) : (s : ℂ) ≠ 0)
    simpa using hd.symm
  intro z hz
  simpa only [hc_one, one_mul] using hfactor hz

/-- The normalized biholomorphism exists and is unique on its domain. -/
theorem normalized_riemann_mapping :
    Specs.D12Complex.Ch12.RiemannMapping.normalized_riemann_mapping_type := by
  intro Ω hΩ hsc hproper z₀ hz₀
  obtain ⟨F, Finv, hF, hFzero, hFpos⟩ :=
    normalized_pair Ω hΩ hsc hproper z₀ hz₀
  refine ⟨F, ⟨⟨Finv, hF⟩, hFzero, hFpos⟩, ?_⟩
  rintro G ⟨⟨Ginv, hG⟩, hGzero, hGpos⟩
  exact normalized_pair_unique hz₀ hG hF hGzero hFzero hGpos hFpos

end D12Complex.RiemannMapping
