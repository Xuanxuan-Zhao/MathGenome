import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GreenConformalInvariance
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CanonicalGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.GreenSymmetry
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.GreenRegularBoundary
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Conformal invariance uses normalized logarithmic poles and leastness,
without any boundary extension of a biholomorphism. The last theorem assembles
all assertions of paper.tex:2681–2691 for the canonical representative. -/
noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology

namespace D12Complex

lemma biholomorphic_deriv_ne_zero {Ω Ω' : Set ℂ} {F G : ℂ → ℂ}
    (h : BiholomorphicPair Ω Ω' F G) {a : ℂ} (ha : a ∈ Ω) :
    deriv F a ≠ 0 := by
  have hcomp := (h.2.1.2 (F a) (h.2.2.1 ha)).hasDerivAt.comp a (h.1.2 a ha).hasDerivAt
  have hid : (G ∘ F) =ᶠ[𝓝 a] id :=
    eventually_of_mem (h.1.1.mem_nhds ha) (fun z hz => h.2.2.2.2.1 hz)
  have hprod : deriv G (F a) * deriv F a = 1 :=
    (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod

lemma biholomorphic_local_factor {Ω Ω' : Set ℂ} {F G : ℂ → ℂ}
    (h : BiholomorphicPair Ω Ω' F G) {a : ℂ} (ha : a ∈ Ω) :
    ∃ U : Set ℂ, ∃ q : ℂ → ℂ, a ∈ U ∧ U ⊆ Ω ∧ HolomorphicOn U q ∧
      (∀ z ∈ U, q z ≠ 0) ∧ ∀ z ∈ U, F z - F a = (z - a) * q z := by
  let q := dslope F a
  have hdiff : DifferentiableOn ℂ F Ω :=
    fun z hz => (h.1.2 z hz).differentiableWithinAt
  have hq : DifferentiableOn ℂ q Ω :=
    (Complex.differentiableOn_dslope (h.1.1.mem_nhds ha)).mpr hdiff
  let U := Ω ∩ q ⁻¹' ({0}ᶜ : Set ℂ)
  have hU : IsOpen U :=
    hq.continuousOn.isOpen_inter_preimage h.1.1 isClosed_singleton.isOpen_compl
  refine ⟨U, q, ⟨ha, ?_⟩, inter_subset_left, ⟨hU, ?_⟩, ?_, ?_⟩
  · change q a ≠ 0
    simpa [q] using biholomorphic_deriv_ne_zero h ha
  · intro z hz
    exact (hq z hz.1).differentiableAt (h.1.1.mem_nhds hz.1)
  · intro z hz
    exact hz.2
  · intro z hz
    simpa only [q, smul_eq_mul] using (sub_smul_dslope F a z).symm

end D12Complex

namespace D12Complex.GreenConformal

lemma harmonic_log_norm_holomorphic {U : Set ℂ} {q : ℂ → ℂ}
    (hq : HolomorphicOn U q) (hn : ∀ z ∈ U, q z ≠ 0) :
    HarmonicOn U (fun z => Real.log ‖q z‖) := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hq.1).mpr
  intro z hz
  have hd : DifferentiableOn ℂ q U := fun w hw => (hq.2 w hw).differentiableWithinAt
  exact (hd.analyticAt (hq.1.mem_nhds hz)).harmonicAt_log_norm (hn z hz)

lemma normalized_pole_pullback_of_factorization
    {Ω Ω' U : Set ℂ} {F G q : ℂ → ℂ} {a : ℂ} {v : ℂ → ℝ}
    (hbi : BiholomorphicPair Ω Ω' F G) (ha : a ∈ Ω)
    (haU : a ∈ U) (hUΩ : U ⊆ Ω) (hq : HolomorphicOn U q)
    (hn : ∀ z ∈ U, q z ≠ 0)
    (hfac : ∀ z ∈ U, F z - F a = (z - a) * q z)
    (hp : HasNormalizedLogPole Ω' (F a) v) :
    HasNormalizedLogPole Ω a (v ∘ F) := by
  obtain ⟨r, hr, hrΩ, H, hH, hHeq⟩ := hp
  have hFc : ContinuousOn F U := fun z hz =>
    (hbi.1.2 z (hUΩ hz)).continuousAt.continuousWithinAt
  have hV : IsOpen (U ∩ F ⁻¹' ball (F a) r) :=
    hFc.isOpen_inter_preimage hq.1 isOpen_ball
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV a ⟨haU, mem_ball_self hr⟩
  have hsU : ball a s ⊆ U := fun z hz => (hsV hz).1
  have hsF : MapsTo F (ball a s) (ball (F a) r) := fun z hz => (hsV hz).2
  have hFs : HolomorphicOn (ball a s) F :=
    ⟨isOpen_ball, fun z hz => hbi.1.2 z (hUΩ (hsU hz))⟩
  have hcomp : HarmonicOn (ball a s) (H ∘ F) :=
    HarmonicFoundation.harmonicOn_comp_holomorphic _ _ _ _ hH hFs hsF
  have hlog : HarmonicOn (ball a s) (fun z => Real.log ‖q z‖) :=
    HarmonicRemovable.harmonicOn_mono (harmonic_log_norm_holomorphic hq hn)
      isOpen_ball hsU
  refine ⟨s, hs, fun z hz => hUΩ (hsU hz),
    fun z => H (F z) - Real.log ‖q z‖,
    HarmonicRemovable.harmonicOn_sub hcomp hlog, ?_⟩
  intro z hz
  have hza : z ≠ a := hz.2
  have hFza : F z ≠ F a := by
    intro he
    have hinj : InjOn F Ω := (biholomorphicPair_bijOn Ω Ω' F G hbi).1.2.1
    exact hza (hinj (hUΩ (hsU hz.1)) ha he)
  have hHval := hHeq ⟨hsF hz.1, hFza⟩
  dsimp only at hHval
  have hlogfac : Real.log ‖F z - F a‖ =
      Real.log ‖z - a‖ + Real.log ‖q z‖ := by
    rw [hfac z (hsU hz.1), norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza))
        (norm_ne_zero_iff.mpr (hn z (hsU hz.1)))]
  simp only [Function.comp_apply]
  rw [hHval, hlogfac]
  ring

lemma positive_green_pullback_of_factorization
    {Ω Ω' U : Set ℂ} {F G q : ℂ → ℂ} {a : ℂ} {v : ℂ → ℝ}
    (hbi : BiholomorphicPair Ω Ω' F G) (ha : a ∈ Ω)
    (haU : a ∈ U) (hUΩ : U ⊆ Ω) (hq : HolomorphicOn U q)
    (hn : ∀ z ∈ U, q z ≠ 0)
    (hfac : ∀ z ∈ U, F z - F a = (z - a) * q z)
    (hv : IsPositiveGreen Ω' (F a) v) :
    IsPositiveGreen Ω a (v ∘ F) := by
  have hmap : MapsTo F (Ω \ {a}) (Ω' \ {F a}) := by
    intro z hz
    refine ⟨hbi.2.2.1 hz.1, ?_⟩
    intro he
    have hinj : InjOn F Ω := (biholomorphicPair_bijOn Ω Ω' F G hbi).1.2.1
    exact hz.2 (hinj hz.1 ha he)
  refine ⟨HarmonicFoundation.harmonicOn_comp_holomorphic _ _ _ _ hv.1
    ⟨hbi.1.1.sdiff isClosed_singleton, fun z hz => hbi.1.2 z hz.1⟩ hmap,
    normalized_pole_pullback_of_factorization hbi ha haU hUΩ hq hn hfac hv.2.1, ?_⟩
  intro z hz
  exact hv.2.2 (F z) (hmap hz)

end D12Complex.GreenConformal

namespace D12Complex.GreenConformalInvariance

lemma positive_green_pullback {Ω V : Set ℂ} {F G : ℂ → ℂ} {a : ℂ}
    {v : ℂ → ℝ} (hF : BiholomorphicPair Ω V F G) (ha : a ∈ Ω)
    (hv : IsPositiveGreen V (F a) v) : IsPositiveGreen Ω a (v ∘ F) := by
  obtain ⟨U, q, haU, hUΩ, hq, hqn, hfac⟩ := biholomorphic_local_factor hF ha
  exact GreenConformal.positive_green_pullback_of_factorization hF ha haU hUΩ hq hqn hfac hv

/-- Leastness is applied to the forward and inverse pullbacks. Only the
interior holomorphic inverse identities are used. -/
theorem canonical_green_conformal :
    Specs.D12Complex.Ch14.GreenConformalInvariance.canonical_green_conformal_type := by
  intro Ω V F hΩ hΩb hV hVb hF a ha z hz
  change canonicalGreen V (F a) (F z) = canonicalGreen Ω a z
  obtain ⟨G, hFG⟩ := hF
  have hGF : BiholomorphicPair V Ω G F :=
    ⟨hFG.2.1, hFG.1, hFG.2.2.2.1, hFG.2.2.1,
      hFG.2.2.2.2.2, hFG.2.2.2.2.1⟩
  have hFa : F a ∈ V := hFG.2.2.1 ha
  have hFz : F z ∈ V \ {F a} := by
    refine ⟨hFG.2.2.1 hz.1, ?_⟩
    intro he
    exact hz.2 ((biholomorphicPair_bijOn Ω V F G hFG).1.2.1 hz.1 ha he)
  have hg := CanonicalGreen.canonical_green Ω a hΩ hΩb ha
  have hg' := CanonicalGreen.canonical_green V (F a) hV hVb hFa
  change IsLeastPositiveGreen Ω a (canonicalGreen Ω a) at hg
  change IsLeastPositiveGreen V (F a) (canonicalGreen V (F a)) at hg'
  have hpull := positive_green_pullback hFG ha hg'.1
  have hpull' : IsPositiveGreen V (F a) (canonicalGreen Ω a ∘ G) := by
    have hh : IsPositiveGreen Ω (G (F a)) (canonicalGreen Ω a) := by
      rw [hFG.2.2.2.2.1 ha]
      exact hg.1
    exact positive_green_pullback hGF hFa hh
  apply le_antisymm
  · have hle := hg'.2 _ hpull' (F z) hFz
    simpa only [Function.comp_apply, hFG.2.2.2.2.1 hz.1] using hle
  · exact hg.2 _ hpull z hz

/-- All assertions of d12:14-07 for the same canonical Green function. -/
theorem green_function_package :
    Specs.D12Complex.Ch14.GreenConformalInvariance.green_function_package_type := by
  intro Ω hΩ hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact CanonicalGreen.canonical_green Ω a hΩ hb ha
  · intro a ha b hb' hab
    exact GreenSymmetry.canonical_green_symmetry Ω a b hΩ hb ha hb' hab
  · intro V F hV hVb hF a ha z hz
    exact canonical_green_conformal Ω V F hΩ hb hV hVb hF a ha z hz
  · intro a ha ξ hξ
    exact GreenRegularBoundary.regular_point_limit Ω a ξ hΩ hb ha hξ
  · intro hreg a ha
    have he := GreenRegularBoundary.zero_extension Ω a hΩ hb ha hreg
    exact ⟨he.1, he.2.1, he.2.2, RegularGreen.correction_solution hΩ hb hreg ha,
      GreenRegularBoundary.regular_domain_identification Ω a hΩ hb ha hreg⟩

end D12Complex.GreenConformalInvariance
