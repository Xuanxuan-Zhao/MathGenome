import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.UnivalentHolomorphicInverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalMappingNormalForm
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.OpenMapping
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential

noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.UnivalentHolomorphicInverse

/-- An injective function on an open plane set cannot have a constant germ. -/
lemma not_constant_germ {Ω : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hi : InjOn f Ω) {a : ℂ} (ha : a ∈ Ω) :
    ¬ (∀ᶠ z in 𝓝 a, f z = f a) := by
  intro h
  have hΩ' : ∀ᶠ z in 𝓝[≠] a, z ∈ Ω :=
    mem_nhdsWithin_of_mem_nhds (hΩ.mem_nhds ha)
  have heq : ∀ᶠ z in 𝓝[≠] a, f z = f a := h.filter_mono nhdsWithin_le_nhds
  obtain ⟨z, hz, he, hne⟩ := (hΩ'.and (heq.and self_mem_nhdsWithin)).exists
  exact hne (hi hz ha he)

/-- Exact fibre counting rules out m > 1. Differentiating the power coordinate
and its inverse then gives the nonzero derivative, without assuming it. -/
theorem injective_holomorphic_deriv_ne_zero :
    Specs.D12Complex.Ch05.UnivalentHolomorphicInverse.injective_holomorphic_deriv_ne_zero_type := by
  intro Ω f _ hf hi a ha
  obtain ⟨m, hm, r, hr, U, φ, ψ, haU, hUΩ, hp, hφ0, hform,
      _, hcount, _, _⟩ :=
    LocalMappingNormalForm.local_mapping_normal_form Ω f a hf ha
      (not_constant_germ hf.1 hi ha)
  have hball : ∀ᶠ w in 𝓝[≠] (f a), w ∈ Metric.ball (f a) (r ^ m) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (f a) (pow_pos hr m))
  obtain ⟨w, hw, hwne⟩ := (hball.and self_mem_nhdsWithin).exists
  obtain ⟨hfin, hcard⟩ := hcount w hw hwne
  have hmle : m ≤ 1 := by
    rw [← hcard]
    exact (Set.ncard_le_one hfin).mpr (fun x hx y hy =>
      hi (hUΩ hx.1) (hUΩ hy.1) (hx.2.trans hy.2.symm))
  have hm1 : m = 1 := Nat.le_antisymm hmle hm
  have hfg : f =ᶠ[𝓝 a] (fun z => φ z + f a) := by
    filter_upwards [hp.1.1.mem_nhds haU] with z hz
    have he := hform z hz
    rw [hm1, pow_one] at he
    exact (sub_eq_iff_eq_add.mp he)
  have hdφ := (hp.1.2 a haU).hasDerivAt
  have hdf : HasDerivAt f (deriv φ a) a :=
    (hdφ.add_const (f a)).congr_of_eventuallyEq hfg
  have hdψ := (hp.2.1.2 (φ a) (hp.2.2.1 haU)).hasDerivAt
  have hl : (fun z => ψ (φ z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hp.1.1.mem_nhds haU] with z hz
    exact hp.2.2.2.2.1 hz
  have hprod : deriv ψ (φ a) * deriv φ a = 1 := by
    simpa using ((hdψ.comp a hdφ).congr_of_eventuallyEq hl.symm).deriv.symm
  rw [hdf.deriv]
  intro hzero
  rw [hzero, mul_zero] at hprod
  exact zero_ne_one hprod

lemma not_constant_on_domain {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsDomain Ω) (hf : HolomorphicOn Ω f) (hi : InjOn f Ω) :
    ¬ ∃ c : ℂ, ∀ z ∈ Ω, f z = c := by
  rintro ⟨c, hc⟩
  obtain ⟨a, ha⟩ := hΩ.1
  apply not_constant_germ hf.1 hi ha
  filter_upwards [hf.1.mem_nhds ha] with z hz
  exact (hc z hz).trans (hc a ha).symm

theorem injective_holomorphic_image_open :
    Specs.D12Complex.Ch05.UnivalentHolomorphicInverse.injective_holomorphic_image_open_type := by
  intro Ω f hΩ hf hi
  exact OpenMapping.image_open_of_nonconstant Ω f hΩ hf
    (not_constant_on_domain hΩ hf hi) Ω hf.1 Subset.rfl

theorem injective_holomorphic_inverse :
    Specs.D12Complex.Ch05.UnivalentHolomorphicInverse.injective_holomorphic_inverse_type := by
  intro Ω f hΩ hf hi
  let g := Function.invFunOn f Ω
  have hgmap : MapsTo g (f '' Ω) Ω := (surjOn_image f Ω).mapsTo_invFunOn
  have hl : LeftInvOn g f Ω := hi.leftInvOn_invFunOn
  have hr : RightInvOn g f (f '' Ω) := (surjOn_image f Ω).rightInvOn_invFunOn
  have hd : ∀ w ∈ f '' Ω, HasDerivAt g (1 / deriv f (g w)) w := by
    intro w hw
    have ha := hgmap hw
    obtain ⟨U, V, h, haU, hfaV, hUΩ, hp, _, hh⟩ :=
      LocalHolomorphicInverse.local_holomorphic_inverse Ω f (g w) hf ha
        (injective_holomorphic_deriv_ne_zero Ω f hΩ hf hi (g w) ha)
    have hwV : w ∈ V := hr hw ▸ hfaV
    have he : g =ᶠ[𝓝 w] h := by
      filter_upwards [hp.2.1.1.mem_nhds hwV] with v hv
      have hhU := hp.2.2.2.1 hv
      have hvimage : v ∈ f '' Ω := ⟨h v, hUΩ hhU, hp.2.2.2.2.2 hv⟩
      exact hi (hgmap hvimage) (hUΩ hhU) ((hr hvimage).trans (hp.2.2.2.2.2 hv).symm)
    have hd' := (hh w hwV).1.congr_of_eventuallyEq he
    rwa [← he.self_of_nhds] at hd'
  refine ⟨g, ⟨hf, ⟨injective_holomorphic_image_open Ω f hΩ hf hi,
    fun w hw => (hd w hw).differentiableAt⟩, mapsTo_image f Ω, hgmap, hl, hr⟩,
    fun w hw => ⟨hd w hw, (hd w hw).deriv⟩⟩

theorem injective_holomorphic_homeomorph :
    Specs.D12Complex.Ch05.UnivalentHolomorphicInverse.injective_holomorphic_homeomorph_type := by
  intro Ω f hΩ hf hi
  obtain ⟨g, hp, _⟩ := injective_holomorphic_inverse Ω f hΩ hf hi
  let e : Ω ≃ₜ (f '' Ω) :=
    { toFun := fun z => ⟨f z, mem_image_of_mem f z.property⟩
      invFun := fun w => ⟨g w, hp.2.2.2.1 w.property⟩
      left_inv := fun z => Subtype.ext (hp.2.2.2.2.1 z.property)
      right_inv := fun w => Subtype.ext (hp.2.2.2.2.2 w.property)
      continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp (show ContinuousOn f Ω from fun z hz =>
        (hf.2 z hz).continuousAt.continuousWithinAt)).subtype_mk _
      continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp (show ContinuousOn g (f '' Ω) from fun w hw =>
        (hp.2.1.2 w hw).continuousAt.continuousWithinAt)).subtype_mk _ }
  exact ⟨e, fun _ => rfl⟩

theorem exponential_local_not_global :
    Specs.D12Complex.Ch05.UnivalentHolomorphicInverse.exponential_local_not_global_type := by
  have hp0 : (2 * Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hshift : ∀ z : ℂ, E (z + (2 * Real.pi : ℂ) * Complex.I) = E z := by
    intro z
    rw [Exponential.E_eq_exp]
    exact Complex.exp_periodic z
  have hne : ∀ z : ℂ, z + (2 * Real.pi : ℂ) * Complex.I ≠ z := by
    intro z he
    exact hp0 (add_left_cancel (he.trans (add_zero z).symm))
  refine ⟨Exponential.holomorphicOn_E, ?_, fun z => ⟨hshift z, hne z⟩, ?_⟩
  · intro z
    rw [Exponential.deriv_E]
    exact Exponential.E_ne_zero z
  · intro hi
    exact hne 0 (hi (hshift 0))

end D12Complex.UnivalentHolomorphicInverse
