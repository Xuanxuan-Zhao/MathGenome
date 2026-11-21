import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalHolomorphicInverse
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
The inverse at a noncritical point, covering both the early local inverse
corollary and the explicit later lemma. Cauchy regularity upgrades weak
holomorphy to a strict derivative; the complete normed-field inverse theorem
then supplies an open partial homeomorphism. We restrict its source to the
original open set and the nonzero-derivative set. The inverse derivative
theorem applies at every point of the resulting target, proving both
holomorphy and the reciprocal derivative formula there.
-/

noncomputable section
open Set
open scoped Topology

namespace D12Complex.LocalHolomorphicInverse

theorem local_holomorphic_inverse :
    Specs.D12Complex.Ch05.LocalHolomorphicInverse.local_holomorphic_inverse_type := by
  intro Ω f a hf ha hnonzero
  have hd : DifferentiableOn ℂ f Ω :=
    fun z hz => (hf.2 z hz).differentiableWithinAt
  have hstrict : HasStrictDerivAt f (deriv f a) a :=
    (hd.analyticAt (hf.1.mem_nhds ha)).hasStrictDerivAt
  have hc : ContinuousOn (deriv f) Ω := (hd.deriv hf.1).continuousOn
  let N : Set ℂ := Ω ∩ (deriv f) ⁻¹' ({0}ᶜ : Set ℂ)
  have hN : IsOpen N := hc.isOpen_inter_preimage hf.1 isClosed_singleton.isOpen_compl
  let e := (hstrict.hasStrictFDerivAt_equiv hnonzero).toOpenPartialHomeomorph f
  let e' := e.restrOpen N hN
  have he : (e' : ℂ → ℂ) = f := rfl
  have ha' : a ∈ e'.source :=
    ⟨(hstrict.hasStrictFDerivAt_equiv hnonzero).mem_toOpenPartialHomeomorph_source,
      ha, hnonzero⟩
  have hsource : e'.source ⊆ Ω := fun _ hz => hz.2.1
  have hnonzero' : ∀ z ∈ e'.source, deriv f z ≠ 0 := fun _ hz => hz.2.2
  have hinverse : ∀ w ∈ e'.target, HasDerivAt e'.symm (1 / deriv f (e'.symm w)) w := by
    intro w hw
    have hz := e'.map_target hw
    simpa only [he, one_div] using
      e'.hasDerivAt_symm hw (hnonzero' _ hz) (hf.2 _ (hsource hz)).hasDerivAt
  refine ⟨e'.source, e'.target, e'.symm, ha', ?_, hsource, ?_, hnonzero', ?_⟩
  · exact he ▸ e'.map_source ha'
  · refine ⟨⟨e'.open_source, fun z hz => hf.2 z (hsource hz)⟩,
      ⟨e'.open_target, fun w hw => (hinverse w hw).differentiableAt⟩,
      ?_, e'.mapsTo_symm, ?_, ?_⟩
    · simpa only [he] using e'.mapsTo
    · simpa only [he] using e'.leftInvOn
    · simpa only [he] using e'.rightInvOn
  · intro w hw
    exact ⟨hinverse w hw, (hinverse w hw).deriv⟩

end D12Complex.LocalHolomorphicInverse
