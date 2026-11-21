import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.IdentityTheorem
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization

/-!
The identity theorem for weak holomorphy (paper.tex:1307–1321).
The upstream local holomorphy/analyticity bridge supplies actual power
series from complex differentiability on an open neighborhood. Mathlib's
analytic identity theorem then propagates the zero germ on a preconnected
set. Accumulation is translated using punctured neighborhoods, so the
value at the accumulation point alone never supplies the hypothesis.
-/

open Filter Set
open scoped Topology

namespace D12Complex.IdentityTheorem

private lemma analyticOnNhd_of_holomorphic {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) : AnalyticOnNhd ℂ f Ω := by
  intro a ha
  exact (LocalZeroFactorization.holomorphicNear_iff_analyticAt f a).mp ⟨Ω, ha, hf⟩

theorem identity_zero_of_accPt :
    Specs.D12Complex.Ch05.IdentityTheorem.identity_zero_of_accPt_type := by
  intro Ω f a hΩ hf ha hacc
  have hzeros : ∃ᶠ z in 𝓝[≠] a, f z = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono fun _ hz => hz.2
  exact (analyticOnNhd_of_holomorphic hf).eqOn_zero_of_preconnected_of_frequently_eq_zero
    hΩ.2.2 ha hzeros

theorem identity_of_accPt :
    Specs.D12Complex.Ch05.IdentityTheorem.identity_of_accPt_type := by
  intro Ω S f g a hΩ hf hg hS ha hacc heq
  have hdiff : HolomorphicOn Ω (fun z => f z - g z) :=
    ⟨hf.1, fun z hz => (hf.2 z hz).sub (hg.2 z hz)⟩
  have hacc' : AccPt a (𝓟 {z | z ∈ Ω ∧ f z - g z = 0}) :=
    hacc.mono (principal_mono.mpr fun z hz => ⟨hS hz, sub_eq_zero.mpr (heq hz)⟩)
  have hzero := identity_zero_of_accPt Ω (fun z => f z - g z) a hΩ hdiff ha hacc'
  exact fun z hz => sub_eq_zero.mp (hzero hz)

end D12Complex.IdentityTheorem
