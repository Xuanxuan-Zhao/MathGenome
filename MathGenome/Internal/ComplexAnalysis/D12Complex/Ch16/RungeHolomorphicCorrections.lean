import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.RungeHolomorphicCorrections
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.RungeAllowedPoles
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.RationalInfinity

noncomputable section
open Set

namespace D12Complex.RungeHolomorphicCorrections
open Ch15
open Specs.D12Complex.Ch07.RationalInfinity.Objects

/-- The filled rational map has an ordinary holomorphic coordinate on any
open set containing none of its spherical poles. This includes cancellations
at roots of the displayed denominator. -/
theorem holomorphic_finiteCoordinate_extension
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (P Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (hfinite : ∀ z ∈ Ω, extension P Q (sphereFinite z) ≠ sphereInfty) :
    HolomorphicOn Ω (fun z => finiteCoordinate (extension P Q (sphereFinite z))) := by
  have hm : ScalarMeromorphicOn univ (extension P Q ∘ sphereFinite) :=
    (RationalInfinity.meromorphic_extension P Q hQ).1.2.1
  refine ⟨hΩ, fun z hz => ?_⟩
  exact (scalarMeromorphicOn_finite_analytic univ
    (extension P Q ∘ sphereFinite) hm z (mem_univ z) (hfinite z hz)).differentiableAt

/-- Runge with all allowed poles outside Ω yields an actual holomorphic correction. -/
theorem holomorphic_correction :
    Specs.D12Complex.Ch16.RungeHolomorphicCorrections.holomorphic_correction_type := by
  intro Ω K U q hΩ hK hKΩ hholes hU hKU hq ε hε
  have hallowed : (sphereFinite '' Ω)ᶜ ⊆ (sphereFinite '' K)ᶜ := by
    intro p hp hpk
    exact hp (image_mono hKΩ hpk)
  obtain ⟨P, Q, hQ, hpoles, _, herror, _⟩ :=
    RungeAllowedPoles.runge_allowed_poles K U q (sphereFinite '' Ω)ᶜ
      hK hU hKU hq hallowed hholes ε hε
  have hfinite : ∀ z ∈ Ω, extension P Q (sphereFinite z) ≠ sphereInfty := by
    intro z hz hinfty
    exact hpoles (sphereFinite z) hinfty ⟨z, hz, rfl⟩
  exact ⟨_, holomorphic_finiteCoordinate_extension Ω hΩ P Q hQ hfinite, herror⟩

/-- Choice of the corrections for arbitrary positive stagewise tolerances. -/
theorem holomorphic_corrections :
    Specs.D12Complex.Ch16.RungeHolomorphicCorrections.holomorphic_corrections_type := by
  intro Ω K q ε hΩ hK hq hε
  have hex (n : ℕ) : ∃ r : ℂ → ℂ,
      HolomorphicOn Ω r ∧ ∀ z ∈ K n, ‖q n z - r z‖ < ε n := by
    obtain ⟨U, hU, hKU, hqn⟩ := hq n
    exact holomorphic_correction Ω (K n) U (q n) hΩ (hK.1 n).1
      (hK.1 n).2.1 (hK.1 n).2.2.1 hU hKU hqn (ε n) (hε n)
  choose r hr he using hex
  exact ⟨r, hr, he⟩

end D12Complex.RungeHolomorphicCorrections
