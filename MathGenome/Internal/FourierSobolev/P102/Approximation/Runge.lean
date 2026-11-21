import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.Runge
import MathGenome.ComplexAnalysis.Topics.D12Complex.Ch15

/-! P1-02, Theorem 1.12: specialize the published full spherical Runge theorem.
The independent statement retains the canonical filled rational extension,
including all poles at infinity, and permits empty K and disconnected V. -/
noncomputable section

namespace P102.Approximation.Runge

/-- Bridge from weak holomorphy to the `DifferentiableOn` interface used here. -/
theorem holomorphicOn_iff_differentiableOn :
    Specs.P102.Approximation.Runge.holomorphicOn_iff_differentiableOn_type := by
  intro V f hV
  constructor
  · intro hf z hz
    exact (hf.2 z hz).differentiableWithinAt
  · intro hf
    exact ⟨hV, fun z hz => (hf z hz).differentiableAt (hV.mem_nhds hz)⟩

/-- Rational approximation with prescribed actual spherical poles. -/
theorem runge_spherical_poles :
    Specs.P102.Approximation.Runge.runge_spherical_poles_type := by
  intro K V f A hK hV hKV hf hA hmeet ε hε
  exact D12Complex.RungeAllowedPoles.runge_allowed_poles K V f A hK hV hKV
    ((holomorphicOn_iff_differentiableOn V f hV).mpr hf) hA hmeet ε hε

end P102.Approximation.Runge
