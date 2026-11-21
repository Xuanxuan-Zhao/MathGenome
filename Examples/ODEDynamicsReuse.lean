import Examples.ODEDynamicsReuseSpecs
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace Examples.GenomeODEProbe

theorem zeroGronwallError : Examples.GenomeODEProbeSpecs.zeroGronwallError := by
  intro s T L u hST hL hcont hu hineq t ht
  have h := D13Unified.Ch05.Gronwall.constant_forward s T 0 L 0 u hST
    (le_refl 0) hL (le_refl 0) hcont hu
    (by simpa using hineq) t ht
  exact le_antisymm (by simpa using h) (hu t ht)

theorem orientationPreserved : Examples.GenomeODEProbeSpecs.orientationPreserved := by
  intro n I A X hA hX s hs hpos
  rcases D13Unified.Ch07.Liouville.real_constant_sign n I A X hA hX with hp | hn
  · exact hp
  · have hneg := hn s hs
    linarith

theorem dirichletPositiveGaps : Examples.GenomeODEProbeSpecs.dirichletPositiveGaps := by
  intro P
  obtain ⟨lam, phi, hphi, B, hmono, hlim, _⟩ := D13Unified.Ch10.Spectrum.spectrum P
  exact ⟨lam, hmono, hlim, fun n => hmono (Nat.lt_succ_self n)⟩

theorem realErgodicZeroMean : Examples.GenomeODEProbeSpecs.realErgodicZeroMean := by
  intro X _ T μ _ hpres herg f hf hmean
  obtain ⟨g, _, hae, _, _, _, _, hconst⟩ :=
    D13Unified.Ch19.Birkhoff.real_birkhoff T μ hpres f hf
  have hzero : g =ᵐ[μ] fun _ => 0 := by simpa only [hmean] using hconst herg
  filter_upwards [hae, hzero] with x hx hz
  simpa only [hz] using hx

theorem complexErgodicZeroMean : Examples.GenomeODEProbeSpecs.complexErgodicZeroMean := by
  intro X _ T μ _ hpres herg f hf hmean
  obtain ⟨g, _, hae, _, _, _, _, hconst⟩ :=
    D13Unified.Ch19.Birkhoff.complex_birkhoff T μ hpres f hf
  have hzero : g =ᵐ[μ] fun _ => 0 := by simpa only [hmean] using hconst herg
  filter_upwards [hae, hzero] with x hx hz
  simpa only [hz] using hx

theorem stableCycleWithLeastPeriod : Examples.GenomeODEProbeSpecs.stableCycleWithLeastPeriod := by
  intro μ ω hμ hω
  obtain ⟨A, hdom, hfield, hstable⟩ := D13Unified.Ch16.HopfPolarExample.stable_circle μ ω hμ hω
  exact ⟨A, hdom, hfield,
    (D13Unified.Ch16.HopfPolarExample.periodic_circle μ ω hμ hω).1, hstable⟩

end Examples.GenomeODEProbe
