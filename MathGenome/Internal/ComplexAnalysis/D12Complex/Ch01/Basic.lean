import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Representation bridges for the canonical definitions in the independent Basic
Spec. Candidate-owned exports below verify their exact expected values.
The bridges use elementary differentiation and metric topology only.
In particular, no analyticity or continuity of the derivative is assumed to
identify weak holomorphy with the punctured increment definition.
-/

open scoped Topology

/-!
The public canonical definitions live in the independent Spec so downstream
Specs can reuse them. These candidate-owned definition exports carry the
expected type/value bindings. Each is an alias of the corresponding public
object, so no separate notion is introduced.
-/
namespace D12Complex.Basic

abbrev IsDomain : Specs.D12Complex.Ch01.Basic.IsDomain_type :=
  _root_.D12Complex.IsDomain

abbrev PuncturedLimitWithin : Specs.D12Complex.Ch01.Basic.PuncturedLimitWithin_type :=
  _root_.D12Complex.PuncturedLimitWithin

abbrev PuncturedLimit : Specs.D12Complex.Ch01.Basic.PuncturedLimit_type :=
  _root_.D12Complex.PuncturedLimit

abbrev ContinuousWithinAtPoint : Specs.D12Complex.Ch01.Basic.ContinuousWithinAtPoint_type :=
  _root_.D12Complex.ContinuousWithinAtPoint

abbrev ContinuousAtPoint : Specs.D12Complex.Ch01.Basic.ContinuousAtPoint_type :=
  _root_.D12Complex.ContinuousAtPoint

abbrev HasComplexDerivativeAt : Specs.D12Complex.Ch01.Basic.HasComplexDerivativeAt_type :=
  _root_.D12Complex.HasComplexDerivativeAt

abbrev ComplexDifferentiableAt : Specs.D12Complex.Ch01.Basic.ComplexDifferentiableAt_type :=
  _root_.D12Complex.ComplexDifferentiableAt

abbrev HolomorphicOn : Specs.D12Complex.Ch01.Basic.HolomorphicOn_type :=
  _root_.D12Complex.HolomorphicOn

abbrev C1HolomorphicOn : Specs.D12Complex.Ch01.Basic.C1HolomorphicOn_type :=
  _root_.D12Complex.C1HolomorphicOn

abbrev PowerSeriesAnalyticAt : Specs.D12Complex.Ch01.Basic.PowerSeriesAnalyticAt_type :=
  _root_.D12Complex.PowerSeriesAnalyticAt

abbrev PowerSeriesAnalyticOn : Specs.D12Complex.Ch01.Basic.PowerSeriesAnalyticOn_type :=
  _root_.D12Complex.PowerSeriesAnalyticOn

abbrev BiholomorphicPair : Specs.D12Complex.Ch01.Basic.BiholomorphicPair_type :=
  _root_.D12Complex.BiholomorphicPair

abbrev IsBiholomorphism : Specs.D12Complex.Ch01.Basic.IsBiholomorphism_type :=
  _root_.D12Complex.IsBiholomorphism

abbrev ConformalOn : Specs.D12Complex.Ch01.Basic.ConformalOn_type :=
  _root_.D12Complex.ConformalOn

abbrev ConformalAt : Specs.D12Complex.Ch01.Basic.ConformalAt_type :=
  _root_.D12Complex.ConformalAt

end D12Complex.Basic

namespace D12Complex

theorem isDomain_iff (Ω : Set ℂ) : IsDomain Ω ↔ IsOpen Ω ∧ IsConnected Ω := by
  simp only [IsDomain, IsConnected]
  tauto

theorem puncturedLimitWithin_iff_tendsto (s : Set ℂ) (f : ℂ → ℂ) (a L : ℂ) :
    PuncturedLimitWithin s f a L ↔ Filter.Tendsto f (𝓝[s \ {a}] a) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [dist_eq_norm]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, fun z hz hza => ?_⟩
    exact hd z hz.1 (norm_pos_iff.mpr (sub_ne_zero.mpr hz.2)) hza
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, fun z hz hpos hza => ?_⟩
    exact hd ⟨hz, sub_ne_zero.mp (norm_pos_iff.mp hpos)⟩ hza

theorem continuousWithinAtPoint_iff (s : Set ℂ) (f : ℂ → ℂ) (a : ℂ) :
    ContinuousWithinAtPoint s f a ↔ ContinuousWithinAt f s a := by
  simp only [ContinuousWithinAtPoint, Metric.continuousWithinAt_iff, dist_eq_norm]

theorem continuousAtPoint_iff (f : ℂ → ℂ) (a : ℂ) :
    ContinuousAtPoint f a ↔ ContinuousAt f a := by
  rw [ContinuousAtPoint, continuousWithinAtPoint_iff, continuousWithinAt_univ]

theorem hasComplexDerivativeAt_iff (f : ℂ → ℂ) (A a : ℂ) :
    HasComplexDerivativeAt f A a ↔ HasDerivAt f A a := by
  rw [HasComplexDerivativeAt, PuncturedLimit, puncturedLimitWithin_iff_tendsto,
    hasDerivAt_iff_tendsto_slope_zero]
  simp only [Set.compl_eq_univ_sdiff, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem complexDifferentiableAt_iff (f : ℂ → ℂ) (a : ℂ) :
    ComplexDifferentiableAt f a ↔ DifferentiableAt ℂ f a := by
  constructor
  · rintro ⟨A, hA⟩
    exact ((hasComplexDerivativeAt_iff f A a).mp hA).differentiableAt
  · intro h
    exact ⟨deriv f a, (hasComplexDerivativeAt_iff f (deriv f a) a).mpr h.hasDerivAt⟩

theorem holomorphicOn_iff_incrementLimit (Ω : Set ℂ) (f : ℂ → ℂ) :
    HolomorphicOn Ω f ↔ IsOpen Ω ∧ ∀ a ∈ Ω, ComplexDifferentiableAt f a := by
  simp only [HolomorphicOn, complexDifferentiableAt_iff]

theorem holomorphicOn_iff_differentiableOn (Ω : Set ℂ) (f : ℂ → ℂ) :
    HolomorphicOn Ω f ↔ IsOpen Ω ∧ DifferentiableOn ℂ f Ω := by
  constructor
  · rintro ⟨hΩ, hf⟩
    exact ⟨hΩ, fun a ha => (hf a ha).differentiableWithinAt⟩
  · rintro ⟨hΩ, hf⟩
    exact ⟨hΩ, fun a ha => hf.differentiableAt (hΩ.mem_nhds ha)⟩

theorem biholomorphicPair_bijOn (Ω V : Set ℂ) (f g : ℂ → ℂ)
    (h : BiholomorphicPair Ω V f g) : Set.BijOn f Ω V ∧ Set.BijOn g V Ω := by
  rcases h with ⟨_, _, hf, hg, hleft, hright⟩
  exact ⟨⟨hf, hleft.injOn, hright.surjOn hg⟩,
    ⟨hg, hright.injOn, hleft.surjOn hf⟩⟩

theorem isBiholomorphism_iff (Ω V : Set ℂ) (f : ℂ → ℂ) :
    IsBiholomorphism Ω V f ↔
      HolomorphicOn Ω f ∧ Set.BijOn f Ω V ∧ ∃ g : ℂ → ℂ,
        HolomorphicOn V g ∧ Set.MapsTo g V Ω ∧
        Set.LeftInvOn g f Ω ∧ Set.RightInvOn g f V := by
  constructor
  · rintro ⟨g, h⟩
    exact ⟨h.1, (biholomorphicPair_bijOn Ω V f g h).1,
      g, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  · rintro ⟨hf, hbij, g, hg, hmaps, hl, hr⟩
    exact ⟨g, hf, hg, hbij.mapsTo, hmaps, hl, hr⟩

end D12Complex
