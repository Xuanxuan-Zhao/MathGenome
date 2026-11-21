import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import Mathlib.Topology.Homeomorph.Defs

/-! Independent statements for paper.tex:3146–3163. All parameter intervals are
normalized to [0,1]. Germs are the canonical neighborhood quotients. The two
half-intervals in concatenation are rescaled affinely; no existence of a
continuation on an arbitrary path is asserted. -/
open scoped Topology
noncomputable section
namespace D12Complex.ContinuationOperations

/-- Continuous clamped parameter on the first half, equal to 1 afterwards. -/
def leftParam (t : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (2 * (t : ℝ))

/-- Continuous clamped parameter on the second half, equal to 0 beforehand. -/
def rightParam (t : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)

/-- The usual concatenation, traversing each given path in half the time. -/
def concatPath (γ δ : unitInterval → ℂ) (t : unitInterval) : ℂ :=
  if (t : ℝ) ≤ 1 / 2 then γ (leftParam t) else δ (rightParam t)

/-- The given germ families on the two rescaled halves. -/
def concatFamily {γ δ : unitInterval → ℂ} (Φ : GermFamily γ) (Ψ : GermFamily δ) :
    GermFamily (concatPath γ δ) := fun t => by
  unfold concatPath
  split_ifs
  · exact Φ (leftParam t)
  · exact Ψ (rightParam t)

end D12Complex.ContinuationOperations

namespace Specs.D12Complex.Ch19.ContinuationUniqueOperations
open _root_.D12Complex
open _root_.D12Complex.ContinuationOperations

def leftParam_type := unitInterval → unitInterval
def leftParam_value : leftParam_type := leftParam
def rightParam_type := unitInterval → unitInterval
def rightParam_value : rightParam_type := rightParam
def concatPath_type := (unitInterval → ℂ) → (unitInterval → ℂ) → unitInterval → ℂ
def concatPath_value : concatPath_type := concatPath
def concatFamily_type := ∀ {γ δ : unitInterval → ℂ}, GermFamily γ → GermFamily δ →
  GermFamily (concatPath γ δ)
def concatFamily_value : concatFamily_type := @concatFamily

/-- Continuous parameter maps pull back local representatives, without
requiring injectivity or monotonicity. -/
def locallyRepresented_comp_type : Prop :=
  ∀ {γ : unitInterval → ℂ} {Φ : GermFamily γ}, LocallyRepresented γ Φ →
    ∀ {ρ : unitInterval → unitInterval}, Continuous ρ →
      LocallyRepresented (γ ∘ ρ) (fun t => Φ (ρ t))

/-- Agreement at every parameter, for any fixed initial germ. -/
def continuation_unique_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (Φ Ψ : GermFamily γ), IsContinuation Ω γ φ Φ → IsContinuation Ω γ φ Ψ →
      ∀ t, Φ t = Ψ t

/-- Reversal starts at the terminal germ (symm 0 = 1). -/
def continuation_reverse_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (Φ : GermFamily γ), IsContinuation Ω γ φ Φ →
      IsContinuation Ω (γ ∘ unitInterval.symm) (Φ (unitInterval.symm 0))
        (fun t => Φ (unitInterval.symm t))

/-- An increasing homeomorphic change preserves all the germs and both endpoints.
HEq only identifies the dependent germ fibres using the endpoint equalities. -/
def continuation_reparam_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (Φ : GermFamily γ) (ρ : unitInterval ≃ₜ unitInterval),
    IsContinuation Ω γ φ Φ → StrictMono ρ →
      IsContinuation Ω (γ ∘ ρ) (Φ (ρ 0)) (fun t => Φ (ρ t)) ∧
        ρ 0 = 0 ∧ ρ 1 = 1 ∧ HEq (Φ (ρ 0)) φ ∧ HEq (Φ (ρ 1)) (Φ 1)

/-- Matching terminal and initial germs suffice for concatenation, including
local representation across the joining parameter. HEq includes equality of
basepoints; the separate endpoint equation also states the path composability. -/
def continuation_concat_type : Prop :=
  ∀ (Ω : Set ℂ) (γ δ : unitInterval → ℂ)
    (φ : HolomorphicGerm (γ 0)) (ψ : HolomorphicGerm (δ 0))
    (Φ : GermFamily γ) (Ψ : GermFamily δ),
    IsContinuation Ω γ φ Φ → IsContinuation Ω δ ψ Ψ →
    γ 1 = δ 0 → HEq (Φ 1) ψ →
      IsContinuation Ω (concatPath γ δ) (concatFamily Φ Ψ 0) (concatFamily Φ Ψ) ∧
        HEq (concatFamily Φ Ψ 0) φ ∧ HEq (concatFamily Φ Ψ 1) (Ψ 1)

end Specs.D12Complex.Ch19.ContinuationUniqueOperations
