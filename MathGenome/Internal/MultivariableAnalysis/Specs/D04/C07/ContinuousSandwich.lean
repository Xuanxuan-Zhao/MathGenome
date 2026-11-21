import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import Mathlib.Topology.Algebra.Support

/-! The pointwise sandwich of paper.tex, d04:07:sandwich (2361–2380).
The input is an ambient function, with its actual topological support inside a
compact K ⊆ V. Integrability is the existing Darboux integrability on an enclosing
box. The output integral is the existing open-domain integral of the actual
zero extension. No a.e. inequalities or continuity assumptions on f are used. -/
noncomputable section
open Set
namespace Specs.D04.C07.ContinuousSandwich
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model

def continuous_sandwichType : Prop :=
  ∀ {n : ℕ} (V K : Set (E n)) (f : E n → ℝ),
    IsOpen V → IsCompact K → K ⊆ V → tsupport f ⊆ K →
    (∃ Q : Box n, Encloses (Function.support f) Q ∧ Integrable f Q) →
    ∀ ε : ℝ, 0 < ε → ∃ gLower gUpper : E n → ℝ,
      Continuous gLower ∧ Continuous gUpper ∧
      HasCompactSupport gLower ∧ HasCompactSupport gUpper ∧
      tsupport gLower ⊆ V ∧ tsupport gUpper ⊆ V ∧
      (∀ x, gLower x ≤ f x ∧ f x ≤ gUpper x) ∧
      OpenIntegrable (fun x : V => gLower x) ∧
      OpenIntegrable (fun x : V => gUpper x) ∧
      OpenIntegrable (fun x : V => gUpper x - gLower x) ∧
      openIntegral (fun x : V => gUpper x - gLower x) < ε
end Specs.D04.C07.ContinuousSandwich
