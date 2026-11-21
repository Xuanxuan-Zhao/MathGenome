import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow

/-! Independent statement of paper.tex, d13:11:flowbox.
Coordinates use ℝ^(dim E - 1), with its standard finite product norm; the
state space may carry any finite-dimensional norm. The nonzero-field
hypothesis excludes dimension zero without excluding the one-dimensional
case (whose transverse coordinate space is the zero-dimensional space).
-/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch11.Flowbox
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A product flowbox with both directions of its coordinate map Cᵏ.
The linear equivalence A records the chosen transverse embedding
z ↦ A(0,z) and its complementarity to the velocity A(1,0). -/
structure Chart (F : AutonomousODE E) (p : E) (k : ℕ) where
  frame : (ℝ × (Fin (Module.finrank ℝ E - 1) → ℝ)) ≃L[ℝ] E
  frame_time : frame (1,0) = autonomousEvalValue F p
  ε : ℝ
  ε_pos : 0 < ε
  transverse : Set (Fin (Module.finrank ℝ E - 1) → ℝ)
  transverse_open : IsOpen transverse
  transverse_zero : 0 ∈ transverse
  coord : OpenPartialHomeomorph (ℝ × (Fin (Module.finrank ℝ E - 1) → ℝ)) E
  source_eq : coord.source = Ioo (-ε) ε ×ˢ transverse
  target_domain : coord.target ⊆ F.domain
  origin : coord (0,0) = p
  target_point : p ∈ coord.target
  regular : ContDiffOn ℝ k coord coord.source
  inverse_regular : ContDiffOn ℝ k coord.symm coord.target
  flow_domain : ∀ q ∈ coord.source, (q.1, p + frame (0,q.2)) ∈ flowDomain F
  formula : ∀ q ∈ coord.source, coord q = flow F q.1 (p + frame (0,q.2))
  velocity : ∀ q ∈ coord.source,
    (fderiv ℝ coord q) (1,0) = autonomousEvalValue F (coord q)
  translation : ∀ q ∈ coord.source, ∀ t : ℝ, (q.1+t,q.2) ∈ coord.source →
    (t,coord q) ∈ flowDomain F ∧ flow F t (coord q) = coord (q.1+t,q.2)

def FlowboxStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, autonomousEvalValue F p ≠ 0 → Nonempty (Chart F p k)

end Specs.D13Unified.Ch11.Flowbox
