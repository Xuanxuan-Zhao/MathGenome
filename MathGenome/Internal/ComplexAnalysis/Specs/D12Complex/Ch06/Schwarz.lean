import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-!
Independent statements for paper.tex:1476–1490, d12:06-03.
The unit disk is `Metric.ball (0 : ℂ) 1`. Total functions represent maps
on this open disk; every hypothesis and function equality is restricted
to the disk. Holomorphy uses the shared weak holomorphy predicate.
-/

namespace Specs.D12Complex.Ch06.Schwarz
open _root_.D12Complex

/-- Schwarz's value estimate at every point of the open unit disk. -/
def norm_le_norm_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (Metric.ball 0 1) f →
    Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) → f 0 = 0 →
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ ‖z‖

/-- Schwarz's derivative estimate at the origin. -/
def norm_deriv_zero_le_one_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (Metric.ball 0 1) f →
    Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) → f 0 = 0 →
    ‖deriv f 0‖ ≤ 1

/-- Equality at any nonzero interior point forces one rotation on the whole disk. -/
def rotation_of_norm_eq_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (Metric.ball 0 1) f →
    Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) → f 0 = 0 →
    ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → ‖f z‖ = ‖z‖ →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ w ∈ Metric.ball (0 : ℂ) 1, f w = c * w

/-- Equality in the derivative estimate forces one rotation on the whole disk. -/
def rotation_of_norm_deriv_eq_one_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (Metric.ball 0 1) f →
    Set.MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) → f 0 = 0 →
    ‖deriv f 0‖ = 1 →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, f z = c * z

/-- Every rotation is a holomorphic disk self-map fixing zero and attains
both equalities (the value equality holds at every point). -/
def rotation_converse_type : Prop :=
  ∀ c : ℂ, ‖c‖ = 1 →
    HolomorphicOn (Metric.ball 0 1) (fun z => c * z) ∧
    Set.MapsTo (fun z => c * z) (Metric.ball 0 1) (Metric.ball 0 1) ∧
    c * 0 = 0 ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, ‖c * z‖ = ‖z‖) ∧
    ‖deriv (fun z : ℂ => c * z) 0‖ = 1

end Specs.D12Complex.Ch06.Schwarz
