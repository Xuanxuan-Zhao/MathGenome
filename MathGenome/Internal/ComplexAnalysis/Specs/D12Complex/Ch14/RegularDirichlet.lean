import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.BarrierSqueeze

/-! The regular Dirichlet problem, paper.tex:2653–2658.
Boundary data are total representatives, constrained only on the boundary.
Solutions are unique on the closure; their values outside it are immaterial. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch14.RegularDirichlet
open _root_.D12Complex

def IsDirichletSolution_type := Set ℂ → (ℂ → ℝ) → (ℂ → ℝ) → Prop
def IsDirichletSolution_value : IsDirichletSolution_type := fun Ω φ u =>
  HarmonicOn Ω u ∧ ContinuousOn u (closure Ω) ∧ EqOn u φ (frontier Ω)

def perronSolution_type := Set ℂ → (ℂ → ℝ) → ℂ → ℝ
def perronSolution_value : perronSolution_type := fun Ω φ z =>
  @ite ℝ (z ∈ Ω) (Classical.propDecidable _) (perronEnvelope Ω φ z) (φ z)

/-- Existence by the specified envelope, exact boundary values, full closure
continuity, bounds on the entire closure, and uniqueness there. -/
def regular_dirichlet_type : Prop :=
  ∀ (Ω : Set ℂ) (φ : ℂ → ℝ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) →
    IsDirichletSolution_value Ω φ (perronSolution_value Ω φ) ∧
    (∀ z ∈ closure Ω, sInf (φ '' frontier Ω) ≤ perronSolution_value Ω φ z ∧
      perronSolution_value Ω φ z ≤ sSup (φ '' frontier Ω)) ∧
    (∀ u : ℂ → ℝ, IsDirichletSolution_value Ω φ u → EqOn u (perronSolution_value Ω φ) (closure Ω))

/-- Linearity on the full closure, for arbitrary real coefficients. -/
def perronSolution_linear_type : Prop :=
  ∀ (Ω : Set ℂ) (φ ψ : ℂ → ℝ) (a b : ℝ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) → ContinuousOn ψ (frontier Ω) →
    EqOn (perronSolution_value Ω (fun z => a * φ z + b * ψ z))
      (fun z => a * perronSolution_value Ω φ z + b * perronSolution_value Ω ψ z) (closure Ω)

def perronEnvelope_linear_type : Prop :=
  ∀ (Ω : Set ℂ) (φ ψ : ℂ → ℝ) (a b : ℝ),
    IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) → ContinuousOn ψ (frontier Ω) →
    EqOn (perronEnvelope Ω (fun z => a * φ z + b * ψ z))
      (fun z => a * perronEnvelope Ω φ z + b * perronEnvelope Ω ψ z) Ω

def perronSolution_nonneg_type : Prop :=
  ∀ (Ω : Set ℂ) (φ : ℂ → ℝ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) → (∀ ξ ∈ frontier Ω, 0 ≤ φ ξ) →
    ∀ z ∈ closure Ω, 0 ≤ perronSolution_value Ω φ z

def perronEnvelope_nonneg_type : Prop :=
  ∀ (Ω : Set ℂ) (φ : ℂ → ℝ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) → (∀ ξ ∈ frontier Ω, 0 ≤ φ ξ) →
    ∀ z ∈ Ω, 0 ≤ perronEnvelope Ω φ z

def perronSolution_mono_type : Prop :=
  ∀ (Ω : Set ℂ) (φ ψ : ℂ → ℝ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) → ContinuousOn ψ (frontier Ω) →
    (∀ ξ ∈ frontier Ω, φ ξ ≤ ψ ξ) →
    ∀ z ∈ closure Ω, perronSolution_value Ω φ z ≤ perronSolution_value Ω ψ z

def perronEnvelope_mono_type : Prop :=
  ∀ (Ω : Set ℂ) (φ ψ : ℂ → ℝ), IsDomain Ω → Bornology.IsBounded Ω →
    (∀ ξ ∈ frontier Ω, BarrierSqueeze.RegularBoundaryPoint_value Ω ξ) →
    ContinuousOn φ (frontier Ω) → ContinuousOn ψ (frontier Ω) →
    (∀ ξ ∈ frontier Ω, φ ξ ≤ ψ ξ) →
    ∀ z ∈ Ω, perronEnvelope Ω φ z ≤ perronEnvelope Ω ψ z

end Specs.D12Complex.Ch14.RegularDirichlet
