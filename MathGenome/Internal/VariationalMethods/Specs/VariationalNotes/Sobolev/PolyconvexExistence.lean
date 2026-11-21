import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Minors
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements for paper.tex, Theorem `thm:polyconvex-existence`
(4130–4157), with the Chapter 8 conventions (3652–3679).
The fixed affine zero-boundary class allows the stronger bounded-open-domain
version below, so in particular every bounded Lipschitz domain is covered.
All independent minor coordinates are quantified in the growth bound.
Energies at other competitors may be +∞. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
namespace VariationalNotes.Sobolev.Polyconvex
open Minors

/-- The density obtained from the full vector of minors, in the canonical
(target,domain) matrix entry convention. -/
def density {d m : ℕ}
    (G : Domain d → Vector m → Coordinates m d → ℝ) :
    Domain d → Vector m → Gradient m d → ℝ :=
  fun x s Z => G x s (allMinors Z)

/-- A real attained minimum over the whole prescribed affine class. -/
def FiniteMinimum {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u₀ : W1p Ω m p) (F : Domain d → Vector m → Gradient m d → ℝ) : Prop :=
  ∃ u ∈ affineClass Ω m p u₀, ∃ e : ℝ,
    energy Ω m p F u = (e : EReal) ∧
    ∀ v ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F v

/-- Finite Carathéodory representation; convexity and the uniform lower bound
hold outside common null sets independent of the state and independent minors.
No joint convexity in the state, and no upper growth, is assumed. -/
structure Hypotheses {d m : ℕ} [NeZero d] [NeZero m]
    (Ω : Opens (Domain d)) (p q : Exponent)
    (G : Domain d → Vector m → Coordinates m d → ℝ)
    (α C : ℝ) (a : Domain d → ℝ) : Prop where
  bounded : Bornology.IsBounded (Ω : Set (Domain d))
  minor_lt : (min m d : ℕ) < p.real
  state_lt : q.real < p.real
  caratheodory : CaratheodorySpecs.Caratheodory (domainMeasure Ω)
    (fun x (y : Vector m × Coordinates m d) => G x y.1 y.2)
  convex : ∀ᵐ x ∂domainMeasure Ω, ∀ s, ConvexOn ℝ univ (G x s)
  alpha_pos : 0 < α
  C_nonneg : 0 ≤ C
  a_integrable : Integrable a (domainMeasure Ω)
  lower_bound : ∀ᵐ x ∂domainMeasure Ω, ∀ s z,
    α * ‖firstMatrix (NeZero.pos m) (NeZero.pos d) z‖ ^ p.real -
      C * ‖s‖ ^ q.real - a x ≤ G x s z

/-- Literal real 2×2 matrix determinant, with rows = target coordinates. -/
def determinant (Z : Gradient 2 2) : ℝ :=
  Matrix.det (fun i j : Fin 2 => Z (i,j))

/-- The matrix-and-determinant representation mentioned explicitly in the source. -/
def matrixDetDensity (G : Domain 2 → Vector 2 → (Gradient 2 2 × ℝ) → ℝ) :
    Domain 2 → Vector 2 → Gradient 2 2 → ℝ :=
  fun x s Z => G x s (Z, determinant Z)

namespace Expected

/-- Full polyconvex existence theorem. `Exponent` includes all finite real q≥1;
strict inequalities give p>max(min(m,d),q). -/
def Existence : Prop :=
  ∀ {d m : ℕ} [NeZero d] [NeZero m] (Ω : Opens (Domain d))
    (p q : Exponent) (u₀ : W1p Ω m p)
    (G : Domain d → Vector m → Coordinates m d → ℝ)
    (α C : ℝ) (a : Domain d → ℝ),
    Hypotheses Ω p q G α C a →
    (∃ v ∈ affineClass Ω m p u₀, ∃ e : ℝ,
      energy Ω m p (density G) v = (e : EReal)) →
    FiniteMinimum Ω p u₀ (density G)

/-- Explicit 2×2 specialization with p>max(2,q). The bound holds for every
matrix Z and independent real t, not only when t=det Z. -/
def MatrixDetExistence : Prop :=
  ∀ (Ω : Opens (Domain 2)) (p q : Exponent) (u₀ : W1p Ω 2 p)
    (G : Domain 2 → Vector 2 → (Gradient 2 2 × ℝ) → ℝ)
    (α C : ℝ) (a : Domain 2 → ℝ),
    Bornology.IsBounded (Ω : Set (Domain 2)) →
    2 < p.real → q.real < p.real →
    CaratheodorySpecs.Caratheodory (domainMeasure Ω)
      (fun x (y : Vector 2 × (Gradient 2 2 × ℝ)) => G x y.1 y.2) →
    (∀ᵐ x ∂domainMeasure Ω, ∀ s, ConvexOn ℝ univ (G x s)) →
    0 < α → 0 ≤ C → Integrable a (domainMeasure Ω) →
    (∀ᵐ x ∂domainMeasure Ω, ∀ s (Z : Gradient 2 2) (t : ℝ),
      α * ‖Z‖ ^ p.real - C * ‖s‖ ^ q.real - a x ≤ G x s (Z,t)) →
    (∃ v ∈ affineClass Ω 2 p u₀, ∃ e : ℝ,
      energy Ω 2 p (matrixDetDensity G) v = (e : EReal)) →
    FiniteMinimum Ω p u₀ (matrixDetDensity G)

end Expected
end VariationalNotes.Sobolev.Polyconvex
