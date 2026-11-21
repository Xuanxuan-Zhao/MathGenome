import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.MetricSpace.Basic

/-! Independent statements of paper.tex:3536–3564 (D12.21.01).
A polynomial family is represented by its finitely many holomorphic coefficient
functions. Functions on neighborhoods are total functions restricted to the stated
open sets, using the shared weak-holomorphy predicate.
-/
noncomputable section
open Set Polynomial

namespace D12Complex.SimpleRootBranches

/-- The polynomial in the root variable, with parameter `z` and coefficients `A`. -/
def familyPolynomial (d : ℕ) (A : ℕ → ℂ → ℂ) (z : ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.monomial j (A j z)

end D12Complex.SimpleRootBranches

namespace Specs.D12Complex.Ch21.SimpleRootBranches
open _root_.D12Complex _root_.D12Complex.SimpleRootBranches

/-- A simple root gives one actual holomorphic branch, unique among all zeros
in a fixed neighborhood of the root for every parameter in a neighborhood of `a`. -/
def simple_root_branch_type : Prop :=
  ∀ (d : ℕ) (A : ℕ → ℂ → ℂ) (Ω : Set ℂ) (a b : ℂ),
    IsOpen Ω → a ∈ Ω → (∀ j ≤ d, HolomorphicOn Ω (A j)) →
    (familyPolynomial d A a).eval b = 0 →
    (familyPolynomial d A a).derivative.eval b ≠ 0 →
    ∃ (U V : Set ℂ) (f : ℂ → ℂ),
      IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧ IsOpen V ∧ b ∈ V ∧
      HolomorphicOn U f ∧ f a = b ∧ MapsTo f U V ∧
      ∀ z ∈ U, ∀ w ∈ V, (familyPolynomial d A z).eval w = 0 ↔ w = f z

/-- All roots at nearby parameters lie on the `d` disjoint holomorphic branches.
The injective enumeration records exactly the original hypothesis of `d` distinct
roots at the center; simplicity is a conclusion, rather than an extra assumption.
The common parameter neighborhood is explicitly a positive-radius disk. -/
def all_simple_root_branches_type : Prop :=
  ∀ (d : ℕ) (A : ℕ → ℂ → ℂ) (Ω : Set ℂ) (a : ℂ) (b : Fin d → ℂ),
    0 < d → IsOpen Ω → a ∈ Ω → (∀ j ≤ d, HolomorphicOn Ω (A j)) →
    A d a ≠ 0 → Function.Injective b →
    (∀ i, (familyPolynomial d A a).eval (b i) = 0) →
    ∃ (r : ℝ) (f : Fin d → ℂ → ℂ) (V : Fin d → Set ℂ),
      0 < r ∧ Metric.ball a r ⊆ Ω ∧
      (∀ i, IsOpen (V i) ∧ b i ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      (∀ i, HolomorphicOn (Metric.ball a r) (f i) ∧ f i a = b i ∧
        MapsTo (f i) (Metric.ball a r) (V i)) ∧
      (∀ z ∈ Metric.ball a r, ∀ i, ∀ w ∈ V i,
        (familyPolynomial d A z).eval w = 0 ↔ w = f i z) ∧
      (∀ z ∈ Metric.ball a r,
        (familyPolynomial d A z).natDegree = d ∧
        Function.Injective (fun i => f i z) ∧
        ∀ w : ℂ, (familyPolynomial d A z).eval w = 0 ↔ ∃ i, w = f i z)

end Specs.D12Complex.Ch21.SimpleRootBranches
