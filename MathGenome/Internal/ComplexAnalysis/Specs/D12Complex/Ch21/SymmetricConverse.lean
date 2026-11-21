import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.SymmetricCoefficients
import Mathlib.Algebra.Polynomial.Bivariate

/-! The symmetric-coefficient converse, paper.tex:3666–3687.
The outer polynomial variable is w and its coefficients are polynomials in z.
We retain the canonical analytic multisets and cyclic growth hypotheses of the
preceding stage. No algebraic equation is part of the input. -/
noncomputable section
open scoped BigOperators
namespace Specs.D12Complex.Ch21.SymmetricConverse
open _root_.D12Complex _root_.D12Complex.SymmetricCoefficientData

/-- A common polynomial denominator clears the entire monic branch equation,
including at ordinary base points where the denominator itself vanishes.
The coefficient at w^d is the nonzero denominator, so the equation is nonzero.
Multiset membership retains all branches without requiring global labels. -/
def symmetric_converse_type : Prop :=
  ∀ (E : Finset RiemannSphere) (d : ℕ) (B : RiemannSphere → Multiset ℂ),
    AnalyticMultiset E d B → (∀ p ∈ E, CyclicPowerGrowth B p) →
    ∃ (D : Polynomial ℂ) (Q : Polynomial (Polynomial ℂ)),
      D ≠ 0 ∧ Q ≠ 0 ∧ Q.coeff d = D ∧ Q.natDegree = d ∧
      (∀ a : ℂ, sphereFinite a ∉ E →
        Q.map (Polynomial.evalRingHom a) =
          Polynomial.C (D.eval a) *
            ((B (sphereFinite a)).map (fun v => Polynomial.X - Polynomial.C v)).prod) ∧
      ∀ a : ℂ, sphereFinite a ∉ E → ∀ v ∈ B (sphereFinite a),
        (Q.map (Polynomial.evalRingHom a)).eval v = 0

end Specs.D12Complex.Ch21.SymmetricConverse
