import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.OpenSetZeros
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic

/-! D12.16.06, paper.tex:2821–2826. The denominator realizes a locally
finite effective divisor with precisely the poles and their orders. The
numerator extends its product with the scalar representative. Equality of
the quotient uses filled meromorphic germs, including at denominator zeros.
No connectedness, nonemptiness, or componentwise nonvanishing of F is assumed. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch16.HolomorphicQuotients
open _root_.D12Complex

def holomorphic_quotients_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
    ∃ (d : Function.locallyFinsuppWithin Ω ℕ) (g h : ℂ → ℂ),
      Specs.D12Complex.Ch16.OpenSetZeros.Realizes_value Ω d h ∧
      (∀ a ∈ Ω, d a ≠ 0 ↔ F a = sphereInfty) ∧
      (∀ a ∈ Ω, ∀ m : ℕ, PoleOfOrderAt (scalarFinitePart F) a m → d a = m) ∧
      HolomorphicOn Ω g ∧
      (∀ a ∈ Ω, g =ᶠ[𝓝[≠] a] h * scalarFinitePart F) ∧
      EqOn g (h * scalarFinitePart F) {a | a ∈ Ω ∧ F a ≠ sphereInfty} ∧
      EqOn F (Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects.fill (g / h)) Ω

end Specs.D12Complex.Ch16.HolomorphicQuotients
