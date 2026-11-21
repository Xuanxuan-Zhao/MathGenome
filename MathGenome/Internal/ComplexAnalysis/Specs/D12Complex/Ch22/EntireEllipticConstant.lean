import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.LatticeGeometry

/-! The scalar, entire-function assertion of paper.tex, d12:22-02.
The lattice and weak holomorphy are the canonical shared objects. -/

namespace Specs.D12Complex.Ch22.EntireEllipticConstant

open _root_.D12Complex
open Specs.D12Complex.Ch22.LatticeGeometry

/-- Every entire function periodic under the given rank-two lattice is constant. -/
def entire_elliptic_constant_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ f : ℂ → ℂ, HolomorphicOn Set.univ f →
      (∀ z w : ℂ, w ∈ lattice ω₁ ω₂ → f (z + w) = f z) →
      ∃ c : ℂ, ∀ z : ℂ, f z = c

end Specs.D12Complex.Ch22.EntireEllipticConstant
