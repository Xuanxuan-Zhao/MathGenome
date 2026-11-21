import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.EllipticResidueSum
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! The zero/pole and finite-value assertions of paper.tex, d12:22-03.
The scalar meromorphic function includes its canonical finite and infinite values.
The effective divisors are finitely supported functions on the literal torus.
Their coefficients are the positive and negative parts of the plane germ orders;
thus neither a choice of representatives nor a pole filler changes multiplicity. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch22.DivisorDegree
open _root_.D12Complex _root_.D12Complex.TorusSurface

/-- All finite fibres have the same positive degree. The value `c = 0` includes
the zero divisor. Subtracting `c` preserves every pole and its exact order. -/
def divisor_degree_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ F : ℂ → RiemannSphere, ScalarMeromorphicOn univ F → Periodic ω₁ ω₂ F →
  (¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c) →
  ∃ N : ℕ, 0 < N ∧ ∃ Z P : Torus ω₁ ω₂ →₀ ℕ,
    (∀ a : ℂ,
      meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤ ∧
      Z (projection ω₁ ω₂ a) = (meromorphicOrderAt (scalarFinitePart F) a).untop₀.toNat ∧
      P (projection ω₁ ω₂ a) = (-(meromorphicOrderAt (scalarFinitePart F) a).untop₀).toNat) ∧
    Z.sum (fun _ n => n) = N ∧ P.sum (fun _ n => n) = N ∧
    ∀ c : ℂ, ∃ V : Torus ω₁ ω₂ →₀ ℕ,
      (∀ a : ℂ,
        meromorphicOrderAt (fun z => scalarFinitePart F z - c) a ≠ ⊤ ∧
        V (projection ω₁ ω₂ a) =
          (meromorphicOrderAt (fun z => scalarFinitePart F z - c) a).untop₀.toNat ∧
        (V (projection ω₁ ω₂ a) ≠ 0 ↔ F a = sphereFinite c) ∧
        (meromorphicOrderAt (fun z => scalarFinitePart F z - c) a < 0 ↔
          meromorphicOrderAt (scalarFinitePart F) a < 0) ∧
        (meromorphicOrderAt (scalarFinitePart F) a < 0 →
          meromorphicOrderAt (fun z => scalarFinitePart F z - c) a =
            meromorphicOrderAt (scalarFinitePart F) a)) ∧
      V.sum (fun _ n => n) = N

end Specs.D12Complex.Ch22.DivisorDegree
