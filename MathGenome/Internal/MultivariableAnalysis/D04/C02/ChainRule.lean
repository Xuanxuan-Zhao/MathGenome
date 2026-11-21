import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.ChainRule
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! The pointwise chain rule in the paper's open-domain remainder formulation.
The upstream equivalence with `HasFDerivAt` transports the library chain rule
back to that formulation, including zero inner increments. Matrix multiplication
uses the shared column-coordinate representation, with no dimension restrictions.
-/
noncomputable section
open Set
namespace D04

section Generic
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem hasTotalDerivative_comp (U : Set X) (V : Set Y)
    (f : X → Y) (g : Y → Z) (a : X) (A : X →L[ℝ] Y) (B : Y →L[ℝ] Z)
    (hf : HasTotalDerivative U f A a) (hg : HasTotalDerivative V g B (f a)) :
    HasTotalDerivative U (g ∘ f) (B.comp A) a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U (g ∘ f) (B.comp A) a hf.1 hf.2.1).mpr
  exact ((hasTotalDerivative_iff_hasFDerivAt V g B (f a) hg.1 hg.2.1).mp hg).comp a
    ((hasTotalDerivative_iff_hasFDerivAt U f A a hf.1 hf.2.1).mp hf)

theorem totalDifferentiableAt_comp (U : Set X) (V : Set Y)
    (f : X → Y) (g : Y → Z) (a : X)
    (hf : TotalDifferentiableAt U f a) (hg : TotalDifferentiableAt V g (f a)) :
    TotalDifferentiableAt U (g ∘ f) a := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨B.comp A, hasTotalDerivative_comp U V f g a A B hA hB⟩

theorem totalDerivative_comp (U : Set X) (V : Set Y)
    (f : X → Y) (g : Y → Z) (a : X)
    (hf : TotalDifferentiableAt U f a) (hg : TotalDifferentiableAt V g (f a)) :
    totalDerivative (g ∘ f) a = (totalDerivative g (f a)).comp (totalDerivative f a) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  rw [totalDerivative_eq U f A a hA, totalDerivative_eq V g B (f a) hB]
  exact totalDerivative_eq U (g ∘ f) (B.comp A) a
    (hasTotalDerivative_comp U V f g a A B hA hB)

end Generic

theorem jacobian_comp {n m p : ℕ} (U : Set (E n)) (V : Set (E m))
    (f : E n → E m) (g : E m → E p) (a : E n)
    (hf : TotalDifferentiableAt U f a) (hg : TotalDifferentiableAt V g (f a)) :
    jacobian (g ∘ f) a = jacobian g (f a) * jacobian f a := by
  change matrixOfLinearMap (totalDerivative (g ∘ f) a).toLinearMap =
    matrixOfLinearMap (totalDerivative g (f a)).toLinearMap *
      matrixOfLinearMap (totalDerivative f a).toLinearMap
  rw [totalDerivative_comp U V f g a hf hg]
  apply (matrixLinearEquiv p n).injective
  rw [matrix_linear_roundtrip, matrix_composition,
    matrix_linear_roundtrip, matrix_linear_roundtrip]
  rfl

/-- The source statement: open-domain differentiability, differential and
Jacobian formulas, for `f : U → V`. Openness and membership are carried by
the two differentiability hypotheses. No nearby derivative continuity is used. -/
theorem chain_rule {n m p : ℕ} (U : Set (E n)) (V : Set (E m))
    (f : E n → E m) (g : E m → E p) (a : E n) (_hUV : MapsTo f U V)
    (hf : TotalDifferentiableAt U f a) (hg : TotalDifferentiableAt V g (f a)) :
    TotalDifferentiableAt U (g ∘ f) a ∧
      totalDerivative (g ∘ f) a = (totalDerivative g (f a)).comp (totalDerivative f a) ∧
      jacobian (g ∘ f) a = jacobian g (f a) * jacobian f a :=
  ⟨totalDifferentiableAt_comp U V f g a hf hg,
    totalDerivative_comp U V f g a hf hg, jacobian_comp U V f g a hf hg⟩

end D04
