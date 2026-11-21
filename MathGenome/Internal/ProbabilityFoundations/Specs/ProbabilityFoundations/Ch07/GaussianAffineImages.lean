import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianLaws

/-!
Independent statements of the affine image assertion of paper.tex,
Theorem 7.7 (2612–2613). Matrices may be rectangular and rank deficient;
both natural dimensions may be zero. `toLp` simply restores the Euclidean
norm to the coordinate vector resulting from matrix multiplication.
-/

open MeasureTheory Matrix

namespace Specs.ProbabilityFoundations.Ch07.GaussianAffineImages

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.GaussianLaws

/-- The covariance parameter of the affine image is admissible. -/
def affineCovariancePosSemidef : Prop :=
  ∀ {d r : ℕ} (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    ∀ A : Matrix (Fin r) (Fin d) ℝ, (A * S * Aᵀ).PosSemidef

/-- Equality of the actual pushforward probability measures. -/
def gaussianLawAffineMap : Prop :=
  ∀ {d r : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    S.PosSemidef → ∀ (A : Matrix (Fin r) (Fin d) ℝ) (b : Euclidean r),
    (gaussianLawValue m S).map (fun x : Euclidean d => WithLp.toLp 2 (A *ᵥ x) + b) =
      gaussianLawValue (WithLp.toLp 2 (A *ᵥ m) + b) (A * S * Aᵀ)

/-- The same assertion for any measurable random vector having the given law. -/
def gaussianRandomVectorAffineLaw : Prop :=
  ∀ {d r : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Euclidean d), Measurable X →
    ∀ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    P.map X = gaussianLawValue m S →
    ∀ (A : Matrix (Fin r) (Fin d) ℝ) (b : Euclidean r),
    P.map (fun ω => WithLp.toLp 2 (A *ᵥ X ω) + b) =
      gaussianLawValue (WithLp.toLp 2 (A *ᵥ m) + b) (A * S * Aᵀ)

end Specs.ProbabilityFoundations.Ch07.GaussianAffineImages
