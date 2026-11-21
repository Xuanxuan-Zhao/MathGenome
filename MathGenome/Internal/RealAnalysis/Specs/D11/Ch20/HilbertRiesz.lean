import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.OrthogonalProjection

/-!
Independent statements for paper.tex:5690–5692, `d11:20:hilbert-riesz`.
A bounded scalar-linear functional is bundled as a continuous linear map;
its norm is the operator norm. The Hilbert space may have any dimension.
The shared `innerFirst` uses the paper's first-slot-linear convention.
-/

namespace D11.Ch20.HilbertRiesz

open D11.Ch20.OrthogonalProjection

universe u v

/-- The explicit conjugation bridge to Mathlib's inner product, together
with scalar linearity in the first slot and conjugate linearity in the second. -/
def conventionStatement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H],
    (∀ x y : H, innerFirst (𝕜 := 𝕜) x y = star (inner 𝕜 x y)) ∧
    (∀ (a : 𝕜) (x y z : H),
      innerFirst (𝕜 := 𝕜) (x + a • y) z =
        innerFirst (𝕜 := 𝕜) x z + a * innerFirst (𝕜 := 𝕜) y z) ∧
    (∀ (a : 𝕜) (x y z : H),
      innerFirst (𝕜 := 𝕜) x (y + a • z) =
        innerFirst (𝕜 := 𝕜) x y + star a * innerFirst (𝕜 := 𝕜) x z)

/-- Every bounded scalar-linear functional on an arbitrary real or complex
Hilbert space has a representing vector of the same norm, and every vector
representing that functional equals this one. The zero functional is included. -/
def statement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (ℓ : H →L[𝕜] 𝕜),
    ∃ h : H,
      (∀ x : H, ℓ x = innerFirst (𝕜 := 𝕜) x h) ∧
      ‖h‖ = ‖ℓ‖ ∧
      (∀ k : H, (∀ x : H, ℓ x = innerFirst (𝕜 := 𝕜) x k) → k = h)

end D11.Ch20.HilbertRiesz
