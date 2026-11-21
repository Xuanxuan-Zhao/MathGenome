import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace

/-! Scalar Lp representation used in paper.tex:1691–1700.
The measure is restricted Euclidean Lebesgue measure, with no boundedness or
finite-measure assumption on the open set. Pairings are scalar bilinear,
including over complex scalars. All dimensions and the empty open set occur.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace P102.U4.NegativeLpRepresentationExpected

/-- Equality holds on every Lp class, not just on compact smooth tests. -/
def IntegralRepresentation : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ g : DomainLp 𝕜 Ω p →L[𝕜] 𝕜,
      ∃ a : DomainLp 𝕜 Ω (ENNReal.conjExponent p),
        ∀ v : DomainLp 𝕜 Ω p, g v = ∫ x in Ω, a x * v x

/-- The same existence statement using the canonical bundled bilinear pairing.
The local instance merely records that a conjugate exponent is at least one. -/
def PairingRepresentation : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ g : DomainLp 𝕜 Ω p →L[𝕜] 𝕜,
      letI : Fact (1 ≤ ENNReal.conjExponent p) :=
        ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
      ∃ a : DomainLp 𝕜 Ω (ENNReal.conjExponent p),
        ∀ v : DomainLp 𝕜 Ω p,
          g v = (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
            (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p) v a

end P102.U4.NegativeLpRepresentationExpected
