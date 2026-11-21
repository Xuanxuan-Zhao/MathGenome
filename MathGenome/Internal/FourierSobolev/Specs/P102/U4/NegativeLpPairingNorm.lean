import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace

/-! Sharp scalar Lp dual-pairing norm, with the bilinear convention of U4-07.
There is no finite-measure, nonempty-domain, or positive-dimension hypothesis. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.U4.NegativeLpPairingNormExpected

/-- The canonical coefficient functional is an isometry, for both scalar fields. -/
def SharpNorm : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) (hp : 1 < p) (_ht : p ≠ ∞),
    letI : Fact (1 ≤ p) := ⟨hp.le⟩
    letI : Fact (1 ≤ ENNReal.conjExponent p) :=
      ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
    ∀ a : DomainLp 𝕜 Ω (ENNReal.conjExponent p),
      ‖((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
        (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)).flip a‖ = ‖a‖

/-- Values of that scalar-linear map are the source's bilinear integrals. -/
def IntegralFormula : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) (hp : 1 < p) (_ht : p ≠ ∞),
    letI : Fact (1 ≤ p) := ⟨hp.le⟩
    letI : Fact (1 ≤ ENNReal.conjExponent p) :=
      ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
    ∀ (a : DomainLp 𝕜 Ω (ENNReal.conjExponent p)) (v : DomainLp 𝕜 Ω p),
      ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
        (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p)).flip a v =
          ∫ x in Ω, v x * a x ∧
      (∫ x in Ω, v x * a x) = ∫ x in Ω, a x * v x

end P102.U4.NegativeLpPairingNormExpected
