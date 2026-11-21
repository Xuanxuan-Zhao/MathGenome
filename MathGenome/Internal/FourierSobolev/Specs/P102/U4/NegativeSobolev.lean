import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension

/-! Negative order spaces for paper.tex:1691–1705. The coefficient index set is
all multi-indices of order at most one, so it consists of zero and the d singletons.
Products use scalar multiplication with no complex conjugation. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions ENNReal
namespace P102.U4

instance negativeConjExponentFact (p : ℝ≥0∞) : Fact (1 ≤ ENNReal.conjExponent p) :=
  ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩

abbrev NegativeSobolev {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] := SobolevZero 𝕜 Ω 1 p →L[𝕜] 𝕜

/-- Indexed by zero and the coordinate singleton multi-indices; the ordinary Pi
norm is exactly the maximum of the coefficient Lp norms. -/
abbrev NegativeCoefficients {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) := SobolevIndex d 1 → DomainLp 𝕜 Ω (ENNReal.conjExponent p)

def negativeFirstSobolevIndex (d : ℕ) (j : Fin d) : SobolevIndex d 1 := ⟨{j}, by simp⟩

/-- The signs give ∫f₀u − ∑ⱼ∫fⱼDⱼu, including complex scalars. -/
def negativePairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : NegativeCoefficients 𝕜 Ω p)
    (u : SobolevZero 𝕜 Ω 1 p) : 𝕜 :=
  ∑ α : SobolevIndex d 1, (-1 : 𝕜) ^ α.val.card *
    ∫ x in Ω, a α x * sobolevDerivative u.val α x

def NegativeRepresents {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : NegativeCoefficients 𝕜 Ω p)
    (f : NegativeSobolev 𝕜 Ω p) : Prop := ∀ u, f u = negativePairing a u

def divergenceDistribution {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} (a : NegativeCoefficients 𝕜 Ω p) : DistributionSpace 𝕜 Ω :=
  ∑ α : SobolevIndex d 1, distributionPartial α.val (regularDistribution Ω (a α))

/-- A map realizes the dual as ordinary distributions precisely when it restricts
to the canonical compactly supported smooth Sobolev classes. -/
def IsNegativeRealization {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (R : NegativeSobolev 𝕜 Ω p →ₗ[𝕜] DistributionSpace 𝕜 Ω) : Prop :=
  Function.Injective R ∧ ∀ (f : NegativeSobolev 𝕜 Ω p) (φ : TestSpace 𝕜 Ω)
    (u : SobolevZero 𝕜 Ω 1 p), sobolevUnderlying u.val = testToDomainLp Ω p φ →
      R f φ = f u

namespace NegativeSobolevExpected

def SpaceType := {d : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → (Ω : Opens (Space d)) →
  (p : ℝ≥0∞) → [Fact (1 ≤ p)] → Type

def SpaceValue : SpaceType := @NegativeSobolev

def PairingFormula : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : NegativeCoefficients 𝕜 Ω p) (u : SobolevZero 𝕜 Ω 1 p),
    negativePairing a u =
      (∫ x in Ω, a (zeroSobolevIndex d 1) x * sobolevUnderlying u.val x) -
      ∑ j : Fin d, ∫ x in Ω, a (negativeFirstSobolevIndex d j) x *
        sobolevDerivative u.val (negativeFirstSobolevIndex d j) x

def DivergenceFormula : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞)
    (a : NegativeCoefficients 𝕜 Ω p),
    divergenceDistribution a = regularDistribution Ω (a (zeroSobolevIndex d 1)) +
      ∑ j : Fin d, distributionPartial {j} (regularDistribution Ω (a (negativeFirstSobolevIndex d j)))

/-- Holder's converse, valid even at the primal endpoints. -/
def Converse : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : NegativeCoefficients 𝕜 Ω p),
    ∃ f : NegativeSobolev 𝕜 Ω p, NegativeRepresents a f ∧ ‖f‖ ≤ ‖a‖

def Realization : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∃ R : NegativeSobolev 𝕜 Ω p →ₗ[𝕜] DistributionSpace 𝕜 Ω,
      IsNegativeRealization Ω p R

/-- The chosen norm is the attained minimum, with the full pairing on W₀ and
its equality as an ordinary distribution. -/
def RepresentationAt {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
    ∃ R : NegativeSobolev 𝕜 Ω p →ₗ[𝕜] DistributionSpace 𝕜 Ω,
      IsNegativeRealization Ω p R ∧
      (∀ f : NegativeSobolev 𝕜 Ω p, ∃ a : NegativeCoefficients 𝕜 Ω p,
        NegativeRepresents a f ∧ R f = divergenceDistribution a ∧
        ‖a‖ = ‖f‖) ∧
      (∀ (a : NegativeCoefficients 𝕜 Ω p) (f : NegativeSobolev 𝕜 Ω p),
        NegativeRepresents a f → R f = divergenceDistribution a) ∧
      (∀ f : NegativeSobolev 𝕜 Ω p,
        IsLeast {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ t = ‖a‖} ‖f‖ ∧
        ‖f‖ = sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p, NegativeRepresents a f ∧ t = ‖a‖})

def Representation : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → RepresentationAt (𝕜 := 𝕜) Ω p

/-- Every fixed finite Lq product norm gives an equivalent infimum convention.
The constants may depend on the dimension and q, but not on the functional. -/
def ProductNormEquivalence : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)],
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : NegativeSobolev 𝕜 Ω p,
      c * ‖f‖ ≤ sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
        NegativeRepresents a f ∧ t = ‖WithLp.toLp q a‖} ∧
      sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
        NegativeRepresents a f ∧ t = ‖WithLp.toLp q a‖} ≤ C * ‖f‖

/-- Also covers any prescribed equivalent product norm, beyond the Lq family. -/
def EquivalentNormInfimum : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∀ (N : NegativeCoefficients 𝕜 Ω p → ℝ)
      (c C : ℝ), 0 < c → 0 < C →
      (∀ a, c * ‖a‖ ≤ N a ∧ N a ≤ C * ‖a‖) →
      ∀ f : NegativeSobolev 𝕜 Ω p,
        c * ‖f‖ ≤ sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
          NegativeRepresents a f ∧ t = N a} ∧
        sInf {t : ℝ | ∃ a : NegativeCoefficients 𝕜 Ω p,
          NegativeRepresents a f ∧ t = N a} ≤ C * ‖f‖

def EmptyDomain : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : NegativeSobolev 𝕜 (⊥ : Opens (Space d)) p), f = 0

def ZeroDimension : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space 0)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ ∞ → ∀ f : NegativeSobolev 𝕜 Ω p,
    ∃ a₀ : DomainLp 𝕜 Ω (ENNReal.conjExponent p), ‖a₀‖ = ‖f‖ ∧
      ∀ u, f u = ∫ x in Ω, a₀ x * sobolevUnderlying u.val x

/-- Exact scalar Lp duality interface used by the finite-product assembly. -/
def ScalarDualityInput : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ g : DomainLp 𝕜 Ω p →L[𝕜] 𝕜,
      ∃ a : DomainLp 𝕜 Ω (ENNReal.conjExponent p),
        (∀ v, g v = (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
          (volume.restrict (Ω : Set (Space d))) p (ENNReal.conjExponent p) v a) ∧ ‖a‖ = ‖g‖

/-- Finite-product proof assembly from the scalar representation interface. -/
def Reduction : Prop := ScalarDualityInput →
  Realization ∧ Representation ∧ ProductNormEquivalence ∧ EquivalentNormInfimum ∧ ZeroDimension

end NegativeSobolevExpected
end P102.U4
