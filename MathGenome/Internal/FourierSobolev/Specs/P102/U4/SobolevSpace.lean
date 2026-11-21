import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Lp.PiLp

/-! Canonical finite derivative-tuple model of the distribution-defined Sobolev space.
The zeroth coordinate will identify this model with a subspace of Lp classes.
The tuple uses the L¹ product norm, regardless of the function exponent p.
No nonemptiness or positive-dimension assumptions are made. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions ENNReal
namespace P102.U4

/-- All coordinate multi-indices of order at most m, including zero. -/
def SobolevIndex (d m : ℕ) := {α : MultiIndex d // α.card ≤ m}

instance (d m : ℕ) : Finite (SobolevIndex d m) := by
  let f : SobolevIndex d m → (Fin d → Fin (m + 1)) := fun α i =>
    ⟨α.val.count i, Nat.lt_succ_of_le ((Multiset.count_le_card _ _).trans α.property)⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro i
  exact congrArg Fin.val (congrFun h i)

instance (d m : ℕ) : Fintype (SobolevIndex d m) := Fintype.ofFinite _

def zeroSobolevIndex (d m : ℕ) : SobolevIndex d m := ⟨0, by simp⟩

abbrev DomainLp {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (p : ℝ≥0∞) :=
  Lp 𝕜 p (volume.restrict (Ω : Set (Space d)))

/-- Bilinear test pairing on Lp classes, continuous also at p=1 and p=∞. -/
def lpTestPairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : TestSpace 𝕜 Ω) : DomainLp 𝕜 Ω p →L[𝕜] 𝕜 := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) := ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  exact ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing (volume.restrict (Ω : Set (Space d)))
    p (ENNReal.conjExponent p)).flip
      ((φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ)

/-- The finite ambient product, with exactly the sum of the coordinate norms. -/
abbrev SobolevTuple {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) := PiLp 1 (fun _ : SobolevIndex d m => DomainLp 𝕜 Ω p)

/-- Each defining distribution equation is a continuous linear equation. -/
def sobolevEquation {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (α : SobolevIndex d m)
    (φ : TestSpace 𝕜 Ω) : SobolevTuple 𝕜 Ω m p →L[𝕜] 𝕜 :=
  (lpTestPairing Ω p φ).comp (PiLp.proj 1 _ α) -
    ((-1 : 𝕜) ^ α.val.card) •
      (lpTestPairing Ω p (testPartialWord Ω (α.val.sort (· ≤ ·)) φ)).comp
        (PiLp.proj 1 _ (zeroSobolevIndex d m))

/-- The closed weak-derivative graph in the finite Lp product. -/
def sobolevSubmodule {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule 𝕜 (SobolevTuple 𝕜 Ω m p) :=
  ⨅ (α : SobolevIndex d m) (φ : TestSpace 𝕜 Ω), (sobolevEquation Ω m p α φ).ker

/-- W^{m,p}(Ω), with its derivative representatives retained in a finite tuple.
The zeroth-coordinate map is proved injective, with precisely the distribution-defined range. -/
abbrev Sobolev {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Type := ↥(sobolevSubmodule 𝕜 Ω m p)

def sobolevDerivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω m p)
    (α : SobolevIndex d m) : DomainLp 𝕜 Ω p := u.val α

def sobolevUnderlying {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω m p) : DomainLp 𝕜 Ω p :=
  sobolevDerivative u (zeroSobolevIndex d m)

/-- The canonical continuous injection into the underlying Lp space. -/
def sobolevUnderlyingCLM {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Sobolev 𝕜 Ω m p →L[𝕜] DomainLp 𝕜 Ω p :=
  (PiLp.proj 1 _ (zeroSobolevIndex d m)).comp (sobolevSubmodule 𝕜 Ω m p).subtypeL

/-- The original distribution-derivative membership condition on an Lp class. -/
def HasSobolevDerivatives {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) (u : DomainLp 𝕜 Ω p) : Prop :=
  ∀ α : MultiIndex d, α.card ≤ m → ∃ v : DomainLp 𝕜 Ω p,
    distributionPartial α (regularDistribution Ω u) = regularDistribution Ω v

namespace SobolevExpected

def SpaceType := {d : ℕ} → (𝕜 : Type) → [RCLike 𝕜] → (Ω : Opens (Space d)) →
  (m : ℕ) → (p : ℝ≥0∞) → [Fact (1 ≤ p)] → Type

def SpaceValue : SpaceType := @Sobolev

def DerivativeType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  {m : ℕ} → {p : ℝ≥0∞} → [Fact (1 ≤ p)] →
  Sobolev 𝕜 Ω m p → SobolevIndex d m → DomainLp 𝕜 Ω p

def DerivativeValue : DerivativeType := @sobolevDerivative

def UnderlyingType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  {m : ℕ} → {p : ℝ≥0∞} → [Fact (1 ≤ p)] →
  Sobolev 𝕜 Ω m p → DomainLp 𝕜 Ω p

def UnderlyingValue : UnderlyingType := @sobolevUnderlying

/-- The tuple model has exactly the source's distribution-defined Lp classes. -/
def UnderlyingRange : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    Set.range (@sobolevUnderlying d 𝕜 _ Ω m p _) =
      {u | HasSobolevDerivatives Ω m p u}

def UnderlyingInjective : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    Function.Injective (@sobolevUnderlying d 𝕜 _ Ω m p _)

def DerivativeDistribution : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω m p) (α : SobolevIndex d m),
    distributionPartial α.val (regularDistribution Ω (sobolevUnderlying u)) =
      regularDistribution Ω (sobolevDerivative u α)

def DerivativeUnique : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω m p) (α : SobolevIndex d m) (v : DomainLp 𝕜 Ω p),
    distributionPartial α.val (regularDistribution Ω (sobolevUnderlying u)) =
      regularDistribution Ω v → v = sobolevDerivative u α

def DerivativeZero : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω m p),
    sobolevDerivative u (zeroSobolevIndex d m) = sobolevUnderlying u

/-- The norm is the sum, not a function-exponent-dependent product norm. -/
def SumNorm : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω m p),
    ‖u‖ = ∑ α : SobolevIndex d m, ‖sobolevDerivative u α‖

def TupleImage : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    Set.range (fun u : Sobolev 𝕜 Ω m p => u.val) =
      {v : SobolevTuple 𝕜 Ω m p | ∀ (α : SobolevIndex d m) (φ : TestSpace 𝕜 Ω),
        (∫ x in Ω, v α x * φ x) = (-1 : 𝕜) ^ α.val.card *
          ∫ x in Ω, v (zeroSobolevIndex d m) x * multiPartial φ α.val x}

def ClosedImage : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    IsClosed (Set.range (fun u : Sobolev 𝕜 Ω m p => u.val))

/-- Normed vector space instances are inherited from the canonical product submodule. -/
def Banach : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    CompleteSpace (Sobolev 𝕜 Ω m p)

/-- Every finite Lq product norm, including the supremum norm, induces this topology. -/
def ProductNormEquivalence : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (q : ℝ≥0∞) [Fact (1 ≤ q)],
    Topology.IsEmbedding (fun u : Sobolev 𝕜 Ω m p =>
      (WithLp.toLp q u.val.ofLp : PiLp q (fun _ : SobolevIndex d m => DomainLp 𝕜 Ω p)))

/-- The linear isometry is the canonical zeroth-coordinate map. -/
def ZeroOrder : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ e : Sobolev 𝕜 Ω 0 p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω p,
      ∀ u, e u = sobolevUnderlying u

def ZeroDimension : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω : Opens (Space 0)),
    ∃ e : Sobolev 𝕜 Ω m p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω p,
      ∀ u, e u = sobolevUnderlying u

def EmptyDomain : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊥ : Opens (Space d)) m p), u = 0

end SobolevExpected
end P102.U4
