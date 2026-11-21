import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L2Space

/-! Independent statements for paper.tex:1439–1449. The gradient takes values in
Euclidean space, not the supremum-norm coordinate product. No boundedness,
boundary regularity, connectedness, or nonemptiness of Ω is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace
namespace P102.U4

-- Keep this goal's auxiliary interface separate from other deferred Specs.
namespace SlabPoincareData

/-- The multi-index for one coordinate derivative. -/
def firstSobolevIndex {d : ℕ} (i : Fin d) : SobolevIndex d 1 := ⟨{i}, by simp⟩

/-- The j-th weak derivative, in the canonical domain Lp space. -/
def sobolevFirstDerivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (j : Fin d) : DomainLp 𝕜 Ω p :=
  sobolevDerivative u (firstSobolevIndex j)

/-- Directional weak derivative, for a real Euclidean direction and either scalar field. -/
def sobolevDirectionalDerivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (e : Space d) : DomainLp 𝕜 Ω p :=
  ∑ j : Fin d, (RCLike.ofReal (e j) : 𝕜) • sobolevFirstDerivative u j

/-- A representative of the vector of weak coordinate derivatives. -/
def sobolevGradientRepresentative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (x : Space d) : EuclideanSpace 𝕜 (Fin d) :=
  WithLp.toLp 2 (fun j => sobolevFirstDerivative u j x)

/-- The gradient is in Lp since every coordinate is. -/
def sobolevGradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) :
    Lp (EuclideanSpace 𝕜 (Fin d)) p (volume.restrict (Ω : Set (Space d))) :=
  (MemLp.of_eval_piLp (fun j => Lp.memLp (sobolevFirstDerivative u j))).toLp
    (sobolevGradientRepresentative u)

/-- The integral with the source's convention: linear in u, conjugate-linear in v. -/
def sobolevGradientPairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (u v : SobolevZero 𝕜 Ω 1 2) : 𝕜 :=
  ∫ x in Ω, ∑ j : Fin d,
    sobolevFirstDerivative u.val j x * star (sobolevFirstDerivative v.val j x)

/-- Containment in a finite slab in the given unit direction. -/
def InSlab {d : ℕ} (Ω : Opens (Space d)) (e : Space d) (a b : ℝ) : Prop :=
  ∀ x ∈ Ω, a < inner ℝ x e ∧ inner ℝ x e < b

end SlabPoincareData

open SlabPoincareData
namespace SlabPoincareExpected

/-- Exact directional and Euclidean-gradient estimates, including p=1 and empty Ω. -/
def Inequality : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (e : Space d) (a b : ℝ), ‖e‖ = 1 → a < b → InSlab Ω e a b →
    ∀ u : SobolevZero 𝕜 Ω 1 p,
      ‖sobolevUnderlying u.val‖ ≤ (b - a) * ‖sobolevDirectionalDerivative u.val e‖ ∧
      (b - a) * ‖sobolevDirectionalDerivative u.val e‖ ≤ (b - a) * ‖sobolevGradient u.val‖

/-- Quantitative norm comparison; in particular the full norm and gradient norm
induce the same topology on W₀. The dimension factor only compares finite
coordinate norms; the Poincaré constant itself is still the exact slab width. -/
def NormEquivalence : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (e : Space d) (a b : ℝ), ‖e‖ = 1 → a < b → InSlab Ω e a b →
    ∀ u : SobolevZero 𝕜 Ω 1 p,
      ‖sobolevGradient u.val‖ ≤ ‖u‖ ∧
      ‖u‖ ≤ (b - a + (d : ℝ)) * ‖sobolevGradient u.val‖

/-- A complete inner product structure on the original vector space, with the
specified integral and norm. Lean's `inner` is linear in its second argument,
so the source pairing is `inner v u`. The new norm's topology must coincide
with the inherited full Sobolev topology. -/
def Hilbert : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (e : Space d) (a b : ℝ), ‖e‖ = 1 → a < b → InSlab Ω e a b →
    ∃ (N : NormedAddCommGroup (SobolevZero 𝕜 Ω 1 2))
      (I : @InnerProductSpace 𝕜 (SobolevZero 𝕜 Ω 1 2) _ N.toSeminormedAddCommGroup),
      N.toAddCommGroup = (inferInstance : AddCommGroup (SobolevZero 𝕜 Ω 1 2)) ∧
      (∀ (c : 𝕜) (u : SobolevZero 𝕜 Ω 1 2), @SMul.smul _ _ I.toSMul c u = c • u) ∧
      @CompleteSpace (SobolevZero 𝕜 Ω 1 2) N.toUniformSpace ∧
      N.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (SobolevZero 𝕜 Ω 1 2)) ∧
      (∀ u, @norm _ N.toNorm u = ‖sobolevGradient u.val‖) ∧
      (∀ u v, @inner 𝕜 _ I.toInner v u = sobolevGradientPairing u v)

end SlabPoincareExpected
end P102.U4
