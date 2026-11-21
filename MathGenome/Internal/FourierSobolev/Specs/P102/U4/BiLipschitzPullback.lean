import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ChainProduct
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.Rademacher
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.MeyersSerrin

/-! Independent scope of the coordinate clause of paper.tex:1677–1686.
The maps are ambient representatives of inverse maps between the two opens.
Their values off the respective domains are unrestricted. The two Lipschitz
conditions and inverse identities in `BiLipschitzChart` imply a homeomorphism
of the open subspaces. No boundary or finite-volume hypothesis is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace P102.U4

structure BiLipschitzChart {d : ℕ} (U V : Opens (Space d)) (L M : ℝ≥0) where
  toFun : Space d → Space d
  invFun : Space d → Space d
  mapsTo : MapsTo toFun V U
  inv_mapsTo : MapsTo invFun U V
  left_inv : ∀ x ∈ V, invFun (toFun x) = x
  right_inv : ∀ y ∈ U, toFun (invFun y) = y
  lipschitz : LipschitzOnWith L toFun V
  inv_lipschitz : LipschitzOnWith M invFun U

/-- The finite-exponent change factor, equal to one at p = ∞. -/
def pullbackLpBound (d : ℕ) (p : ℝ≥0∞) (M : ℝ≥0) : ℝ :=
  ((M : ℝ) ^ d) ^ (1 / p).toReal

/-- A bound for the source's sum of coordinate derivative norms. -/
def pullbackSobolevBound (d : ℕ) (p : ℝ≥0∞) (L M : ℝ≥0) : ℝ :=
  pullbackLpBound d p M * (1 + (d : ℝ) * (L : ℝ))

/-- Canonical measurable representative of the a.e. derivative of a chart. -/
def chartDerivative {d : ℕ} {U V : Opens (Space d)} {L M : ℝ≥0}
    (g : BiLipschitzChart U V L M) : Space d → (Space d →L[ℝ] Space d) :=
  fderiv ℝ g.toFun

namespace BiLipschitzPullbackExpected

/-- Outer-measure inequalities, hence in particular all measurable-set
inequalities. The dimensional constant can be taken to be one. -/
def Distortion : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (U V : Opens (Space d)) (L M : ℝ≥0)
    (g : BiLipschitzChart U V L M),
    (∀ E : Set (Space d),
      volume ((V : Set (Space d)) ∩ g.toFun ⁻¹' E) ≤
        (M : ℝ≥0∞) ^ d * volume ((U : Set (Space d)) ∩ E)) ∧
    (∀ E : Set (Space d),
      volume ((U : Set (Space d)) ∩ g.invFun ⁻¹' E) ≤
        (L : ℝ≥0∞) ^ d * volume ((V : Set (Space d)) ∩ E)) ∧
    (∀ E : Set (Space d), E ⊆ V → volume E = 0 → volume (g.toFun '' E) = 0) ∧
    (∀ E : Set (Space d), E ⊆ U → volume E = 0 → volume (g.invFun '' E) = 0)

/-- Full Lp estimates, including the essential-supremum estimate, and the
bounded scalar-linear operator on equivalence classes. -/
def LpPullback : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (U V : Opens (Space d)) (L M : ℝ≥0) (g : BiLipschitzChart U V L M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (∀ f : Space d → 𝕜, MemLp f p (volume.restrict (U : Set (Space d))) →
      MemLp (f ∘ g.toFun) p (volume.restrict (V : Set (Space d))) ∧
      eLpNorm (f ∘ g.toFun) p (volume.restrict (V : Set (Space d))) ≤
        ((M : ℝ≥0∞) ^ d) ^ (1 / p).toReal *
          eLpNorm f p (volume.restrict (U : Set (Space d)))) ∧
    ∃ T : DomainLp 𝕜 U p →L[𝕜] DomainLp 𝕜 V p,
      (∀ u, T u =ᵐ[volume.restrict (V : Set (Space d))] (u ∘ g.toFun)) ∧
      ‖T‖ ≤ pullbackLpBound d p M

/-- The same derivative is a classical derivative a.e., a weak derivative,
globally essentially bounded, and has the sharp Lipschitz bound. -/
def Derivative : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (U V : Opens (Space d)) (L M : ℝ≥0)
    (g : BiLipschitzChart U V L M),
    Measurable (chartDerivative g) ∧
    (∀ᵐ x ∂volume.restrict (V : Set (Space d)),
      HasFDerivAt g.toFun (chartDerivative g x) x) ∧
    (∀ i j : Fin d,
      LocallyIntegrableOn (fun x => (chartDerivative g x (coordinateVector d j)) i) V volume ∧
      distributionPartial {j} (regularDistribution V (fun x => g.toFun x i)) =
        regularDistribution V (fun x => (chartDerivative g x (coordinateVector d j)) i)) ∧
    MemLp (chartDerivative g) ∞ (volume.restrict (V : Set (Space d))) ∧
    (∀ᵐ x ∂volume.restrict (V : Set (Space d)), ‖chartDerivative g x‖ ≤ L)

/-- The coordinate version of Du(g(x)) Dg(x). Scalar multiplication is by
the real matrix entries, also when the scalar field is complex. The p = ∞
case is included; there is no W^{1,∞} norm-density premise. -/
def SobolevPullback : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (U V : Opens (Space d)) (L M : ℝ≥0) (g : BiLipschitzChart U V L M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ T : Sobolev 𝕜 U 1 p →L[𝕜] Sobolev 𝕜 V 1 p,
      (∀ u, sobolevUnderlying (T u) =ᵐ[volume.restrict (V : Set (Space d))]
        (sobolevUnderlying u ∘ g.toFun)) ∧
      (∀ u (j : Fin d),
        firstWeakDerivative (T u) j =ᵐ[volume.restrict (V : Set (Space d))]
          (fun x => ∑ i : Fin d,
            (chartDerivative g x (coordinateVector d j) i) •
              firstWeakDerivative u i (g.toFun x))) ∧
      ‖T‖ ≤ pullbackSobolevBound d p L M

end BiLipschitzPullbackExpected
end P102.U4
