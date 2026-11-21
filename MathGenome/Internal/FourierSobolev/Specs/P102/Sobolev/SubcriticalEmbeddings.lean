import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalWhole
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension

/-! Independent statement of paper.tex, AN-11-C04-R02, 1782–1828.
The shared Sobolev sum norm is an equivalent full first-order norm, as allowed
at 1708–1710. The gradient length is Euclidean. Scalars can be real or complex.
The Lipschitz condition includes boundedness but does not include connectedness.
The zero-boundary clause imposes no geometry on its open set. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace P102.Sobolev
open P102.U4

/-- The Euclidean weak gradient on an arbitrary open set, using the same
coordinate derivatives as the whole-space interface. -/
def weakGradientOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : U4.Sobolev 𝕜 Ω 1 p) :
    Space d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => sobolevDerivative u (firstIndex i) x)

/-- The target exponent is in the normed Lp range throughout the source range. -/
theorem one_le_criticalExponent {d : ℕ} {p : ℝ≥0} (hp : 1 ≤ p) (hpd : p < d) :
    1 ≤ criticalExponent d p := by
  apply hp.trans
  rw [criticalExponent, le_div_iff₀ (tsub_pos_iff_lt.mpr hpd)]
  calc
    p * (d - p) ≤ p * d := mul_le_mul_of_nonneg_left tsub_le_self (by positivity)
    _ = d * p := mul_comm _ _

/-- The actual inclusion on almost-everywhere classes is a continuous scalar
linear injection, and it preserves the underlying class on the open set. -/
def HasSobolevInclusion {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] : Prop :=
  ∃ I : U4.Sobolev 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω q,
    Function.Injective I ∧ ∀ u,
      (I u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] sobolevUnderlying u

/-- The analogous inclusion for the closed zero-boundary subspace. -/
def HasZeroSobolevInclusion {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] : Prop :=
  ∃ I : SobolevZero 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω q,
    Function.Injective I ∧ ∀ u,
      (I u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] sobolevUnderlying u.val

namespace SubcriticalEmbeddingsExpected

/-- The complete homogeneous whole-space clause, together with its inclusion. -/
def Whole : Prop :=
  SubcriticalWholeExpected.Inequality ∧
  ∀ (d : ℕ), 2 ≤ d → ∀ (p : ℝ≥0) (hp : 1 ≤ p) (hpd : p < d),
    letI : Fact (1 ≤ (criticalExponent d p : ℝ≥0∞)) :=
      ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
    ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (p : ℝ≥0∞))],
      HasSobolevInclusion 𝕜 (⊤ : Opens (Space d)) p (criticalExponent d p)

/-- Full-norm estimate on every bounded Lipschitz open set of dimension at
least two. The arbitrary linear isometry just identifies the shared graph
coordinate model with R^(m+1). The constant is independent of the scalar field. -/
def Lipschitz : Prop :=
  ∀ (m : ℕ), 2 ≤ m + 1 →
    ∀ (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
      (Ω : Opens (Space (m + 1))),
      Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
      ∀ (p : ℝ≥0) (hp : 1 ≤ p) (hpd : p < ((m + 1 : ℕ) : ℝ≥0)),
        letI : Fact (1 ≤ (criticalExponent (m + 1) p : ℝ≥0∞)) :=
          ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
        ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (p : ℝ≥0∞))],
          (∀ u : U4.Sobolev 𝕜 Ω 1 p,
            MemLp (sobolevUnderlying u) (criticalExponent (m + 1) p)
              (volume.restrict (Ω : Set (Space (m + 1)))) ∧
            eLpNorm (sobolevUnderlying u) (criticalExponent (m + 1) p)
                (volume.restrict (Ω : Set (Space (m + 1)))) ≤
              (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) ∧
          HasSobolevInclusion 𝕜 Ω p (criticalExponent (m + 1) p)

/-- Gradient-only estimate on W₀ for an arbitrary open set. Its constant is
uniform in the open set as well as in the scalar field. -/
def Zero : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (p : ℝ≥0) (hp : 1 ≤ p) (hpd : p < d),
    letI : Fact (1 ≤ (criticalExponent d p : ℝ≥0∞)) :=
      ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
    ∃ C : ℝ≥0, ∀ (Ω : Opens (Space d)) (𝕜 : Type) [RCLike 𝕜]
      [Fact (1 ≤ (p : ℝ≥0∞))],
      (∀ u : SobolevZero 𝕜 Ω 1 p,
        MemLp (weakGradientOn u.val) p (volume.restrict (Ω : Set (Space d))) ∧
        MemLp (sobolevUnderlying u.val) (criticalExponent d p)
          (volume.restrict (Ω : Set (Space d))) ∧
        eLpNorm (sobolevUnderlying u.val) (criticalExponent d p)
            (volume.restrict (Ω : Set (Space d))) ≤
          (C : ℝ≥0∞) * eLpNorm (weakGradientOn u.val) p
            (volume.restrict (Ω : Set (Space d)))) ∧
      HasZeroSobolevInclusion 𝕜 Ω p (criticalExponent d p)

end SubcriticalEmbeddingsExpected
end P102.Sobolev
