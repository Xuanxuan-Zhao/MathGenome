import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalEmbeddings

/-! Independent statement of paper.tex, Theorem U5-02, 1962–2034.
Exponents include infinity. The reciprocal convention is `∞.toReal⁻¹ = 0`.
All three ranges are retained, including reversed subcritical interpolation
when r > p*, p = ∞, and the exceptional d = p = 1 endpoint.
The domain estimate uses the actual Euclidean gradient plus the zeroth-order
Lp norm, rather than an assumed extension norm. ENNReal.rpow_zero = 1
implements omission of zero-exponent factors, even when the base is zero.
The Sobolev objects are the shared distribution-defined almost-everywhere classes.
-/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace P102.Sobolev.GagliardoNirenberg
open P102.U4

/-- The subcritical exponent, only used under p < d. -/
def sobolevExponent (d : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  criticalExponent d p.toNNReal

/-- Exactly the three source ranges; critical infinity is excluded. -/
def AllowedRange (d : ℕ) (p r q : ℝ≥0∞) : Prop :=
  (p < d ∧ ((r ≤ q ∧ q ≤ sobolevExponent d p) ∨
    (sobolevExponent d p ≤ q ∧ q ≤ r))) ∨
  (p = d ∧ 2 ≤ d ∧ r ≤ q ∧ q ≠ ⊤) ∨
  (((d : ℝ≥0∞) < p ∨ (d = 1 ∧ p = 1)) ∧ r ≠ ⊤ ∧ r ≤ q)

/-- The dilation equation, using 1/∞ = 0. -/
def Scaling (d : ℕ) (p r q : ℝ≥0∞) (a : ℝ) : Prop :=
  q.toReal⁻¹ = a * (p.toReal⁻¹ - (d : ℝ)⁻¹) + (1 - a) * r.toReal⁻¹

/-- Whole-space family, with C independent of u. -/
def Whole : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
    ∀ (p r q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ r → 1 ≤ q →
    ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → AllowedRange d p r q → Scaling d p r q a →
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
      MemLp (sobolevUnderlying u) r volume →
      MemLp (sobolevUnderlying u) q volume ∧
      eLpNorm (sobolevUnderlying u) q volume ≤
        (C : ℝ≥0∞) * eLpNorm (weakGradient u) p volume ^ a *
          eLpNorm (sobolevUnderlying u) r volume ^ (1 - a)

/-- The same complete family on every bounded Lipschitz open set, including
one-dimensional and disconnected sets. The coordinate isometry is arbitrary. -/
def Domain : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : ℕ)
    (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    ∀ (p r q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ r → 1 ≤ q →
    ∀ (a : ℝ), 0 ≤ a → a ≤ 1 → AllowedRange (m + 1) p r q →
    Scaling (m + 1) p r q a →
    ∃ C : ℝ≥0, ∀ u : U4.Sobolev 𝕜 Ω 1 p,
      MemLp (sobolevUnderlying u) r (volume.restrict (Ω : Set (Space (m + 1)))) →
      MemLp (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space (m + 1)))) ∧
      eLpNorm (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space (m + 1)))) ≤
        (C : ℝ≥0∞) *
          (eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space (m + 1)))) +
            eLpNorm (sobolevUnderlying u) p (volume.restrict (Ω : Set (Space (m + 1))))) ^ a *
          eLpNorm (sobolevUnderlying u) r (volume.restrict (Ω : Set (Space (m + 1)))) ^ (1 - a)

end P102.Sobolev.GagliardoNirenberg
