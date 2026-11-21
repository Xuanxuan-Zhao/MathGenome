import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.OrthonormalExpansion
import Mathlib.SetTheory.Cardinal.Basic

/-!
Independent statements for paper.tex 7465–7497, the cardinal invariant and
unitary classification. A basis means the shared maximal orthonormal family,
with arbitrary index universes. Cardinal lifts compare different universes.
A unitary is a scalar-linear isometric equivalence, over either ℝ or ℂ.
No nonzero, nonempty, finite-dimensional or separability condition is imposed.
Existence, finite-subset-net expansion, Parseval and countable coefficient
support are the accepted OrthonormalExpansion prerequisites.
-/

noncomputable section

namespace ExpandedFA.Hilbert.HilbertCardinalityClassification.Spec
universe u v t w z

/-- Any two orthonormal bases of the same Hilbert space have equal cardinality,
including empty bases and finite bases. -/
def BasisCardinalityInvariant : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) (κ : Type z) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H) (f : κ → H),
    OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H ι e →
    OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H κ f →
    Cardinal.lift.{z} (Cardinal.mk ι) = Cardinal.lift.{w} (Cardinal.mk κ)

/-- Every prescribed bijection of orthonormal bases extends to a unitary. -/
def BasisBijectionExtends : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type t) (ι : Type w) (κ : Type z) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (e : ι → H) (f : κ → K),
    OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H ι e →
    OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 K κ f →
    ∀ p : ι ≃ κ, ∃ U : H ≃ₗᵢ[𝕜] K, ∀ i, U (e i) = f (p i)

/-- For any choices of bases, unitary equivalence is exactly equality of
basis cardinalities. This includes zero spaces and all infinite cardinals. -/
def UnitaryClassification : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (K : Type t) (ι : Type w) (κ : Type z) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (e : ι → H) (f : κ → K),
    OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H ι e →
    OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 K κ f →
    (Nonempty (H ≃ₗᵢ[𝕜] K) ↔
      Cardinal.lift.{z} (Cardinal.mk ι) = Cardinal.lift.{w} (Cardinal.mk κ))

end ExpandedFA.Hilbert.HilbertCardinalityClassification.Spec
