import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.OrthonormalExpansion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.SingularApproximation
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Definitions for paper.tex 11408–11442. Scalars are real or complex, both
Hilbert spaces and all basis index types are arbitrary (possibly empty).
`basisSquareSum` is an extended nonnegative sum, hence includes divergent
families. It is NOT the real `tsum`, which would assign zero to divergence.
The canonical squared size takes the supremum over orthonormal bases realized
as subsets of H. The theorem `SquareSumInBasis` identifies it with the sum in
EVERY basis, including bases indexed in other universes. This supremum avoids
making a noncanonical basis choice in the definitions.

The finite-valued norm is defined on the subtype S₂. Compactness, the singular
value equality, the ideal operations and the complete Hilbert structure are
allocated to HilbertSchmidtBasis; they are not assumed in these definitions.
`singularSquareSum` uses the accepted canonical ordered values starting at 1,
with their existing zero padding. It does not define S₂ on general operators.
-/
noncomputable section
namespace ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec
universe u v w a b c
open scoped InnerProductSpace ENNReal

abbrev IsBasis {𝕜 : Type u} {H : Type v} {ι : Type a} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (e : ι → H) : Prop :=
  ExpandedFA.Hilbert.OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H ι e

/-- The column square sum, before imposing any basis hypothesis. -/
abbrev BasisSquareSumType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] {ι : Type a}, (H →L[𝕜] K) → (ι → H) → ℝ≥0∞

def BasisSquareSumValue : BasisSquareSumType.{u, v, w, a} :=
  fun T e => ∑' i, ENNReal.ofReal (‖T (e i)‖ ^ 2)

/-- The extended square sum of matrix coefficients, source index first. -/
abbrev MatrixSquareSumType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] {ι : Type a} {κ : Type b}, (H →L[𝕜] K) → (ι → H) → (κ → K) → ℝ≥0∞

def MatrixSquareSumValue : MatrixSquareSumType.{u, v, w, a, b} :=
  fun {𝕜} _ {_} {_} _ _ _ _ {_} {_} T e f => ∑' i, ∑' j, ENNReal.ofReal (‖inner 𝕜 (f j) (T (e i))‖ ^ 2)

/-- Canonical squared Hilbert–Schmidt size; no compactness hypothesis. -/
abbrev HilbertSchmidtSquareType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → ℝ≥0∞

def HilbertSchmidtSquareValue : HilbertSchmidtSquareType.{u, v, w} :=
  fun {𝕜} _ {H} {_} _ _ _ _ _ _ T => ⨆ (S : Set H) (_ : IsBasis (𝕜 := 𝕜) (Subtype.val : S → H)),
    BasisSquareSumValue T (Subtype.val : S → H)

/-- S₂ is exactly finiteness of the extended matrix square sum. -/
abbrev IsHilbertSchmidtType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → Prop

def IsHilbertSchmidtValue : IsHilbertSchmidtType.{u, v, w} :=
  fun T => HilbertSchmidtSquareValue T < ∞

/-- Hilbert–Schmidt maps between the original Hilbert spaces. -/
abbrev HilbertSchmidtMapType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], Type (max v w)

abbrev HilbertSchmidtMapValue : HilbertSchmidtMapType.{u, v, w} :=
  fun {𝕜} _ {H} {K} _ _ _ _ _ _ => {T : H →L[𝕜] K // IsHilbertSchmidtValue T}

/-- The finite Hilbert–Schmidt norm on S₂. -/
abbrev HilbertSchmidtNormType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K) → ℝ

def HilbertSchmidtNormValue : HilbertSchmidtNormType.{u, v, w} :=
  fun T => Real.sqrt (HilbertSchmidtSquareValue T.val).toReal

/-- Squared sum of the canonical ordered, zero-padded singular values. -/
abbrev SingularSquareSumType := ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K], (H →L[𝕜] K) → ℝ≥0∞

def SingularSquareSumValue : SingularSquareSumType.{u, v, w} :=
  fun T => ∑' n : ℕ, ENNReal.ofReal
    (ExpandedFA.CompactSpectral.SingularApproximation.Spec.SingularValueValue T (n + 1) ^ 2)

def FiniteSumSupremum : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K] {ι : Type a} (T : H →L[𝕜] K) (e : ι → H),
    BasisSquareSumValue T e = ⨆ s : Finset ι, ∑ i ∈ s, ENNReal.ofReal (‖T (e i)‖ ^ 2)

def MatrixIdentity : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {ι : Type a} {κ : Type b} (T : H →L[𝕜] K)
    (e : ι → H) (f : κ → K),
    IsBasis (𝕜 := 𝕜) f → BasisSquareSumValue T e = MatrixSquareSumValue T e f

def AdjointBasisIdentity : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {ι : Type a} {κ : Type b} (T : H →L[𝕜] K)
    (e : ι → H) (f : κ → K),
    IsBasis (𝕜 := 𝕜) e → IsBasis (𝕜 := 𝕜) f →
    BasisSquareSumValue T e = BasisSquareSumValue (ContinuousLinearMap.adjoint T) f

def BasisIndependence : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {ι : Type a} {ι' : Type b} (T : H →L[𝕜] K)
    (e : ι → H) (e' : ι' → H),
    IsBasis (𝕜 := 𝕜) e → IsBasis (𝕜 := 𝕜) e' → BasisSquareSumValue T e = BasisSquareSumValue T e'

def SquareSumInBasis : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {ι : Type a} (T : H →L[𝕜] K) (e : ι → H),
    IsBasis (𝕜 := 𝕜) e → HilbertSchmidtSquareValue T = BasisSquareSumValue T e

def FinitenessInBasis : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {ι : Type a} (T : H →L[𝕜] K) (e : ι → H),
    IsBasis (𝕜 := 𝕜) e → (IsHilbertSchmidtValue T ↔ Summable (fun i => ‖T (e i)‖ ^ 2))

def NormSquareInBasis : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] {ι : Type a}
    (T : HilbertSchmidtMapValue (𝕜 := 𝕜) (H := H) (K := K)) (e : ι → H),
    IsBasis (𝕜 := 𝕜) e → 0 ≤ HilbertSchmidtNormValue T ∧
    HilbertSchmidtNormValue T ^ 2 = ∑' i, ‖T.val (e i)‖ ^ 2

def ZeroSquare : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
    HilbertSchmidtSquareValue (0 : H →L[𝕜] K) = 0 ∧ IsHilbertSchmidtValue (0 : H →L[𝕜] K)

end ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec

