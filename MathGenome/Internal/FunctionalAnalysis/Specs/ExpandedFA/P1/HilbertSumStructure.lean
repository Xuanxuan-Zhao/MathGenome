import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSum

/-!
Independent statements for the Hilbert and coordinate clauses of
`fa2:p1:c02:hilbert-sum-complete`, paper.tex 497–529.

The space, its norm, its inner product, and its coordinate maps are the
canonical objects fixed by the direct-sum interface. `HasSum` uses the net
of finite-subset sums. No enumeration, countability, separability, or
nonempty-index assumption is made. The inner-product assertions hold even
without completeness of the summands; completeness is required only for
the completeness assertion. The support/density clauses are allocated
separately to `root_hilbert_sum_support_density`.
-/

noncomputable section
open scoped ComplexConjugate
universe u v w
namespace ExpandedFA.P1.HilbertSumStructure.Spec
open ExpandedFA.P1.C02HilbertSum.Spec

/-- Absolute summability, its quantitative bound, and the finite-subset
sum giving the canonical inner product. -/
def AbsoluteInnerSummability : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)]
    (x y : Space H),
    Summable (fun i => ‖inner 𝕜 (x i) (y i)‖) ∧
    (∑' i, ‖inner 𝕜 (x i) (y i)‖) ≤ ‖x‖ * ‖y‖ ∧
    HasSum (fun i => inner 𝕜 (x i) (y i)) (inner 𝕜 x y)

/-- The actual product is additive in each slot, conjugate-linear in the
first, linear in the second, conjugate symmetric, and positive definite. -/
def InnerProductLaws : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)],
    (∀ x y z : Space H, inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z) ∧
    (∀ x y z : Space H, inner 𝕜 x (y + z) = inner 𝕜 x y + inner 𝕜 x z) ∧
    (∀ (a : 𝕜) (x y : Space H),
      inner 𝕜 (a • x) y = conj a * inner 𝕜 x y) ∧
    (∀ (a : 𝕜) (x y : Space H),
      inner 𝕜 x (a • y) = a * inner 𝕜 x y) ∧
    (∀ x y : Space H, inner 𝕜 y x = conj (inner 𝕜 x y)) ∧
    (∀ x : Space H, 0 ≤ RCLike.re (inner 𝕜 x x)) ∧
    (∀ x : Space H, inner 𝕜 x x = 0 ↔ x = 0)

/-- Compatibility with the already fixed norm and the manuscript's
nonnegative sum (both as a tsum and as a supremum over finite subsets). -/
def NormSquaredFormula : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)]
    (x : Space H),
    RCLike.re (inner 𝕜 x x) = ‖x‖ ^ 2 ∧
    ‖x‖ ^ 2 = ∑' i, ‖x i‖ ^ 2 ∧
    ‖x‖ ^ 2 = squaredSum H (fun i => x i)

/-- Completeness for the original norm and topology. Combined with the
canonical compatible inner product, this asserts that the sum is Hilbert. -/
def Completeness : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, CompleteSpace (H i)], CompleteSpace (Space H)

/-- Each coordinate projection has operator norm at most one and is
nonexpansive for the given norms. Zero summands are permitted. -/
def CoordinateContractive : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)] (i : I),
    ‖coordinate (𝕜 := 𝕜) H i‖ ≤ 1 ∧
    LipschitzWith 1 (coordinate (𝕜 := 𝕜) H i)

/-- Each coordinate inclusion is likewise contractive. -/
def InclusionContractive : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)] (i : I),
    ‖inclusion (𝕜 := 𝕜) H i‖ ≤ 1 ∧
    LipschitzWith 1 (inclusion (𝕜 := 𝕜) H i)

/-- The same inclusion preserves all distances and norms. -/
def InclusionIsometric : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)]
    {𝕜 : Type w} [RCLike 𝕜] [∀ i, InnerProductSpace 𝕜 (H i)] (i : I),
    Isometry (inclusion (𝕜 := 𝕜) H i) ∧
    ∀ a : H i, ‖inclusion (𝕜 := 𝕜) H i a‖ = ‖a‖

end ExpandedFA.P1.HilbertSumStructure.Spec
