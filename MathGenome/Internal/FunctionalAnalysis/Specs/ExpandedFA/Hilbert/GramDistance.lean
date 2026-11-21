import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertProjection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
Independent statements for paper.tex 8009–8047, `fa2:p2:gram-distance`.
The scalar convention is Gᵢⱼ = ⟪yᵢ,yⱼ⟫ and bᵢ = ⟪yᵢ,x⟫.
All ambient spaces may be incomplete. Finite index types include the empty
list; a subset of the indices represents a sublist, with its inherited vectors.
The complex distance identities use the canonical embedding of the real
squared distance into the scalar field. The determinant ratio is asserted only
under linear independence, together with a nonzero denominator.
-/
noncomputable section
open scoped InnerProductSpace ComplexOrder
open Matrix

namespace ExpandedFA.Hilbert.GramDistance.Spec
universe u v w

/-- The conjugate-first right hand side of the normal equations. -/
def rhs (𝕜 : Type u) {E : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (y : ι → E) (x : E) : ι → 𝕜 :=
  fun i => ⟪y i, x⟫_𝕜

/-- The specified inverse-Gram coefficients, combined in the original space. -/
def leastSquaresPoint (𝕜 : Type u) {E : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
    (y : ι → E) (x : E) : E :=
  ∑ j, ((gram 𝕜 y)⁻¹ *ᵥ rhs 𝕜 y x) j • y j

/-- The actual augmented matrix, with one final row and column. -/
def augmentedGram (𝕜 : Type u) {E : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (y : ι → E) (x : E) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) 𝕜 :=
  fromBlocks (gram 𝕜 y) (of fun i (_ : Unit) => rhs 𝕜 y x i)
    (of fun (_ : Unit) i => star (rhs 𝕜 y x i))
    (of fun (_ : Unit) (_ : Unit) => (‖x‖ : 𝕜) ^ 2)

def GramPositivity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] (y : ι → E),
    (gram 𝕜 y).PosSemidef ∧ ((gram 𝕜 y).PosDef ↔ LinearIndependent 𝕜 y)

/-- The explicit inverse-Gram sum is the unique nearest point in the span. -/
def IndependentNearestPoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
    (y : ι → E), LinearIndependent 𝕜 y → ∀ x : E,
    let Y := Submodule.span 𝕜 (Set.range y)
    let p := leastSquaresPoint 𝕜 y x
    p ∈ Y ∧ (∀ z ∈ Y, ‖x - p‖ ≤ ‖x - z‖) ∧
      ∀ q ∈ Y, (∀ z ∈ Y, ‖x - q‖ ≤ ‖x - z‖) → q = p

def IndependentDistanceFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
    (y : ι → E), LinearIndependent 𝕜 y → ∀ x : E,
    let G := gram 𝕜 y
    let b := rhs 𝕜 y x
    let Y := Submodule.span 𝕜 (Set.range y)
    G.det ≠ 0 ∧
      (Metric.infDist x (Y : Set E) : 𝕜) ^ 2 =
        (‖x‖ : 𝕜) ^ 2 - star b ⬝ᵥ G⁻¹ *ᵥ b ∧
      (Metric.infDist x (Y : Set E) : 𝕜) ^ 2 = (augmentedGram 𝕜 y x).det / G.det

/-- No determinant quotient is asserted for a dependent list. -/
def DependentDeterminant : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
    (y : ι → E), ¬ LinearIndependent 𝕜 y → (gram 𝕜 y).det = 0

/-- A spanning independent sublist always exists, including for a dependent or
empty original list. The independent formulas apply to each such sublist. -/
def IndependentSpanningSublist : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] (y : ι → E),
    ∃ s : Set ι, LinearIndependent 𝕜 (fun i : s => y i) ∧
      Submodule.span 𝕜 (Set.range (fun i : s => y i)) =
        Submodule.span 𝕜 (Set.range y)

/-- Any independent sublist with the same span supplies the distance and
nearest point for the original target, even when the original list depends. -/
def SpanningSublistFormulas : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
    (y : ι → E) (s : Set ι),
    letI : Fintype s := Fintype.ofFinite s
    letI : DecidableEq s := Classical.decEq s
    let ys := fun i : s => y i
    LinearIndependent 𝕜 ys →
    Submodule.span 𝕜 (Set.range ys) = Submodule.span 𝕜 (Set.range y) →
    ∀ x : E,
    let Y := Submodule.span 𝕜 (Set.range y)
    let p := leastSquaresPoint 𝕜 ys x
    let G := gram 𝕜 ys
    let b := rhs 𝕜 ys x
    (p ∈ Y ∧ (∀ z ∈ Y, ‖x - p‖ ≤ ‖x - z‖) ∧
      ∀ q ∈ Y, (∀ z ∈ Y, ‖x - q‖ ≤ ‖x - z‖) → q = p) ∧
    G.det ≠ 0 ∧
      (Metric.infDist x (Y : Set E) : 𝕜) ^ 2 =
        (‖x‖ : 𝕜) ^ 2 - star b ⬝ᵥ G⁻¹ *ᵥ b ∧
      (Metric.infDist x (Y : Set E) : 𝕜) ^ 2 = (augmentedGram 𝕜 ys x).det / G.det

def EmptyList : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] [DecidableEq ι]
    [IsEmpty ι] (y : ι → E) (x : E),
    (gram 𝕜 y).det = 1 ∧ Submodule.span 𝕜 (Set.range y) = ⊥ ∧
      leastSquaresPoint 𝕜 y x = 0 ∧
      Metric.infDist x (Submodule.span 𝕜 (Set.range y) : Set E) = ‖x‖

end ExpandedFA.Hilbert.GramDistance.Spec
