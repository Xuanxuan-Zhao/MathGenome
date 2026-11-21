import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent statements for paper.tex:3489–3501.
The domain is the actual positive half-line, with its trace Borel structure
and the completion of the pullback of Lebesgue volume. The real powers are embedded in either
scalar field. Membership uses the upstream raw space, hence ordinary measurable
representatives and the ordinary a.e. convention. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch10.InclusionFailure

abbrev PositiveHalfLine := Ioi (0 : ℝ)

def halfLineVolume : Measure PositiveHalfLine :=
  (volume : Measure ℝ).comap Subtype.val

/-- The raw space on completed Lebesgue measure. The type tag changes only
its sigma-algebra; its elements remain the same points of `(0,∞)`. -/
def lebesgueLp (𝕂 : Type*) [RCLike 𝕂] (p : ℝ) : Set (PositiveHalfLine → 𝕂) :=
  @LpDefinition.rawLp_value (NullMeasurableSpace PositiveHalfLine halfLineVolume) 𝕂
    inferInstance inferInstance inferInstance halfLineVolume.completion p

/-- `x⁻ᵃ 1_s`, restricted to the positive half-line. -/
def cutoffPower (𝕂 : Type*) [RCLike 𝕂] (s : Set ℝ) (a : ℝ) : PositiveHalfLine → 𝕂 :=
  fun x => s.indicator (fun t : ℝ => ((t ^ (-a) : ℝ) : 𝕂)) x

abbrev nearZero (𝕂 : Type*) [RCLike 𝕂] (a : ℝ) := cutoffPower 𝕂 (Ioo 0 1) a
abbrev atInfinity (𝕂 : Type*) [RCLike 𝕂] (b : ℝ) := cutoffPower 𝕂 (Ioi 1) b

/-- All choices in the source's first exponent range, including `a = 1/q`. -/
def nearZero_separates : Prop := ∀ (𝕂 : Type*) [RCLike 𝕂] (p q a : ℝ),
  1 ≤ p → p < q → 1 / q ≤ a → a < 1 / p →
  nearZero 𝕂 a ∈ lebesgueLp 𝕂 p ∧
  nearZero 𝕂 a ∉ lebesgueLp 𝕂 q

/-- All choices in the second exponent range, including `b = 1/p`. -/
def atInfinity_separates : Prop := ∀ (𝕂 : Type*) [RCLike 𝕂] (p q b : ℝ),
  1 ≤ p → p < q → 1 / q < b → b ≤ 1 / p →
  atInfinity 𝕂 b ∈ lebesgueLp 𝕂 q ∧
  atInfinity 𝕂 b ∉ lebesgueLp 𝕂 p

/-- In particular neither of these raw spaces includes the other. -/
def neither_inclusion : Prop := ∀ (𝕂 : Type*) [RCLike 𝕂] (p q : ℝ),
  1 ≤ p → p < q →
  (¬ lebesgueLp 𝕂 p ⊆
      lebesgueLp 𝕂 q) ∧
  (¬ lebesgueLp 𝕂 q ⊆
      lebesgueLp 𝕂 p)

/-- The exclusions hold for the ordinary a.e. classes: no change on a null
set can give a representative in the other space. Completion has the same
ordinary null sets and a.e. filter as `halfLineVolume`. -/
def ordinary_ae_class_separation : Prop := ∀ (𝕂 : Type*) [RCLike 𝕂] (p q a b : ℝ),
  1 ≤ p → p < q → 1 / q ≤ a → a < 1 / p → 1 / q < b → b ≤ 1 / p →
  (∀ g : PositiveHalfLine → 𝕂, nearZero 𝕂 a =ᵐ[halfLineVolume] g →
    g ∉ lebesgueLp 𝕂 q) ∧
  (∀ g : PositiveHalfLine → 𝕂, atInfinity 𝕂 b =ᵐ[halfLineVolume] g →
    g ∉ lebesgueLp 𝕂 p)

end Specs.D11.Ch10.InclusionFailure
