import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-! Independent statements for `fa2:p4:stieltjes-bridge`.
A measure on a closed interval is represented by its zero extension to ℝ.
Restriction explicitly supplies that extension for an arbitrary ambient measure.
The scalar field can be either ℝ or ℂ. -/
namespace ExpandedFA.FunctionSpaces.BVMeasureBridgeSpec
open Set MeasureTheory Filter
open scoped Topology ENNReal
open ScalarRieszMarkovSpec

noncomputable def cumulative {𝕜 : Type*} [RCLike 𝕜]
    (ν : VectorMeasure ℝ 𝕜) (t : ℝ) : 𝕜 := ν (Iic t)

noncomputable def intervalCumulative {𝕜 : Type*} [RCLike 𝕜]
    (a b : ℝ) (ν : VectorMeasure ℝ 𝕜) : ℝ → 𝕜 :=
  cumulative (ν.restrict (Icc a b))

/-- Canonical zero extension of an actual scalar Borel measure on [a,b]. -/
noncomputable def extendByZero {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (ν : VectorMeasure (Icc a b) 𝕜) : VectorMeasure ℝ 𝕜 := ν.map Subtype.val

/-- Explicit equivalence with the subtype interpretation of an interval measure.
This also identifies the scalar integral and total variation, without loss at
any boundary point. -/
def SubtypeBridge : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (ν : VectorMeasure (Icc a b) 𝕜),
    IsFiniteMeasure ν.variation →
    IsFiniteMeasure (extendByZero ν).variation ∧
    (extendByZero ν).restrict (Icc a b) = extendByZero ν ∧
    (∀ s : Set ℝ, MeasurableSet s → extendByZero ν s = ν (Subtype.val ⁻¹' s)) ∧
    (∀ t, intervalCumulative a b (extendByZero ν) t = ν {x | (x : ℝ) ≤ t}) ∧
    (extendByZero ν).variation (Icc a b) = ν.variation univ ∧
    (∀ f : ℝ → 𝕜, scalarIntegral (extendByZero ν) f = scalarIntegral ν (f ∘ Subtype.val))

/-- No order condition on the endpoints is needed, so empty and singleton
intervals are included. Finiteness refers to total variation. -/
def ForwardBridge : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (ν : VectorMeasure ℝ 𝕜),
    IsFiniteMeasure ν.variation →
    (∀ t, ContinuousWithinAt (intervalCumulative a b ν) (Ici t) t) ∧
    BoundedVariationOn (intervalCumulative a b ν) univ ∧
    (∀ t, t < a → intervalCumulative a b ν t = 0) ∧
    (∀ t, b ≤ t → intervalCumulative a b ν t = ν (Icc a b)) ∧
    (∀ s t, s ≤ t → (ν.restrict (Icc a b)) (Ioc s t) =
      intervalCumulative a b ν t - intervalCumulative a b ν s) ∧
    eVariationOn (intervalCumulative a b ν) univ = ν.variation (Icc a b)

/-- The forward result directly for measures whose domain is the original
closed interval, with the original cumulative function and mass. -/
def SubtypeForwardBridge : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (ν : VectorMeasure (Icc a b) 𝕜),
    IsFiniteMeasure ν.variation →
    let F : ℝ → 𝕜 := fun t => ν {x | (x : ℝ) ≤ t}
    (∀ t, ContinuousWithinAt F (Ici t) t) ∧ BoundedVariationOn F univ ∧
    (∀ t, t < a → F t = 0) ∧ (∀ t, b ≤ t → F t = ν univ) ∧
    (∀ s t, s ≤ t → extendByZero ν (Ioc s t) = F t - F s) ∧
    eVariationOn F univ = ν.variation univ

/-- Normalization fixes the otherwise undetermined additive constant. -/
def NormalizedBV {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ) (F : ℝ → 𝕜) : Prop :=
  (∀ t, ContinuousWithinAt F (Ici t) t) ∧ BoundedVariationOn F univ ∧
  (∀ t, t < a → F t = 0) ∧ (∀ t, b ≤ t → F t = F b)

def ConverseBridge : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (F : ℝ → 𝕜), NormalizedBV a b F →
    ∃ ν : VectorMeasure ℝ 𝕜,
      IsFiniteMeasure ν.variation ∧ ν.restrict (Icc a b) = ν ∧
      (∀ t, cumulative ν t = F t) ∧
      eVariationOn F univ = ν.variation univ ∧
      (∀ s t, s ≤ t → ν (Ioc s t) = F t - F s) ∧
      ∀ η : VectorMeasure ℝ 𝕜, IsFiniteMeasure η.variation →
        (∀ t, cumulative η t = F t) → η = ν

/-- The converse with the resulting measure on the original closed interval. -/
def SubtypeConverseBridge : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (F : ℝ → 𝕜), NormalizedBV a b F →
    ∃ ν : VectorMeasure (Icc a b) 𝕜,
      IsFiniteMeasure ν.variation ∧
      (∀ t, ν {x | (x : ℝ) ≤ t} = F t) ∧
      eVariationOn F univ = ν.variation univ ∧
      (∀ s t, s ≤ t → extendByZero ν (Ioc s t) = F t - F s) ∧
      ∀ η : VectorMeasure (Icc a b) 𝕜, IsFiniteMeasure η.variation →
        (∀ t, η {x | (x : ℝ) ≤ t} = F t) → η = ν

/-- A tagged partition. Repeated points and the zero-cell partition are
allowed; this also handles a singleton interval. -/
structure TaggedPartition (a b : ℝ) where
  n : ℕ
  point : ℕ → ℝ
  mono : Monotone point
  first : point 0 = a
  last : point n = b
  tag : ℕ → ℝ
  tag_mem : ∀ i < n, tag i ∈ Icc (point i) (point (i+1))

/-- The isolated first term includes the lower endpoint atom. The remaining
increments are the ordinary global right-continuous increments on (a,b]. -/
noncomputable def stieltjesSum {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (p : TaggedPartition a b) (F f : ℝ → 𝕜) : 𝕜 :=
  f a * F a + ∑ i ∈ Finset.range p.n,
    f (p.tag i) * (F (p.point (i+1)) - F (p.point i))

/-- All sufficiently fine tagged sums converge to the scalar integral. The
integrand is only required to be continuous on the original closed interval. -/
def StieltjesFunctional : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (ν : VectorMeasure ℝ 𝕜),
    IsFiniteMeasure ν.variation → ∀ f : ℝ → 𝕜, ContinuousOn f (Icc a b) →
    Integrable f (ν.variation.restrict (Icc a b)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ p : TaggedPartition a b,
        (∀ i < p.n, p.point (i+1) - p.point i < δ) →
        ‖stieltjesSum p (intervalCumulative a b ν) f -
          scalarIntegral (ν.restrict (Icc a b)) f‖ < ε
/-- Arbitrary interval functions can be used as ambient integrands by setting
them to zero outside the interval; no continuity outside [a,b] is required. -/
noncomputable def intervalIntegrand {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}
    (f : C(Icc a b, 𝕜)) (x : ℝ) : 𝕜 :=
  if hx : x ∈ Icc a b then f ⟨x, hx⟩ else 0

/-- The integral identity directly for continuous functions on the actual
closed-interval subtype, not just restrictions of chosen ambient functions. -/
def SubtypeStieltjesFunctional : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) (ν : VectorMeasure (Icc a b) 𝕜),
    IsFiniteMeasure ν.variation → ∀ f : C(Icc a b, 𝕜),
    Integrable f ν.variation ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ p : TaggedPartition a b,
        (∀ i < p.n, p.point (i+1) - p.point i < δ) →
        ‖stieltjesSum p (fun t => ν {x | (x : ℝ) ≤ t}) (intervalIntegrand f) -
          scalarIntegral ν f‖ < ε

end ExpandedFA.FunctionSpaces.BVMeasureBridgeSpec
