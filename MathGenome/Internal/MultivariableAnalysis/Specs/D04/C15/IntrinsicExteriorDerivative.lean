import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.ChartIndependentTangentSpaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.DifferentialIdentities

/-! Intrinsic tangent covector fields on the shared embedded C² manifold model.
At a boundary point C¹ means local C¹ extendibility of chart coefficients.
The coordinate differential uses derivatives within the chart source, so it does
not differentiate an arbitrary zero extension across a genuine boundary. -/
noncomputable section
open Set
open scoped BigOperators Classical
namespace Specs.D04.C15.IntrinsicExteriorDerivative
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
namespace Model

abbrev Tangent {k n : ℕ} (M : Set (E n)) (x : M) := tangentSpace 2 k M x
abbrev IntrinsicForm {k n : ℕ} (M : Set (E n)) (p : ℕ) :=
  (x : M) → Covector (Tangent (k := k) M x) p

/-- The differential with codomain restricted to the intrinsic tangent space.
Its range is a summand in the defining supremum, without assuming independence. -/
def chartTangentMap {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 2 k n M) (u : E k) (hu : u ∈ c.source) :
    E k →ₗ[ℝ] Tangent (k := k) M ⟨c.toFun u, (c.map_source hu).1⟩ :=
  (chartDifferential c u).toLinearMap.codRestrict _ (by
    intro v
    have h : LinearMap.range (chartDifferential c u).toLinearMap ≤
        tangentSpace 2 k M (c.toFun u) :=
      le_iSup_of_le c (le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le rfl le_rfl)))
    exact h ⟨v, rfl⟩)

/-- Values outside the source only make this an ambient representative. -/
def chartPullback {k n p : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 2 k n M) (ω : IntrinsicForm (k := k) M p) : FormField k p :=
  fun u => if hu : u ∈ c.source then
    (ω ⟨c.toFun u, (c.map_source hu).1⟩).compLinearMap (chartTangentMap c u hu)
    else 0

/-- The usual continuity condition in tangent trivializations. -/
def IntrinsicContinuous {k n p : ℕ} {M : Set (E n)}
    (ω : IntrinsicForm (k := k) M p) : Prop :=
  ∀ c : EmbeddedChart 2 k n M, ∀ I : MultiIndex k p,
    ContinuousOn (fun u => coefficient (standardBasis k) (chartPullback c ω u) I) c.source

/-- No compatibility or derivative certificate is included in this condition.
It asserts only local C¹ extensions of the coordinate form itself. -/
def IntrinsicC1 {k n p : ℕ} {M : Set (E n)}
    (ω : IntrinsicForm (k := k) M p) : Prop :=
  ∀ (c : EmbeddedChart 2 k n M) (u : E k), u ∈ c.source →
    ∃ (W : Set (E k)) (η : FormField k p), IsOpen W ∧ u ∈ W ∧
      IsCrForm (some 1) W η ∧ EqOn η (chartPullback c ω) (c.source ∩ W)

def withinExteriorDerivative {k p : ℕ} (S : Set (E k)) (η : FormField k p) :
    FormField k (p + 1) :=
  fun u => ∑ I : MultiIndex k p, ∑ j : Fin k,
    (fderivWithin ℝ (fun v => coefficient (standardBasis k) (η v) I) S u)
      (standardBasis k j) • coordinateExteriorTerm j I

/-- The full chart characterization, including the flat boundary. -/
def HasIntrinsicExteriorDerivative {k n p : ℕ} {M : Set (E n)}
    (ω : IntrinsicForm (k := k) M p) (η : IntrinsicForm (k := k) M (p+1)) : Prop :=
  ∀ (c : EmbeddedChart 2 k n M) (u : E k), u ∈ c.source →
    chartPullback c η u = withinExteriorDerivative c.source (chartPullback c ω) u

def ambientRestriction {k n p : ℕ} (M : Set (E n)) (ω : FormField n p) :
    IntrinsicForm (k := k) M p :=
  fun x => (ω x).compLinearMap (Tangent (k := k) M x).subtype

def intrinsicWedge {k n p q : ℕ} {M : Set (E n)}
    (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q) :
    IntrinsicForm (k := k) M (p+q) := fun x => wedge (α x) (β x)

def gradedDerivativeProduct {k n p q : ℕ} {M : Set (E n)}
    (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q)
    (dα : IntrinsicForm (k := k) M (p+1)) (dβ : IntrinsicForm (k := k) M (q+1)) :
    IntrinsicForm (k := k) M (p+q+1) := fun x =>
  castCovector (by omega : (p+1)+q = p+q+1) (wedge (dα x) (β x)) +
    (-1 : ℝ)^p • castCovector (by omega : p+(q+1) = p+q+1) (wedge (α x) (dβ x))
/-- A total selector; existence under IntrinsicC1 is a theorem, not part of
this definition. Values on non-C¹ fields have no asserted analytic meaning. -/
def intrinsicExteriorDerivative {k n p : ℕ} {M : Set (E n)}
    (ω : IntrinsicForm (k := k) M p) : IntrinsicForm (k := k) M (p+1) :=
  if h : ∃ η : IntrinsicForm (k := k) M (p+1),
      IntrinsicContinuous η ∧ HasIntrinsicExteriorDerivative ω η
    then h.choose else fun _ => 0
end Model
open Model

abbrev IntrinsicFormType := {k n : ℕ} → Set (E n) → ℕ → Type
def IntrinsicFormValue : IntrinsicFormType := @Model.IntrinsicForm
abbrev chartPullbackType := {k n p : ℕ} → {M : Set (E n)} →
  EmbeddedChart 2 k n M → IntrinsicForm (k := k) M p → FormField k p
def chartPullbackValue : chartPullbackType := @Model.chartPullback
abbrev IntrinsicContinuousType := {k n p : ℕ} → {M : Set (E n)} →
  IntrinsicForm (k := k) M p → Prop
def IntrinsicContinuousValue : IntrinsicContinuousType := @Model.IntrinsicContinuous
abbrev IntrinsicC1Type := {k n p : ℕ} → {M : Set (E n)} →
  IntrinsicForm (k := k) M p → Prop
def IntrinsicC1Value : IntrinsicC1Type := @Model.IntrinsicC1
abbrev withinExteriorDerivativeType := {k p : ℕ} → Set (E k) → FormField k p → FormField k (p+1)
def withinExteriorDerivativeValue : withinExteriorDerivativeType := @Model.withinExteriorDerivative
abbrev HasIntrinsicExteriorDerivativeType := {k n p : ℕ} → {M : Set (E n)} →
  IntrinsicForm (k := k) M p → IntrinsicForm (k := k) M (p+1) → Prop
def HasIntrinsicExteriorDerivativeValue : HasIntrinsicExteriorDerivativeType :=
  @Model.HasIntrinsicExteriorDerivative
abbrev ambientRestrictionType := {k n p : ℕ} → (M : Set (E n)) → FormField n p →
  IntrinsicForm (k := k) M p
def ambientRestrictionValue : ambientRestrictionType := @Model.ambientRestriction
abbrev intrinsicWedgeType := {k n p q : ℕ} → {M : Set (E n)} →
  IntrinsicForm (k := k) M p → IntrinsicForm (k := k) M q → IntrinsicForm (k := k) M (p+q)
def intrinsicWedgeValue : intrinsicWedgeType := @Model.intrinsicWedge

abbrev intrinsicExteriorDerivativeType := {k n p : ℕ} → {M : Set (E n)} →
  IntrinsicForm (k := k) M p → IntrinsicForm (k := k) M (p+1)
def intrinsicExteriorDerivativeValue : intrinsicExteriorDerivativeType := @Model.intrinsicExteriorDerivative

/-- Existence and uniqueness on every C² embedded manifold, without compactness,
orientability, nonemptiness, degree bounds, or a boundaryless assumption. -/
def intrinsic_exteriorDerivative_exists_uniqueType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ ω : IntrinsicForm (k := k) M p, IntrinsicC1 ω →
      ∃! η : IntrinsicForm (k := k) M (p+1),
        IntrinsicContinuous η ∧ HasIntrinsicExteriorDerivative ω η

def intrinsic_exteriorDerivative_uniqueType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (ω : IntrinsicForm (k := k) M p) (η ζ : IntrinsicForm (k := k) M (p+1)),
      HasIntrinsicExteriorDerivative ω η → HasIntrinsicExteriorDerivative ω ζ → η = ζ

def intrinsic_ambientRestrictionType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (O : Set (E n)) (ω : FormField n p), M ⊆ O → IsCrForm (some 1) O ω →
      IntrinsicC1 (ambientRestriction (k := k) M ω) ∧
      IntrinsicContinuous (ambientRestriction (k := k) M (exteriorDerivative ω)) ∧
      HasIntrinsicExteriorDerivative (ambientRestriction (k := k) M ω)
        (ambientRestriction (k := k) M (exteriorDerivative ω))

def intrinsic_product_ruleType : Prop :=
  ∀ {k n p q : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q)
      (dα : IntrinsicForm (k := k) M (p+1)) (dβ : IntrinsicForm (k := k) M (q+1)),
      IntrinsicC1 α → IntrinsicC1 β →
      HasIntrinsicExteriorDerivative α dα → HasIntrinsicExteriorDerivative β dβ →
        IntrinsicC1 (intrinsicWedge α β) ∧
        HasIntrinsicExteriorDerivative (intrinsicWedge α β) (gradedDerivativeProduct α β dα dβ)

def intrinsic_above_dimensionType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M → k < p →
    ∀ ω : IntrinsicForm (k := k) M p, ∀ x : M, ω x = 0

def intrinsic_top_derivativeType : Prop :=
  ∀ {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ ω : IntrinsicForm (k := k) M k,
      HasIntrinsicExteriorDerivative ω (fun _ => 0)

def intrinsic_zero_dimensionType : Prop :=
  ∀ {n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 0 M →
    ∀ ω : IntrinsicForm (k := 0) M p, IntrinsicC1 ω ∧
      IntrinsicContinuous ω ∧ HasIntrinsicExteriorDerivative ω (fun _ => 0)

def intrinsicExteriorDerivative_specType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ ω : IntrinsicForm (k := k) M p, IntrinsicC1 ω →
      IntrinsicContinuous (intrinsicExteriorDerivative ω) ∧
        HasIntrinsicExteriorDerivative ω (intrinsicExteriorDerivative ω)

def intrinsicExteriorDerivative_ambientType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (O : Set (E n)) (ω : FormField n p), M ⊆ O → IsCrForm (some 1) O ω →
      intrinsicExteriorDerivative (ambientRestriction (k := k) M ω) =
        ambientRestriction (k := k) M (exteriorDerivative ω)

def intrinsicExteriorDerivative_wedgeType : Prop :=
  ∀ {k n p q : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q),
      IntrinsicC1 α → IntrinsicC1 β →
        intrinsicExteriorDerivative (intrinsicWedge α β) =
          gradedDerivativeProduct α β (intrinsicExteriorDerivative α) (intrinsicExteriorDerivative β)

def intrinsicExteriorDerivative_high_degreeType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M → k ≤ p →
    ∀ (ω : IntrinsicForm (k := k) M p) (x : M), intrinsicExteriorDerivative ω x = 0

/-- In a boundary chart d of the chart form is evaluated using any local C¹
extension; the result is independent of that extension and of the chart. -/
def intrinsicExteriorDerivative_chartType : Prop :=
  ∀ {k n p : ℕ} {M : Set (E n)}, IsEmbeddedManifold 2 k M →
    ∀ (ω : IntrinsicForm (k := k) M p), IntrinsicC1 ω →
      ∀ (c : EmbeddedChart 2 k n M) (u : E k), u ∈ c.source →
        ∀ (W : Set (E k)) (α : FormField k p), IsOpen W → u ∈ W →
          IsCrForm (some 1) W α → EqOn α (chartPullback c ω) (c.source ∩ W) →
            chartPullback c (intrinsicExteriorDerivative ω) u = exteriorDerivative α u

end Specs.D04.C15.IntrinsicExteriorDerivative
