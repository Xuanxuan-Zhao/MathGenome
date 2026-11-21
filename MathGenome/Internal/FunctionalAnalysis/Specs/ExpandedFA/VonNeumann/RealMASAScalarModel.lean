import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealAbelianComplexification
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Metrizable.Basic

/-! The full real scalar-model clause of `fa2:p2:abelian-von-neumann`.
The complexification and all fixed Lp spaces are the shared native objects.
There is no nonzero-space or positive-mass hypothesis. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.VonNeumann.RealMASAScalarModel.Spec
open TraceIdeals.RealComplexification
open TraceIdeals.RealComplexification.Spec
open RealAbelianComplexification.Spec
open RealAbelianComplexification.Spec.NativeLp
universe u

/-- Compact metrizable Borel geometry, with a finite regular positive measure
and an actual measure-preserving involutive homeomorphism. -/
structure Geometry where
  X : Type u
  [topology : TopologicalSpace X]
  [compact : CompactSpace X]
  [hausdorff : T2Space X]
  [metrizable : TopologicalSpace.MetrizableSpace X]
  [measurable : MeasurableSpace X]
  [borel : BorelSpace X]
  μ : Measure X
  [finite : IsFiniteMeasure μ]
  [regular : μ.Regular]
  tau : X ≃ₜ X
  preserving : MeasurePreserving tau μ μ
  involutive : Function.Involutive tau

attribute [instance] Geometry.topology Geometry.compact Geometry.hausdorff
  Geometry.metrizable Geometry.measurable Geometry.borel Geometry.finite Geometry.regular

def Geometry.involution (G : Geometry.{u}) : InvolutionData G.μ :=
  ⟨G.tau, G.preserving, G.involutive⟩

/-- The constant-one class on native complex L², also when the measure is zero. -/
def Geometry.oneL2 (G : Geometry.{u}) : Lp ℂ 2 G.μ :=
  (memLp_const (1 : ℂ)).toLp (fun _ : G.X => (1 : ℂ))

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
local instance : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

/-- A norm-separable, conjugation-stable C* core on the canonical
complexification, with the same cyclic vector and full strong closure. -/
structure SeparableCore (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H) where
  algebra : StarSubalgebra ℂ (Space H →L[ℂ] Space H)
  included : algebra ≤ complexAlgebra A
  closed : IsClosed (algebra : Set (Space H →L[ℂ] Space H))
  separable : TopologicalSpace.IsSeparable (algebra : Set (Space H →L[ℂ] Space H))
  stable : ∀ R ∈ algebra, gamma R ∈ algebra
  cyclic : SeparableMASA.Spec.IsCyclic algebra (inclusion e)
  strongClosure :
    @closure _ (OperatorTopology.Spec.StrongTopologyValue ℂ (Space H) (Space H))
      (algebra : Set (Space H →L[ℂ] Space H)) = (complexAlgebra A : Set _)

def SeparableCoreConstruction : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    SeparableMASA.Spec.RealIsMASA A → ∀ e : H,
      SeparableMASA.Spec.RealIsCyclic A e → Nonempty (SeparableCore A e)

/-- The normalized, equivariant complex model has the entire multiplier algebra
as its image. Cyclicity and the existence of these data are conclusions below. -/
structure NormalizedComplexModel (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H) where
  geometry : Geometry.{u}
  Uc : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 geometry.μ
  normalized : Uc (inclusion e) = geometry.oneL2
  equivariant : ∀ z : Space H,
    Uc (conjugation z) = conjugatePullback geometry.involution (Uc z)
  all_multipliers : ∀ R : Space H →L[ℂ] Space H,
    R ∈ complexAlgebra A ↔ ∃ f : Lp ℂ ∞ geometry.μ,
      ∀ z, Uc (R z) = ScalarMultiplicationCommutant.Spec.multiplier geometry.μ f (Uc z)

/-- Complete simultaneous real and complex representation, with quotient-level
symbol uniqueness and the induced isometric real star algebra equivalence. -/
structure ScalarModel (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H) where
  complexModel : NormalizedComplexModel A e
  U : H ≃ₗᵢ[ℝ] Fixed complexModel.geometry.involution 2
  restriction : ∀ x, (U x).val = complexModel.Uc (inclusion x)
  all_multipliers : ∀ T : H →L[ℝ] H,
    T ∈ A ↔ ∃ f : Fixed complexModel.geometry.involution ∞,
      ∀ x, U (T x) = restrictedMultiplier complexModel.geometry.involution f (U x)
  symbol_unique : ∀ (T : H →L[ℝ] H)
    (f g : Fixed complexModel.geometry.involution ∞),
    (∀ x, U (T x) = restrictedMultiplier complexModel.geometry.involution f (U x)) →
    (∀ x, U (T x) = restrictedMultiplier complexModel.geometry.involution g (U x)) → f = g
  symbol_norm : ∀ (T : H →L[ℝ] H) (f : Fixed complexModel.geometry.involution ∞),
    (∀ x, U (T x) = restrictedMultiplier complexModel.geometry.involution f (U x)) →
      ‖T‖ = ‖f‖
  symbolEquiv : Fixed complexModel.geometry.involution ∞ ≃⋆ₐ[ℝ] A
  symbolIsometry : Isometry symbolEquiv
  symbolIntertwining : ∀ f x,
    U ((symbolEquiv f : H →L[ℝ] H) x) =
      restrictedMultiplier complexModel.geometry.involution f (U x)

/-- No cyclic vector, measure, unitary or scalar model is an input. -/
def FullRepresentation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    SeparableMASA.Spec.RealIsMASA A →
      ∃ e : H, SeparableMASA.Spec.RealIsCyclic A e ∧ Nonempty (ScalarModel A e)

/-- All real conclusions follow from a model constructed with the required
normalization, equivariance, and full complex multiplier equality. -/
def NormalizedDescent : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : StarSubalgebra ℝ (H →L[ℝ] H)) (e : H),
    NormalizedComplexModel A e → Nonempty (ScalarModel A e)

/-- The analytic construction for any of the real cyclic vectors furnished by
the upstream MASA cyclic theorem. -/
def NormalizedConstruction : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (A : StarSubalgebra ℝ (H →L[ℝ] H)),
    SeparableMASA.Spec.RealIsMASA A → ∀ e : H,
      SeparableMASA.Spec.RealIsCyclic A e → Nonempty (NormalizedComplexModel A e)

/-- Restricting an equivariant unitary is onto the genuine fixed real form. -/
def EquivariantRestriction : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type u) [MeasurableSpace X] (μ : Measure X) (D : InvolutionData μ)
    (V : Space H ≃ₗᵢ[ℂ] Lp ℂ 2 μ),
    (∀ z, V (conjugation z) = conjugatePullback D (V z)) →
    ∃ U : H ≃ₗᵢ[ℝ] Fixed D 2, ∀ x, (U x).val = V (inclusion x)

end ExpandedFA.VonNeumann.RealMASAScalarModel.Spec
