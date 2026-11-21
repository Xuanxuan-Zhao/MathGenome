import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.BorelBaire
import Mathlib.MeasureTheory.Measure.Regular

/-!
Independent specifications for paper.tex:5325–5336.
The measure's sigma-algebra is exactly `borel X`; in particular no ambient
measurable-space instance or completion changes the domain. Setwise formulas
use native outer values when evaluated on arbitrary sets. The global regularity
predicates quantify only over the Borel sets or the open sets stated in the source.
Radon and its stronger variant are named on locally compact Hausdorff spaces.
-/
namespace Specs.D11.Ch18.RadonPredicates

open Set MeasureTheory
open scoped ENNReal
universe u

-- Local only: every occurrence below has the explicitly fixed Borel domain.
local instance {Y : Type u} [TopologicalSpace Y] : MeasurableSpace Y := borel Y


/-- Type of a regularity predicate at a specified set. -/
def setPredicateType :=
  ∀ {X : Type u} [TopologicalSpace X], @Measure X (borel X) → Set X → Prop

/-- The source's infimum over all open supersets, with extended-real values. -/
def outerRegularOnValue : setPredicateType.{u} := fun μ E =>
  μ E = ⨅ (U : Set _) (_ : E ⊆ U) (_ : IsOpen U), μ U

/-- The source's supremum over all compact subsets. -/
def compactInnerRegularOnValue : setPredicateType.{u} := fun μ E =>
  μ E = ⨆ (K : Set _) (_ : K ⊆ E) (_ : IsCompact K), μ K

def measurePredicateType :=
  ∀ {X : Type u} [TopologicalSpace X], @Measure X (borel X) → Prop

def compactFiniteValue : measurePredicateType.{u} := fun μ =>
  ∀ K, IsCompact K → μ K < ∞

def locallyFiniteValue : measurePredicateType.{u} := fun μ =>
  ∀ x, ∃ U, x ∈ U ∧ IsOpen U ∧ μ U < ∞

def outerRegularBorelValue : measurePredicateType.{u} := fun μ =>
  ∀ E, MeasurableSet[borel _] E → outerRegularOnValue μ E

def compactInnerRegularOpenValue : measurePredicateType.{u} := fun μ =>
  ∀ U, IsOpen U → compactInnerRegularOnValue μ U

def compactInnerRegularBorelValue : measurePredicateType.{u} := fun μ =>
  ∀ E, MeasurableSet[borel _] E → compactInnerRegularOnValue μ E

def lchMeasurePredicateType :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X],
    @Measure X (borel X) → Prop

/-- Exactly the three Radon conditions: no all-Borel inner regularity is added. -/
def isRadonValue : lchMeasurePredicateType.{u} := fun μ =>
  compactFiniteValue μ ∧ outerRegularBorelValue μ ∧ compactInnerRegularOpenValue μ

/-- Folland's stronger regularity class, kept separate from Radon. -/
def isFullyRegularValue : lchMeasurePredicateType.{u} := fun μ =>
  isRadonValue μ ∧ compactInnerRegularBorelValue μ

def compactFinite_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    compactFiniteValue μ ↔ IsFiniteMeasureOnCompacts μ

def locallyFinite_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    locallyFiniteValue μ ↔ IsLocallyFiniteMeasure μ

def outerRegularBorel_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    outerRegularBorelValue μ ↔ Measure.OuterRegular μ

def compactInnerRegularOpen_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    compactInnerRegularOpenValue μ ↔ μ.InnerRegularWRT IsCompact IsOpen

def compactInnerRegularBorel_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)),
    compactInnerRegularBorelValue μ ↔ Measure.InnerRegular μ

def isRadon_iff_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), isRadonValue μ ↔ Measure.Regular μ

def isFullyRegular_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)),
    isFullyRegularValue μ ↔ Measure.Regular μ ∧ Measure.InnerRegular μ

def isFullyRegular_isRadon : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), isFullyRegularValue μ → isRadonValue μ

end Specs.D11.Ch18.RadonPredicates
