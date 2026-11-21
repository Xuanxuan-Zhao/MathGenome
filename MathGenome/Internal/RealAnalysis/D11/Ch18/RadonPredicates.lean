import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch18.BorelBaire
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonPredicates

/-!
# The regularity predicates of Chapter 18

`μ` is always a measure on the shared Borel structure. Setwise formulas use
native outer values on arbitrary sets; the global conditions quantify over
exactly Borel sets or open sets. Evaluating a non-Borel set does not declare
it Borel measurable. All infima and suprema are in `[0,∞]`.

On LCH Hausdorff spaces `isRadon` means compact finiteness, Borel outer
regularity and open compact-inner regularity. `isFullyRegular` adds compact
inner regularity on all Borel sets. The bridges below inspect and match the
actual native classes, including the strict-approximation fields used there.
No countability, finite total mass or nonempty-space assumption is imposed.
-/
namespace D11.Ch18

open Set MeasureTheory
open scoped ENNReal Topology
universe u

-- Local only: every occurrence below has the explicitly fixed Borel domain.
local instance {Y : Type u} [TopologicalSpace Y] : MeasurableSpace Y := borel Y

variable {X : Type u} [TopologicalSpace X]

/-- Outer approximation by open supersets at a specified set. -/
def outerRegularOn (μ : @Measure X (borelSpace X)) (E : Set X) : Prop :=
  μ E = ⨅ (U : Set X) (_ : E ⊆ U) (_ : IsOpen U), μ U

/-- Inner approximation by compact subsets at a specified set. -/
def compactInnerRegularOn (μ : @Measure X (borelSpace X)) (E : Set X) : Prop :=
  μ E = ⨆ (K : Set X) (_ : K ⊆ E) (_ : IsCompact K), μ K

/-- Finite mass on every compact set. -/
def compactFinite (μ : @Measure X (borelSpace X)) : Prop :=
  ∀ K, IsCompact K → μ K < ∞

/-- Each point has an open neighborhood of finite mass. -/
def locallyFinite (μ : @Measure X (borelSpace X)) : Prop :=
  ∀ x, ∃ U, x ∈ U ∧ IsOpen U ∧ μ U < ∞

/-- Outer regularity on precisely the Borel domain of the measure. -/
def outerRegularBorel (μ : @Measure X (borelSpace X)) : Prop :=
  ∀ E, MeasurableSet[borelSpace X] E → outerRegularOn μ E

/-- Compact-inner regularity on open sets only. -/
def compactInnerRegularOpen (μ : @Measure X (borelSpace X)) : Prop :=
  ∀ U, IsOpen U → compactInnerRegularOn μ U

/-- The separate, stronger all-Borel compact-inner predicate. -/
def compactInnerRegularBorel (μ : @Measure X (borelSpace X)) : Prop :=
  ∀ E, MeasurableSet[borelSpace X] E → compactInnerRegularOn μ E

/-- Radon in the manuscript (also Cohn's regular Borel and Folland's Radon class). -/
def isRadon [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) : Prop :=
  compactFinite μ ∧ outerRegularBorel μ ∧ compactInnerRegularOpen μ

/-- The stronger Folland regular class, with compact-inner regularity on all Borel sets. -/
def isFullyRegular [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) : Prop :=
  isRadon μ ∧ compactInnerRegularBorel μ

/-- Native finiteness on compacts has exactly the stated quantifiers. -/
theorem compactFinite_iff (μ : @Measure X (borelSpace X)) :
    compactFinite μ ↔ IsFiniteMeasureOnCompacts μ := by
  constructor
  · intro h
    exact ⟨fun {_} hK => h _ hK⟩
  · intro h K hK
    exact h.lt_top_of_isCompact hK

/-- Native neighborhood finiteness is equivalent to open neighborhood finiteness. -/
theorem locallyFinite_iff (μ : @Measure X (borelSpace X)) :
    locallyFinite μ ↔ IsLocallyFiniteMeasure μ := by
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hx, hU, hμU⟩ := h x
    exact ⟨U, hU.mem_nhds hx, hμU⟩
  · intro h x
    let := h
    exact μ.exists_isOpen_measure_lt_top x

/-- Equality to the infimum is equivalent to the native strict outer approximation. -/
theorem outerRegularBorel_iff (μ : @Measure X (borelSpace X)) :
    outerRegularBorel μ ↔ Measure.OuterRegular μ := by
  constructor
  · intro h
    refine ⟨fun {E} hE r hr => ?_⟩
    rw [h E hE] at hr
    simpa only [iInf_lt_iff, exists_prop] using hr
  · intro h E _hE
    let := h
    exact E.measure_eq_iInf_isOpen μ

/-- Equality to the supremum matches the native open-set compact approximation. -/
theorem compactInnerRegularOpen_iff (μ : @Measure X (borelSpace X)) :
    compactInnerRegularOpen μ ↔ μ.InnerRegularWRT IsCompact IsOpen := by
  constructor
  · intro h U hU r hr
    rw [h U hU] at hr
    simpa only [lt_iSup_iff, exists_prop] using hr
  · intro h U hU
    exact h.measure_eq_iSup hU

/-- `Measure.InnerRegular` quantifies over all Borel sets here, unlike the open condition. -/
theorem compactInnerRegularBorel_iff (μ : @Measure X (borelSpace X)) :
    compactInnerRegularBorel μ ↔ Measure.InnerRegular μ := by
  constructor
  · intro h
    refine ⟨fun {E} hE r hr => ?_⟩
    rw [h E hE] at hr
    simpa only [lt_iSup_iff, exists_prop] using hr
  · intro h E hE
    exact h.innerRegular.measure_eq_iSup hE

/-- The native `Regular` class has exactly the manuscript's three Radon predicates. -/
theorem isRadon_iff_regular [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) : isRadon μ ↔ Measure.Regular μ := by
  constructor
  · rintro ⟨hfin, hout, hin⟩
    exact { toIsFiniteMeasureOnCompacts := (compactFinite_iff μ).mp hfin
            toOuterRegular := (outerRegularBorel_iff μ).mp hout
            innerRegular := (compactInnerRegularOpen_iff μ).mp hin }
  · intro h
    exact ⟨(compactFinite_iff μ).mpr h.toIsFiniteMeasureOnCompacts,
      (outerRegularBorel_iff μ).mpr h.toOuterRegular,
      (compactInnerRegularOpen_iff μ).mpr h.innerRegular⟩

/-- Full Borel inner regularity is an additional native class, not part of `Regular`. -/
theorem isFullyRegular_iff [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) :
    isFullyRegular μ ↔ Measure.Regular μ ∧ Measure.InnerRegular μ := by
  exact and_congr (isRadon_iff_regular μ) (compactInnerRegularBorel_iff μ)

theorem isFullyRegular_isRadon [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borelSpace X)) (h : isFullyRegular μ) : isRadon μ :=
  h.1

end D11.Ch18
