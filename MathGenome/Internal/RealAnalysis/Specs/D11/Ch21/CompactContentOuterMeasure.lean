import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactContentCluster
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory
import Mathlib.MeasureTheory.Measure.Content

/-!
Independent specification for the outer-measure part of
`paper.tex:5852–5854`, `D11.21.compact_content_radon_measure`.

`Content G` is the native finite nonnegative compact content. The conversion
from the preceding real-valued content is specified below. The core results
hold for every such content; normalization and a covering-number bound are
unnecessary here. Invariance is used only for the translation results.
No countability or sigma-finiteness assumption occurs.

Regularity and nonzero mass of the resulting Borel measure are allocated to
`d11_21_compact_content_radon_measure`, which uses this construction.
-/

noncomputable section
namespace Specs.D11.Ch21.CompactContentOuterMeasure

open Set TopologicalSpace MeasureTheory
open scoped ENNReal
universe u

/-- Reinterpret a real-valued finite nonnegative content, using only its
content laws. Closedness in the native additivity field adds no assumption
to the supplied disjoint-compact additivity law. -/
def realContent_type : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G] (h : Compacts G → ℝ),
    (∀ K, 0 ≤ h K) →
    (∀ K L : Compacts G, (K : Set G) ⊆ L → h K ≤ h L) →
    (∀ K L, h (K ⊔ L) ≤ h K + h L) →
    (∀ K L : Compacts G, Disjoint (K : Set G) (L : Set G) →
      h (K ⊔ L) = h K + h L) → Content G

def realContent_value : realContent_type.{u} :=
  fun h hn hm hs ha =>
    { toFun := fun K => ⟨h K, hn K⟩
      mono' := fun K L hKL => hm K L hKL
      sup_disjoint' := fun K L hd _ _ => NNReal.eq (ha K L hd)
      sup_le' := fun K L => hs K L }

def realContent_apply : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] (h : Compacts G → ℝ)
    (hn : ∀ K, 0 ≤ h K)
    (hm : ∀ K L : Compacts G, (K : Set G) ⊆ L → h K ≤ h L)
    (hs : ∀ K L, h (K ⊔ L) ≤ h K + h L)
    (ha : ∀ K L : Compacts G, Disjoint (K : Set G) (L : Set G) →
      h (K ⊔ L) = h K + h L) (K : Compacts G),
    realContent_value h hn hm hs ha K = ENNReal.ofReal (h K)

def openCost_type : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G], Content G → Opens G → ℝ≥0∞

def openCost_value : openCost_type.{u} :=
  fun {G} _ c U => ⨆ (K : Compacts G) (_ : (K : Set G) ⊆ U), c K

def outerCost_type : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G], Content G → Set G → ℝ≥0∞

def outerCost_value : outerCost_type.{u} :=
  fun c A => ⨅ (U : Set _) (hU : IsOpen U) (_ : A ⊆ U), openCost_value c ⟨U, hU⟩

def outerMeasure_type : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G], Content G → OuterMeasure G

def outerMeasure_value : outerMeasure_type.{u} := fun c => c.outerMeasure

def outerMeasure_apply : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G]
    (c : Content G) (A : Set G), outerMeasure_value c A = outerCost_value c A

/-- The displayed infimum itself, with unrestricted countable subadditivity. -/
def outerCost_axioms : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G] (c : Content G),
    outerCost_value c ∅ = 0 ∧ Monotone (outerCost_value c) ∧
      ∀ A : ℕ → Set G, outerCost_value c (⋃ n, A n) ≤ ∑' n, outerCost_value c (A n)

def outerMeasure_open : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G]
    (c : Content G) (U : Opens G), outerMeasure_value c U = openCost_value c U

def borel_le_caratheodory : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G] (c : Content G),
    borel G ≤ (outerMeasure_value c).caratheodory

/-- Borel membership implies the splitting test on every subset. -/
def borel_splitting : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G]
    (c : Content G) (B : Set G), MeasurableSet[borel G] B →
      ∀ A : Set G, outerMeasure_value c A =
        outerMeasure_value c (A ∩ B) + outerMeasure_value c (A \ B)

def borelMeasure_type : Type (u + 1) :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G], Content G → @Measure G (borel G)

def borelMeasure_value : borelMeasure_type.{u} :=
  fun {G} _ _ c => @Content.measure G _ c inferInstance (borel G)
    (@BorelSpace.mk G _ (borel G) rfl)

/-- Agreement is on Borel sets; arbitrary-set evaluation does not enlarge
the specified Borel sigma-algebra. -/
def borelMeasure_apply : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [T2Space G]
    (c : Content G) (B : Set G), MeasurableSet[borel G] B →
      borelMeasure_value c B = outerMeasure_value c B

def openCost_left_image : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : Content G)
    (hc : ∀ (a : G) (K : Compacts G),
      c (K.map (fun x => a * x) (continuous_const_mul a)) = c K)
    (a : G) (U : Opens G),
    openCost_value c ⟨(fun x => a * x) '' U, (Homeomorph.mulLeft a).isOpenMap _ U.isOpen⟩ =
      openCost_value c U

def outerMeasure_left_image : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (c : Content G)
    (hc : ∀ (a : G) (K : Compacts G),
      c (K.map (fun x => a * x) (continuous_const_mul a)) = c K)
    (a : G) (A : Set G),
    outerMeasure_value c ((fun x => a * x) '' A) = outerMeasure_value c A

/-- Bridge to every real content supplied by the preceding construction,
using the same compact normalization set and without choosing a new content. -/
def sourceContent_type : Type (u + 1) :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : PositiveCompacts G) (h : Compacts G → ℝ),
    CompactContentCluster.ContentProperties G K₀ h → Content G

def sourceContent_value : sourceContent_type.{u} := fun _ h hh =>
  realContent_value h (fun K => (hh.2.2.1 K).1) hh.2.2.2.2.1
    hh.2.2.2.2.2.1 hh.2.2.2.2.2.2

def sourceContent_laws : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : PositiveCompacts G) (h : Compacts G → ℝ)
    (hh : CompactContentCluster.ContentProperties G K₀ h),
    (∀ K, sourceContent_value K₀ h hh K = ENNReal.ofReal (h K)) ∧
    (∀ (a : G) (K : Compacts G),
      sourceContent_value K₀ h hh (K.map (fun x => a * x) (continuous_const_mul a)) =
        sourceContent_value K₀ h hh K)

def source_formulas : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (K₀ : PositiveCompacts G) (h : Compacts G → ℝ)
    (hh : CompactContentCluster.ContentProperties G K₀ h),
    (∀ U : Opens G, openCost_value (sourceContent_value K₀ h hh) U =
      ⨆ (K : Compacts G) (_ : (K : Set G) ⊆ U), ENNReal.ofReal (h K)) ∧
    (∀ A : Set G, outerMeasure_value (sourceContent_value K₀ h hh) A =
      ⨅ (U : Set G) (hU : IsOpen U) (_ : A ⊆ U),
        ⨆ (K : Compacts G) (_ : (K : Set G) ⊆ U), ENNReal.ofReal (h K))

end Specs.D11.Ch21.CompactContentOuterMeasure
