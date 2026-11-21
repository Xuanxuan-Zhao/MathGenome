import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Independent specification for paper.tex, Chapter 21,
`d11:21:lch-group-interface` (lines 5821–5827).

The group is Hausdorff and locally compact. No countability, metrizability,
sigma-compactness, or measure assumption is imposed. Measurability below is
with respect to the Borel sigma-algebra, not a completion or a product
sigma-algebra. The Radon predicates are the separate Chapter 18 interface.
-/

namespace Specs.D11.Ch21.LchGroupInterface

universe u

/-- The source's convention for a locally compact group. -/
def locallyCompactGroupType : Type (u + 1) :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G], Prop

def locallyCompactGroupValue : locallyCompactGroupType.{u} :=
  fun G _ _ => IsTopologicalGroup G ∧ T2Space G ∧ LocallyCompactSpace G

/-- Unpacks joint continuity of multiplication and continuity of inversion. -/
def locallyCompactGroupIffStatement : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G],
    locallyCompactGroupValue G ↔
      Continuous (fun p : G × G => p.1 * p.2) ∧
      Continuous (fun x : G => x⁻¹) ∧ T2Space G ∧ LocallyCompactSpace G

/-- The translations are specified as actual homeomorphisms, with their maps fixed. -/
def translationType : Type (u + 1) :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G], G → G ≃ₜ G

def leftTranslationValue : translationType.{u} :=
  fun _ _ _ _ a => Homeomorph.mulLeft a

def rightTranslationValue : translationType.{u} :=
  fun _ _ _ _ a => Homeomorph.mulRight a

def inversionType : Type (u + 1) :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G], G ≃ₜ G

def inversionValue : inversionType.{u} :=
  fun G _ _ _ => Homeomorph.inv G

/-- Records the pointwise formulas independently of the bundled maps. -/
def mapFormulasStatement : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (a x : G),
    leftTranslationValue G a x = a * x ∧
    rightTranslationValue G a x = x * a ∧ inversionValue G x = x⁻¹

/-- The explicit inverses given in the source proof. -/
def inverseFormulasStatement : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (a : G),
    (leftTranslationValue G a).symm = leftTranslationValue G a⁻¹ ∧
    (rightTranslationValue G a).symm = rightTranslationValue G a⁻¹ ∧
    (inversionValue G).symm = inversionValue G

/-- Preservation, in both directions, of opens, Borel sets, and compact sets. -/
def PreservesOpenBorelCompact (G : Type u) [TopologicalSpace G] [MeasurableSpace G]
    (f : G → G) : Prop :=
  Continuous f ∧ Measurable f ∧
    (∀ s : Set G, (IsOpen (f '' s) ↔ IsOpen s) ∧
      (IsOpen (f ⁻¹' s) ↔ IsOpen s)) ∧
    (∀ s : Set G, (MeasurableSet (f '' s) ↔ MeasurableSet s) ∧
      (MeasurableSet (f ⁻¹' s) ↔ MeasurableSet s)) ∧
    (∀ s : Set G, (IsCompact (f '' s) ↔ IsCompact s) ∧
      (IsCompact (f ⁻¹' s) ↔ IsCompact s))

/-- The full preservation conclusion in the original LCH setting. -/
def preservationStatement : Prop :=
  ∀ (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (a : G),
    PreservesOpenBorelCompact G (fun x => a * x) ∧
    PreservesOpenBorelCompact G (fun x => x * a) ∧
    PreservesOpenBorelCompact G (fun x => x⁻¹)

end Specs.D11.Ch21.LchGroupInterface
