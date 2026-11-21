import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Homeomorph.Defs

/-! Independent specification of paper.tex, d10:18:two-origins.
The carrier really is an equivalence quotient of the topological disjoint sum.
The quotient instance is Mathlib's coinduced topology, with no separation axiom.
Paracompactness is reserved for the separately allocated goal. -/

open Set Topology TopologicalSpace

namespace D10Topology.Ch18.TwoOriginsData

def rawCoordinate : ℝ ⊕ ℝ → ℝ := Sum.elim id id

/-- Equal coordinates are identified except that the two zeroes stay distinct. -/
def relation : Setoid (ℝ ⊕ ℝ) where
  r a b := rawCoordinate a = rawCoordinate b ∧ (rawCoordinate a ≠ 0 ∨ a = b)
  iseqv := {
    refl := fun a => ⟨rfl, Or.inr rfl⟩
    symm := by
      rintro a b ⟨h, hn | rfl⟩
      · exact ⟨h.symm, Or.inl (h ▸ hn)⟩
      · exact ⟨rfl, Or.inr rfl⟩
    trans := by
      rintro a b c ⟨hab, hn | rfl⟩ ⟨hbc, hcn | hbc'⟩
      · exact ⟨hab.trans hbc, Or.inl hn⟩
      · exact ⟨hab.trans hbc, Or.inl hn⟩
      · exact ⟨hbc, Or.inl hcn⟩
      · exact ⟨hbc, Or.inr hbc'⟩ }

abbrev Line := Quotient relation

def classMap : ℝ ⊕ ℝ → Line := Quotient.mk relation

def sheet : Bool → ℝ → ℝ ⊕ ℝ
  | false => Sum.inl
  | true => Sum.inr

def chart (i : Bool) (x : ℝ) : Line := classMap (sheet i x)
def origin (i : Bool) : Line := chart i 0
def coordinate : Line → ℝ := Quotient.lift rawCoordinate (fun _ _ h => h.1)

end D10Topology.Ch18.TwoOriginsData

namespace Specs.D10Topology.Ch18.TwoOriginsTopology
open _root_.D10Topology.Ch18.TwoOriginsData

def lineType := Type
def lineValue : lineType := Line
def classMapType := (ℝ ⊕ ℝ) → Line
def classMapValue : classMapType := classMap
def chartType := Bool → ℝ → Line
def chartValue : chartType := chart
def originType := Bool → Line
def originValue : originType := origin
def coordinateType := Line → ℝ
def coordinateValue : coordinateType := coordinate

def class_eq : Prop := ∀ a b : ℝ ⊕ ℝ,
  classMap a = classMap b ↔
    rawCoordinate a = rawCoordinate b ∧ (rawCoordinate a ≠ 0 ∨ a = b)
def quotient_topology : Prop := ∀ U : Set Line,
  IsOpen U ↔ IsOpen (classMap ⁻¹' U)
def quotient_map : Prop := IsQuotientMap classMap
def chart_eq : Prop := ∀ (i j : Bool) (x y : ℝ),
  chart i x = chart j y ↔ x = y ∧ (x ≠ 0 ∨ i = j)
def coordinate_chart : Prop := ∀ (i : Bool) (x : ℝ), coordinate (chart i x) = x
def coordinate_continuous : Prop := Continuous coordinate
def coordinate_open : Prop := IsOpenMap coordinate
def chart_continuous : Prop := ∀ i : Bool, Continuous (chart i)
def chart_open_embedding : Prop := ∀ i : Bool, IsOpenEmbedding (chart i)
def chart_range : Prop := ∀ i : Bool, range (chart i) = {origin (!i)}ᶜ
def chart_homeomorph : Prop := ∀ i : Bool,
  ∃ h : ℝ ≃ₜ ({origin (!i)}ᶜ : Set Line), ∀ x : ℝ, (h x).val = chart i x
def charts_cover : Prop := range (chart false) ∪ range (chart true) = univ
def locally_metrizable : Prop := ∀ x : Line,
  ∃ U : Set Line, IsOpen U ∧ x ∈ U ∧ MetrizableSpace U
def second_countable : Prop := SecondCountableTopology Line
def t1 : Prop := T1Space Line
def origins_distinct : Prop := origin false ≠ origin true
/-- Even neighborhoods which are not open must intersect away from the origins. -/
def origin_neighborhoods_intersect : Prop := ∀ U V : Set Line,
  U ∈ nhds (origin false) → V ∈ nhds (origin true) →
    ∃ x : ℝ, x ≠ 0 ∧ chart false x ∈ U ∩ V
def not_hausdorff : Prop := ¬ T2Space Line
def not_metrizable : Prop := ¬ MetrizableSpace Line

end Specs.D10Topology.Ch18.TwoOriginsTopology
