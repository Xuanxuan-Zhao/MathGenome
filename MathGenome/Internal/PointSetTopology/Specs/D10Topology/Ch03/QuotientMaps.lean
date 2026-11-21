import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.SumsAndFinalTopologies

/-!
Independent specification for paper.tex, d10:03:quotient and
d10:03:quotient-universal. All topologies are on the displayed underlying
types. No separation or nonemptiness assumption is imposed.
The canonical data are shared here, without assumed theorem certificates.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch03.QuotientData

/-- The source's surjective open-preimage definition. -/
def QuotientMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (q : X → Y) : Prop :=
  Function.Surjective q ∧ ∀ V : Set Y, IsOpen V ↔ IsOpen (q ⁻¹' V)

/-- A saturated subset contains every fiber it meets. -/
def Saturated {X : Type u} {Y : Type v} (q : X → Y) (A : Set X) : Prop :=
  A = q ⁻¹' (q '' A)

/-- The final topology of a single map (in particular, of a surjection). -/
@[instance_reducible] def quotientTopology {X : Type u} {Y : Type v}
    [tX : TopologicalSpace X] (q : X → Y) : TopologicalSpace Y :=
  TopologicalSpace.coinduced q tX

/-- The equivalence-class set carries the final topology of its class map. -/
@[instance_reducible] def equivalenceQuotientTopology {X : Type u}
    [TopologicalSpace X] (r : Setoid X) : TopologicalSpace (Quotient r) :=
  quotientTopology (Quotient.mk r)

end D10Topology.Ch03.QuotientData

namespace Specs.D10Topology.Ch03.QuotientMaps
open _root_.D10Topology.Ch03.QuotientData
open _root_.D10Topology.Ch03.SumFinalData
open _root_.D10Topology.Ch02.CharacteristicMaps

def quotientMapType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] →
    (X → Y) → Prop
def quotientMapValue : quotientMapType := @QuotientMap

def saturatedType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → (X → Y) → Set X → Prop
def saturatedValue : saturatedType := @Saturated

def quotientTopologyType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [TopologicalSpace X] → (X → Y) → TopologicalSpace Y
def quotientTopologyValue : quotientTopologyType := @quotientTopology

def equivalenceQuotientTopologyType : Type (u + 1) :=
  {X : Type u} → [TopologicalSpace X] → (r : Setoid X) → TopologicalSpace (Quotient r)
def equivalenceQuotientTopologyValue : equivalenceQuotientTopologyType :=
  @equivalenceQuotientTopology

def quotientMap_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (q : X → Y),
    QuotientMap q ↔ IsQuotientMap q

def saturated_iff_fiberwise : Prop :=
  ∀ {X : Type u} {Y : Type v} (q : X → Y) (A : Set X),
    Saturated q A ↔ ∀ x ∈ A, ∀ x', q x' = q x → x' ∈ A

def saturated_iff_union_fibers : Prop :=
  ∀ {X : Type u} {Y : Type v} (q : X → Y) (A : Set X),
    Saturated q A ↔ ∃ B : Set Y, A = ⋃ y ∈ B, q ⁻¹' {y}

def quotientTopology_isOpen_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] (q : X → Y) (V : Set Y),
    IsOpen[quotientTopology q] V ↔ IsOpen (q ⁻¹' V)

def quotientTopology_eq_final : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] (q : X → Y),
    quotientTopology q = finalTopology (fun _ : Unit => q)

def quotientTopology_quotientMap : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] (q : X → Y),
    Function.Surjective q → @QuotientMap X Y tX (quotientTopology q) q

def quotientMap_iff_topology : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [tY : TopologicalSpace Y]
    (q : X → Y), QuotientMap q ↔ Function.Surjective q ∧ tY = quotientTopology q

def equivalenceQuotient_isOpen_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] (r : Setoid X) (V : Set (Quotient r)),
    IsOpen[equivalenceQuotientTopology r] V ↔ IsOpen (Quotient.mk r ⁻¹' V)

def equivalenceQuotient_classMap : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] (r : Setoid X),
    @QuotientMap X (Quotient r) tX (equivalenceQuotientTopology r) (Quotient.mk r)

/-- Equality of classes is precisely the original equivalence relation. -/
def equivalenceQuotient_class_eq : Prop :=
  ∀ {X : Type u} (r : Setoid X) (x x' : X),
    Quotient.mk r x = Quotient.mk r x' ↔ r x x'

def quotient_continuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), QuotientMap q → Continuous q

def quotient_continuous_iff : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (q : X → Y), QuotientMap q → ∀ h : Y → Z,
      Continuous h ↔ Continuous (h ∘ q)

/-- Unique as a function, with both continuity and the full descent equation. -/
def quotient_descent : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (q : X → Y), QuotientMap q → ∀ f : X → Z, Continuous f →
      (∀ x x', q x = q x' → f x = f x') →
        ∃! g : Y → Z, Continuous g ∧ g ∘ q = f

/-- Even the single Sierpiński target detects the quotient topology. -/
def quotient_of_sierpinski_test : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (q : X → Y), Continuous q → Function.Surjective q →
      (∀ h : Y → Bool, Continuous[tX, topology] (h ∘ q) →
        Continuous[tY, topology] h) → QuotientMap q

/-- Testing every target suffices. Targets in the universe of Y already
    suffice: take Y with its final topology as one target. The forward mapping
    theorem above applies to targets in any universe. -/
def quotient_of_mapping_test : Prop :=
  ∀ {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (q : X → Y), Continuous q → Function.Surjective q →
      (∀ (Z : Type v) (tZ : TopologicalSpace Z) (h : Y → Z),
        Continuous[tX, tZ] (h ∘ q) → Continuous[tY, tZ] h) → QuotientMap q

def continuous_open_surjection_quotient : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), Continuous q → IsOpenMap q → Function.Surjective q → QuotientMap q

def continuous_closed_surjection_quotient : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y), Continuous q → IsClosedMap q → Function.Surjective q → QuotientMap q

def quotient_comp : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (q : X → Y) (r : Y → Z), QuotientMap q → QuotientMap r → QuotientMap (r ∘ q)

def continuous_section_quotient : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (q : X → Y) (s : Y → X), Continuous q → Function.Surjective q →
      Continuous s → Function.RightInverse s q → QuotientMap q

end Specs.D10Topology.Ch03.QuotientMaps
