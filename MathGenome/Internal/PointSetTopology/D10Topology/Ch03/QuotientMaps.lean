import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.SumsAndFinalTopologies

/-!
Quotient maps, saturation, equivalence-class quotients and descent, for
paper.tex d10:03:quotient and d10:03:quotient-universal. The source definition
is explicitly compared with Mathlib before its map APIs are used.
All results allow empty spaces and impose no separation axiom.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch03

def QuotientMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (q : X → Y) : Prop :=
  QuotientData.QuotientMap q

def Saturated {X : Type u} {Y : Type v} (q : X → Y) (A : Set X) : Prop :=
  QuotientData.Saturated q A

@[instance_reducible] def quotientTopology {X : Type u} {Y : Type v}
    [TopologicalSpace X] (q : X → Y) : TopologicalSpace Y :=
  QuotientData.quotientTopology q

@[instance_reducible] def equivalenceQuotientTopology {X : Type u}
    [TopologicalSpace X] (r : Setoid X) : TopologicalSpace (Quotient r) :=
  QuotientData.equivalenceQuotientTopology r

theorem saturated_iff_fiberwise {X : Type u} {Y : Type v} (q : X → Y) (A : Set X) :
    Saturated q A ↔ ∀ x ∈ A, ∀ x', q x' = q x → x' ∈ A := by
  change A = q ⁻¹' (q '' A) ↔ _
  constructor
  · intro h x hx x' heq
    rw [h]
    exact ⟨x, hx, heq.symm⟩
  · intro h
    apply Subset.antisymm
    · exact subset_preimage_image q A
    · rintro x' ⟨x, hx, heq⟩
      exact h x hx x' heq.symm

theorem saturated_iff_union_fibers {X : Type u} {Y : Type v} (q : X → Y) (A : Set X) :
    Saturated q A ↔ ∃ B : Set Y, A = ⋃ y ∈ B, q ⁻¹' {y} := by
  constructor
  · intro h
    refine ⟨q '' A, ?_⟩
    change A = q ⁻¹' (q '' A) at h
    conv_lhs => rw [h]
    ext x
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    exact ⟨fun hx => ⟨q x, hx, rfl⟩, fun ⟨y, hy, heq⟩ => heq.symm ▸ hy⟩
  · rintro ⟨B, hB⟩
    apply (saturated_iff_fiberwise q A).mpr
    intro x hx x' heq
    rw [hB] at hx ⊢
    simpa only [mem_iUnion, mem_preimage, mem_singleton_iff, heq] using hx

section Maps
variable {X : Type u} {Y : Type v} {Z : Type w}
  [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [TopologicalSpace Z]

theorem quotientMap_iff_mathlib (q : X → Y) : QuotientMap q ↔ IsQuotientMap q := by
  constructor
  · rintro ⟨hs, ho⟩
    exact ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen (fun V => (ho V).symm), hs⟩
  · intro h
    exact ⟨h.surjective, fun _ => h.isCoinducing.isOpen_preimage.symm⟩

theorem quotientMap_iff_topology (q : X → Y) :
    QuotientMap q ↔ Function.Surjective q ∧ tY = quotientTopology q := by
  rw [quotientMap_iff_mathlib]
  exact ⟨fun h => ⟨h.surjective, h.eq_coinduced⟩, fun h => ⟨⟨h.2⟩, h.1⟩⟩

theorem quotient_continuous (q : X → Y) (hq : QuotientMap q) : Continuous q :=
  ((quotientMap_iff_mathlib q).mp hq).continuous

theorem quotient_continuous_iff (q : X → Y) (hq : QuotientMap q) (h : Y → Z) :
    Continuous h ↔ Continuous (h ∘ q) :=
  ((quotientMap_iff_mathlib q).mp hq).continuous_iff

theorem quotient_descent (q : X → Y) (hq : QuotientMap q) (f : X → Z)
    (hf : Continuous f) (hfib : ∀ x x', q x = q x' → f x = f x') :
    ∃! g : Y → Z, Continuous g ∧ g ∘ q = f := by
  classical
  let g : Y → Z := fun y => f (Classical.choose (hq.1 y))
  have hg : g ∘ q = f := by
    funext x
    exact hfib _ x (Classical.choose_spec (hq.1 (q x)))
  refine ⟨g, ⟨(quotient_continuous_iff q hq g).mpr (hg.symm ▸ hf), hg⟩, ?_⟩
  intro k hk
  funext y
  obtain ⟨x, rfl⟩ := hq.1 y
  exact (congrFun hk.2 x).trans (congrFun hg x).symm

theorem quotient_of_sierpinski_test (q : X → Y) (hc : Continuous q)
    (hs : Function.Surjective q)
    (ht : ∀ h : Y → Bool, Continuous[tX, Ch02.CharacteristicMaps.topology] (h ∘ q) →
      Continuous[tY, Ch02.CharacteristicMaps.topology] h) : QuotientMap q := by
  refine ⟨hs, fun V => ⟨fun hV => hV.preimage hc, ?_⟩⟩
  intro hV
  apply (Ch02.characteristic_continuous_iff_open V).mp
  apply ht
  have heq : Ch02.characteristic V ∘ q = Ch02.characteristic (q ⁻¹' V) := by
    rfl
  rw [heq]
  exact (Ch02.characteristic_continuous_iff_open (q ⁻¹' V)).mpr hV

theorem quotient_of_mapping_test (q : X → Y) (hc : Continuous q)
    (hs : Function.Surjective q)
    (ht : ∀ (Z : Type v) (tZ : TopologicalSpace Z) (h : Y → Z),
      Continuous[tX, tZ] (h ∘ q) → Continuous[tY, tZ] h) : QuotientMap q := by
  have hid : Continuous[tY, quotientTopology q] (id : Y → Y) :=
    ht Y (quotientTopology q) id continuous_coinduced_rng
  refine ⟨hs, fun V => ⟨fun hV => hV.preimage hc, ?_⟩⟩
  intro hV
  exact @Continuous.isOpen_preimage Y Y tY (quotientTopology q) id hid V hV

theorem continuous_open_surjection_quotient (q : X → Y) (hc : Continuous q)
    (ho : IsOpenMap q) (hs : Function.Surjective q) : QuotientMap q :=
  (quotientMap_iff_mathlib q).mpr (ho.isQuotientMap hc hs)

theorem continuous_closed_surjection_quotient (q : X → Y) (hc : Continuous q)
    (hcl : IsClosedMap q) (hs : Function.Surjective q) : QuotientMap q :=
  (quotientMap_iff_mathlib q).mpr (hcl.isQuotientMap hc hs)

theorem quotient_comp (q : X → Y) (r : Y → Z) (hq : QuotientMap q)
    (hr : QuotientMap r) : QuotientMap (r ∘ q) :=
  (quotientMap_iff_mathlib _).mpr
    (((quotientMap_iff_mathlib r).mp hr).comp ((quotientMap_iff_mathlib q).mp hq))

theorem continuous_section_quotient (q : X → Y) (s : Y → X) (hc : Continuous q)
    (_hs : Function.Surjective q) (hsc : Continuous s) (hsec : Function.RightInverse s q) :
    QuotientMap q :=
  (quotientMap_iff_mathlib q).mpr (IsQuotientMap.of_inverse hsc hc hsec)

end Maps

theorem quotientTopology_isOpen_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    (q : X → Y) (V : Set Y) :
    IsOpen[quotientTopology q] V ↔ IsOpen (q ⁻¹' V) := Iff.rfl

theorem quotientTopology_eq_final {X : Type u} {Y : Type v} [TopologicalSpace X]
    (q : X → Y) : quotientTopology q = finalTopology (fun _ : Unit => q) := by
  unfold quotientTopology QuotientData.quotientTopology finalTopology SumFinalData.finalTopology
  simp only [iSup_const]

theorem quotientTopology_quotientMap {X : Type u} {Y : Type v} [tX : TopologicalSpace X]
    (q : X → Y) (hs : Function.Surjective q) :
    @QuotientMap X Y tX (quotientTopology q) q := ⟨hs, fun _ => Iff.rfl⟩

theorem equivalenceQuotient_isOpen_iff {X : Type u} [TopologicalSpace X]
    (r : Setoid X) (V : Set (Quotient r)) :
    IsOpen[equivalenceQuotientTopology r] V ↔ IsOpen (Quotient.mk r ⁻¹' V) := Iff.rfl

theorem equivalenceQuotient_classMap {X : Type u} [tX : TopologicalSpace X]
    (r : Setoid X) :
    @QuotientMap X (Quotient r) tX (equivalenceQuotientTopology r) (Quotient.mk r) :=
  quotientTopology_quotientMap _ (fun y => Quotient.exists_rep y)

theorem equivalenceQuotient_class_eq {X : Type u} (r : Setoid X) (x x' : X) :
    Quotient.mk r x = Quotient.mk r x' ↔ r x x' := Quotient.eq

end D10Topology.Ch03
