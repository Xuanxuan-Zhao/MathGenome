import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.ProperInfinity
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.OnePointConstruction
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.ProperPerfect

/-! Extension at infinity (paper.tex, d10:11:proper-infinity).
No noncompactness, nonemptiness or surjectivity assumption is imposed. -/

open Set Topology
universe u v

namespace D10Topology.Ch11

/-- Extend a map by sending the added point to the added point. -/
abbrev plusMap {X : Type u} {Y : Type v} (f : X → Y) : Xplus X → Xplus Y :=
  OnePoint.map f

theorem plusMap_inclusion {X : Type u} {Y : Type v} (f : X → Y) (x : X) :
    plusMap f (plusInclusion x) = plusInclusion (f x) := rfl

theorem plusMap_infinity {X : Type u} {Y : Type v} (f : X → Y) :
    plusMap f (plusInfinity X) = plusInfinity Y := rfl

theorem continuous_plusMap_iff_proper {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (hX : LCH X) (hY : LCH Y)
    (f : X → Y) (_hf : Continuous f) :
    Continuous (plusMap f) ↔ Proper f := by
  let : T2Space X := hX.2
  let : T2Space Y := hY.2
  let : WeaklyLocallyCompactSpace Y :=
    (locallyCompact_iff_weaklyLocallyCompactSpace Y).mp hY.1
  -- In Hausdorff spaces compact sets are closed, so the library's
  -- coclosed-compact filters are exactly the compact-complement filters.
  rw [plusMap, OnePoint.continuous_map_iff,
    Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
  exact isProperMap_iff_tendsto_cocompact.symm.trans (isProperMap_iff_proper hY f)

/-- A homeomorphism extends with its inverse extended in the same way. -/
def plusHomeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : Xplus X ≃ₜ Xplus Y :=
  e.onePointCongr

theorem plusHomeomorph_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (z : Xplus X) :
    plusHomeomorph e z = plusMap e z := rfl

theorem homeomorphism_extends {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (_hX : LCH X) (_hY : LCH Y)
    (e : X ≃ₜ Y) :
    ∃ E : Xplus X ≃ₜ Xplus Y,
      (∀ x : X, E (plusInclusion x) = plusInclusion (e x)) ∧
      E (plusInfinity X) = plusInfinity Y :=
  ⟨plusHomeomorph e, fun _ => rfl, rfl⟩

end D10Topology.Ch11
