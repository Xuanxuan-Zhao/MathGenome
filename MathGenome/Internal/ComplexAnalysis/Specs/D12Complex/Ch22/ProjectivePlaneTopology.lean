import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open Set
namespace D12Complex.ProjectivePlaneTopology

/-- Coordinates in order Z, X, Y. -/
abbrev HomogeneousVector := {v : Fin 3 → ℂ // v ≠ 0}
/-- The literal scalar-orbit quotient of the nonzero vectors of ℂ³. -/
def ComplexProjectivePlane := Projectivization ℂ (Fin 3 → ℂ)
instance : TopologicalSpace ComplexProjectivePlane :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin 3 → ℂ))))
def projection (v : HomogeneousVector) : ComplexProjectivePlane :=
  Projectivization.mk ℂ v.val v.property

/-- The coordinate-i-nonzero open set, specified without choosing representatives. -/
def coordinatePatch (i : Fin 3) : Set ComplexProjectivePlane :=
  {p | ∃ v : HomogeneousVector, projection v = p ∧ v.val i ≠ 0}

/-- A totalized ratio; continuity is asserted only where the denominator is nonzero. -/
def coordinateRatio (i j : Fin 3) : ComplexProjectivePlane → ℂ :=
  Projectivization.lift (fun v : HomogeneousVector => v.val j / v.val i) (by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ t ht
    have ht0 : t ≠ 0 := by
      intro h
      apply hv
      simpa [h] using ht
    change v = t • w at ht
    subst v
    exact mul_div_mul_left _ _ ht0)

/-- The two coordinate ratios, in the order obtained by deleting coordinate i. -/
def affineCoordinate (i : Fin 3) (p : ComplexProjectivePlane) : Fin 2 → ℂ :=
  fun j => coordinateRatio i (i.succAbove j) p

/-- Insert 1 in coordinate i, giving the inverse affine parametrization. -/
def affineParam (i : Fin 3) (z : Fin 2 → ℂ) : ComplexProjectivePlane :=
  projection ⟨i.insertNth 1 z, by
    intro h
    have := congrFun h i
    simp at this⟩

end D12Complex.ProjectivePlaneTopology

namespace Specs.D12Complex.Ch22.ProjectivePlaneTopology
open _root_.D12Complex.ProjectivePlaneTopology

def HomogeneousVector_type := Type
def HomogeneousVector_value : HomogeneousVector_type := {v : Fin 3 → ℂ // v ≠ 0}
def ComplexProjectivePlane_type := Type
def ComplexProjectivePlane_value : ComplexProjectivePlane_type := Projectivization ℂ (Fin 3 → ℂ)
def projection_type := HomogeneousVector → ComplexProjectivePlane
def projection_value : projection_type := fun v => Projectivization.mk ℂ v.val v.property
def coordinatePatch_type := Fin 3 → Set ComplexProjectivePlane
def coordinatePatch_value : coordinatePatch_type := fun i =>
  {p | ∃ v : HomogeneousVector, projection v = p ∧ v.val i ≠ 0}
def coordinateRatio_type := Fin 3 → Fin 3 → ComplexProjectivePlane → ℂ
def coordinateRatio_value : coordinateRatio_type := coordinateRatio
def affineCoordinate_type := Fin 3 → ComplexProjectivePlane → (Fin 2 → ℂ)
def affineCoordinate_value : affineCoordinate_type := fun i p j => coordinateRatio i (i.succAbove j) p
def affineParam_type := Fin 3 → (Fin 2 → ℂ) → ComplexProjectivePlane
def affineParam_value : affineParam_type := affineParam

def projection_quotient_type : Prop := Topology.IsQuotientMap projection
def projection_open_type : Prop := IsOpenMap projection
def projective_compact_type : Prop := CompactSpace ComplexProjectivePlane
def projective_hausdorff_type : Prop := T2Space ComplexProjectivePlane
def projective_secondCountable_type : Prop := SecondCountableTopology ComplexProjectivePlane

def affine_charts_type : Prop :=
  ∃ c : Fin 3 → OpenPartialHomeomorph ComplexProjectivePlane (Fin 2 → ℂ),
    (∀ i, (c i).source = coordinatePatch i) ∧
    (∀ i, (c i).target = univ) ∧
    (∀ i p, c i p = affineCoordinate i p) ∧
    (∀ i z, (c i).symm z = affineParam i z) ∧
    (∀ p, ∃ i, p ∈ (c i).source)

/-- Compact Hausdorff, second countable quotient, with the three prescribed charts. -/
def projective_plane_topology_type : Prop :=
  Topology.IsQuotientMap projection ∧ CompactSpace ComplexProjectivePlane ∧
  T2Space ComplexProjectivePlane ∧ SecondCountableTopology ComplexProjectivePlane ∧
  affine_charts_type

end Specs.D12Complex.Ch22.ProjectivePlaneTopology
