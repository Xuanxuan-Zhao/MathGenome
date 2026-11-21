import Mathlib.Analysis.Complex.Isometry
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! Independent geometric specification of paper.tex:363–369.
The plane is ℂ with its Euclidean distance. The vertex set is the usual
regular polygon, including arbitrary center, nonzero size and initial vertex.
Symmetries are ALL bijective metric isometries preserving that vertex set.
In particular membership does not assume linearity, a fixed center, or a
rotation/reflection normal form. Multiplication is composition, right map first.
-/
noncomputable section
namespace Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries

open Complex
open scoped ComplexConjugate

/-- A positive turn of one vertex. -/
def root (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / n)

/-- A regular polygon with center `c` and first vertex `c + a`. -/
def vertices (n : ℕ) (c a : ℂ) : Set ℂ :=
  Set.range (fun i : Fin n => c + a * root n ^ i.val)

/-- Full geometric symmetry group of any vertex set. -/
def symmetryGroup (P : Set ℂ) : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | ∀ z, f z ∈ P ↔ z ∈ P}
  one_mem' := by intro z; rfl
  mul_mem' := by
    intro f g hf hg z
    exact (hf (g z)).trans (hg z)
  inv_mem' := by
    intro f hf z
    simpa only [IsometryEquiv.apply_inv_self] using (hf (f⁻¹ z)).symm

/-- The rotation about zero through exactly `2π/n`. -/
def turn (n : ℕ) : ℂ ≃ᵢ ℂ :=
  (rotation (Circle.exp (2 * Real.pi / n))).toIsometryEquiv

/-- Reflection in the real axis, an axis through the first vertex. -/
def mirror : ℂ ≃ᵢ ℂ := Complex.conjLIE.toIsometryEquiv

/-- Regularity is expressed by explicit Euclidean coordinates, with no
assumption about the symmetry group. -/
def IsRegularPolygon (n : ℕ) (P : Set ℂ) : Prop :=
  ∃ c a : ℂ, a ≠ 0 ∧ P = vertices n c a

/-- Exhaustion, faithful identification, and the specified generators.
Mathlib's `sr i` means `s * r^i`, so its pointwise formula has exponent `-i`.
The source normal form `r^i * s` is separately required below. -/
def CanonicalIdentification : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∃ e : DihedralGroup n ≃* symmetryGroup (vertices n 0 1),
      ((e (DihedralGroup.r 1) : symmetryGroup (vertices n 0 1)) : ℂ ≃ᵢ ℂ) = turn n ∧
      ((e (DihedralGroup.sr 0) : symmetryGroup (vertices n 0 1)) : ℂ ≃ᵢ ℂ) = mirror

/-- Cardinality is the actual finite cardinality of the complete geometric
symmetry group, rather than a count of a supplied subgroup of motions. -/
def GeometricOrder : Prop :=
  ∀ (n : ℕ) (P : Set ℂ), 3 ≤ n → IsRegularPolygon n P →
    Finite (symmetryGroup P) ∧ Nat.card (symmetryGroup P) = 2 * n

/-- The geometric generators obey the displayed source relations. -/
def GeneratorRelations : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    turn n ^ n = 1 ∧ mirror ^ 2 = 1 ∧ mirror * turn n * mirror = (turn n)⁻¹

/-- Unique choice of exponent and family for each geometric symmetry. -/
def UniqueNormalForms : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∀ f : symmetryGroup (vertices n 0 1),
      ∃! p : Fin n × Bool,
        (f : ℂ ≃ᵢ ℂ) = if p.2 then turn n ^ p.1.val * mirror else turn n ^ p.1.val

/-- An arbitrary regular polygon has the same full symmetry group, by an
isomorphism; this includes arbitrary center, size, and initial direction. -/
def GeneralIdentification : Prop :=
  ∀ (n : ℕ) (P : Set ℂ), 3 ≤ n → IsRegularPolygon n P →
    Nonempty (DihedralGroup n ≃* symmetryGroup P)

/-- All the source conclusions with the actual geometric generators, for an
arbitrary polygon in the stated coordinates. The reflection axis passes
through `c` and the vertex `c + a`; no restriction on that axis is imposed. -/
def FullGeometricModel : Prop :=
  ∀ (n : ℕ) (c a : ℂ), 3 ≤ n → a ≠ 0 →
    ∃ e : DihedralGroup n ≃* symmetryGroup (vertices n c a),
      let r := e (DihedralGroup.r 1)
      let s := e (DihedralGroup.sr 0)
      (∀ z : ℂ, (r : ℂ ≃ᵢ ℂ) z = c + root n * (z - c)) ∧
      (∀ z : ℂ, (s : ℂ ≃ᵢ ℂ) z = c + a * conj ((z - c) / a)) ∧
      r ^ n = 1 ∧ s ^ 2 = 1 ∧ s * r * s = r⁻¹ ∧
      ∀ f : symmetryGroup (vertices n c a),
        ∃! p : Fin n × Bool, f = if p.2 then r ^ p.1.val * s else r ^ p.1.val

end Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
