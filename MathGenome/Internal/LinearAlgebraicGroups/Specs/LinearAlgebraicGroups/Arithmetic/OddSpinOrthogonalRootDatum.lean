import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbstractPairing
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.OddSpinOrthogonalRootDatum

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing characterValue)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open AbstractPairing (Datum Root)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

abbrev Index (n : ℕ) := ULift.{u} ((Fin n ⊕ Fin n) ⊕ Unit)

def partner {n : ℕ} (i : Index n) : Index n :=
  ⟨i.down.elim (fun j => .inl (j.elim Sum.inr Sum.inl)) Sum.inr⟩

def gramCoefficient {n : ℕ} (R : Type u) [CommRing R] (i : Index n) : R :=
  i.down.elim (fun _ => 1) (fun _ => 2)

def gram (n : ℕ) (R : Type u) [CommRing R] : Matrix (Index n) (Index n) R :=
  fun i j => if partner i = j then gramCoefficient R i else 0

/-- The determinant-one isometries of the polar form of the split odd quadratic space. -/
def orthogonalMatrices (n : ℕ) (R : Type u) [CommRing R] :
    Subgroup (SpecialLinearGroup (Index n) R) where
  carrier := {g | g.valᵀ * gram n R * g.val = gram n R}
  one_mem' := by simp [SpecialLinearGroup.coe_one]
  mul_mem' {a b} ha hb := by
    change a.valᵀ * gram n R * a.val = gram n R at ha
    change b.valᵀ * gram n R * b.val = gram n R at hb
    change (a * b).valᵀ * gram n R * (a * b).val = gram n R
    rw [SpecialLinearGroup.coe_mul, transpose_mul]
    calc
      _ = b.valᵀ * (a.valᵀ * gram n R * a.val) * b.val := by simp only [mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' {a} ha := by
    change a.valᵀ * gram n R * a.val = gram n R at ha
    change (a⁻¹).valᵀ * gram n R * (a⁻¹).val = gram n R
    have hl : a.val * (a⁻¹).val = 1 := by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]
      rfl
    calc
      _ = (a⁻¹).valᵀ * (a.valᵀ * gram n R * a.val) * (a⁻¹).val := by rw [ha]
      _ = (a.val * (a⁻¹).val)ᵀ * gram n R * (a.val * (a⁻¹).val) := by
        rw [transpose_mul]
        simp only [mul_assoc]
      _ = _ := by rw [hl, transpose_one, one_mul, mul_one]

def diagonalUnit {n : ℕ} {R : Type u} [CommRing R] (t : Fin n → Rˣ) (i : Index n) : Rˣ :=
  i.down.elim (fun j => j.elim t (fun a => (t a)⁻¹)) (fun _ => 1)

variable {k : Type u} [Field k] {n : ℕ} {O : AffineAlgebraicGroup k}

/-- Natural point identifications of the split orthogonal group and its diagonal torus. -/
structure PointCoordinates (T : ClosedSubgroup O.val) (n : ℕ) where
  orthogonal (R : TestAlgebra k) : GroupPoints O.val R ≃* orthogonalMatrices.{u,u} n R
  torus (R : TestAlgebra k) : GroupPoints T.group R ≃* (Fin n → Rˣ)
  orthogonal_natural {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints O.val R) :
    (orthogonal S (mapPoints a g)).val.val = a.hom.toRingHom.mapMatrix (orthogonal R g).val.val
  torus_natural {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T.group R) (i : Fin n) :
    torus S (mapPoints a t) i = Units.map a.hom.toMonoidHom (torus R t i)
  inclusion (R : TestAlgebra k) (t : GroupPoints T.group R) :
    (orthogonal R (t ≫ T.inclusion.hom.hom)).val.val =
      diagonal (fun i => (diagonalUnit (torus R t) i : R))

/-- Markings of the actual character and cocharacter lattices in the diagonal coordinates. -/
structure LatticeCoordinates {T : ClosedSubgroup O.val} [IsCommMonObj T.group.X]
    (p : PointCoordinates T n) where
  characters : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ)
  cocharacters : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)
  pairing_eq (χ : Character T.group) (c : Cocharacter T.group) :
    pairing T.group χ c = ∑ i, characters (Additive.ofMul χ) i * cocharacters (Additive.ofMul c) i
  character_eval (R : TestAlgebra k) (t : GroupPoints T.group R) (χ : Character T.group) :
    characterValue χ R t =
      ((∏ i, (p.torus R t i) ^ (characters (Additive.ofMul χ) i) : Rˣ) : R)
  cocharacter_eval (R : TestAlgebra k) (z : Rˣ) (c : Cocharacter T.group) (i : Fin n) :
    p.torus R (cocharacterPoint c R z) i = z ^ (cocharacters (Additive.ofMul c) i)

def coordinate (n : ℕ) (i : Fin n) : Fin n → ℤ := Pi.single i 1

def roots (n : ℕ) : Set (Fin n → ℤ) :=
  {v | (∃ i, v = coordinate n i ∨ v = -coordinate n i) ∨
    ∃ i j, i ≠ j ∧ (v = coordinate n i - coordinate n j ∨
      v = coordinate n i + coordinate n j ∨ v = -(coordinate n i + coordinate n j))}

def corootPairs (n : ℕ) : Set ((Fin n → ℤ) × (Fin n → ℤ)) :=
  {p | (∃ i, (p.1 = coordinate n i ∧ p.2 = 2 • coordinate n i) ∨
      (p.1 = -coordinate n i ∧ p.2 = -(2 • coordinate n i))) ∨
    ∃ i j, i ≠ j ∧ p.1 = p.2 ∧
      (p.1 = coordinate n i - coordinate n j ∨ p.1 = coordinate n i + coordinate n j ∨
        p.1 = -(coordinate n i + coordinate n j))}

/-- The roots and the paired roots and attached coroots in the marked lattices of the split
odd orthogonal group, including both signs and the rank-one case. -/
def Statement : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) ≠ 0 → 0 < n →
    ∀ (O : AffineAlgebraicGroup k) (T : ClosedSubgroup O.val),
      IsReductive O → IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∀ [IsCommMonObj T.group.X] (p : PointCoordinates T n) (l : LatticeCoordinates p),
        (fun χ => l.characters (Additive.ofMul χ)) '' absoluteRoots T = roots n ∧
        ∃ d : Datum T,
          Set.range (fun α : Root T =>
            (l.characters (d.rootDatum.root α), l.cocharacters (d.rootDatum.coroot α))) =
            corootPairs n

end

end LinearAlgebraicGroups.Specs.Arithmetic.OddSpinOrthogonalRootDatum
