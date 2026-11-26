import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralTorus
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open AlgebraicGeometry CategoryTheory Matrix
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.OddSpinOrthogonalGeometry

open GeometricRadicals (IsSplitTorus IsSemisimple IsMaximalTorus baseChangedSubgroup)

noncomputable section

abbrev Index (n : ℕ) := ULift.{u} ((Fin n ⊕ Fin n) ⊕ Unit)

def e {n : ℕ} (i : Fin n) : Index.{u} n := ⟨.inl (.inl i)⟩
def f {n : ℕ} (i : Fin n) : Index.{u} n := ⟨.inl (.inr i)⟩
def r (n : ℕ) : Index.{u} n := ⟨.inr ()⟩

/-- The partner of a hyperbolic basis vector, fixing the norm-one line. -/
def partner {n : ℕ} : Index.{u} n → Index.{u} n
  | ⟨.inl (.inl i)⟩ => f i
  | ⟨.inl (.inr i)⟩ => e i
  | ⟨.inr ()⟩ => r n

/-- The polar Gram matrix of the split odd quadratic form. -/
def gram (n : ℕ) (A : Type u) [CommRing A] : Matrix (Index n) (Index n) A :=
  fun i j ↦ if j = partner i then (if i = r n then 2 else 1) else 0

def diagonalEntry {n : ℕ} {A : Type u} [CommRing A] (t : Fin n → Aˣ) :
    Index.{u} n → A
  | ⟨.inl (.inl i)⟩ => t i
  | ⟨.inl (.inr i)⟩ => ↑((t i)⁻¹)
  | ⟨.inr ()⟩ => 1

def orthogonalMatrices (n : ℕ) (A : Type u) [CommRing A] :
    Subgroup (SpecialLinearGroup (Index n) A) where
  carrier := {M | M.valᵀ * gram n A * M.val = gram n A}
  one_mem' := by simp [SpecialLinearGroup.coe_one]
  mul_mem' {a b} ha hb := by
    change a.valᵀ * _ * a.val = _ at ha
    change b.valᵀ * _ * b.val = _ at hb
    change (a.val * b.val)ᵀ * _ * (a.val * b.val) = _
    rw [transpose_mul]
    calc
      _ = b.valᵀ * (a.valᵀ * gram n A * a.val) * b.val := by
        simp only [mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' {a} ha := by
    change a.valᵀ * _ * a.val = _ at ha
    change (a⁻¹).valᵀ * _ * (a⁻¹).val = _
    calc
      _ = (a⁻¹).valᵀ * (a.valᵀ * gram n A * a.val) * (a⁻¹).val := by rw [ha]
      _ = (a.val * (a⁻¹).val)ᵀ * gram n A * (a.val * (a⁻¹).val) := by
        rw [transpose_mul]
        simp only [mul_assoc]
      _ = _ := by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel]; simp

variable {k : Type u} [Field k]

/-- Scalar maps act entrywise on the determinant-one isometries. -/
def mapOrthogonal {n : ℕ} {A B : TestAlgebra k} (a : A ⟶ B) :
    orthogonalMatrices n A →* orthogonalMatrices n B :=
  ((SpecialLinearGroup.map a.hom.toRingHom).comp (orthogonalMatrices n A).subtype).codRestrict _ <| by
    intro x
    have h := congrArg a.hom.toRingHom.mapMatrix x.property
    have hGram : a.hom.toRingHom.mapMatrix (gram n A) = gram n B := by
      ext i j
      change a.hom (gram n A i j) = gram n B i j
      unfold gram
      split_ifs <;> simp [map_ofNat]
    change a.hom.toRingHom.mapMatrix (x.val.valᵀ * gram n A * x.val.val) = _ at h
    change (a.hom.toRingHom.mapMatrix x.val.val)ᵀ * gram n B *
      (a.hom.toRingHom.mapMatrix x.val.val) = _
    have ht : a.hom.toRingHom.mapMatrix x.val.valᵀ =
        (a.hom.toRingHom.mapMatrix x.val.val)ᵀ := rfl
    rw [map_mul, map_mul, ht, hGram] at h
    exact h

def orthogonalPoints (k : Type u) [Field k] (n : ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj A := GrpCat.of (orthogonalMatrices n A)
  map a := GrpCat.ofHom (mapOrthogonal a)
  map_id _ := by apply GrpCat.ext; intro x; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; rfl

def torusPoints (k : Type u) [Field k] (n : ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj A := GrpCat.of (Fin n → Aˣ)
  map a := GrpCat.ofHom (MonoidHom.pi fun i ↦ (Units.map a.hom.toMonoidHom).comp (Pi.evalMonoidHom _ i))
  map_id _ := by apply GrpCat.ext; intro x; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; rfl

/-- The two functor identifications, with the specified diagonal inclusion. -/
structure MarkedModel (n : ℕ) (O : AffineAlgebraicGroup k) (T : ClosedSubgroup O.val) where
  orthogonal : (groupPointsFunctor k).obj O.val ≅ orthogonalPoints k n
  torus : (groupPointsFunctor k).obj T.group ≅ torusPoints k n
  inclusion_matrix : ∀ (A : TestAlgebra k) (t : Points T.group.X A),
    ((orthogonal.hom.app A (t ≫ T.inclusion.hom.hom)).val.val :
      Matrix (Index n) (Index n) A) = diagonal (diagonalEntry (torus.hom.app A t))

def Geometry : Prop :=
  ∀ {k : Type u} [Field k] (n : ℕ), 1 ≤ n → (2 : k) ≠ 0 →
    ∀ (O : AffineAlgebraicGroup k) (T : ClosedSubgroup O.val),
      IsSplitTorus T.group → MarkedModel n O T →
      Smooth O.val.X.hom → GeometricallyConnected O.val.X.hom →
        IsSemisimple O ∧
        CentralTorus.IsSchemeCentre (GeometricRadicals.identitySubgroup O) ∧
        (∀ (Y : SchemeOver k) (g : Y ⟶ O.val.X), Centralizes (𝟙 O.val) g → g = 1) ∧
        RepresentsSubgroup T (fun _ g ↦ Centralizes T.inclusion g) ∧
        (∀ (K : Type u) [Field K] [Algebra k K],
          ∃ h : IsClosedImmersion ((groupBaseChange k K).map T.inclusion).hom.hom.left,
            RepresentsSubgroup (baseChangedSubgroup K T h)
              (fun _ g ↦ Centralizes ((groupBaseChange k K).map T.inclusion) g)) ∧
        ∃ h : IsClosedImmersion
            ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
          IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)

end
end LinearAlgebraicGroups.Specs.OddSpinOrthogonalGeometry
