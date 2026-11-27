import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellFactorization
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace DerivedFormalization.Specs.ComplexCellCokernels

open Model.Complexes ComplexGenerators ComplexCellFactorization

/-- Every component map admits a module-linear retraction. -/
def degreewiseSplitMonoType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y),
    iCellValue A f → ∀ k : ℤ, IsSplitMono (f.f k)

/-- The colimit exhibits the cokernel as the increasing union of the stages.
The first stage is zero and each successive quotient is a sum of spheres. -/
def filtrationType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y), iCellValue A f →
    ∃ (F : ℕ ⥤ Cochains A) (ι : F ⟶ (Functor.const ℕ).obj (cokernel f)),
      IsZero (F.obj 0) ∧ Nonempty (IsColimit (Cocone.mk _ ι)) ∧
      (∀ (n : ℕ) (k : ℤ), IsSplitMono ((ι.app n).f k)) ∧
      ∀ n : ℕ,
        let g := F.map (homOfLE (Nat.le_succ n))
        (∀ k : ℤ, IsSplitMono (g.f k)) ∧
        ∃ (K : Type u) (degree : K → ℤ),
          Nonempty (cokernel g ≅ ∐ (fun i : K ↦ sphereValue A (degree i)))

def degreewiseProjectiveType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y), iCellValue A f →
    ∀ k : ℤ, Projective ((cokernel f).X k)

def kProjectiveType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y), iCellValue A f →
    (cokernel f).IsKProjective

/-- The signed Hom of left module complexes takes values in abelian groups. -/
def kProjectiveIffHomAcyclicType : Prop :=
  ∀ (A : Type u) [Ring A] (P : Cochains A),
    P.IsKProjective ↔ ∀ (E : Cochains A), E.Acyclic →
      (CochainComplex.HomComplex P E).Acyclic

def homAcyclicType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y), iCellValue A f →
    ∀ (E : Cochains A), E.Acyclic → (CochainComplex.HomComplex (cokernel f) E).Acyclic

end DerivedFormalization.Specs.ComplexCellCokernels
