import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.ExactOperations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.Triangularization

noncomputable section

open Unipotent

variable {k : Type u} [Field k]

/-- Invertible upper triangular matrices over an arbitrary commutative ring. -/
def upperTriangular (ι R : Type*) [Fintype ι] [LinearOrder ι] [DecidableEq ι] [CommRing R] :
    Subgroup (Matrix.GeneralLinearGroup ι R) where
  carrier := {g | g.val.IsUpperTriangular}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' := Matrix.BlockTriangular.mul
  inv_mem' {g} hg := by
    change g.val.IsUpperTriangular at hg
    change g⁻¹.val.IsUpperTriangular
    let := g.invertible
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg

/-- The functor represented by the upper triangular group `T_n`. -/
def upperTriangularPoints (k : Type u) [Field k] (n : ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (upperTriangular (Index n) R)
  map a := GrpCat.ofHom <| ((Matrix.GeneralLinearGroup.map a.hom.toRingHom).comp
    (upperTriangular (Index n) _).subtype).codRestrict _ fun g ↦ g.property.map a.hom
  map_id _ := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  map_comp _ _ := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

/-- Simplicity of a rational representation in the right comodule model. -/
def IsSimple {A : HopfAlgebraCategory k} {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : RightComodule k A V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule k V, ρ.IsSubcomodule W → W = ⊥ ∨ W = ⊤

def SimpleRepresentationsAreLines (A : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RightComodule k A V), IsSimple ρ → Module.finrank k V = 1

/-- The successive prefixes of an adapted basis span a full flag of subcomodules,
with zero and the whole representation as its end terms. -/
def HasInvariantFullFlags (A : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RightComodule k A V),
    ∃ b : Module.Basis (Index.{u} (Module.finrank k V)) k V,
      ∀ j : Fin (Module.finrank k V + 1),
        ρ.IsSubcomodule (Submodule.span k (b '' {i | i.down.val < j.val}))

/-- Representability of the upper triangular matrix group on all test algebras. -/
def UpperTriangularRepresentability : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), ∃ T : AffineAlgebraicGroup k,
    Nonempty ((groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n)

def EmbedsUpperTriangular (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (n : ℕ) (T : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n) ∧
    ∃ f : G.val ⟶ T.val, IsClosedImmersion f.hom.hom.left

def HasUnipotentKernelAndDiagonalizableQuotient (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (U : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
    IsNormalSubgroup U.inclusion ∧ IsUnipotent (closedSubgroupAlgebraicGroup U) ∧
      IsFppfGroupQuotient U q ∧
        ∃ (M : Type u) (_ : CommGroup M) (_ : Group.FG M),
          Nonempty (Q.val ≅ (DiagonalizableGroups.diagonalGroup k M).val)

def FourEquivalentConditions : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (A : HopfAlgebraCategory k),
    (((affineHopfSpec k).obj (op A)).val ≅ G.val) →
      (SimpleRepresentationsAreLines A ↔ HasInvariantFullFlags A) ∧
      (HasInvariantFullFlags A ↔ EmbedsUpperTriangular G) ∧
      (EmbedsUpperTriangular G ↔ HasUnipotentKernelAndDiagonalizableQuotient G)

def UpperTriangularSplitSolvable : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (T : AffineAlgebraicGroup k),
    ((groupPointsFunctor k).obj T.val ≅ upperTriangularPoints k n) →
      SchemeDerivedGroup.IsSplitSolvable T.val

end

end LinearAlgebraicGroups.Specs.Triangularization
