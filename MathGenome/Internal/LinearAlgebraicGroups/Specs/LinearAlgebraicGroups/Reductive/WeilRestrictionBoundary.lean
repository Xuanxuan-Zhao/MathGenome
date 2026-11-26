import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.WeilRestrictionBoundary

open LinearAlgebraicGroups.WeilRestriction (extendedUnits tensorMap tensorCancellation)
open Specs.StandardGroups (multiplicativePoints)
open Algebra.TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable section

set_option backward.isDefEq.respectTransparency false
open GeometricRadicals

variable {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

/-- The residue homomorphism evaluates the scalar-extension tensor product at the
embedding of the purely inseparable field in the algebraic closure. -/
noncomputable def residue (e : K →ₐ[k] L) : L ⊗[k] K →ₐ[L] L :=
  e.liftEquiv k L K L

def LocalTensorAlgebra : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    [IsPurelyInseparable k K], ¬ Function.Surjective (algebraMap k K) →
    ∀ e : K →ₐ[k] AlgebraicClosure k,
      let A := AlgebraicClosure k ⊗[k] K
      let r := residue e
      let J := RingHom.ker r.toRingHom
      IsLocalRing A ∧ J.IsMaximal ∧ J ≠ ⊥ ∧ IsNilpotent J ∧ Function.Surjective r ∧
      ∃ d : (A ⧸ J) ≃ₐ[AlgebraicClosure k] AlgebraicClosure k,
        ∀ x : A, d (Ideal.Quotient.mk J x) = r x

/-- The group represented by the unit functor is smooth and geometrically connected. -/
def SmoothGeometricallyConnected : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (G : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj G.val ≅ extendedUnits k K) →
    Smooth G.val.X.hom ∧ GeometricallyConnected G.val.X.hom

/-- All unipotent closed subgroups of the restriction itself are trivial. -/
def GroundFieldUnipotentSubgroups : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (G : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj G.val ≅ extendedUnits k K) →
    ∀ U : ClosedSubgroup G.val, Unipotent.IsUnipotent (Unipotent.closedSubgroupAlgebraicGroup U) →
      IsTrivialSubgroup U


/-- The trivial closed subgroup already satisfies the largest-subgroup property over the
ground field. -/
def GroundFieldRadical : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (G : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj G.val ≅ extendedUnits k K) →
    IsUnipotentRadical G (identitySubgroup G)

section PrincipalUnits

variable {F A : Type u} [Field F] [CommRing A] [Algebra F A]

/-- The extension of an ideal to the tensor product with a test algebra. -/
abbrev extendedPrincipalIdeal (I : Ideal A) (R : TestAlgebra F) : Ideal (R ⊗[F] A) :=
  I.map (includeRight : A →ₐ[F] R ⊗[F] A).toRingHom

/-- The subgroup of units congruent to one modulo the extended ideal. -/
def principalUnitsAt (I : Ideal A) (R : TestAlgebra F) : Subgroup (R ⊗[F] A)ˣ :=
  (Units.map (Ideal.Quotient.mk (extendedPrincipalIdeal I R)).toMonoidHom).ker

theorem mem_principalUnitsAt (I : Ideal A) (R : TestAlgebra F) (x : (R ⊗[F] A)ˣ) :
    x ∈ principalUnitsAt I R ↔ x.val - 1 ∈ extendedPrincipalIdeal I R := by
  rw [principalUnitsAt, MonoidHom.mem_ker, Units.ext_iff]
  exact (Ideal.Quotient.eq (I := extendedPrincipalIdeal I R))

/-- The group functor of principal units attached to an ideal. -/
def principalUnits (I : Ideal A) : TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (principalUnitsAt I R)
  map {R S} f := GrpCat.ofHom <|
    (((extendedUnits F A).map f).hom.comp (principalUnitsAt I R).subtype).codRestrict
      (principalUnitsAt I S) (by
        intro x
        have hx := x.property
        rw [mem_principalUnitsAt] at hx ⊢
        change (tensorMap F A f.hom x.val) - 1 ∈ extendedPrincipalIdeal I S
        rw [← map_one (tensorMap F A f.hom), ← map_sub]
        have h : (extendedPrincipalIdeal I R).map (tensorMap F A f.hom).toRingHom =
            extendedPrincipalIdeal I S := by
          rw [Ideal.map_map]
          congr 1
          apply RingHom.ext
          intro a
          change (f.hom 1) ⊗ₜ[F] a = 1 ⊗ₜ[F] a
          rw [map_one]
        rw [← h]
        exact Ideal.mem_map_of_mem _ hx)
  map_id R := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((extendedUnits F A).map_id R) x.val
  map_comp f g := by
    apply GrpCat.ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((extendedUnits F A).map_comp f g) x.val

/-- The additive vector group on the scalar extension of a vector space. -/
def vectorPoints (V : Type u) [AddCommGroup V] [Module F V] : TestAlgebra F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Multiplicative (R ⊗[F] V))
  map f := GrpCat.ofHom
    (((LinearMap.rTensor V f.hom.toLinearMap).toAddMonoidHom).toMultiplicative)
  map_id R := by
    apply GrpCat.ext
    intro x
    change (LinearMap.rTensor V (LinearMap.id : R →ₗ[F] R)) x = x
    rw [LinearMap.rTensor_id]
    rfl
  map_comp f g := by
    apply GrpCat.ext
    intro x
    change (LinearMap.rTensor V (g.hom.toLinearMap.comp f.hom.toLinearMap)) x =
      (LinearMap.rTensor V g.hom.toLinearMap) ((LinearMap.rTensor V f.hom.toLinearMap) x)
    rw [LinearMap.rTensor_comp_apply]

/-- Principal units in a nilpotent ideal of a finite algebra are represented by an
affine algebraic group. -/
def PrincipalUnitsRepresentable : Prop :=
  ∀ {F A : Type u} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (I : Ideal A), IsNilpotent I →
    ∃ G : AffineAlgebraicGroup F,
      Nonempty ((groupPointsFunctor F).obj G.val ≅ principalUnits I)

def VectorGroupsRepresentable : Prop :=
  ∀ (F V : Type u) [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V],
    ∃ G : AffineAlgebraicGroup F,
      Nonempty ((groupPointsFunctor F).obj G.val ≅ vectorPoints (F := F) V)

/-- The subspace (I^{i+1}) inside (I^i). -/
abbrev nextPower (I : Ideal A) (i : ℕ) : Submodule F (I ^ i : Ideal A) :=
  (I ^ (i + 1) : Ideal A).restrictScalars F |>.comap ((I ^ i : Ideal A).restrictScalars F).subtype

/-- Each successive quotient is the additive group of the corresponding quotient of ideal
powers. The displayed formula evaluates the quotient map on every test algebra. -/
def PrincipalUnitsSuccessiveQuotients : Prop :=
  ∀ {F A : Type u} [Field F] [CommRing A] [Algebra F A] (I : Ideal A),
    IsNilpotent I → ∀ (i : ℕ), 0 < i →
    ∃ q : principalUnits (I ^ i) ⟶ vectorPoints (F := F) ((I ^ i : Ideal A) ⧸ nextPower I i),
      ∀ (R : TestAlgebra F),
        Function.Surjective (q.app R) ∧
        (∀ x : (principalUnits (I ^ i)).obj R, q.app R x = 1 ↔
          (x.val : (R ⊗[F] A)ˣ).val - 1 ∈ extendedPrincipalIdeal (I ^ (i + 1)) R) ∧
        ∀ (x : (principalUnits (I ^ i)).obj R) (z : R ⊗[F] (I ^ i : Ideal A)),
          ((I ^ i : Ideal A).restrictScalars F).subtype.lTensor R z =
              (x.val : (R ⊗[F] A)ˣ).val - 1 →
          q.app R x = Multiplicative.ofAdd ((nextPower I i).mkQ.lTensor R z)

/-- The residue on each scalar extension, followed by cancellation of the ground field. -/
def residueAt (r : A →ₐ[F] F) (R : TestAlgebra F) : R ⊗[F] A →ₐ[R] R :=
  (Algebra.TensorProduct.rid F R R).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id R R) r)

end PrincipalUnits

/-- After extension to the algebraic closure the unit functor splits by reduction to the
residue field and scalar inclusion. Its kernel is the nontrivial geometric radical. -/
def GeometricUnitSequence : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    [IsPurelyInseparable k K], ¬ Function.Surjective (algebraMap k K) →
    ∀ (G : AffineAlgebraicGroup k)
      (g : (groupPointsFunctor k).obj G.val ≅ extendedUnits k K),
    ∃ e : K →ₐ[k] AlgebraicClosure k,
    let L := AlgebraicClosure k
    let A := L ⊗[k] K
    let r := residue e
    let J := RingHom.ker r.toRingHom
    let H := GeometricGroup G
    let N := geometricUnipotentRadical G
    ∃ (a : (groupPointsFunctor L).obj H.val ≅ extendedUnits L A)
      (T : AffineAlgebraicGroup L) (t : (groupPointsFunctor L).obj T.val ≅ multiplicativePoints L)
      (p : H.val ⟶ T.val) (s : T.val ⟶ H.val)
      (n : (groupPointsFunctor L).obj N.group ≅ principalUnits J),
      IsSchemeKernel p N ∧ s ≫ p = 𝟙 T.val ∧ ¬ IsTrivialSubgroup N ∧
      ∀ (R : TestAlgebra L),
        (∀ x : ((groupPointsFunctor L).obj H.val).obj R,
          tensorCancellation k K L R (a.hom.app R x : (R ⊗[L] A)ˣ).val =
            (g.hom.app ((restrictTestAlgebra k L).obj R) (baseChangePoint k L G.val.X R x) :
              (((restrictTestAlgebra k L).obj R) ⊗[k] K)ˣ).val) ∧
        (∀ x : ((groupPointsFunctor L).obj H.val).obj R,
          (t.hom.app R (((groupPointsFunctor L).map p).app R x) : Rˣ).val =
            residueAt r R (a.hom.app R x : (R ⊗[L] A)ˣ).val) ∧
        (∀ x : ((groupPointsFunctor L).obj T.val).obj R,
          (a.hom.app R (((groupPointsFunctor L).map s).app R x) : (R ⊗[L] A)ˣ).val =
            (t.hom.app R x : Rˣ).val ⊗ₜ[L] (1 : A)) ∧
        (∀ x : ((groupPointsFunctor L).obj N.group).obj R,
          a.hom.app R (((groupPointsFunctor L).map N.inclusion).app R x) =
            (n.hom.app R x).val)

end
end LinearAlgebraicGroups.Specs.WeilRestrictionBoundary
