import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

open AlgebraicGeometry CategoryTheory
open scoped MonoidAlgebra

universe u v
noncomputable section

namespace LinearAlgebraicGroups.Specs.Unipotent

/-- A group of unipotent linear transformations over an algebraically closed field
admits a basis adapted to a common full flag with trivial successive actions. -/
def GeometricPointFlag : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {Γ : Type v} [Group Γ]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : _root_.Representation K Γ V),
    (∀ g, IsNilpotent (ρ g - 1)) →
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ g, IsUpperUnitriangular (LinearMap.toMatrix b b (ρ g))

/-- For a smooth affine algebraic group, unipotence can be tested in any faithful
finite-dimensional rational representation on its algebraic-closure points. -/
def GeometricPointCriterion : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (_ : Smooth G.val.X.hom)
    (n : ℕ) (L : AffineAlgebraicGroup k)
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k (Index.{u} n))
    (f : G.val ⟶ L.val) (_ : IsClosedImmersion f.hom.hom.left),
    let K := CommAlgCat.of k (AlgebraicClosure k)
    IsUnipotent G ↔
      ∀ g : ((groupPointsFunctor k).obj G.val).obj K,
        IsNilpotent ((l.hom.app K (((groupPointsFunctor k).map f).app K g)).val - 1)

/-- The subgroup of units killed by the p-th power map. -/
def primeRoots (p : ℕ) (R : Type u) [CommRing R] : Subgroup Rˣ where
  carrier := {a | a ^ p = 1}
  one_mem' := one_pow p
  mul_mem' := fun {a b} ha hb ↦ by show (a * b) ^ p = 1; rw [mul_pow, ha, hb, mul_one]
  inv_mem' := fun {a} ha ↦ by show a⁻¹ ^ p = 1; rw [inv_pow, ha, inv_one]

/-- The p-th roots of unity, on every commutative test algebra. -/
def primeRootsPoints (k : Type u) [Field k] (p : ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (primeRoots p R)
  map a := GrpCat.ofHom <| ((Units.map a.hom.toMonoidHom).comp (primeRoots p _).subtype).codRestrict _
    fun x ↦ by
      change (Units.map a.hom.toMonoidHom x.val) ^ p = 1
      rw [← map_pow, show x.val ^ p = 1 from x.property, map_one]
  map_id _ := by apply GrpCat.ext; intro x; apply Subtype.ext; apply Units.ext; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; apply Subtype.ext; apply Units.ext; rfl

/-- The spectrum of the group algebra of the cyclic character group of order p. -/
abbrev muPrime (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] : AffineAlgebraicGroup k :=
  StandardGroups.spectrum k (k[Multiplicative (ZMod p)])

/-- In characteristic p the group scheme of p-th roots of unity has trivial
geometric points and is nonunipotent. -/
def GeometricPointCounterexample : Prop :=
  ∀ {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    let G := muPrime k p
    Nonempty ((groupPointsFunctor k).obj G.val ≅ primeRootsPoints k p) ∧
    Subsingleton (((groupPointsFunctor k).obj G.val).obj (CommAlgCat.of k (AlgebraicClosure k))) ∧
    ¬ IsUnipotent G ∧ ¬ Smooth G.val.X.hom

end LinearAlgebraicGroups.Specs.Unipotent
