import MathGenome.Internal.Specs.D07.Ch15.GenericUnsolvability
import MathGenome.Internal.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField
import MathGenome.Internal.D07.Ch15.RadicalsImplySolvable
import MathGenome.Internal.D07.Ch15.SolvableGroups

universe u v w
noncomputable section
namespace D07.Ch15.GenericUnsolvability
open Polynomial
open Specs.D07.Ch15.GenericUnsolvability
open Specs.D07.Ch15.GenericUnsolvabilitySymmetricRationalFixedField
open Specs.D07.Ch15.RadicalDefinition

/-- Changing the scalar field by an isomorphism does not change the
scalar-fixing automorphisms of an extension. -/
def automorphismBaseChange {A : Type*} {B : Type*} (L : Type*)
    [Field A] [Field B] [Field L] [Algebra B L] (e : A ≃+* B) :
    letI := Algebra.compHom L e.toRingHom
    (L ≃ₐ[A] L) ≃* (L ≃ₐ[B] L) := by
  letI := Algebra.compHom L e.toRingHom
  let f : (L ≃ₐ[A] L) → (L ≃ₐ[B] L) := fun σ =>
    { σ.toRingEquiv with
      commutes' := fun b => by
        change σ (algebraMap B L b) = algebraMap B L b
        have h := σ.commutes (e.symm b)
        change σ (algebraMap B L (e (e.symm b))) = algebraMap B L (e (e.symm b)) at h
        simpa only [RingEquiv.apply_symm_apply] using h }
  let g : (L ≃ₐ[B] L) → (L ≃ₐ[A] L) := fun σ =>
    { σ.toRingEquiv with commutes' := fun a => σ.commutes (e a) }
  exact
    { toFun := f
      invFun := g
      left_inv := fun σ => AlgEquiv.ext fun _ => rfl
      right_inv := fun σ => AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }

/-- Splitting-field transport along an isomorphism of coefficient fields. -/
theorem splittingField_baseChange {A : Type*} {B : Type*} (L : Type*)
    [Field A] [Field B] [Field L] [Algebra B L]
    (e : A ≃+* B) (p : A[X]) [IsSplittingField B L (p.map e.toRingHom)] :
    letI := Algebra.compHom L e.toRingHom
    IsSplittingField A L p := by
  letI := Algebra.compHom L e.toRingHom
  letI : Algebra B A := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap B L b = algebraMap B L (e (e.symm b))
    rw [e.apply_symm_apply]
  have h := IsSplittingField.map (K := A) (L := L) (p.map e.toRingHom)
  have he : (p.map e.toRingHom).map (algebraMap B A) = p := by
    rw [Polynomial.map_map]
    change p.map (e.symm.toRingHom.comp e.toRingHom) = p
    have hm : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by
      ext a
      exact e.symm_apply_apply a
    rw [hm, Polynomial.map_id]
  rwa [he] at h

/-- The polynomial automorphism group can be computed in a splitting field
whose scalars have been transported from an isomorphic coefficient field. -/
def galoisGroupBaseChange {A : Type*} {B : Type*} (L : Type*)
    [Field A] [Field B] [Field L] [Algebra B L]
    (e : A ≃+* B) (p : A[X]) [IsSplittingField B L (p.map e.toRingHom)] :
    p.Gal ≃* (L ≃ₐ[B] L) := by
  letI := Algebra.compHom L e.toRingHom
  letI := splittingField_baseChange L e p
  exact (IsSplittingField.algEquiv L p).autCongr.symm.trans
    (automorphismBaseChange L e)

theorem empty_tuple_case : EmptyTupleCase.{u, v} := by
  intro K M _ _ _ s
  refine ⟨by simp, by simp [tuplePolynomial], ?_⟩
  constructor <;> simp [tuplePolynomial]

theorem generic_galois_group : GenericGaloisGroup.{u, v} := by
  intro K M _ _ _ _ n s hs
  by_cases hn : n = 0
  · subst n
    have hp : tuplePolynomial K 0 M s = 1 := (empty_tuple_case K M s).2.1
    rw [hp]
    exact ⟨MulEquiv.ofUnique⟩
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨e, _, he⟩ :=
      GenericUnsolvabilitySymmetricRationalFixedField.coefficient_polynomial_transport K M n s hs
    letI : IsSplittingField (coefficients K n) (Rational K n) (genericPolynomial K n) :=
      (GenericUnsolvabilitySymmetricRationalFixedField.separable_splitting_field K n hn').2.2.2
    haveI : IsSplittingField (coefficients K n) (Rational K n)
        ((tuplePolynomial K n M s).map e.toRingHom) := by rw [he]; infer_instance
    obtain ⟨g, _⟩ :=
      GenericUnsolvabilitySymmetricRationalFixedField.automorphism_group K n hn'
    exact ⟨(galoisGroupBaseChange (Rational K n) e.toRingEquiv
      (tuplePolynomial K n M s)).trans g.symm⟩

theorem generic_not_solvable_by_radicals : GenericNotSolvableByRadicals.{u, v, w} := by
  intro K M _ _ _ _ n s hs hn Ω _ _ _ _ hroots
  letI hsolv := RadicalsImplySolvable.all_radical_roots_group
    (IntermediateField.adjoin K (Set.range s)) Ω (tuplePolynomial K n M s)
    hroots
  obtain ⟨e⟩ := generic_galois_group K M n s hs
  have : Group.IsSolvable (Equiv.Perm (Fin n)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact SolvableGroups.symmetric_not_solvable n hn this

end D07.Ch15.GenericUnsolvability
