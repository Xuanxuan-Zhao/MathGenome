import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Module
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.NonpositiveAlgebras

open CategoryTheory

universe u v

namespace DerivedFormalization

abbrev CommDGAlgebra := Affine.CommDGAlgebra
abbrev NonpositiveCDGA := Affine.NonpositiveCDGA

variable {k : Type u} [Field k] [CharZero k]

namespace CommDGAlgebra

abbrev Hom (A B : CommDGAlgebra.{u,v} k) := Affine.CommDGAlgebra.Hom A B
abbrev IsNonpositive (A : CommDGAlgebra.{u,v} k) := Affine.CommDGAlgebra.IsNonpositive A

/-- Modules over the underlying DG algebra in the one-object convention. -/
abbrev Module (A : CommDGAlgebra.{u,v} k) := RightDGAlgebraModule A.toDGAlgebra

end CommDGAlgebra

namespace NonpositiveCDGA

abbrev inclusion := Affine.NonpositiveCDGA.inclusion
abbrev forgetComplex := Affine.NonpositiveCDGA.forgetComplex
abbrev Hom (A B : NonpositiveCDGA.{u,v} k) := A ⟶ B
abbrev AlgebraUnder (A : NonpositiveCDGA.{u,v} k) := Affine.NonpositiveCDGA.AlgebraUnder A
abbrev AlgebraUnderOver {A B : NonpositiveCDGA.{u,v} k} (b : A ⟶ B) :=
  Affine.NonpositiveCDGA.AlgebraUnderOver b
abbrev OverBase {P Q B : NonpositiveCDGA.{u,v} k} (p : P ⟶ B) (q : Q ⟶ B) (f : P ⟶ Q) :=
  Affine.NonpositiveCDGA.OverBase p q f
abbrev IsQuasiIso {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) :=
  Affine.NonpositiveCDGA.IsQuasiIso f
abbrev DegreewiseSurjective {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) :=
  Affine.NonpositiveCDGA.DegreewiseSurjective f
abbrev quasiIsomorphisms := Affine.NonpositiveCDGA.quasiIsomorphisms
abbrev boundaryIdeal (A : NonpositiveCDGA.{u,v} k) := Affine.NonpositiveCDGA.boundaryIdeal A
abbrev H0 (A : NonpositiveCDGA.{u,v} k) := Affine.NonpositiveCDGA.H0 A
abbrev h0Functor := Affine.NonpositiveCDGA.h0Functor
noncomputable abbrev ordinary (S : CommAlgCat.{v} k) := Affine.NonpositiveCDGA.ordinary S
noncomputable abbrev ordinaryFunctor := Affine.NonpositiveCDGA.ordinaryFunctor

open Specs.DerivedFormalization.Affine.NonpositiveAlgebras

theorem overBase_iff : OverBaseCondition.{u,v} := by
  intro k _ _ A B b P Q f
  constructor
  · rintro ⟨g, rfl⟩
    exact congrArg Under.Hom.right (Over.w g)
  · intro h
    have h' : f ≫ Q.hom = P.hom := Under.UnderMorphism.ext h
    exact ⟨Over.homMk f h', rfl⟩

theorem isQuasiIso_iff : QuasiIsoCriterion.{u,v} := by
  intro k _ _ A B f
  change QuasiIso f.chainMap ↔ _
  rw [quasiIso_iff]
  exact forall_congr' fun i => quasiIsoAt_iff_isIso_homologyMap f.chainMap i

theorem h0Map_on_classes : H0MapOnClasses.{u,v} := by
  intro k _ _ A B f x
  rfl

open Specs.DerivedFormalization.DG.Basic (cyclesZero boundariesZero zeroShort h0Hom)

private noncomputable def h0QuotientIso (A : NonpositiveCDGA.{u,v} k) :
    ModuleCat.of k A.H0 ≅ ModuleCat.of k (h0Hom A.complex) := by
  let p : cyclesZero A.complex →ₗ[k] A.H0 :=
    A.h0Class.toLinearMap.comp (LinearMap.ker (zeroShort A.complex).g.hom).subtype
  have hp : LinearMap.ker p = boundariesZero A.complex := by
    ext x
    change Ideal.Quotient.mk A.boundaryIdeal x.val = 0 ↔
      ∃ y, (zeroShort A.complex).moduleCatToCycles y = x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (∃ y : A.complex.X (-1), A.complex.d (-1) 0 y = x.val) ↔ _
    exact ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩, fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩⟩
  have hs : Function.Surjective p := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective k A.boundaryIdeal x
    exact ⟨⟨y, A.d_zero_apply y⟩, rfl⟩
  exact ((LinearMap.quotKerEquivOfSurjective p hs).symm.trans
    (Submodule.quotEquivOfEq _ _ hp)).toModuleIso

/-- The quotient algebra has the same underlying k-module as cohomology. -/
noncomputable def h0HomologyIso (A : NonpositiveCDGA.{u,v} k) :
    ModuleCat.of k A.H0 ≅ A.complex.homology 0 :=
  h0QuotientIso A ≪≫ A.complex.h0HomologyIso

theorem h0Homology : H0Homology.{u,v} := fun A => ⟨h0HomologyIso A⟩

theorem ordinary_components : OrdinaryComponents.{u,v} := by
  dsimp only [OrdinaryComponents]
  intro k _ _ S
  refine ⟨fun _ _ => rfl, rfl, ?_, fun _ _ => rfl⟩
  intro i hi
  exact ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k S) i hi)

private noncomputable def ordinaryMapAtZero {S T : CommAlgCat.{v} k}
    (f : ordinary S ⟶ ordinary T) : S ⟶ T :=
  CommAlgCat.ofHom
    { toFun := fun x => f.chainMap.f 0 x
      map_one' := f.map_one
      map_mul' := f.map_mul 0 0 0 rfl
      map_zero' := map_zero (f.chainMap.f 0).hom
      map_add' := map_add (f.chainMap.f 0).hom
      commutes' c := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        change (f.chainMap.f 0).hom (c • (ordinary S).one) = c • (ordinary T).one
        rw [map_smul]
        exact congrArg (fun x : (ordinary T).complex.X 0 => c • x) f.map_one }

/-- The degree-zero embedding induces bijections on morphisms. -/
noncomputable def ordinaryFullyFaithful (k : Type u) [Field k] [CharZero k] :
    (ordinaryFunctor.{u,v} k).FullyFaithful where
  preimage := ordinaryMapAtZero
  map_preimage {S T} f := by
    apply Affine.CommDGAlgebra.Hom.ext_chainMap
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases h : i = 0
    · subst i
      rfl
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 (ModuleCat.of k S) i h).eq_of_src _ _
  preimage_map {S T} f := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

theorem ordinary_embedding : OrdinaryEmbedding.{u,v} :=
  fun k => ⟨(ordinaryFullyFaithful k).full, (ordinaryFullyFaithful k).faithful⟩

end NonpositiveCDGA

abbrev DerivedAffine := Affine.DerivedAffine
noncomputable abbrev derivedSpec := Affine.derivedSpec

theorem derivedSpec_isLocalization :
    Specs.DerivedFormalization.Affine.NonpositiveAlgebras.DerivedSpecLocalization.{u,v} :=
  fun _ => Localization.isLocalization_op

end DerivedFormalization
