import Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.CategoryTheory.Whiskering

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite Coalgebra HopfAlgebra WithConv
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

/-- Spectrum is an antiequivalence on all commutative Hopf algebras. -/
theorem affineHopfSpecEquivalence : Specs.AffineHopfSpecEquivalence.{u} := by
  intro k _
  let ff : (affineHopfSpec k).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := affineGroupInclusion k)
      (hopfSpec.fullyFaithful (R := CommRingCat.of k))
  exact ⟨ff.faithful, ff.full, ⟨fun G ↦ by
    obtain ⟨A, ⟨i⟩⟩ := essImage_hopfSpec.mpr G.property
    exact ⟨A, ⟨InducedCategory.isoMk i⟩⟩⟩⟩

/-- Spectrum restricts to an antiequivalence between the two finite-type categories. -/
theorem finiteTypeHopfSpecEquivalence : Specs.FiniteTypeHopfSpecEquivalence.{u} := by
  intro k _
  let ff : (finiteTypeHopfSpec k).FullyFaithful :=
    { preimage := fun {X Y} f ↦ (InducedCategory.homMk (X := Y.unop) (Y := X.unop)
        ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage f.hom).unop).op
      map_preimage := fun f ↦ InducedCategory.hom_ext
        ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f.hom)
      preimage_map := fun f ↦ by
        apply Quiver.Hom.unop_inj
        apply InducedCategory.hom_ext
        exact congrArg Quiver.Hom.unop
          ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage_map f.unop.hom.op) }
  refine ⟨ff.faithful, ff.full, ⟨?_⟩⟩
  intro G
  obtain ⟨A, ⟨i⟩⟩ := essImage_hopfSpec.mpr G.property.1
  let e := (Grp.forget _).mapIso i
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : LocallyOfFiniteType ((Grp.forget (SchemeOver k)).obj G.val).hom := G.property.2.1
  have h := locallyOfFiniteType_comp e.hom.left ((Grp.forget (SchemeOver k)).obj G.val).hom
  rw [Over.w e.hom] at h
  have hA : Algebra.FiniteType k A.unop :=
    (hopfSpec_locallyOfFiniteType_iff k A.unop).mp h
  exact ⟨op ⟨A.unop, hA⟩, ⟨InducedCategory.isoMk i⟩⟩

/-- The affine antiequivalence, with the Hopf spectrum as forward functor. -/
def affineHopfEquivalence (k : Type u) [Field k] :
    (HopfAlgebraCategory k)ᵒᵖ ≌ AffineGroupCategory k :=
  letI := affineHopfSpecEquivalence k
  (affineHopfSpec k).asEquivalence

/-- The finite-type antiequivalence, with the same Hopf spectrum as forward functor. -/
def finiteTypeHopfEquivalence (k : Type u) [Field k] :
    (FiniteTypeHopfAlgebraCategory k)ᵒᵖ ≌ AffineAlgebraicGroupCategory k :=
  letI := finiteTypeHopfSpecEquivalence k
  (finiteTypeHopfSpec k).asEquivalence

/-- The coordinates of an affine group scheme as a commutative Hopf algebra. -/
def coordinateHopf (G : AffineGroupCategory k) : HopfAlgebraCategory k :=
  ((affineHopfEquivalence k).inverse.obj G).unop

/-- Spectrum of the coordinate Hopf algebra recovers the affine group, with its group law. -/
def coordinateHopfSpecIso (G : AffineGroupCategory k) :
    (affineHopfSpec k).obj (op (coordinateHopf G)) ≅ G :=
  (affineHopfEquivalence k).counitIso.app G

/-- The underlying algebra and its pullbacks are the global-sections functor. -/
theorem coordinateHopfComparison : Specs.CoordinateHopfComparison.{u} := by
  intro k _ _
  let H := (affineHopfSpec k).inv ⋙ (forgetHopfAlgebra k).op
  let U := schemeOfAffineGroup k
  let : (algSpec (CommRingCat.of k)).Faithful := algSpec.instFaithful
  let : (algSpec (CommRingCat.of k)).Full := algSpec.instFull
  let a := algΓAlgSpecAdjunction (CommRingCat.of k)
  let c : H ⋙ algSpec (CommRingCat.of k) ≅ U :=
    Functor.isoWhiskerRight (affineHopfSpec k).asEquivalence.counitIso U
  let e : U ⋙ algΓ (CommRingCat.of k) ≅ H :=
    Functor.isoWhiskerRight c.symm (algΓ (CommRingCat.of k)) ≪≫
      Functor.isoWhiskerLeft H (asIso a.counit)
  refine ⟨e.symm, ?_⟩
  intro G
  change a.unit.app (U.obj G) ≫ (algSpec _).map (e.hom.app G) = c.inv.app G
  have he : e.hom.app G = (a.homEquiv _ _).symm (c.inv.app G) := by
    rw [a.homEquiv_counit]
    rfl
  rw [he]
  exact (a.homEquiv (U.obj G) (H.obj G)).apply_symm_apply (c.inv.app G)

/-- Multiplication, identity and inversion on the spectrum are the spectra of the three Hopf
operations, with the canonical tensor product comparison for multiplication. -/
theorem hopfSpecOperations : Specs.HopfSpecOperations.{u} := by
  intro k _ A
  exact ⟨rfl, rfl, rfl⟩

/-- A Hopf algebra map induces the opposite spectrum map and intertwines antipodes. -/
theorem hopfSpecMorphism : Specs.HopfSpecMorphism.{u} := by
  intro k _ A B a
  refine ⟨rfl, ?_⟩
  let X := op (CommAlgCat.of k A)
  let Y := op (CommAlgCat.of k B)
  let : GrpObj X := CommAlgCat.grpObjOpOf
  let : GrpObj Y := CommAlgCat.grpObjOpOf
  let f : Y ⟶ X := (CommAlgCat.ofHom a.hom.toAlgHom).op
  let : IsMonHom f := inferInstanceAs (IsMonHom (CommAlgCat.ofHom a.hom.toAlgHom).op)
  exact (congrArg (fun g : Y ⟶ X ↦ g.unop.hom) (GrpObj.inv_hom f)).symm

/-- A Hopf spectrum is commutative exactly when the comultiplication is cocommutative. -/
theorem hopfSpecCommutativity : Specs.HopfSpecCommutativity.{u} := by
  intro k _ A
  refine ⟨?_, fun h ↦ ?_⟩
  · intro h
    let D := op (CommAlgCat.of k A)
    let : GrpObj D := CommAlgCat.grpObjOpOf
    let F := testSpec k
    let : F.Braided := braidedAlgSpec (R := CommRingCat.of k)
    let m := Functor.LaxMonoidal.μ F D D
    have hh : (β_ (F.obj D) (F.obj D)).hom ≫ (m ≫ F.map μ[D]) =
        m ≫ F.map μ[D] := h.mul_comm
    have hl : m ≫ F.map ((β_ D D).hom ≫ μ[D]) = m ≫ F.map μ[D] := by
      rw [F.map_comp, ← Category.assoc, Functor.LaxBraided.braided, Category.assoc]
      exact hh
    have hs : (β_ D D).hom ≫ μ[D] = μ[D] :=
      (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective ((cancel_epi m).mp hl)
    constructor
    ext x
    exact congrArg (fun f : D ⊗ D ⟶ D ↦ f.unop.hom x) hs
  · let : IsCocomm k A := h
    exact isCommMonObj_spec_asOver_spec (R := CommRingCat.of k) (A := CommRingCat.of A)

private theorem isCommMonObj_of_groupIso {G H : GroupScheme k} (e : G ≅ H)
    (h : IsCommMonObj G.X) : IsCommMonObj H.X := by
  rw [isCommMonObj_iff_isMulCommutative] at h ⊢
  intro T
  let f := e.hom.hom.hom
  let g := e.inv.hom.hom
  have hgf : g ≫ f = 𝟙 H.X := (Grp.forget _).congr_map e.inv_hom_id
  let := h T
  constructor
  constructor
  intro p q
  simpa only [MonObj.mul_comp, Category.assoc, hgf, Category.comp_id] using
    congrArg (· ≫ f) (mul_comm' (p ≫ g) (q ≫ g))

/-- Commutativity is detected by the comultiplication on the coordinate Hopf algebra. -/
theorem coordinateHopfCommutativity : Specs.CoordinateHopfCommutativity.{u} := by
  intro k _ _ G
  let e := (affineGroupInclusion k).mapIso ((affineHopfSpec k).asEquivalence.counitIso.app G)
  exact ⟨fun h ↦ (hopfSpecCommutativity k _).mp (isCommMonObj_of_groupIso e.symm h),
    fun h ↦ isCommMonObj_of_groupIso e ((hopfSpecCommutativity k _).mpr h)⟩

/-- The isomorphism from convolution algebra maps to group-valued points of the spectrum. -/
def hopfSpecPointIso (A : HopfAlgebraCategory k) : convolutionPoints A ≅
    (groupPointsFunctor k).obj ((hopfSpec (CommRingCat.of k)).obj (op A)) := by
  let e (R : TestAlgebra k) : (convolutionPoints A).obj R ≅
      ((groupPointsFunctor k).obj ((hopfSpec (CommRingCat.of k)).obj (op A))).obj R :=
    (Spec.mapMulEquiv (R := k) (S := A) (T := R)).toGrpIso
  have he (R : TestAlgebra k) (f : WithConv (A →ₐ[k] R)) :
      (e R).hom f = Spec.mapMulEquiv (R := k) (S := A) (T := R) f := rfl
  refine NatIso.ofComponents e ?_
  intro R S a
  apply GrpCat.ext
  intro f
  change (e S).hom (toConv (a.hom.comp f.ofConv)) = mapPoints a ((e R).hom f)
  rw [he, he]
  apply Over.OverMorphism.ext
  exact Spec.map_comp (CommRingCat.ofHom f.ofConv.toRingHom)
    (CommRingCat.ofHom a.hom.toRingHom)

/-- The spectrum represents convolution, compatibly with morphisms of Hopf algebras. -/
theorem hopfSpecPoints : Specs.HopfSpecPoints.{u} := by
  intro k _
  refine ⟨hopfSpecPointIso, fun _ _ _ ↦ rfl, ?_⟩
  intro A B a R f
  apply Over.OverMorphism.ext
  exact Spec.map_comp (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)
    (CommRingCat.ofHom f.ofConv.toRingHom)

/-- Any affine group scheme represents convolution on its coordinate Hopf algebra. -/
theorem coordinateHopfPoints : Specs.CoordinateHopfPoints.{u} := by
  intro k _ _ G
  obtain ⟨e, he, _⟩ := hopfSpecPoints k
  let A := ((affineHopfSpec k).inv.obj G).unop
  let c := (affineGroupInclusion k).mapIso ((affineHopfSpec k).asEquivalence.counitIso.app G)
  refine ⟨e A ≪≫ (groupPointsFunctor k).mapIso c, ?_⟩
  intro R f
  change (((e A).hom.app R f : Points _ R) ≫ c.hom.hom.hom).left = _
  change ((e A).hom.app R f : Points _ R).left ≫ c.hom.hom.hom.left = _
  rw [he]
  rfl

end
end LinearAlgebraicGroups
