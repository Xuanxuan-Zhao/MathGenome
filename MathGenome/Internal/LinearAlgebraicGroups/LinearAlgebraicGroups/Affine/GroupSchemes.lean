import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.Algebra.Group.Ext
import Mathlib.AlgebraicGeometry.Morphisms.Affine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

/-- Group objects in schemes over the field. -/
abbrev GroupScheme : Specs.GroupSchemeType.{u} := Specs.GroupScheme

/-- Group schemes whose underlying scheme is affine. -/
abbrev AffineGroupScheme : Specs.AffineGroupSchemeType.{u} := Specs.AffineGroupScheme

/-- Affine group schemes with a finite-type structure morphism. -/
abbrev AffineAlgebraicGroup : Specs.AffineAlgebraicGroupType.{u} := Specs.AffineAlgebraicGroup

variable {k : Type u} [Field k]

private theorem hom_ext_of_points {X Y : SchemeOver k} (hX : IsAffine X.left)
    {f g : X ⟶ Y} (h : ∀ (R : TestAlgebra k) (p : Points X R), p ≫ f = p ≫ g) :
    f = g := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  have he := h A.unop e.hom
  simpa using congrArg (e.inv ≫ ·) he

private def groupLawFunctor {X : SchemeOver k} (L : NaturalGroupLaw X) :
    ((TestAlgebra k)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} where
  obj R := letI := L.group R.unop.unop; GrpCat.of (Points X R.unop.unop)
  map {R S} a :=
    letI := L.group R.unop.unop
    letI := L.group S.unop.unop
    GrpCat.ofHom
      { toFun := mapPoints a.unop.unop
        map_one' := L.map_one a.unop.unop
        map_mul' := L.map_mul a.unop.unop }
  map_id R := by
    apply GrpCat.ext
    intro p
    change (testSpec k).map (𝟙 (op R.unop.unop)) ≫ p = p
    simp
  map_comp a b := by
    apply GrpCat.ext
    intro p
    change (testSpec k).map (b.unop.unop.op ≫ a.unop.unop.op) ≫ p =
      (testSpec k).map b.unop.unop.op ≫ (testSpec k).map a.unop.unop.op ≫ p
    rw [Functor.map_comp, Category.assoc]

private def lawRepresentation {X : SchemeOver k} (L : NaturalGroupLaw X)
    {A : (TestAlgebra k)ᵒᵖ} (e : (testSpec k).obj A ≅ X) :
    (groupLawFunctor L ⋙ forget _).RepresentableBy A where
  homEquiv {B} := (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv.trans
    { toFun := (· ≫ e.hom)
      invFun := (· ≫ e.inv)
      left_inv := by intro p; simp
      right_inv := by
        intro p
        let q : Points X B.unop := p
        change (q ≫ e.inv) ≫ e.hom = q
        simp }
  homEquiv_comp f p := by
    change (testSpec k).map (f ≫ p) ≫ e.hom =
      (testSpec k).map f ≫ (testSpec k).map p ≫ e.hom
    rw [Functor.map_comp, Category.assoc]

private theorem inducedGroupLaw_injective (X : SchemeOver k) (hX : IsAffine X.left) :
    Function.Injective (inducedGroupLaw X) := by
  intro a b h
  apply GrpObj.ext
  apply MonObj.ext
  apply hom_ext_of_points (X := X ⊗ X) (by
    let : IsAffine X.left := hX
    change IsAffine (pullback X.hom X.hom)
    infer_instance)
  intro R p
  have hp := congrArg (fun L : NaturalGroupLaw X ↦
    (L.group R).mul (p ≫ fst X X) (p ≫ snd X X)) h
  change lift (p ≫ fst X X) (p ≫ snd X X) ≫ a.toMonObj.mul =
    lift (p ≫ fst X X) (p ≫ snd X X) ≫ b.toMonObj.mul at hp
  simpa only [lift_comp_fst_snd] using hp

private theorem naturalGroupLaw_ext {X : SchemeOver k} {L M : NaturalGroupLaw X}
    (h : L.group = M.group) : L = M := by
  cases L
  cases M
  cases h
  rfl

private theorem inducedGroupLaw_surjective (X : SchemeOver k) (hX : IsAffine X.left) :
    Function.Surjective (inducedGroupLaw X) := by
  intro L
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let ρ := lawRepresentation L e
  let : GrpObj A := GrpObj.ofRepresentableBy A (groupLawFunctor L) ρ
  let : (testSpec k).Braided := AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)
  let : GrpObj ((testSpec k).obj A) := (testSpec k).grpObjObj
  let s : GrpObj X := GrpObj.ofIso e
  refine ⟨s, ?_⟩
  apply naturalGroupLaw_ext
  funext R
  apply Group.ext
  funext p q
  let B : (TestAlgebra k)ᵒᵖ := op R
  let i := (yonedaGrpObjIsoOfRepresentableBy A (groupLawFunctor L) ρ).hom.app (op B)
  let p' : B ⟶ A := ρ.homEquiv.symm p
  let q' : B ⟶ A := ρ.homEquiv.symm q
  have hi (t : B ⟶ A) : i t = (testSpec k).map t ≫ e.hom := rfl
  have hp : (testSpec k).map p' ≫ e.hom = p := ρ.homEquiv.apply_symm_apply p
  have hq : (testSpec k).map q' ≫ e.hom = q := ρ.homEquiv.apply_symm_apply q
  have hm : (testSpec k).map (p' * q') ≫ e.hom = (L.group R).mul p q := by
    have hmul : i (p' * q') = (L.group R).mul (i p') (i q') := i.hom.map_mul p' q'
    exact (hi _).symm.trans (hmul.trans (congrArg₂ (L.group R).mul
      ((hi p').trans hp) ((hi q').trans hq)))
  have : IsMonHom e.hom := isMonHom_ofIso e
  change p * q = (L.group R).mul p q
  calc
    p * q = ((testSpec k).map p' ≫ e.hom) * ((testSpec k).map q' ≫ e.hom) := by
      rw [hp, hq]
    _ = ((testSpec k).map p' * (testSpec k).map q') ≫ e.hom :=
      (MonObj.mul_comp _ _ e.hom).symm
    _ = (testSpec k).map (p' * q') ≫ e.hom := congrArg (· ≫ e.hom)
      ((testSpec k).map_mul p' q').symm
    _ = (L.group R).mul p q := hm

/-- Affine scheme group structures are in bijection with natural group laws on points. -/
theorem groupLawComparison : Specs.GroupLawComparison.{u} := by
  intro k _ X hX
  exact ⟨inducedGroupLaw_injective X hX, inducedGroupLaw_surjective X hX⟩

/-- The point law and its reconstruction, on an arbitrary affine scheme. -/
def groupLawEquiv (X : SchemeOver k) (hX : IsAffine X.left) :
    GrpObj X ≃ NaturalGroupLaw X :=
  Equiv.ofBijective _ (groupLawComparison k X hX)

/-- The comparison specialized to the underlying scheme of any affine algebraic group. -/
def AffineAlgebraicGroup.groupLawEquiv (G : AffineAlgebraicGroup k) :
    GrpObj G.1.X ≃ NaturalGroupLaw G.1.X :=
  LinearAlgebraicGroups.groupLawEquiv G.1.X G.2.1

private theorem pointGroupHom_monoidHom (G H : GroupScheme k) (hG : IsAffine G.X.left)
    (α : (groupPointsFunctor k).obj G ⟶ (groupPointsFunctor k).obj H) :
    ∃ f : G.X ⟶ H.X, ∀ (R : TestAlgebra k) (p : Points G.X R), α.app R p = p ≫ f := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hG
  refine ⟨e.inv ≫ α.app A.unop e.hom, ?_⟩
  intro R p
  let a : op R ⟶ A := (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (p ≫ e.inv)
  have ha : (testSpec k).map a ≫ e.hom = p := by simp [a]
  have hn := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (α.naturality a.unop)) e.hom
  change α.app R ((testSpec k).map a ≫ e.hom) = (testSpec k).map a ≫ α.app A.unop e.hom at hn
  rw [ha] at hn
  rw [hn]
  have hae : (testSpec k).map a = p ≫ e.inv := by simp [a]
  rw [hae]
  exact Category.assoc ..

/-- Natural transformations of group-valued points are exactly group scheme homomorphisms
when the source is affine. -/
theorem groupHomComparison : Specs.GroupHomComparison.{u} := by
  intro k _ G H hG
  constructor
  · intro f g he
    apply Grp.hom_ext
    apply hom_ext_of_points hG
    intro R p
    exact DFunLike.congr_fun (congrArg (fun τ ↦ (τ.app R).hom) he) p
  · intro α
    obtain ⟨f, hf⟩ := pointGroupHom_monoidHom G H hG α
    have : IsMonHom f := by
      constructor
      · apply hom_ext_of_points (X := 𝟙_ (SchemeOver k)) (by
          change IsAffine (Spec (CommRingCat.of k))
          infer_instance)
        intro R p
        rw [show p = toUnit ((testSpec k).obj (op R)) from toUnit_unique _ _]
        change (1 : Points G.X R) ≫ f = (1 : Points H.X R)
        rw [← hf R]
        exact (α.app R).hom.map_one
      · apply hom_ext_of_points (X := G.X ⊗ G.X) (by
          let : IsAffine G.X.left := hG
          change IsAffine (pullback G.X.hom G.X.hom)
          infer_instance)
        intro R p
        let x := p ≫ fst G.X G.X
        let y := p ≫ snd G.X G.X
        calc
          p ≫ μ[G.X] ≫ f = (x * y) ≫ f := by simp [x, y, Hom.mul_def]
          _ = (x ≫ f) * (y ≫ f) := by
            rw [← hf R (x * y), ← hf R x, ← hf R y]
            exact (α.app R).hom.map_mul x y
          _ = p ≫ (f ⊗ₘ f) ≫ μ[H.X] := by
            have hl : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
              apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
            simp only [Hom.mul_def, hl, Category.assoc]
    refine ⟨Grp.homMk f, ?_⟩
    ext R p
    exact (hf R p).symm

/-- The bijection on homomorphisms in its equivalence form. -/
def groupHomEquiv (G H : GroupScheme k) (hG : IsAffine G.X.left) :
    (G ⟶ H) ≃ ((groupPointsFunctor k).obj G ⟶ (groupPointsFunctor k).obj H) :=
  Equiv.ofBijective _ (groupHomComparison k G H hG)

/-- The comparison on homomorphisms between affine algebraic groups. -/
def AffineAlgebraicGroup.groupHomEquiv (G H : AffineAlgebraicGroup k) :
    (G.1 ⟶ H.1) ≃ ((groupPointsFunctor k).obj G.1 ⟶ (groupPointsFunctor k).obj H.1) :=
  LinearAlgebraicGroups.groupHomEquiv G.1 H.1 G.2.1

/-- Points of a scheme fibre product are pairs of points with equal image. -/
theorem pullbackPoints : Specs.PullbackPoints.{u} := by
  intro k _ X Y Z f g R
  constructor
  · intro p q h
    exact pullback.hom_ext (congrArg (fun a : CompatiblePoints f g R ↦ a.1.1) h)
      (congrArg (fun a : CompatiblePoints f g R ↦ a.1.2) h)
  · intro p
    refine ⟨pullback.lift p.1.1 p.1.2 p.2, Subtype.ext ?_⟩
    exact Prod.ext (pullback.lift_fst ..) (pullback.lift_snd ..)

/-- The fibre product formula is natural in the test algebra. -/
theorem pullbackPointsNaturality : Specs.PullbackPointsNaturality.{u} := by
  intro k _ X Y Z f g R S a p
  exact Subtype.ext (Prod.ext (Category.assoc ..) (Category.assoc ..))

/-- The fibre product formula as an equivalence of point sets. -/
def pullbackPointsEquiv {X Y Z : SchemeOver k} (f : X ⟶ Z) (g : Y ⟶ Z) (R : TestAlgebra k) :
    Points (pullback f g) R ≃ CompatiblePoints f g R :=
  Equiv.ofBijective _ (pullbackPoints k f g R)

/-- The point formula for the pullback of group schemes uses its group scheme projections. -/
theorem groupPullbackPoints : Specs.GroupPullbackPoints.{u} := by
  intro k _ G H L f g R
  let F := Grp.forget (SchemeOver k)
  let e := PreservesPullback.iso F f g
  have hp : groupPullbackPointPair f g R =
      pullbackPointPair f.hom.hom g.hom.hom R ∘ e.homToEquiv := by
    funext p
    let p' : Points (F.obj (pullback f g)) R := p
    apply Subtype.ext
    apply Prod.ext
    · change p' ≫ F.map (pullback.fst f g) = (p' ≫ e.hom) ≫ pullback.fst (F.map f) (F.map g)
      rw [Category.assoc, PreservesPullback.iso_hom_fst F f g]
    · change p' ≫ F.map (pullback.snd f g) = (p' ≫ e.hom) ≫ pullback.snd (F.map f) (F.map g)
      rw [Category.assoc, PreservesPullback.iso_hom_snd F f g]
  rw [hp]
  exact (pullbackPoints k f.hom.hom g.hom.hom R).comp e.homToEquiv.bijective

/-- The group scheme pullback formula is natural in the test algebra. -/
theorem groupPullbackPointsNaturality : Specs.GroupPullbackPointsNaturality.{u} := by
  intro k _ G H L f g R S a p
  exact Subtype.ext (Prod.ext (Category.assoc ..) (Category.assoc ..))

/-- Multiplication in the fibre product is coordinatewise on points. -/
theorem groupPullbackPointsMultiplication : Specs.GroupPullbackPointsMultiplication.{u} := by
  intro k _ G H L f g R p q
  exact Prod.ext (MonObj.mul_comp p q (pullback.fst f g).hom.hom)
    (MonObj.mul_comp p q (pullback.snd f g).hom.hom)

/-- The fibre product of group schemes on points, as an equivalence of sets. -/
def groupPullbackPointsEquiv {G H L : GroupScheme k} (f : G ⟶ H) (g : L ⟶ H) (R : TestAlgebra k) :
    Points (pullback f g).X R ≃ CompatiblePoints f.hom.hom g.hom.hom R :=
  Equiv.ofBijective _ (groupPullbackPoints k f g R)

/-- Scalar extension does not change points when the test algebra is over the extension. -/
theorem baseChangePoints : Specs.BaseChangePoints.{u} := by
  intro k K _ _ _ X R
  constructor
  · intro p q h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun a : Points X ((restrictTestAlgebra k K).obj R) ↦ a.left) h
    · exact (Over.w p).trans (Over.w q).symm
  · intro p
    let T := (testSpec K).obj (op R)
    have hp : p.left ≫ X.hom = T.hom ≫ fieldSpecMap k K := by
      rw [Over.w p]
      exact restrictTestAlgebra_spec_hom k K R
    refine ⟨Over.homMk (pullback.lift p.left T.hom hp) (pullback.lift_snd ..), ?_⟩
    apply Over.OverMorphism.ext
    exact pullback.lift_fst ..

/-- The scalar extension formula is natural in the algebra over the extension field. -/
theorem baseChangePointsNaturality : Specs.BaseChangePointsNaturality.{u} := by
  intro k K _ _ _ X R S a p
  apply Over.OverMorphism.ext
  change ((testSpec K).map a.op).left ≫ p.left ≫ pullback.fst X.hom (fieldSpecMap k K) =
    ((testSpec k).map ((restrictTestAlgebra k K).map a).op).left ≫
      p.left ≫ pullback.fst X.hom (fieldSpecMap k K)
  rfl

/-- The scalar extension formula commutes with morphisms of schemes. -/
theorem baseChangePointsSchemeNaturality : Specs.BaseChangePointsSchemeNaturality.{u} := by
  intro k K _ _ _ X Y f R p
  apply Over.OverMorphism.ext
  change (p.left ≫ ((baseChange k K).map f).left) ≫ pullback.fst Y.hom (fieldSpecMap k K) =
    (p.left ≫ pullback.fst X.hom (fieldSpecMap k K)) ≫ f.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

/-- Scalar extension identifies the point groups by the usual projection. -/
theorem baseChangePointsGroupLaw : Specs.BaseChangePointsGroupLaw.{u} := by
  intro k K _ _ _ G R p q
  let F := baseChange k K
  let p' : Points (F.obj G.X) R := p
  let q' : Points (F.obj G.X) R := q
  let x := baseChangePoint k K G.X R p'
  let y := baseChangePoint k K G.X R q'
  let t : Points (F.obj (G.X ⊗ G.X)) R :=
    lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X
  have hxy : baseChangePoint k K (G.X ⊗ G.X) R t = lift x y := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← baseChangePointsSchemeNaturality k K (fst G.X G.X) R t, lift_fst]
      change baseChangePoint k K G.X R
        ((lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map (fst G.X G.X)) = x
      rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
    · rw [← baseChangePointsSchemeNaturality k K (snd G.X G.X) R t, lift_snd]
      change baseChangePoint k K G.X R
        ((lift p' q' ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫ F.map (snd G.X G.X)) = y
      rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
  change baseChangePoint k K G.X R (lift p' q' ≫
      (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X])) = lift x y ≫ μ[G.X]
  rw [← Category.assoc]
  change baseChangePoint k K G.X R (t ≫ (baseChange k K).map μ[G.X]) = _
  rw [baseChangePointsSchemeNaturality, hxy]

/-- The scalar extension formula as an equivalence of point sets. -/
def baseChangePointsEquiv (K : Type u) [Field K] [Algebra k K] (X : SchemeOver k)
    (R : TestAlgebra K) :
    Points ((baseChange k K).obj X) R ≃ Points X ((restrictTestAlgebra k K).obj R) :=
  Equiv.ofBijective _ (baseChangePoints k K X R)


/-- The scalar extension formula as an isomorphism of groups. -/
def baseChangePointGroupEquiv (K : Type u) [Field K] [Algebra k K] (G : GroupScheme k)
    (R : TestAlgebra K) :
    Points ((groupBaseChange k K).obj G).X R ≃* Points G.X ((restrictTestAlgebra k K).obj R) where
  toEquiv := baseChangePointsEquiv K G.X R
  map_mul' := baseChangePointsGroupLaw k K G R

end

end LinearAlgebraicGroups
