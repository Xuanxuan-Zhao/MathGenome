import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.RightQuotientSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Specs (fppfOver schemeFppfSheaf SubgroupSections RightCosets rightCosetProjection
  rightCosetMap rightCosetAction projectSection actOnSection)

abbrev rightCosetPresheaf : Specs.RightCosetPresheafType.{u} := @Specs.rightCosetPresheaf
abbrev rightQuotientSheaf : Specs.RightQuotientSheafType.{u} := @Specs.rightQuotientSheaf
abbrev rightQuotientProjection : Specs.RightQuotientProjectionType.{u} := @Specs.rightQuotientProjection
abbrev rightQuotientBasePoint : Specs.RightQuotientBasePointType.{u} := @Specs.rightQuotientBasePoint
abbrev rightQuotientMap : Specs.RightQuotientMapType.{u} := @Specs.rightQuotientMap
abbrev rightQuotientAction : Specs.RightQuotientActionType.{u} := @Specs.rightQuotientAction

theorem rightQuotientLocalLifts : Specs.RightQuotientLocalLifts.{u} := by
  intro k _ G H
  change Presheaf.IsLocallySurjective (fppfOver k)
    (rightCosetProjection H ≫ toSheafify (fppfOver k) (rightCosetPresheaf H))
  have : Presheaf.IsLocallySurjective (fppfOver k) (rightCosetProjection H) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun T ⟨x⟩ ↦ by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨⟨g⟩, rfl⟩)
  infer_instance

theorem subgroupMembershipDescent : Specs.SubgroupMembershipDescent.{u} := by
  classical
  intro k _ G H T p S hS hp
  let i := H.inclusion.hom.hom
  have : IsClosedImmersion i.left := H.isClosedImmersion
  have : Mono i := Over.mono_of_mono_left i
  let P := (fppfOver k).yoneda.obj H.group.X
  let Q := (fppfOver k).yoneda.obj G.X
  let b {U : SchemeOver k} (f : U ⟶ T) (hf : S f) : U ⟶ H.group.X :=
    Classical.choose (hp f hf)
  have hb {U : SchemeOver k} (f : U ⟶ T) (hf : S f) : b f hf ≫ i = f ≫ p :=
    Classical.choose_spec (hp f hf)
  let family : Presieve.FamilyOfElements P.obj S.arrows := fun _ f hf ↦ b f hf
  have hc : family.Compatible := by
    intro U₁ U₂ V a₁ a₂ f₁ f₂ hf₁ hf₂ e
    change a₁ ≫ b f₁ hf₁ = a₂ ≫ b f₂ hf₂
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, hb f₁ hf₁, hb f₂ hf₂, ← Category.assoc, ← Category.assoc, e]
  obtain ⟨a, ha, _⟩ := (P.property.isSheafFor S hS) family hc
  change ∃ a : T ⟶ H.group.X, a ≫ i = p
  refine ⟨a, (Q.property.isSheafFor S hS).isSeparatedFor.ext ?_⟩
  intro U f hf
  change f ≫ a ≫ i = f ≫ p
  have hfa : f ≫ a = b f hf := ha f hf
  rw [← Category.assoc, hfa, hb f hf]

theorem rightQuotientProjectionEquality : Specs.RightQuotientProjectionEquality.{u} := by
  intro k _ G H T g g'
  let J := fppfOver k
  let C := rightCosetPresheaf H
  let x : C.obj (op T) := ⟨QuotientGroup.mk g⟩
  let y : C.obj (op T) := ⟨QuotientGroup.mk g'⟩
  change (toSheafify J C).app (op T) x = (toSheafify J C).app (op T) y ↔
    g⁻¹ * g' ∈ SubgroupSections H T
  constructor
  · intro e
    have hS := Presheaf.equalizerSieve_mem J (toSheafify J C) x y e
    apply subgroupMembershipDescent H _ _ hS
    intro U f hf
    have he : (QuotientGroup.mk (s := SubgroupSections H U) (f ≫ g)) =
        QuotientGroup.mk (f ≫ g') := congrArg ULift.down hf
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    exact QuotientGroup.eq.mp he
  · intro h
    have e : x = y := congrArg ULift.up (QuotientGroup.eq.mpr h)
    rw [e]

theorem rightQuotientMapOnLifts : Specs.RightQuotientMapOnLifts.{u} := by
  intro k _ G G' H H' f h comm T g
  let x : (rightCosetPresheaf H).obj (op T) := ⟨QuotientGroup.mk g⟩
  have e := congrArg (fun p => p.app (op T) x)
    (toSheafify_naturality (fppfOver k) (rightCosetMap f h comm))
  exact e.symm

theorem rightQuotientActionOnLifts : Specs.RightQuotientActionOnLifts.{u} := by
  intro k _ G H T a b
  let J := fppfOver k
  let A := (schemeFppfSheaf G.X).obj
  let C := rightCosetPresheaf H
  let F := sheafification J (Type (u + 1))
  let l : A ⊗ C ⟶ A ⊗ F.obj C := 𝟙 A ⊗ₘ toSheafify J C
  let m : A ⊗ F.obj C ⟶ F.obj A ⊗ F.obj C :=
    lift (fst _ _ ≫ toSheafify J A) (snd _ _)
  have e : l ≫ m = toSheafify J (A ⊗ C) ≫ (prodComparisonIso F A C).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [l, m, Category.assoc, lift_fst, tensorHom_fst_assoc,
        prodComparisonIso_hom, prodComparison_fst]
      exact toSheafify_naturality J (fst A C)
    · simp only [l, m, Category.assoc, lift_snd, tensorHom_snd, prodComparisonIso_hom,
        prodComparison_snd]
      exact toSheafify_naturality J (snd A C)
  have he : l ≫ rightQuotientAction H = rightCosetAction H ≫ toSheafify J C := by
    change l ≫ m ≫ (prodComparisonIso F A C).inv ≫ sheafifyMap J (rightCosetAction H) = _
    rw [← Category.assoc l, e]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (toSheafify_naturality J (rightCosetAction H)).symm
  let t : (A ⊗ C).obj (op T) := (⟨a⟩, ⟨QuotientGroup.mk b⟩)
  exact congrArg (fun p => p.app (op T) t) he

private theorem actOnSection_naturality {k : Type u} [Field k] {G : Specs.GroupScheme k}
    (H : Specs.ClosedSubgroup G) {T U : SchemeOver k} (f : U ⟶ T) (a : T ⟶ G.X)
    (x : (rightQuotientSheaf H).obj.obj (op T)) :
    (rightQuotientSheaf H).obj.map f.op (actOnSection H a x) =
      actOnSection H (f ≫ a) ((rightQuotientSheaf H).obj.map f.op x) := by
  let t : ((schemeFppfSheaf G.X).obj ⊗ (rightQuotientSheaf H).obj).obj (op T) :=
    (⟨a⟩, x)
  exact ((rightQuotientAction H).naturality_apply f.op t).symm

theorem rightQuotientActionLaws : Specs.RightQuotientActionLaws.{u} := by
  intro k _ G H T x
  let q := (rightQuotientProjection H).hom
  have := rightQuotientLocalLifts H
  let S := Presheaf.imageSieve q x
  have hS : S ∈ fppfOver k T := Presheaf.imageSieve_mem _ q x
  have sep := ((rightQuotientSheaf H).property.isSheafFor S hS).isSeparatedFor
  constructor
  · apply sep.ext
    intro U f hf
    obtain ⟨⟨g⟩, hg⟩ := hf
    change projectSection H g = (rightQuotientSheaf H).obj.map f.op x at hg
    rw [actOnSection_naturality, MonObj.comp_one, ← hg, rightQuotientActionOnLifts, one_mul]
  · intro a b
    apply sep.ext
    intro U f hf
    obtain ⟨⟨g⟩, hg⟩ := hf
    change projectSection H g = (rightQuotientSheaf H).obj.map f.op x at hg
    rw [actOnSection_naturality, actOnSection_naturality, actOnSection_naturality,
      MonObj.comp_mul, ← hg, rightQuotientActionOnLifts, rightQuotientActionOnLifts,
      rightQuotientActionOnLifts, mul_assoc]

private theorem testSpec_coverDense (k : Type u) [Field k] :
    (testSpec k).IsCoverDense (fppfOver k) where
  is_cover T := by
    let C := T.left.affineCover
    let V (j : C.I₀) : SchemeOver k := Over.mk (C.f j ≫ T.hom)
    let f (j : C.I₀) : V j ⟶ T := Over.homMk (C.f j)
    apply (fppfOver k).superset_covering (S := Sieve.ofArrows V f)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro U _ ⟨j⟩
      have hj : IsAffine (V j).left := Scheme.isAffine_affineCover _ _
      obtain ⟨R, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hj
      exact ⟨⟨R, e.inv, e.hom ≫ f j, by simp⟩⟩
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact Precoverage.generate_mem_toGrothendieck
        (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ C.mem₀)

private theorem testSpec_cocontinuous (k : Type u) [Field k] :
    (testSpec k).IsCocontinuous ((testSpec k).inducedTopology (fppfOver k)) (fppfOver k) := by
  have := testSpec_coverDense k
  have : (testSpec k).Full := (algSpec.fullyFaithful (R := CommRingCat.of k)).full
  have : (testSpec k).Faithful := (algSpec.fullyFaithful (R := CommRingCat.of k)).faithful
  infer_instance

theorem affineRightQuotientComparison : Specs.AffineRightQuotientComparison.{u} := by
  intro k _ G H
  let J := fppfOver k
  let F := testSpec k
  let K := F.inducedTopology J
  let P := rightCosetPresheaf H
  have : F.IsCocontinuous K J := testSpec_cocontinuous k
  let iso := (F.pushforwardContinuousSheafificationCompatibility (Type (u + 1)) K J).app P
  exact ⟨(sheafToPresheaf K _).mapIso iso,
    F.toSheafify_pullbackSheafificationCompatibility (Type (u + 1)) K J P⟩

theorem affineRightQuotientLocalLifts : Specs.AffineRightQuotientLocalLifts.{u} := by
  intro k _ G H
  have := testSpec_cocontinuous k
  have := rightQuotientLocalLifts H
  exact Presheaf.isLocallySurjective_whisker ((testSpec k).inducedTopology (fppfOver k))
    (fppfOver k) (testSpec k) (rightQuotientProjection H).hom

end

end LinearAlgebraicGroups
