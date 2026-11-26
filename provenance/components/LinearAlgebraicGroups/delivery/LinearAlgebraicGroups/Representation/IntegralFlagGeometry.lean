import Specs.LinearAlgebraicGroups.Representation.IntegralFlagGeometry
import LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Representation.FlagLineBundle
import LinearAlgebraicGroups.Representation.IntegralMarkedOppositeBorel
import LinearAlgebraicGroups.Representation.SpreadProjectiveRightTorsor
import LinearAlgebraicGroups.Representation.RelativeCovarianceLine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency false

universe u

namespace LinearAlgebraicGroups.Representation.IntegralFlagGeometry

noncomputable section

open Specs.FlagCohomology (SchemeOverRing)
open Specs.IntegralFlagGeometry
open SpreadProjectiveRightTorsor (changeBaseMap_isPullback changeBase_kernelPair)
open Specs.SpreadProjectiveRightTorsor (changeBaseGroup)
open private arithmeticProjectiveProper kernelPair_transport localSections_transport invert_comparison
  baseChange_structureProperty
  from LinearAlgebraicGroups.Representation.SpreadProjectiveRightTorsor
open private flagCover_and_polynomialChart
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private kBorel_smooth_connected
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private IsMultiplicativeSection isMultiplicativeSection_changeBase
  changeBaseGroupCompOfEq changeBaseGroupCompOfEq_projection
  from LinearAlgebraicGroups.Representation.IntegralMarkedOppositeBorel

section Quotient

variable {A B : Type u} [CommRing A] [CommRing B]

private theorem descendAlongEffectiveEpi {X Y Z : SchemeOverRing A} (q : X ⟶ Y)
    [EffectiveEpi q.left] (f : X ⟶ Z)
    (h : ∀ ⦃T : SchemeOverRing A⦄ (a b : T ⟶ X), a ≫ q = b ≫ q → a ≫ f = b ≫ f) :
    ∃ v : Y ⟶ Z, q ≫ v = f := by
  have hs {T : Scheme.{u}} (a b : T ⟶ X.left) (hab : a ≫ q.left = b ≫ q.left) :
      a ≫ f.left = b ≫ f.left := by
    let S : SchemeOverRing A := Over.mk (a ≫ X.hom)
    let a' : S ⟶ X := Over.homMk a rfl
    let b' : S ⟶ X := Over.homMk b (by
      change b ≫ X.hom = a ≫ X.hom
      rw [← Over.w q, ← Category.assoc, ← hab, Category.assoc])
    exact congrArg Over.Hom.left (h a' b' (Over.OverMorphism.ext hab))
  let v := EffectiveEpi.desc q.left f.left hs
  have hv : q.left ≫ v = f.left := EffectiveEpi.fac _ _ _
  refine ⟨Over.homMk v ?_, Over.OverMorphism.ext hv⟩
  exact (cancel_epi q.left).mp (by rw [← Category.assoc, hv, Over.w, Over.w])

/-- Two effective quotient projections with the same kernel pair give the same
quotient over the base. -/
theorem exists_quotientIso_of_kernelPair {W X Y Z : SchemeOverRing A}
    (a b : W ⟶ X) (q : X ⟶ Y) (r : X ⟶ Z)
    [EffectiveEpi q.left] [EffectiveEpi r.left]
    (hq : IsPullback a b q q) (hr : IsPullback a b r r) :
    ∃ e : Y ≅ Z, q ≫ e.hom = r := by
  obtain ⟨v, hv⟩ := descendAlongEffectiveEpi q r (by
    intro T x y hxy
    calc
      x ≫ r = hq.lift x y hxy ≫ a ≫ r := (hq.lift_fst_assoc _ _ _ _).symm
      _ = hq.lift x y hxy ≫ b ≫ r := by rw [hr.w]
      _ = y ≫ r := hq.lift_snd_assoc _ _ _ _)
  obtain ⟨w, hw⟩ := descendAlongEffectiveEpi r q (by
    intro T x y hxy
    calc
      x ≫ q = hr.lift x y hxy ≫ a ≫ q := (hr.lift_fst_assoc _ _ _ _).symm
      _ = hr.lift x y hxy ≫ b ≫ q := by rw [hq.w]
      _ = y ≫ q := hr.lift_snd_assoc _ _ _ _)
  let : Epi q := Over.epi_of_epi_left _
  let : Epi r := Over.epi_of_epi_left _
  exact ⟨⟨v, w, (cancel_epi q).mp (by rw [← Category.assoc, hv, hw, Category.comp_id]),
    (cancel_epi r).mp (by rw [← Category.assoc, hw, hv, Category.comp_id])⟩, hv⟩

private theorem whiskerLeft_isPullback (W : SchemeOverRing A) {X Y : SchemeOverRing A}
    (q : X ⟶ Y) : IsPullback (snd W X) (W ◁ q) q (snd W Y) := by
  refine IsPullback.mk' (whiskerLeft_snd _ _).symm ?_ ?_
  · intro T a b hab he
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst W Y) he
    · exact hab
  · intro T a b hab
    refine ⟨lift (b ≫ fst W Y) a, lift_snd _ _, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [hab]

private theorem effectiveEpi_whiskerLeft (W : SchemeOverRing A)
    {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    EffectiveEpi (W ◁ q).left := by
  have h := (whiskerLeft_isPullback W q).map (Over.forget (Spec (CommRingCat.of A)))
  let : Flat (W ◁ q).left := MorphismProperty.of_isPullback h ‹Flat q.left›
  let : Surjective (W ◁ q).left := MorphismProperty.of_isPullback h ‹Surjective q.left›
  let : LocallyOfFinitePresentation (W ◁ q).left :=
    MorphismProperty.of_isPullback h ‹LocallyOfFinitePresentation q.left›
  infer_instance

private theorem effectiveEpi_of_fppf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f] : EffectiveEpi f := inferInstance

private theorem effectiveEpi_precomp_iso {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z)
    [EffectiveEpi f] : EffectiveEpi (e.hom ≫ f) := by
  let condition {W : Scheme.{u}} (a : X ⟶ W)
      (h : ∀ ⦃T : Scheme.{u}⦄ (g₁ g₂ : T ⟶ X),
        g₁ ≫ e.hom ≫ f = g₂ ≫ e.hom ≫ f → g₁ ≫ a = g₂ ≫ a)
      {T : Scheme.{u}} (g₁ g₂ : T ⟶ Y) (hg : g₁ ≫ f = g₂ ≫ f) :
      g₁ ≫ e.inv ≫ a = g₂ ≫ e.inv ≫ a := by
    rw [← Category.assoc, ← Category.assoc]
    exact h (g₁ ≫ e.inv) (g₂ ≫ e.inv) (by simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hg)
  refine ⟨⟨⟨fun a h => EffectiveEpi.desc f (e.inv ≫ a) (condition a (@h)), ?_, ?_⟩⟩⟩
  · intro W a h
    simp only [Category.assoc, EffectiveEpi.fac, Iso.hom_inv_id_assoc]
  · intro W a h v hv
    apply EffectiveEpi.uniq
    rw [← cancel_epi e.hom, ← Category.assoc, hv, Iso.hom_inv_id_assoc]

private theorem rightMultiply_lift {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    {T : SchemeOverRing A} (g : T ⟶ G.X) (b : T ⟶ H.X) :
    prod.lift g b ≫ rightMultiply i = g * (b ≫ i.hom.hom) := by
  simp [Specs.RelativeCovarianceLine.rightMultiply, MonObj.comp_mul]

private theorem quotient_rightMultiply {G H : Grp (SchemeOverRing A)} {i : H ⟶ G}
    {Y : SchemeOverRing A} {q : G.X ⟶ Y}
    (hq : IsPullback prod.fst (rightMultiply i) q q)
    {T : SchemeOverRing A} (g : T ⟶ G.X) (b : T ⟶ H.X) :
    (g * (b ≫ i.hom.hom)) ≫ q = g ≫ q := by
  rw [← rightMultiply_lift, Category.assoc, ← hq.w, prod.lift_fst_assoc]

private theorem quotient_difference {G H : Grp (SchemeOverRing A)} {i : H ⟶ G}
    {Y : SchemeOverRing A} {q : G.X ⟶ Y}
    (hq : IsPullback prod.fst (rightMultiply i) q q)
    {T : SchemeOverRing A} (g g' : T ⟶ G.X) (he : g ≫ q = g' ≫ q) :
    ∃ b : T ⟶ H.X, g * (b ≫ i.hom.hom) = g' := by
  let t := hq.lift g g' he
  refine ⟨t ≫ prod.snd, ?_⟩
  have ht : t ≫ prod.fst = g := hq.lift_fst _ _ _
  rw [← ht]
  simpa only [t, Specs.RelativeCovarianceLine.rightMultiply, MonObj.comp_mul, Category.assoc] using
    hq.lift_snd g g' he

/-- Left multiplication descends to a right quotient presented by its fppf
projection and right-multiplication kernel pair. -/
theorem exists_quotientAction {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    {Y : SchemeOverRing A} (q : G.X ⟶ Y)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hq : IsPullback prod.fst (rightMultiply i) q q) :
    ∃ a : ModObj G.X Y, μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul := by
  let M := G.X
  let F := M ◁ q
  let : EffectiveEpi F.left := effectiveEpi_whiskerLeft M q
  obtain ⟨a, ha⟩ := descendAlongEffectiveEpi F (μ[M] ≫ q) (by
    intro T x y hxy
    have h₁ : x ≫ fst M M = y ≫ fst M M := by
      simpa only [F, Category.assoc, whiskerLeft_fst] using congrArg (· ≫ fst M Y) hxy
    have h₂ : x ≫ snd M M ≫ q = y ≫ snd M M ≫ q := by
      simpa only [F, Category.assoc, whiskerLeft_snd] using congrArg (· ≫ snd M Y) hxy
    obtain ⟨b, hb⟩ := quotient_difference hq (x ≫ snd M M) (y ≫ snd M M) h₂
    rw [← Category.assoc, ← Category.assoc, ← lift_comp_fst_snd x, ← lift_comp_fst_snd y]
    change ((x ≫ fst M M) * (x ≫ snd M M)) ≫ q =
      ((y ≫ fst M M) * (y ≫ snd M M)) ≫ q
    rw [h₁, ← hb, ← mul_assoc, quotient_rightMultiply hq])
  have eval {T : SchemeOverRing A} (h g : T ⟶ M) :
      lift h (g ≫ q) ≫ a = (h * g) ≫ q := by
    rw [← lift_whiskerLeft, Category.assoc, ha]
    rfl
  have hUnit : η[M] ▷ Y ≫ a = (λ_ Y).hom := by
    let : EffectiveEpi ((𝟙_ (SchemeOverRing A)) ◁ q).left :=
      effectiveEpi_whiskerLeft _ q
    let : Epi ((𝟙_ (SchemeOverRing A)) ◁ q) := Over.epi_of_epi_left _
    apply (cancel_epi ((𝟙_ (SchemeOverRing A)) ◁ q)).mp
    have hComp : (𝟙_ (SchemeOverRing A)) ◁ q ≫ η[M] ▷ Y =
        lift (fst (𝟙_ (SchemeOverRing A)) M ≫ η[M])
          (snd (𝟙_ (SchemeOverRing A)) M ≫ q) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, whiskerRight_fst, whiskerLeft_fst_assoc, lift_fst]
        rfl
      · simp only [Category.assoc, whiskerRight_snd, whiskerLeft_snd, lift_snd]
        rfl
    rw [← Category.assoc, hComp, eval, leftUnitor_hom, whiskerLeft_snd]
    change (fst (𝟙_ (SchemeOverRing A)) M ≫ η[M] * snd _ _) ≫ q = _
    rw [toUnit_unique (fst (𝟙_ (SchemeOverRing A)) M) (toUnit _)]
    exact congrArg (· ≫ q) (one_mul _)
  have hAssoc : μ[M] ▷ Y ≫ a = (α_ M M Y).hom ≫ M ◁ a ≫ a := by
    let : EffectiveEpi ((M ⊗ M) ◁ q).left := effectiveEpi_whiskerLeft _ q
    let : Epi ((M ⊗ M) ◁ q) := Over.epi_of_epi_left _
    apply (cancel_epi ((M ⊗ M) ◁ q)).mp
    let x := fst (M ⊗ M) M ≫ fst M M
    let y := fst (M ⊗ M) M ≫ snd M M
    let z := snd (M ⊗ M) M
    have hL : (M ⊗ M) ◁ q ≫ μ[M] ▷ Y = lift (x * y) (z ≫ q) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, whiskerRight_fst, whiskerLeft_fst_assoc, lift_fst]
        exact (lift_comp_fst_snd (fst (M ⊗ M) M) =≫ μ[M]).symm
      · simp only [Category.assoc, whiskerRight_snd, whiskerLeft_snd, lift_snd]
        rfl
    have hR : (M ⊗ M) ◁ q ≫ (α_ M M Y).hom ≫ M ◁ a =
        lift x (lift y (z ≫ q) ≫ a) := by
      have hs : (M ⊗ M) ◁ q ≫ (α_ M M Y).hom ≫ snd M (M ⊗ Y) = lift y (z ≫ q) := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.assoc, associator_hom_snd_fst, whiskerLeft_fst_assoc, lift_fst]
          rfl
        · simp only [Category.assoc, associator_hom_snd_snd, whiskerLeft_snd, lift_snd]
          rfl
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, whiskerLeft_fst, associator_hom_fst, whiskerLeft_fst_assoc, lift_fst]
        rfl
      · simpa only [Category.assoc, whiskerLeft_snd, lift_snd] using congrArg (· ≫ a) hs
    calc
      _ = lift (x * y) (z ≫ q) ≫ a := by rw [← Category.assoc, hL]
      _ = lift x (lift y (z ≫ q) ≫ a) ≫ a := by rw [eval, eval, eval, mul_assoc]
      _ = _ := by simpa only [Category.assoc] using (congrArg (· ≫ a) hR).symm
  refine ⟨⟨a, ?_, ?_⟩, ha.symm⟩
  · exact hUnit
  · exact hAssoc

private theorem changeBase_quotientAction (φ : A →+* B)
    {G : Grp (SchemeOverRing A)} {Y : SchemeOverRing A}
    (q : G.X ⟶ Y) (a : ModObj G.X Y)
    (ha : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul) :
    μ[((changeBase φ).mapGrp.obj G).X] ≫ (changeBase φ).map q =
      (𝟙 _ ⊗ₘ (changeBase φ).map q) ≫
        Functor.LaxMonoidal.μ (changeBase φ) G.X Y ≫ (changeBase φ).map a.smul := by
  let F := changeBase φ
  change Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X] ≫ F.map q =
    (𝟙 _ ⊗ₘ F.map q) ≫ Functor.LaxMonoidal.μ F G.X Y ≫ F.map a.smul
  have hn := Functor.LaxMonoidal.μ_natural F (𝟙 G.X) q
  rw [F.map_id] at hn
  rw [← F.map_comp, ha, F.map_comp, ← Category.assoc, ← hn, Category.assoc]

private theorem rightMultiply_transport {G H G' H' : Grp (SchemeOverRing B)}
    {i : H ⟶ G} {i' : H' ⟶ G'} (e : G ⟶ G') (t : H ⟶ H')
    (ht : i ≫ e = t ≫ i') :
    prod.map e.hom.hom t.hom.hom ≫ rightMultiply i' = rightMultiply i ≫ e.hom.hom := by
  have hi : i.hom.hom ≫ e.hom.hom = t.hom.hom ≫ i'.hom.hom :=
    congrArg (fun g : H ⟶ G' => g.hom.hom) ht
  simp only [Specs.RelativeCovarianceLine.rightMultiply, MonObj.comp_mul, MonObj.mul_comp, Category.assoc]
  rw [prod.map_fst, prod.map_snd_assoc, ← hi]

private theorem equivariant_of_quotientProjections {G G' : Grp (SchemeOverRing B)}
    {Y Y' : SchemeOverRing B} (q : G.X ⟶ Y) (r : G'.X ⟶ Y')
    (e : G ⟶ G') (v : Y ⟶ Y') (hv : q ≫ v = e.hom.hom ≫ r)
    (a : G.X ⊗ Y ⟶ Y) (a' : G'.X ⊗ Y' ⟶ Y')
    (ha : μ[G.X] ≫ q = (𝟙 _ ⊗ₘ q) ≫ a)
    (ha' : μ[G'.X] ≫ r = (𝟙 _ ⊗ₘ r) ≫ a')
    [EffectiveEpi ((𝟙 G.X ⊗ₘ q) : G.X ⊗ G.X ⟶ G.X ⊗ Y).left] :
    a ≫ v = (e.hom.hom ⊗ₘ v) ≫ a' := by
  let : Epi (𝟙 G.X ⊗ₘ q) := Over.epi_of_epi_left _
  apply (cancel_epi (𝟙 G.X ⊗ₘ q)).mp
  calc
    _ = μ[G.X] ≫ q ≫ v := by rw [← Category.assoc, ← ha, Category.assoc]
    _ = (e.hom.hom ⊗ₘ e.hom.hom) ≫ (𝟙 G'.X ⊗ₘ r) ≫ a' := by
      rw [hv, ← Category.assoc, IsMonHom.mul_hom, Category.assoc, ha']
    _ = _ := by
      rw [← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hv]

/-- A preferred field quotient can be compared with a fibre of the arithmetic
torsor as soon as the marked group and subgroup have been identified. -/
theorem exists_flagIso_of_fibreSubgroup {k : Type u} [Field k] (φ : A →+* k)
    (M : Specs.IntegralFlagGeometry.Model A) {G : Specs.AffineAlgebraicGroup k}
    (P : Specs.FlagLineBundle.OppositeBorelPair G)
    (e : (changeBase φ).mapGrp.obj M.group ≅ G.val)
    (b : (changeBase φ).mapGrp.obj M.borel ≅ P.negative.group)
    (hb : (changeBase φ).mapGrp.map M.inclusion ≫ e.hom = b.hom ≫ P.negative.inclusion)
    (Q : Specs.QuotientEmbedding.Presentation P.negative)
    (hQ : IsPullback prod.fst (rightMultiply P.negative.inclusion) Q.projection Q.projection) :
    ∃ (v : (changeBase φ).obj M.flag ≅ Q.scheme) (a : ModObj G.val.X Q.scheme),
      μ[G.val.X] ≫ Q.projection = (𝟙 _ ⊗ₘ Q.projection) ≫ a.smul ∧
      (changeBase φ).map M.quotient ≫ v.hom = e.hom.hom.hom ≫ Q.projection ∧
      Functor.LaxMonoidal.μ (changeBase φ) M.group.X M.flag ≫
          (changeBase φ).map M.action.smul ≫ v.hom =
        (e.hom.hom.hom ⊗ₘ v.hom) ≫ a.smul := by
  let F := changeBase φ
  let G' := F.mapGrp.obj M.group
  let H' := F.mapGrp.obj M.borel
  let q := F.map M.quotient
  let i := F.mapGrp.map M.inclusion
  let e' : G'.X ≅ G.val.X := (Grp.forget _).mapIso e
  let b' := (Grp.forget _).mapIso b
  let r := e'.hom ≫ Q.projection
  have hq : IsPullback prod.fst (rightMultiply i) q q :=
    changeBase_kernelPair φ M.inclusion M.quotient M.kernelPair
  have hr : IsPullback (prod.fst : G'.X ⨯ H'.X ⟶ G'.X) (rightMultiply i) r r :=
    hQ.of_iso' (prod.mapIso e' b') e' e' (Iso.refl _) (prod.map_fst _ _)
      (rightMultiply_transport e.hom b.hom hb) (Category.comp_id _).symm
      (Category.comp_id _).symm
  let hbase := (changeBaseMap_isPullback φ M.quotient).flip
  let : Flat q.left := MorphismProperty.of_isPullback hbase M.quotientFlat
  let : Surjective q.left := MorphismProperty.of_isPullback hbase M.quotientSurjective
  let : LocallyOfFinitePresentation q.left := MorphismProperty.of_isPullback hbase M.quotientLfp
  let : Flat Q.projection.left := Q.flat
  let : Surjective Q.projection.left := Q.surjective
  let : LocallyOfFinitePresentation Q.projection.left := Q.finitePresentation
  have hEffq : EffectiveEpi q.left := effectiveEpi_of_fppf q.left
  have hEffQ : EffectiveEpi Q.projection.left :=
    @effectiveEpi_of_fppf _ _ Q.projection.left Q.flat Q.surjective Q.finitePresentation
  have hEffr : EffectiveEpi r.left :=
    @effectiveEpi_precomp_iso _ _ _ ((Over.forget _).mapIso e') Q.projection.left hEffQ
  have hqr : ∃ v : F.obj M.flag ≅ Q.scheme, q ≫ v.hom = r :=
    @exists_quotientIso_of_kernelPair k _ _ _ _ _ prod.fst (rightMultiply i) q r hEffq hEffr hq hr
  obtain ⟨v, hv⟩ := hqr
  obtain ⟨a, ha⟩ := exists_quotientAction P.negative.inclusion Q.projection hQ
  refine ⟨v, a, ha, hv, ?_⟩
  let : EffectiveEpi ((𝟙 G'.X ⊗ₘ q) : G'.X ⊗ G'.X ⟶ G'.X ⊗ F.obj M.flag).left :=
    effectiveEpi_whiskerLeft G'.X q
  rw [← Category.assoc]
  exact equivariant_of_quotientProjections q Q.projection e.hom v.hom hv
    (Functor.LaxMonoidal.μ F M.group.X M.flag ≫ F.map M.action.smul) a.smul
    (changeBase_quotientAction φ M.quotient M.action M.quotientEquivariant) ha
end Quotient

/-- A scheme with a closed embedding into relative projective space is proper
over the specified base ring. -/
theorem proper_of_projectiveOver {A : Type u} [CommRing A] (Y : SchemeOverRing A)
    (h : IsProjectiveOver Y) : IsProper Y.hom := by
  obtain ⟨n, j, hj⟩ := h
  let : IsClosedImmersion j.left := hj
  let : IsProper (projectiveSpace A n).hom := arithmeticProjectiveProper n
  rw [← Over.w j]
  infer_instance

section GenericQuotient

open Specs.SpreadProjectiveRightTorsor (HasLocalSections)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.QuotientEmbedding (Presentation)

private theorem fieldQuotient_localSections {k : Type u} [Field k]
    {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G} (Q : Presentation P.negative) :
    HasLocalSections Q.projection := by
  intro y
  obtain ⟨U, s, hs, hy⟩ := (flagCover_and_polynomialChart Q).1 y
  exact ⟨U, s ≫ Q.projection, s, hs, hy, rfl⟩

private theorem exists_genericQuotient {k : Type u} [Field k]
    {G₀ H₀ : Grp (SchemeOverRing k)} (i : H₀ ⟶ G₀) {G : Specs.AffineAlgebraicGroup k}
    (P : OppositeBorelPair G) (eG : G₀ ≅ G.val) (eH : H₀ ≅ P.negative.group)
    (hi : i ≫ eG.hom = eH.hom ≫ P.negative.inclusion) :
    ∃ (Y : SchemeOverRing k), Smooth Y.hom ∧
      (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module.Finite k V)
        (j : Y ⟶ Specs.ProjectiveSpaces.projectiveSpace k V), IsClosedImmersion j.left) ∧
      ∃ q : G₀.X ⟶ Y, Smooth q.left ∧ Surjective q.left ∧
        IsPullback prod.fst (rightMultiply i) q q ∧ HasLocalSections q := by
  obtain ⟨_, ⟨Q⟩, hQ⟩ := FlagLineBundle.oppositeFlagGeometry k G P
  obtain ⟨hY, _, _, V, hV, hModule, hFinite, _, j, hj, _⟩ := hQ Q
  let e : G₀.X ≅ G.val.X := (Grp.forget _).mapIso eG
  let q : G₀.X ⟶ Q.scheme := e.hom ≫ Q.projection
  have hB := (kBorel_smooth_connected G P.negative P.negativeBorel).1
  have hSmooth : Smooth Q.projection.left :=
    ((HomogeneousQuotient.homogeneousQuotient k G P.negative).2 Q).2 hB
  have hi' : P.negative.inclusion ≫ eG.inv = eH.inv ≫ i :=
    invert_comparison eH eG i P.negative.inclusion hi.symm
  have hq : Q.projection ≫ (Iso.refl Q.scheme).hom = e.inv ≫ q := by
    simp [q]
  refine ⟨Q.scheme, hY, ⟨V, hV, hModule, hFinite, j, hj⟩, q, ?_, ?_, ?_, ?_⟩
  · let : Smooth Q.projection.left := hSmooth
    change Smooth (e.hom.left ≫ Q.projection.left)
    infer_instance
  · let : Surjective Q.projection.left := Q.surjective
    change Surjective (e.hom.left ≫ Q.projection.left)
    infer_instance
  · exact kernelPair_transport P.negative.inclusion i eG.symm eH.symm hi'
      (Iso.refl _) Q.projection q hq (HomogeneousQuotient.quotientPullback Q)
  · exact localSections_transport e.symm (Iso.refl _) _ q hq (fieldQuotient_localSections Q)

end GenericQuotient

section RelativeLine

open Specs.RelativeCovarianceLine (Torsor)
open Specs.SpreadProjectiveRightTorsor (HasLocalSections)

private theorem localSections_onOpens {A : Type u} [CommRing A] {X Y : SchemeOverRing A}
    (q : X ⟶ Y) (h : HasLocalSections q) :
    ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧ ∃ s : U.toScheme ⟶ X.left, s ≫ q.left = U.ι := by
  intro y
  obtain ⟨_, j, s, hj, hy, hs⟩ := h y
  let : IsOpenImmersion j.left := hj
  refine ⟨j.left.opensRange, hy, j.left.isoOpensRange.inv ≫ s.left, ?_⟩
  rw [Category.assoc, ← Over.comp_left, hs, Scheme.Hom.isoOpensRange_inv_comp]

private def modelOfTorsor {A : Type u} [CommRing A] (T : Torsor A)
    (hf : Flat T.quotient.hom) (hp : IsProjectiveOver T.quotient)
    (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ a.smul) : Model A :=
  ⟨T, hf, hp, a, ha⟩

private theorem modelOfTorsor_line {A : Type u} [CommRing A] (T : Torsor A)
    (hf : Flat T.quotient.hom) (hp : IsProjectiveOver T.quotient)
    (a : ModObj T.group.X T.quotient)
    (ha : μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ a.smul) :
    (modelOfTorsor T hf hp a ha).IsLineBundle ∧ (modelOfTorsor T hf hp a ha).HasEquivariantLine :=
  ⟨RelativeCovarianceLine.isLineBundle A T, RelativeCovarianceLine.equivariantLine A T a ha⟩

end RelativeLine

section FibreLine

open Specs.FlagCohomology (FlagKernelPair flagLineData flagLineSheaf flagTransition)
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.RelativeCovarianceLine (Torsor CartesianChange)
open Specs.QuotientEmbedding (Presentation)
open Specs.CharacterDescent (Character)

variable {A B : Type u} [CommRing A] [CommRing B]

private theorem fibreSquare_of_isos (φ : A →+* B) {X Y : SchemeOverRing A}
    (q : X ⟶ Y) {X' Y' : SchemeOverRing B} (q' : X' ⟶ Y')
    (eX : X' ≅ (changeBase φ).obj X) (eY : Y' ≅ (changeBase φ).obj Y)
    (h : eX.hom ≫ (changeBase φ).map q = q' ≫ eY.hom) :
    IsPullback (eX.hom.left ≫ fibreProjection φ X) q'.left q.left
      (eY.hom.left ≫ fibreProjection φ Y) := by
  have hIso : IsPullback eX.hom.left q'.left ((changeBase φ).map q).left eY.hom.left :=
    IsPullback.of_horiz_isIso ⟨congrArg Over.Hom.left h⟩
  exact hIso.paste_horiz (changeBaseMap_isPullback φ q).flip

private theorem fibreProjection_comm_of_comm (φ : A →+* B) {X Y : SchemeOverRing A}
    (q : X ⟶ Y) {X' Y' : SchemeOverRing B} (q' : X' ⟶ Y')
    (a : X' ⟶ (changeBase φ).obj X) (b : Y' ⟶ (changeBase φ).obj Y)
    (h : a ≫ (changeBase φ).map q = q' ≫ b) :
    (a.left ≫ fibreProjection φ X) ≫ q.left = q'.left ≫ b.left ≫ fibreProjection φ Y := by
  rw [Category.assoc, ← (changeBaseMap_isPullback φ q).w, ← Category.assoc,
    ← Over.comp_left, h, Over.comp_left, Category.assoc]

private theorem map_rightMultiply (φ : A →+* B) {G H : Grp (SchemeOverRing A)}
    (i : H ⟶ G) :
    (PreservesLimitPair.iso (changeBase φ) G.X H.X).inv ≫ (changeBase φ).map (rightMultiply i) =
      rightMultiply ((changeBase φ).mapGrp.map i) := by
  let F := changeBase φ
  let e := PreservesLimitPair.iso F G.X H.X
  have hfst : e.inv ≫ F.map prod.fst = prod.fst := PreservesLimitPair.iso_inv_fst F G.X H.X
  have hsnd : e.inv ≫ F.map prod.snd = prod.snd := PreservesLimitPair.iso_inv_snd F G.X H.X
  change e.inv ≫ F.map (prod.fst * (prod.snd ≫ i.hom.hom)) = _
  simp only [F.map_mul, F.map_comp, MonObj.comp_mul, ← Category.assoc]
  rw [hfst, hsnd]
  rfl

variable {k : Type u} [Field k] {G : Specs.AffineAlgebraicGroup k} {P : OppositeBorelPair G}

private def inverseCharacterCoordinate (p : BorelProjection P) (χ : Character P.torus.group) :
    Γ(P.negative.group.X.left, ⊤) :=
  let r := (𝟙 P.negative.group.X)⁻¹ ≫ (p.projection ≫ χ).hom.hom
  let L := Specs.DiagonalizableGroups.groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters
  ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ r.left.appTop)
    (MonoidAlgebra.single Specs.DiagonalizableGroups.integerGenerator (1 : k))

private theorem flagTransition_eq_appTop (p : BorelProjection P) (χ : Character P.torus.group) :
    flagTransition p χ = (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X).left.appTop
      (inverseCharacterCoordinate p χ) := by
  let s : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X := prod.snd
  let r := (p.projection ≫ χ).hom.hom
  let c := (Scheme.ΓSpecIso (CommRingCat.of (Specs.DiagonalizableGroups.groupAlgebra k
    Specs.DiagonalizableGroups.IntegerCharacters))).inv
      (MonoidAlgebra.single Specs.DiagonalizableGroups.integerGenerator (1 : k))
  change (s⁻¹ ≫ r).left.appTop c = s.left.appTop (((𝟙 _)⁻¹ ≫ r).left.appTop c)
  have h : s ≫ (𝟙 _)⁻¹ ≫ r = s⁻¹ ≫ r := by
    rw [← Category.assoc, GrpObj.comp_inv, Category.comp_id]
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, Category.assoc, CommRingCat.comp_apply] using
    (congrArg (fun a => a.left.appTop c) h).symm

private theorem fieldLineComparison (T : Torsor A) (φ : A →+* k)
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (hQ : FlagKernelPair Q)
    (eG : (changeBase φ).mapGrp.obj T.group ≅ G.val)
    (eH : (changeBase φ).mapGrp.obj T.subgroup ≅ P.negative.group)
    (hi : (changeBase φ).mapGrp.map T.inclusion ≫ eG.hom = eH.hom ≫ P.negative.inclusion)
    (v : (changeBase φ).obj T.quotient ≅ Q.scheme)
    (hv : (changeBase φ).map T.projection ≫ v.hom = eG.hom.hom.hom ≫ Q.projection)
    (hc : (eH.inv.hom.hom.left ≫ fibreProjection φ T.subgroup.X).appTop
      (T.character⁻¹ : Γ(T.subgroup.X.left, ⊤)ˣ) = inverseCharacterCoordinate p χ) :
    let f := v.inv.left ≫ fibreProjection φ T.quotient
    let g := eG.inv.hom.hom.left ≫ fibreProjection φ T.group.X
    ∃ (h : g ≫ T.projection.left = Q.projection.left ≫ f)
      (e : (Scheme.Modules.pullback f).obj T.line ≅ flagLineSheaf Q p χ hQ),
      T.lineData.IsPullbackMap (flagLineData Q p χ hQ) f g h
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ e.hom) := by
  let F := changeBase φ
  let D := T.lineData
  let E := flagLineData Q p χ hQ
  let eg : G.val.X ≅ F.obj T.group.X := ((Grp.forget _).mapIso eG).symm
  let eh : P.negative.group.X ≅ F.obj T.subgroup.X := ((Grp.forget _).mapIso eH).symm
  let eprod := PreservesLimitPair.iso F T.group.X T.subgroup.X
  let ej : E.overlap ≅ F.obj D.overlap := prod.mapIso eg eh ≪≫ eprod.symm
  let ey : Q.scheme ≅ F.obj T.quotient := v.symm
  have hq : eg.hom ≫ F.map D.projection = E.projection ≫ ey.hom :=
    (invert_comparison eg.symm v _ _ hv.symm).symm
  have hfirst : ej.hom ≫ F.map D.first = E.first ≫ eg.hom := by
    change (prod.map eg.hom eh.hom ≫ eprod.inv) ≫ F.map prod.fst = prod.fst ≫ eg.hom
    rw [Category.assoc, PreservesLimitPair.iso_inv_fst, prod.map_fst]
  have hsecond : ej.hom ≫ F.map D.second = E.second ≫ eg.hom := by
    have hi' : P.negative.inclusion ≫ eG.inv = eH.inv ≫ F.mapGrp.map T.inclusion :=
      invert_comparison eH eG _ _ hi.symm
    change (prod.map eg.hom eh.hom ≫ eprod.inv) ≫ F.map (rightMultiply T.inclusion) = _
    rw [Category.assoc, map_rightMultiply]
    exact rightMultiply_transport eG.inv eH.inv hi'
  let d : D.overlap ⟶ T.subgroup.X := prod.snd
  let d' : E.overlap ⟶ P.negative.group.X := prod.snd
  have hsnd : ej.hom ≫ F.map d = d' ≫ eh.hom := by
    change (prod.map eg.hom eh.hom ≫ eprod.inv) ≫ F.map prod.snd = prod.snd ≫ eh.hom
    rw [Category.assoc, PreservesLimitPair.iso_inv_snd, prod.map_snd]
  have hr : ej.hom ≫ F.map D.overlapProjection = E.overlapProjection ≫ ey.hom := by
    change ej.hom ≫ F.map (D.first ≫ D.projection) = (E.first ≫ E.projection) ≫ ey.hom
    rw [Functor.map_comp, ← Category.assoc, hfirst, Category.assoc, hq, Category.assoc]
  let f := ey.hom.left ≫ fibreProjection φ T.quotient
  let g : E.torsor.left ⟶ D.torsor.left := eg.hom.left ≫ fibreProjection φ T.group.X
  let j : E.overlap.left ⟶ D.overlap.left := ej.hom.left ≫ fibreProjection φ D.overlap
  let C : CartesianChange D E f :=
    { torsorMap := g
      overlapMap := j
      torsorSquare := fibreSquare_of_isos φ _ _ eg ey hq
      overlapSquare := fibreSquare_of_isos φ _ _ ej ey hr
      first_eq := fibreProjection_comm_of_comm φ _ _ _ _ hfirst
      second_eq := fibreProjection_comm_of_comm φ _ _ _ _ hsecond
      multiplier_eq := by
        let c : Γ(T.subgroup.X.left, ⊤) := (T.character⁻¹ : Γ(T.subgroup.X.left, ⊤)ˣ)
        change j.appTop (d.left.appTop c) = flagTransition p χ
        change (d.left.appTop ≫ j.appTop) c = flagTransition p χ
        rw [← Scheme.Hom.comp_appTop, fibreProjection_comm_of_comm φ d d' _ _ hsnd,
          Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        change (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X).left.appTop
          ((eH.inv.hom.hom.left ≫ fibreProjection φ T.subgroup.X).appTop
            (T.character⁻¹ : Γ(T.subgroup.X.left, ⊤)ˣ)) = flagTransition p χ
        rw [hc, flagTransition_eq_appTop] }
  obtain ⟨e, he⟩ := (RelativeCovarianceLine.cartesianComparison A k T E f C).1
  exact ⟨C.torsorSquare.w, e, he⟩

end FibreLine

section Refinement

open Specs.RelativeCovarianceLine (Torsor)
open Specs.SpreadProjectiveRightTorsor (HasLocalSections)
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private theorem affine_changeBase (φ : A →+* B) (X : SchemeOverRing A) (h : IsAffine X.left) :
    IsAffine ((changeBase φ).obj X).left := by
  let : IsAffine X.left := h
  let : IsAffineHom X.hom := isAffineHom_of_isAffine _
  change IsAffine (pullback X.hom (Spec.map (CommRingCat.ofHom φ)))
  infer_instance

private def baseChangedTorsor (r : A →+* B) {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    (hi : IsClosedImmersion i.hom.hom.left) (hG : Smooth G.X.hom) (hH : Smooth H.X.hom)
    (hGa : IsAffine G.X.left) (hHa : IsAffine H.X.left) (c : Γ(H.X.left, ⊤)ˣ)
    (hc : IsMultiplicativeSection H c) (Y : SchemeOverRing B) (hY : Smooth Y.hom)
    (hP : IsProjectiveOver Y) (q : ((changeBaseGroup r).obj G).X ⟶ Y)
    (hq : Smooth q.left) (hs : Surjective q.left)
    (hpair : IsPullback prod.fst (rightMultiply ((changeBaseGroup r).map i)) q q)
    (hsec : HasLocalSections q) : Torsor B :=
  let : IsProper Y.hom := proper_of_projectiveOver Y hP
  { group := (changeBaseGroup r).obj G
    subgroup := (changeBaseGroup r).obj H
    inclusion := (changeBaseGroup r).map i
    closedSubgroup := MorphismProperty.of_isPullback (changeBaseMap_isPullback r i.hom.hom).flip hi
    smoothGroup := MorphismProperty.pullback_snd _ _ hG
    smoothSubgroup := MorphismProperty.pullback_snd _ _ hH
    affineGroup := affine_changeBase r G.X hGa
    affineSubgroup := affine_changeBase r H.X hHa
    quotient := Y
    smoothQuotient := hY
    separatedQuotient := inferInstance
    projection := q
    smoothProjection := hq
    surjectiveProjection := hs
    kernelPair := hpair
    localSections := localSections_onOpens q hsec
    character := Units.map (fibreProjection r H.X).appTop.hom.toMonoidHom c
    character_mul := isMultiplicativeSection_changeBase r H hc }

private abbrev groupComparison (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C}
    (h : ψ.comp φ = κ) (G : Grp (SchemeOverRing A)) :
    (changeBaseGroup κ).obj G ≅ (changeBaseGroup ψ).obj ((changeBaseGroup φ).obj G) :=
  (changeBaseGroupCompOfEq φ ψ h.symm).app G

private theorem groupComparison_inv_projection (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C}
    (h : ψ.comp φ = κ) (G : Grp (SchemeOverRing A)) :
    (groupComparison φ ψ h G).inv.hom.hom.left ≫ fibreProjection κ G.X =
      fibreProjection ψ ((changeBase φ).obj G.X) ≫ fibreProjection φ G.X := by
  let e := (Grp.forget _ ⋙ Over.forget _).mapIso (groupComparison φ ψ h G)
  apply (cancel_epi e.hom).mp
  change e.hom ≫ e.inv ≫ _ = e.hom ≫ _
  rw [Iso.hom_inv_id_assoc]
  exact (changeBaseGroupCompOfEq_projection φ ψ h.symm G).symm

private def refinedFibreIso (φ : A →+* B) (ψ : B →+* C)
    {G : Grp (SchemeOverRing A)} {J : Grp (SchemeOverRing C)}
    (e : (changeBase (ψ.comp φ)).mapGrp.obj G ≅ J) :
    (changeBase ψ).mapGrp.obj ((changeBase φ).mapGrp.obj G) ≅ J :=
  ((changeBaseGroupCompOfEq φ ψ rfl).app G).symm ≪≫ e

private theorem refinedFibreIso_inv_projection (φ : A →+* B) (ψ : B →+* C)
    {G : Grp (SchemeOverRing A)} {J : Grp (SchemeOverRing C)}
    (e : (changeBase (ψ.comp φ)).mapGrp.obj G ≅ J) :
    (refinedFibreIso φ ψ e).inv.hom.hom.left ≫ fibreProjection ψ ((changeBase φ).obj G.X) ≫
        fibreProjection φ G.X =
      e.inv.hom.hom.left ≫ fibreProjection (ψ.comp φ) G.X := by
  change (e.inv ≫ (changeBaseGroupCompOfEq φ ψ rfl).hom.app G).hom.hom.left ≫ _ = _
  rw [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    changeBaseGroupCompOfEq_projection φ ψ rfl]

private theorem refinedFibreIntegralProjection {R : Type u} [CommRing R]
    (α : R →+* A) (φ : A →+* B) (ψ : B →+* C) {κ : R →+* B}
    (h : φ.comp α = κ) (G : Grp (SchemeOverRing R)) {J : Grp (SchemeOverRing C)}
    (e : (changeBaseGroup (ψ.comp φ)).obj ((changeBaseGroup α).obj G) ≅ J) :
    let X := (changeBase α).obj G.X
    (refinedFibreIso φ ψ e).inv.hom.hom.left ≫ fibreProjection ψ ((changeBase φ).obj X) ≫
        (groupComparison α φ h G).inv.hom.hom.left ≫ fibreProjection κ G.X =
      e.inv.hom.hom.left ≫ fibreProjection (ψ.comp φ) X ≫ fibreProjection α G.X := by
  intro X
  rw [groupComparison_inv_projection α φ h G]
  have hcomp : (refinedFibreIso φ ψ e).inv.hom.hom.left ≫
      fibreProjection ψ ((changeBase φ).obj X) ≫ fibreProjection φ X =
        e.inv.hom.hom.left ≫ fibreProjection (ψ.comp φ) X :=
    refinedFibreIso_inv_projection φ ψ e
  calc
    _ = ((refinedFibreIso φ ψ e).inv.hom.hom.left ≫ fibreProjection ψ ((changeBase φ).obj X) ≫
        fibreProjection φ X) ≫ fibreProjection α G.X := by
      simp only [Category.assoc] <;> rfl
    _ = _ := by rw [hcomp, Category.assoc]

private theorem refinedFibreIso_inclusion (φ : A →+* B) (ψ : B →+* C)
    {G H : Grp (SchemeOverRing A)} {G' H' : Grp (SchemeOverRing C)} (i : H ⟶ G) (j : H' ⟶ G')
    (eG : (changeBase (ψ.comp φ)).mapGrp.obj G ≅ G')
    (eH : (changeBase (ψ.comp φ)).mapGrp.obj H ≅ H')
    (h : (changeBase (ψ.comp φ)).mapGrp.map i ≫ eG.hom = eH.hom ≫ j) :
    (changeBase ψ).mapGrp.map ((changeBase φ).mapGrp.map i) ≫ (refinedFibreIso φ ψ eG).hom =
      (refinedFibreIso φ ψ eH).hom ≫ j := by
  let c := changeBaseGroupCompOfEq φ ψ rfl
  change ((changeBase φ).mapGrp ⋙ (changeBase ψ).mapGrp).map i ≫ (c.inv.app G ≫ eG.hom) =
    (c.inv.app H ≫ eH.hom) ≫ j
  rw [← Category.assoc, c.inv.naturality i, Category.assoc, h, Category.assoc]

private theorem appTop_pullUnit_inv {X Y Z : Scheme.{u}} (t : X ⟶ Y) (g : Z ⟶ X)
    (c : Γ(Y, ⊤)ˣ) :
    g.appTop ((Units.map t.appTop.hom.toMonoidHom c)⁻¹).val =
      (g ≫ t).appTop (c⁻¹ : Γ(Y, ⊤)ˣ) := by
  rw [← map_inv (Units.map t.appTop.hom.toMonoidHom) c, Scheme.Hom.comp_appTop]
  rfl

private theorem appTop_eq_of_factorizations {W X Y Z : Scheme.{u}}
    (f : W ⟶ Z) (g : W ⟶ X) (h : W ⟶ Y) (a : X ⟶ Z) (p : X ⟶ Y)
    (hf : f = g ≫ a) (hh : g ≫ p = h) (c : Γ(Y, ⊤)) (d : Γ(Z, ⊤))
    (hd : a.appTop d = p.appTop c) : f.appTop d = h.appTop c := by
  rw [hf, ← hh, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, hd]

end Refinement

section Assembly

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralMarkedOppositeBorel (RelativeBorel FieldComparison relativeGroup integerMap)
open Specs.SpreadProjectiveRightTorsor (HasLocalSections)
open Specs.FlagCohomology (FlagKernelPair)
open Specs.CharacterDescent (Character)
open Specs.IntegralSemisimpleModel (Integers)

private abbrev refinedTorsor {B : Type u} [CommRing B] {D : BasedRootDatum.{u}} {I : Specs.IntegralSemisimpleModel.Model D}
    {m : ℕ} (H : RelativeBorel I m) (r : BaseRing.{u} m →+* B)
    (Y : SchemeOverRing B) (hY : Smooth Y.hom) (hP : IsProjectiveOver Y)
    (q : ((changeBaseGroup r).obj (relativeGroup I m)).X ⟶ Y)
    (hq : Smooth q.left) (hs : Surjective q.left)
    (hpair : IsPullback prod.fst (rightMultiply ((changeBaseGroup r).map H.inclusion)) q q)
    (hsec : HasLocalSections q) : Specs.RelativeCovarianceLine.Torsor B :=
  baseChangedTorsor r H.inclusion H.closed
    (baseChange_structureProperty @Smooth (integerMap m) I.group.X I.smooth) H.smooth
    (affine_changeBase (integerMap m) I.group.X I.affine) H.affine H.character
    H.characterMultiplicative Y hY hP q hq hs hpair hsec

private theorem exists_identifiedFibre {B k : Type u} [CommRing B] [Field k]
    {D : BasedRootDatum.{u}} {I : Specs.IntegralSemisimpleModel.Model D} {m : ℕ} {w : D.X}
    {H : RelativeBorel I m} {τ : BaseRing.{u} m →+* k} (F : FieldComparison I τ w H)
    (ψ : B →+* k) (M : Model B) (integersToBase : Integers.{u} →+* B)
    (e : (changeBaseGroup integersToBase).obj I.group ≅ M.group)
    (eG : (changeBaseGroup ψ).obj M.group ≅ F.realization.pinned.pair.G.val)
    (eH : (changeBaseGroup ψ).obj M.borel ≅ F.pair.negative.group)
    (hi : (changeBaseGroup ψ).map M.inclusion ≫ eG.hom = eH.hom ≫ F.pair.negative.inclusion)
    (hc : let χ : Character F.pair.torus.group :=
        F.torus_eq.symm ▸ Additive.toMul (F.realization.datumIso.val.weightEquiv w)
      let b : F.pair.negative.group.X.left ⟶ M.borel.X.left :=
        eH.inv.hom.hom.left ≫ fibreProjection ψ M.borel.X
      b.appTop (M.character⁻¹).val = inverseCharacterCoordinate F.projection χ)
    (he : eG.inv.hom.hom.left ≫ fibreProjection ψ M.group.X ≫ e.inv.hom.hom.left ≫
        fibreProjection integersToBase I.group.X =
      F.integralIso.inv.hom.hom.left ≫ integralFibreProjection I.group) :
    ∃ F' : FibreIdentification ψ M D w, Nonempty (MarkedIntegralFibre ψ M I integersToBase e F') := by
  let G := F.realization.pinned.pair.G
  let χ : Character F.pair.torus.group := F.torus_eq.symm ▸ Additive.toMul (F.realization.datumIso.val.weightEquiv w)
  obtain ⟨⟨Q⟩, _⟩ := HomogeneousQuotient.homogeneousQuotient k G F.pair.negative
  have hQ : FlagKernelPair Q := HomogeneousQuotient.quotientPullback Q
  obtain ⟨v, a, ha, hv, hact⟩ := exists_flagIso_of_fibreSubgroup ψ M F.pair eG eH hi Q hQ
  let F' : FibreIdentification ψ M D w :=
    { additive := F.additive
      realization := F.realization
      pair := F.pair
      torus_eq := F.torus_eq
      positive_eq := F.positive_eq
      projection := F.projection
      presentation := Q
      kernelPair := hQ
      flagAction := a
      flagAction_quotient := ha
      groupIso := eG
      borelIso := eH
      flagIso := v
      inclusion_eq := hi
      quotient_eq := hv
      action_eq := hact
      character_eq := hc
      lineIso := fieldLineComparison M.torsor ψ Q F.projection χ hQ eG eH hi v hv hc }
  exact ⟨F', ⟨{
    groupIso := F.integralIso
    torusIso := F.torusIso
    rootCoordinate := F.rootCoordinate
    group_eq := he
    torus_eq := F.torus_marking
    pin_eq := F.simple_marking
    weight_eq := F.weight_marking
    root_eq := F.root_marking }⟩⟩

private def transportFibreIso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (ψ : B →+* C) {G : Grp (SchemeOverRing A)} {G' : Grp (SchemeOverRing B)}
    {J : Grp (SchemeOverRing C)} (t : (changeBaseGroup r).obj G ≅ G')
    (e : (changeBaseGroup (ψ.comp r)).obj G ≅ J) : (changeBaseGroup ψ).obj G' ≅ J :=
  ((changeBaseGroup ψ).mapIso t).symm ≪≫ refinedFibreIso r ψ e

private theorem transportFibreIso_inv_projection {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (ψ : B →+* C) {G : Grp (SchemeOverRing A)} {G' : Grp (SchemeOverRing B)}
    {J : Grp (SchemeOverRing C)} (t : (changeBaseGroup r).obj G ≅ G')
    (e : (changeBaseGroup (ψ.comp r)).obj G ≅ J) :
    (transportFibreIso r ψ t e).inv.hom.hom.left ≫ fibreProjection ψ G'.X =
      (refinedFibreIso r ψ e).inv.hom.hom.left ≫ fibreProjection ψ ((changeBase r).obj G.X) ≫
        t.hom.hom.hom.left := by
  let f := t.hom.hom.hom
  change ((refinedFibreIso r ψ e).inv ≫ (changeBaseGroup ψ).map t.hom).hom.hom.left ≫
    fibreProjection ψ G'.X = _
  rw [Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  exact congrArg ((refinedFibreIso r ψ e).inv.hom.hom.left ≫ ·) (changeBaseMap_isPullback ψ f).w

private theorem transportFibreIso_inclusion {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (ψ : B →+* C) {G H : Grp (SchemeOverRing A)} {G' H' : Grp (SchemeOverRing B)}
    {J K : Grp (SchemeOverRing C)} (i : H ⟶ G) (i' : H' ⟶ G') (j : K ⟶ J)
    (tG : (changeBaseGroup r).obj G ≅ G') (tH : (changeBaseGroup r).obj H ≅ H')
    (eG : (changeBaseGroup (ψ.comp r)).obj G ≅ J) (eH : (changeBaseGroup (ψ.comp r)).obj H ≅ K)
    (h : (changeBaseGroup r).map i ≫ tG.hom = tH.hom ≫ i')
    (he : (changeBaseGroup (ψ.comp r)).map i ≫ eG.hom = eH.hom ≫ j) :
    (changeBaseGroup ψ).map i' ≫ (transportFibreIso r ψ tG eG).hom =
      (transportFibreIso r ψ tH eH).hom ≫ j := by
  let F := changeBaseGroup ψ
  have hi : i' ≫ tG.inv = tH.inv ≫ (changeBaseGroup r).map i :=
    invert_comparison tH tG _ _ h.symm
  have h' := refinedFibreIso_inclusion r ψ i j eG eH he
  change F.map i' ≫ F.map tG.inv ≫ (refinedFibreIso r ψ eG).hom =
    (F.map tH.inv ≫ (refinedFibreIso r ψ eH).hom) ≫ j
  rw [← Category.assoc, ← F.map_comp, hi, F.map_comp, Category.assoc, h', Category.assoc]

private theorem pullbackFunction_of_iso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (ψ : B →+* C) {G : Grp (SchemeOverRing A)} {G' : Grp (SchemeOverRing B)}
    {J : Grp (SchemeOverRing C)} (t : (changeBaseGroup r).obj G ≅ G')
    (e : (changeBaseGroup (ψ.comp r)).obj G ≅ J)
    (c : Γ(G.X.left, ⊤)) (d : Γ(G'.X.left, ⊤))
    (hd : let a : ((changeBase r).obj G.X).left ⟶ G'.X.left := t.hom.hom.hom.left
      a.appTop d = (fibreProjection r G.X).appTop c) :
    let b : J.X.left ⟶ G'.X.left :=
      (transportFibreIso r ψ t e).inv.hom.hom.left ≫ fibreProjection ψ G'.X
    b.appTop d = (e.inv.hom.hom.left ≫ fibreProjection (ψ.comp r) G.X).appTop c := by
  intro b
  let a : ((changeBase r).obj G.X).left ⟶ G'.X.left := t.hom.hom.hom.left
  let g : J.X.left ⟶ ((changeBase r).obj G.X).left :=
    (refinedFibreIso r ψ e).inv.hom.hom.left ≫ fibreProjection ψ ((changeBase r).obj G.X)
  have h : b = g ≫ a :=
    (transportFibreIso_inv_projection r ψ t e).trans
      (Category.assoc (refinedFibreIso r ψ e).inv.hom.hom.left
        (fibreProjection ψ ((changeBase r).obj G.X)) a).symm
  let p : ((changeBase r).obj G.X).left ⟶ G.X.left := fibreProjection r G.X
  let f : J.X.left ⟶ G.X.left := e.inv.hom.hom.left ≫ fibreProjection (ψ.comp r) G.X
  have hg : g ≫ p = f :=
    (Category.assoc (refinedFibreIso r ψ e).inv.hom.hom.left
      (fibreProjection ψ ((changeBase r).obj G.X)) p).trans (refinedFibreIso_inv_projection r ψ e)
  exact appTop_eq_of_factorizations b g f a p h hg c d hd

private theorem transportedFibreCharacter {B k : Type u} [CommRing B] [Field k]
    {D : BasedRootDatum.{u}} {I : Specs.IntegralSemisimpleModel.Model D} {m : ℕ} {w : D.X}
    (H : RelativeBorel I m) (r : BaseRing.{u} m →+* B) (ψ : B →+* k)
    (F : FieldComparison I (ψ.comp r) w H) (M : Model B)
    (tH : (changeBaseGroup r).obj H.borel ≅ M.borel)
    (hc : let b : ((changeBase r).obj H.borel.X).left ⟶ M.borel.X.left := tH.hom.hom.hom.left
      b.appTop (M.character⁻¹).val = (fibreProjection r H.borel.X).appTop (H.character⁻¹).val) :
    let eH := transportFibreIso r ψ tH F.borelIso
    let b : F.pair.negative.group.X.left ⟶ M.borel.X.left :=
      eH.inv.hom.hom.left ≫ fibreProjection ψ M.borel.X
    let χ : Character F.pair.torus.group :=
      F.torus_eq.symm ▸ Additive.toMul (F.realization.datumIso.val.weightEquiv w)
    b.appTop (M.character⁻¹).val = inverseCharacterCoordinate F.projection χ :=
  (pullbackFunction_of_iso r ψ tH F.borelIso (H.character⁻¹).val (M.character⁻¹).val hc).trans
    F.character_eq

private theorem transportedIntegralProjection {B k : Type u} [CommRing B] [Field k]
    {D : BasedRootDatum.{u}} {I : Specs.IntegralSemisimpleModel.Model D} {m : ℕ} {w : D.X}
    (H : RelativeBorel I m) (r : BaseRing.{u} m →+* B) (ψ : B →+* k)
    (F : FieldComparison I (ψ.comp r) w H) (M : Model B)
    (integersToBase : Integers.{u} →+* B) (hr : r.comp (integerMap m) = integersToBase)
    (tG : (changeBaseGroup r).obj (relativeGroup I m) ≅ M.group) :
    let e := groupComparison (integerMap m) r hr I.group ≪≫ tG
    let eG := transportFibreIso r ψ tG F.groupIso
    eG.inv.hom.hom.left ≫ fibreProjection ψ M.group.X ≫ e.inv.hom.hom.left ≫
        fibreProjection integersToBase I.group.X = F.integralIso.inv.hom.hom.left ≫ integralFibreProjection I.group := by
  let e := groupComparison (integerMap m) r hr I.group
  let eG := transportFibreIso r ψ tG F.groupIso
  let t := (Grp.forget _ ⋙ Over.forget _).mapIso tG
  let g := (refinedFibreIso r ψ F.groupIso).inv.hom.hom.left ≫
        fibreProjection ψ ((changeBase r).obj (relativeGroup I m).X)
  have h : eG.inv.hom.hom.left ≫ fibreProjection ψ M.group.X = g ≫ t.hom :=
    (transportFibreIso_inv_projection r ψ tG F.groupIso).trans (Category.assoc _ _ _).symm
  change eG.inv.hom.hom.left ≫ fibreProjection ψ M.group.X ≫ (tG.inv ≫ e.inv).hom.hom.left ≫
    fibreProjection integersToBase I.group.X = _
  rw [Grp.comp_hom_hom, Over.comp_left]
  calc
    _ = (eG.inv.hom.hom.left ≫ fibreProjection ψ M.group.X) ≫ t.inv ≫ e.inv.hom.hom.left ≫
        fibreProjection integersToBase I.group.X := by simp only [Category.assoc] <;> rfl
    _ = g ≫ e.inv.hom.hom.left ≫ fibreProjection integersToBase I.group.X := by
      rw [h, Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      change ((refinedFibreIso r ψ F.groupIso).inv.hom.hom.left ≫ _) ≫ _ = _
      rw [Category.assoc]
      exact (refinedFibreIntegralProjection (integerMap m) r ψ hr I.group F.groupIso).trans
        F.group_composition

private theorem exists_identifiedFibreAfterRestriction {B k : Type u} [CommRing B] [Field k]
    {D : BasedRootDatum.{u}} {I : Specs.IntegralSemisimpleModel.Model D} {m : ℕ} {w : D.X}
    (H : RelativeBorel I m) (r : BaseRing.{u} m →+* B) (ψ : B →+* k)
    (F : FieldComparison I (ψ.comp r) w H) (M : Model B)
    (integersToBase : Integers.{u} →+* B) (hr : r.comp (integerMap m) = integersToBase)
    (tG : (changeBaseGroup r).obj (relativeGroup I m) ≅ M.group)
    (tH : (changeBaseGroup r).obj H.borel ≅ M.borel)
    (hi : (changeBaseGroup r).map H.inclusion ≫ tG.hom = tH.hom ≫ M.inclusion)
    (hc : let b : ((changeBase r).obj H.borel.X).left ⟶ M.borel.X.left := tH.hom.hom.hom.left
      b.appTop (M.character⁻¹).val = (fibreProjection r H.borel.X).appTop (H.character⁻¹).val) :
    let e := groupComparison (integerMap m) r hr I.group ≪≫ tG
    ∃ F' : FibreIdentification ψ M D w, Nonempty (MarkedIntegralFibre ψ M I integersToBase e F') := by
  let e := groupComparison (integerMap m) r hr I.group
  let eG := transportFibreIso r ψ tG F.groupIso
  let eH := transportFibreIso r ψ tH F.borelIso
  refine exists_identifiedFibre F ψ M integersToBase (e ≪≫ tG) eG eH
    (transportFibreIso_inclusion r ψ H.inclusion M.inclusion F.pair.negative.inclusion tG tH
      F.groupIso F.borelIso hi F.inclusion_eq)
    (transportedFibreCharacter H r ψ F M tH hc)
    (transportedIntegralProjection H r ψ F M integersToBase hr tG)

private theorem markedModelsAfterSpreading {B : Type u} [CommRing B]
    {D : BasedRootDatum.{u}} {I : Specs.IntegralSemisimpleModel.Model D} {m : ℕ} {w : D.X}
    (H : RelativeBorel I m)
    (hF : ∀ (k : Type u) [Field k] (φ : BaseRing.{u} m →+* k), Nonempty (FieldComparison I φ w H))
    (r : BaseRing.{u} m →+* B) (integersToBase : Integers.{u} →+* B)
    (hr : r.comp (integerMap m) = integersToBase)
    (Y : SchemeOverRing B) (hY : Smooth Y.hom) (hf : Flat Y.hom) (hp : IsProjectiveOver Y)
    (q : ((changeBaseGroup r).obj (relativeGroup I m)).X ⟶ Y)
    (hq : Smooth q.left) (hs : Surjective q.left)
    (hpair : IsPullback prod.fst (rightMultiply ((changeBaseGroup r).map H.inclusion)) q q)
    (hsec : HasLocalSections q) :
    ∃ M : Model B, M.IsLineBundle ∧ M.HasEquivariantLine ∧
      ∃ e : (changeBaseGroup integersToBase).obj I.group ≅ M.group,
        ∀ (k : Type u) [Field k] (ψ : B →+* k),
          ∃ F' : FibreIdentification ψ M D w, Nonempty (MarkedIntegralFibre ψ M I integersToBase e F') := by
  let T := refinedTorsor H r Y hY hp q hq hs hpair hsec
  let : Smooth T.projection.left := T.smoothProjection
  let : Surjective T.projection.left := T.surjectiveProjection
  obtain ⟨a, ha⟩ := exists_quotientAction T.inclusion T.projection T.kernelPair
  let M : Model B := modelOfTorsor T hf hp a ha
  let tG : (changeBaseGroup r).obj (relativeGroup I m) ≅ M.group := Iso.refl _
  let tH : (changeBaseGroup r).obj H.borel ≅ M.borel := Iso.refl _
  let e := groupComparison (integerMap m) r hr I.group ≪≫ tG
  obtain ⟨hLine, hEquiv⟩ := modelOfTorsor_line T hf hp a ha
  refine ⟨M, hLine, hEquiv, e, ?_⟩
  intro k _ ψ
  obtain ⟨F⟩ := hF k (ψ.comp r)
  refine exists_identifiedFibreAfterRestriction H r ψ F M integersToBase hr tG tH ?_ ?_
  · change (changeBaseGroup r).map H.inclusion ≫ 𝟙 _ = 𝟙 _ ≫ (changeBaseGroup r).map H.inclusion
    rw [Category.comp_id, Category.id_comp]
  · exact (appTop_pullUnit_inv (fibreProjection r H.borel.X) (𝟙 _) H.character).trans (by
      rw [Category.id_comp])

/-- The same arithmetic quotient and inverse-character line give the marked
opposite-Borel flags over the rational field and at all non-inverted primes. -/
theorem integralFlagGeometry : Statement.{u} := by
  intro D hss hspan w
  obtain ⟨_, ⟨I⟩⟩ := Classification.IntegralSemisimpleModel.integralSemisimpleModel D hss hspan
  obtain ⟨m, hm, H, hF⟩ := IntegralMarkedOppositeBorel.exists_integralMarkedOppositeBorel D hss hspan I w
  obtain ⟨F⟩ := hF RationalField.{u} (rationalMap hm)
  obtain ⟨Y, hY, ⟨V, hV, hModule, hFinite, j, hj⟩, q, hq, hs, hpair, hsec⟩ :=
    exists_genericQuotient ((changeBaseGroup (rationalMap hm)).map H.inclusion)
      F.pair F.groupIso F.borelIso F.inclusion_eq
  let G := relativeGroup I m
  have hG : Smooth G.X.hom := baseChange_structureProperty @Smooth (integerMap m) I.group.X I.smooth
  have hGa : IsAffine G.X.left := affine_changeBase (integerMap m) I.group.X I.affine
  obtain ⟨n, hn, _, r, hr, _, Y', hY', hf, hp, q', hq', hs', hpair', hsec', _⟩ :=
    SpreadProjectiveRightTorsor.spreadProjectiveRightTorsor m hm G H.borel H.inclusion
      hGa H.affine hG H.smooth H.closed Y hY V hV hModule hFinite j hj q hq hs hpair hsec
  obtain ⟨M, hL, hEq, e, hField⟩ :=
    markedModelsAfterSpreading H hF r (integerMap n) hr Y' hY' hf hp q' hq' hs' hpair' hsec'
  exact ⟨{
    m := n
    nonzero := hn
    model := M
    integralGroup := I
    fromIntegers := e
    lineBundle := hL
    lineEquivariant := hEq
    fieldFibre := hField }⟩

end Assembly

end

end LinearAlgebraicGroups.Representation.IntegralFlagGeometry
