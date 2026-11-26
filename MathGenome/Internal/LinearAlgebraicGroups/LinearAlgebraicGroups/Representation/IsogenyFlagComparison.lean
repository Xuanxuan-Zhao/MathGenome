import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.IsogenyFlagComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.IsogenyFlagComparison

open _root_.LinearAlgebraicGroups.Specs
open Specs.IsogenyFlagComparison
open Specs.FlagLineBundle
open Specs.QuotientEmbedding (Presentation)
open Specs.CentralIsogenies (IsCentralIsogeny characterPullback)
open Specs.NormalizerLatticeAction (SplitImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private flat_of_surjective_torus_map pushforwardNormalizes whiskerRight_isPullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private conjugateLe_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private forget_comp schemeKernel_eq_iff characterValue_pullback
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private kBorel_smooth_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private projection_eq_iff represent_of_fppf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

open private compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

open private torus_of_split torus_multiplicativeType
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private whiskerLeft_pullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
open private fibreTorsor splitFibrePoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private apply_conjugateFamily_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

variable {k : Type u} [Field k]

private theorem descend {X Y Z : SchemeOver k} (p : X ⟶ Y) (s : X ⟶ Z)
    [Flat p.left] [Surjective p.left] [QuasiCompact p.left]
    (hs : ∀ ⦃A : SchemeOver k⦄ (x y : A ⟶ X), x ≫ p = y ≫ p → x ≫ s = y ≫ s) :
    ∃ d : Y ⟶ Z, p ≫ d = s := by
  have h (A : Scheme) (x y : A ⟶ X.left) (e : x ≫ p.left = y ≫ p.left) :
      x ≫ s.left = y ≫ s.left := by
    let X' : SchemeOver k := Over.mk (x ≫ X.hom)
    let x' : X' ⟶ X := Over.homMk x
    let y' : X' ⟶ X := Over.homMk y (by
      change y ≫ X.hom = x ≫ X.hom
      rw [← Over.w p, ← Category.assoc, ← Category.assoc, e])
    exact congrArg Over.Hom.left (hs x' y' (Over.OverMorphism.ext e))
  let d := EffectiveEpi.desc p.left s.left (h _)
  have hd : p.left ≫ d = s.left := EffectiveEpi.fac p.left s.left (h _)
  have dw : d ≫ Z.hom = Y.hom := (cancel_epi p.left).mp (by
    rw [← Category.assoc, hd, Over.w s, Over.w p])
  exact ⟨Over.homMk d dw, Over.OverMorphism.ext hd⟩

private theorem flat_of_surjective_group_hom (A B : AffineAlgebraicGroup k)
    (f : A.val ⟶ B.val) [Surjective f.hom.hom.left] [IsReduced B.val.X.left] :
    Flat f.hom.hom.left := by
  obtain ⟨I, q, i, ⟨h, hflat, _, _, _, hclosed⟩, _, _⟩ :=
    LinearAlgebraicGroups.schemeImageFactorization A B f
  have hleft : q.hom.hom.left ≫ i.hom.hom.left = f.hom.hom.left :=
    congrArg (fun p : A.val ⟶ B.val ↦ p.hom.hom.left) h
  letI : Surjective (q.hom.hom.left ≫ i.hom.hom.left) := hleft.symm ▸ inferInstance
  letI : Surjective i.hom.hom.left := Surjective.of_comp q.hom.hom.left i.hom.hom.left
  letI := hclosed
  letI := hflat
  letI : IsIso i.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  rw [← hleft]
  infer_instance

private theorem subgroup_inverse_image {G H : GroupScheme k}
    {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    (f : G ⟶ H) (b : B.group ⟶ C.group) (hb : b ≫ C.inclusion = B.inclusion ≫ f)
    [Flat b.hom.hom.left] [Surjective b.hom.hom.left] [QuasiCompact b.hom.hom.left]
    {N : ClosedSubgroup G} (hn : IsSchemeKernel f N)
    (j : N.group ⟶ B.group) (hj : j ≫ B.inclusion = N.inclusion) :
    IsPullback B.inclusion.hom.hom b.hom.hom f.hom.hom C.inclusion.hom.hom := by
  let Bi := B.inclusion.hom.hom
  let Ci := C.inclusion.hom.hom
  let q := b.hom.hom
  let F := f.hom.hom
  letI : IsClosedImmersion Bi.left := B.isClosedImmersion
  letI : IsClosedImmersion Ci.left := C.isClosedImmersion
  haveI : Mono Bi := Over.mono_of_mono_left Bi
  haveI : Mono Ci := Over.mono_of_mono_left Ci
  have hcomm : Bi ≫ F = q ≫ Ci := by rw [← forget_comp, ← forget_comp, hb]
  have liftB {S : SchemeOver k} (g : S ⟶ G.X) (c : S ⟶ C.group.X)
      (hgc : g ≫ F = c ≫ Ci) : ∃ a : S ⟶ B.group.X, a ≫ Bi = g := by
    let t := pullback.snd q c
    let v := pullback.fst q c
    have hp := (IsPullback.of_hasPullback q c).map (Over.forget _)
    letI : Flat t.left := MorphismProperty.of_isPullback hp (inferInstanceAs (Flat q.left))
    letI : Surjective t.left :=
      MorphismProperty.of_isPullback hp (inferInstanceAs (Surjective q.left))
    letI : QuasiCompact t.left :=
      MorphismProperty.of_isPullback hp (inferInstanceAs (QuasiCompact q.left))
    have ht : (v ≫ Bi) ≫ F = (t ≫ g) ≫ F := by
      rw [Category.assoc, hcomm, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, hgc]
    obtain ⟨n, he⟩ := (schemeKernel_eq_iff hn (v ≫ Bi) (t ≫ g)).1 ht
    let w := v * (n ≫ j.hom.hom)
    have hw : w ≫ Bi = t ≫ g := by
      change (v * (n ≫ j.hom.hom)) ≫ Bi = _
      rw [MonObj.mul_comp, Category.assoc, ← forget_comp, hj, he, mul_inv_cancel_left]
    obtain ⟨a, ha⟩ := descend t w (by
      intro A x y hxy
      apply (cancel_mono Bi).mp
      simpa only [Category.assoc, hw] using congrArg (fun a ↦ a ≫ g) hxy)
    haveI : Epi t := Over.epi_of_epi_left t
    refine ⟨a, (cancel_epi t).mp ?_⟩
    rw [← Category.assoc, ha, hw]
  have ex (c : PullbackCone F Ci) :
      ∃ a : c.pt ⟶ B.group.X, a ≫ Bi = c.fst := liftB c.fst c.snd c.condition
  choose a ha using ex
  refine IsPullback.of_isLimit' ⟨hcomm⟩
    (PullbackCone.IsLimit.mk hcomm a ha (fun c ↦ ?_) (fun c m hm _ ↦ ?_))
  · apply (cancel_mono Ci).mp
    rw [Category.assoc, ← hcomm, ← Category.assoc, ha, c.condition]
  · exact (cancel_mono Bi).mp (hm.trans (ha c).symm)

/-- A corresponding opposite Borel is the full scheme inverse image under
the central isogeny. -/
theorem oppositeBorelInverseImage : OppositeBorelInverseImage.{u} := by
  intro k _ G' G P' P f hf r
  let B' := Unipotent.closedSubgroupAlgebraicGroup P'.negative
  let B := Unipotent.closedSubgroupAlgebraicGroup P.negative
  let b := r.borel.hom.hom.left
  have hc := congrArg (fun j : P'.negative.group ⟶ G.val ↦ j.hom.hom.left) r.borel_comm
  letI : IsClosedImmersion P'.negative.inclusion.hom.hom.left := P'.negative.isClosedImmersion
  letI : IsClosedImmersion P.negative.inclusion.hom.hom.left := P.negative.isClosedImmersion
  letI : IsFinite f.hom.hom.left := hf.1
  haveI : IsFinite (b ≫ P.negative.inclusion.hom.hom.left) := by
    rw [show b ≫ P.negative.inclusion.hom.hom.left =
      P'.negative.inclusion.hom.hom.left ≫ f.hom.hom.left from hc]
    infer_instance
  letI : IsFinite b := IsFinite.of_comp b P.negative.inclusion.hom.hom.left
  letI : Surjective b := r.borel_surjective
  letI : Smooth B.val.X.hom := (kBorel_smooth_connected G P.negative P.negativeBorel).1
  letI : IsReduced B.val.X.left := isReduced_of_smooth_over_field B.val.X.hom
  letI : Flat b := flat_of_surjective_group_hom B' B r.borel
  obtain ⟨N, hN, hz⟩ := hf.2.2.2
  obtain ⟨jT, hjT⟩ :=
    Classification.CentralIsogenies.kernel_le_maximalTorus RootData.SchemeCentre.schemeCentre
      G' P'.reductive P'.torus P'.split P'.maximal N hz
  obtain ⟨jB, hjB⟩ := P'.inNegative
  exact subgroup_inverse_image f r.borel r.borel_comm hN (jT ≫ jB)
    (by rw [Category.assoc, hjB, hjT])

private theorem group_hom_finitePresentation (A B : AffineAlgebraicGroup k)
    (f : A.val ⟶ B.val) [IsFinite f.hom.hom.left] :
    LocallyOfFinitePresentation f.hom.hom.left := by
  letI : LocallyOfFiniteType B.val.X.hom := B.property.2.1
  letI : IsLocallyNoetherian B.val.X.left := LocallyOfFiniteType.isLocallyNoetherian B.val.X.hom
  infer_instance

private theorem quotient_epi {G : GroupScheme k} (B : ClosedSubgroup G) :
    Epi (rightQuotientProjection B) := by
  letI : Sheaf.IsLocallySurjective (rightQuotientProjection B) :=
    LinearAlgebraicGroups.rightQuotientLocalLifts B
  infer_instance

/-- The map induced by the central isogeny on the right fppf quotients is
represented by an isomorphism of flag schemes. -/
theorem flagQuotientComparison : FlagQuotientComparison.{u} := by
  intro k _ G' G P' P f hf r Q' Q
  let F := f.hom.hom
  let q := F ≫ Q.projection
  have hp := oppositeBorelInverseImage f hf r
  letI : IsFinite F.left := hf.1
  letI : Flat F.left := hf.2.1
  letI : Surjective F.left := hf.2.2.1
  letI : LocallyOfFinitePresentation F.left := group_hom_finitePresentation G' G f
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  letI : Flat q.left := inferInstanceAs (Flat (F.left ≫ Q.projection.left))
  letI : Surjective q.left := inferInstanceAs (Surjective (F.left ≫ Q.projection.left))
  letI : LocallyOfFinitePresentation q.left :=
    inferInstanceAs (LocallyOfFinitePresentation (F.left ≫ Q.projection.left))
  have hcomm : ∀ (T : SchemeOver k) (g h : T ⟶ G'.val.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections P'.negative T := by
    intro T g h
    simp only [q, ← Category.assoc]
    rw [projection_eq_iff]
    change (∃ b : T ⟶ P.negative.group.X,
        b ≫ P.negative.inclusion.hom.hom = (g ≫ F)⁻¹ * (h ≫ F)) ↔
      ∃ b' : T ⟶ P'.negative.group.X, b' ≫ P'.negative.inclusion.hom.hom = g⁻¹ * h
    have he : (g⁻¹ * h) ≫ F = (g ≫ F)⁻¹ * (h ≫ F) := by
      rw [MonObj.mul_comp, GrpObj.inv_comp]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨hp.lift (g⁻¹ * h) b (he.trans hb.symm), hp.lift_fst _ _ _⟩
    · rintro ⟨b, hb⟩
      refine ⟨b ≫ r.borel.hom.hom, ?_⟩
      rw [Category.assoc, ← hp.w, ← Category.assoc, hb, he]
  obtain ⟨v, hv⟩ := represent_of_fppf P'.negative q hcomm
  let e := compareRepresentatives Q' v
  have he : Q'.projection ≫ e.hom = q := compareRepresentatives_projection Q' q v hv
  have hmap :
      rightQuotientProjection P'.negative ≫ rightQuotientMap f r.borel r.borel_comm.symm =
        (fppfOver k).uliftYoneda.map F ≫ rightQuotientProjection P.negative := by
    apply (sheafToPresheaf _ _).map_injective
    ext T ⟨g⟩
    exact rightQuotientMapOnLifts f r.borel r.borel_comm.symm (T := T.unop) g
  refine ⟨e, he, ?_⟩
  haveI := quotient_epi P'.negative
  let Y := (fppfOver k).uliftYoneda.{u + 1}
  let q' := rightQuotientProjection P'.negative
  let φ := rightQuotientMap f r.borel r.borel_comm.symm
  apply (cancel_epi (q' ≫ Q'.quotientIso.hom)).mp
  change (q' ≫ Q'.quotientIso.hom) ≫ Q'.quotientIso.inv ≫ φ ≫ Q.quotientIso.hom =
    (q' ≫ Q'.quotientIso.hom) ≫ Y.map e.hom
  calc
    _ = q' ≫ φ ≫ Q.quotientIso.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = Y.map F ≫ rightQuotientProjection P.negative ≫ Q.quotientIso.hom := by
      rw [← Category.assoc, show q' ≫ φ = Y.map F ≫ rightQuotientProjection P.negative from hmap,
        Category.assoc]
    _ = Y.map F ≫ Y.map Q.projection := by rw [Q.quotientProjection]
    _ = (q' ≫ Q'.quotientIso.hom) ≫ Y.map e.hom := by
      rw [show q' ≫ Q'.quotientIso.hom = Y.map Q'.projection from Q'.quotientProjection,
        ← Functor.map_comp, ← Functor.map_comp, he]

private theorem projection_commutes
    {G' G : AffineAlgebraicGroup k} {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    {f : G'.val ⟶ G.val} (r : Restrictions f P' P)
    (p' : BorelProjection P') (p : BorelProjection P) :
    r.borel ≫ p.projection = p'.projection ≫ r.torus := by
  letI : IsClosedImmersion P.negative.inclusion.hom.hom.left := P.negative.isClosedImmersion
  letI : Mono P.negative.inclusion.hom.hom := Over.mono_of_mono_left _
  have hs : p'.inclusion ≫ r.borel = r.torus ≫ p.inclusion := by
    apply Grp.hom_ext
    apply (cancel_mono P.negative.inclusion.hom.hom).mp
    have he : (p'.inclusion ≫ r.borel) ≫ P.negative.inclusion =
        (r.torus ≫ p.inclusion) ≫ P.negative.inclusion := by
      calc
        _ = P'.torus.inclusion ≫ f := by
          rw [Category.assoc, r.borel_comm, ← Category.assoc, p'.inclusion_comp]
        _ = _ := by rw [Category.assoc, p.inclusion_comp, r.torus_comm]
    exact congrArg (fun a : P'.torus.group ⟶ G.val ↦ a.hom.hom) he
  let B' := Unipotent.closedSubgroupAlgebraicGroup P'.negative
  let U' := Unipotent.closedSubgroupAlgebraicGroup (G := B') p'.radical
  let T := Unipotent.closedSubgroupAlgebraicGroup P.torus
  let h := r.borel ≫ p.projection
  have hk : p'.radical.inclusion ≫ h = 0 :=
    Unipotent.homFromUnipotentToMultiplicativeType U' T _
      p'.isRadical.2.1 (torus_multiplicativeType (torus_of_split P.split))
  have hsection : p'.inclusion ≫ h = r.torus := by
    change p'.inclusion ≫ (r.borel ≫ p.projection) = r.torus
    rw [← Category.assoc, hs, Category.assoc, p.section_projection, Category.comp_id]
  apply Grp.hom_ext
  change h.hom.hom = p'.projection.hom.hom ≫ r.torus.hom.hom
  let v := p'.projection.hom.hom ≫ p'.inclusion.hom.hom
  have hv : v ≫ p'.projection.hom.hom = p'.projection.hom.hom := by
    rw [Category.assoc, ← forget_comp, p'.section_projection]
    exact Category.comp_id _
  obtain ⟨u, hu⟩ := (schemeKernel_eq_iff p'.isKernel v (𝟙 _)).mp (hv.trans (Category.id_comp _).symm)
  have he : v * (u ≫ p'.radical.inclusion.hom.hom) = 𝟙 _ := by
    rw [hu, mul_inv_cancel_left]
  calc
    h.hom.hom = (v * (u ≫ p'.radical.inclusion.hom.hom)) ≫ h.hom.hom := by rw [he, Category.id_comp]
    _ = p'.projection.hom.hom ≫ r.torus.hom.hom := by
      rw [MonObj.mul_comp, Category.assoc u, ← forget_comp, hk]
      change (v ≫ h.hom.hom) * (u ≫ (1 : _ ⟶ P.torus.group.X)) = _
      rw [MonObj.comp_one, mul_one]
      change (p'.projection.hom.hom ≫ p'.inclusion.hom.hom) ≫ h.hom.hom = _
      rw [Category.assoc, ← forget_comp, hsection]

private theorem affineLine_point_surjective (R : TestAlgebra k) :
    Function.Surjective (linePoint R) := by
  intro x
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let h := (F.preimage x).unop
  refine ⟨h.hom Polynomial.X, ?_⟩
  have hh : (CommAlgCat.ofHom (Polynomial.aeval (h.hom Polynomial.X)) :
      CommAlgCat.of k (Polynomial k) ⟶ R) = h := by
    apply CommAlgCat.hom_ext
    apply Polynomial.algHom_ext
    exact Polynomial.aeval_X _
  calc
    linePoint R (h.hom Polynomial.X) = (testSpec k).map h.op :=
      congrArg (fun a : CommAlgCat.of k (Polynomial k) ⟶ R ↦ (testSpec k).map a.op) hh
    _ = x := F.map_preimage x

private theorem over_epi {X Y : SchemeOver k} (p : X ⟶ Y) [Flat p.left] [Surjective p.left] :
    Epi p := by
  letI : Epi p.left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left p

private theorem whiskerLeft_epi {X Y Z : SchemeOver k} (p : Y ⟶ Z)
    [Flat p.left] [Surjective p.left] : Epi (X ◁ p) := by
  have hp := (whiskerLeft_pullback (H := X) p).flip.map (Over.forget _)
  letI : Flat (X ◁ p).left := MorphismProperty.of_isPullback hp (inferInstanceAs (Flat p.left))
  letI : Surjective (X ◁ p).left :=
    MorphismProperty.of_isPullback hp (inferInstanceAs (Surjective p.left))
  exact over_epi _

set_option maxHeartbeats 4000000 in
/-- The associated line bundle for the pulled-back character is the
equivariant pullback of the target bundle. -/
theorem flagBundleComparison : FlagBundleComparison.{u} := by
  intro k _ G' G P' P f hf r p' p χ Q' Q a' a ha' ha L' L
  obtain ⟨e, he, _⟩ := flagQuotientComparison f hf r Q' Q
  have hχ : p'.projection ≫ characterPullback r.torus χ =
      r.borel ≫ p.projection ≫ χ := by
    change p'.projection ≫ r.torus ≫ χ = _
    rw [← Category.assoc, ← projection_commutes r p' p, Category.assoc]
  let F := f.hom.hom
  let ℓ := affineLine k
  let b : G'.val.X ⨯ ℓ ⟶ G.val.X ⨯ ℓ := prod.map F (𝟙 ℓ)
  let v := b ≫ L.trivialization
  letI : Flat F.left := hf.2.1
  letI : Surjective F.left := hf.2.2.1
  letI : IsFinite F.left := hf.1
  letI : IsAffine G'.val.X.left := G'.property.1
  letI : LocallyOfFiniteType G'.val.X.hom := G'.property.2.1
  letI : IsLocallyNoetherian G'.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G'.val.X.hom
  letI : IsNoetherian G'.val.X.left := ⟨⟩
  letI := Q'.flat
  letI := Q'.surjective
  letI : QuasiCompact Q'.projection.left := inferInstance
  let T' := L'.trivialization
  have hT' := L'.trivializes.map (Over.forget _)
  letI : Flat T'.left := MorphismProperty.of_isPullback hT' Q'.flat
  letI : Surjective T'.left := MorphismProperty.of_isPullback hT' Q'.surjective
  letI : QuasiCompact T'.left :=
    MorphismProperty.of_isPullback hT' (inferInstanceAs (QuasiCompact Q'.projection.left))
  letI : Epi T' := over_epi T'
  have htransport (R : TestAlgebra k) (x : Points (G'.val.X ⨯ ℓ) R)
      (g : Points G'.val.X R) (z : R) (hx : x = prod.lift g (linePoint R z)) :
      x ≫ v = prod.lift (g ≫ F) (linePoint R z) ≫ L.trivialization := by
    rw [hx]
    change prod.lift g (linePoint R z) ≫ prod.map F (𝟙 ℓ) ≫ L.trivialization = _
    rw [← Category.assoc, prod.lift_map]
    exact congrArg (fun a : Points ℓ R ↦ prod.lift (g ≫ F) a ≫ L.trivialization)
      (Category.comp_id (linePoint R z))
  have hvdesc (R : TestAlgebra k) (x y : Points (G'.val.X ⨯ ℓ) R)
      (hxy : x ≫ T' = y ≫ T') : x ≫ v = y ≫ v := by
    let g := x ≫ prod.fst
    let h := y ≫ prod.fst
    obtain ⟨z, hz⟩ := affineLine_point_surjective R (x ≫ prod.snd)
    obtain ⟨w, hw⟩ := affineLine_point_surjective R (y ≫ prod.snd)
    have hx : x = prod.lift g (linePoint R z) :=
      prod.hom_ext (prod.lift_fst _ _).symm (hz.symm.trans (prod.lift_snd _ _).symm)
    have hy : y = prod.lift h (linePoint R w) :=
      prod.hom_ext (prod.lift_fst _ _).symm (hw.symm.trans (prod.lift_snd _ _).symm)
    have hgh : g ≫ Q'.projection = h ≫ Q'.projection := by
      change x ≫ prod.fst ≫ Q'.projection = y ≫ prod.fst ≫ Q'.projection
      rw [L'.trivializes.w, ← Category.assoc, ← Category.assoc, hxy]
    obtain ⟨c, hc⟩ := (projection_eq_iff Q' g h).mp hgh
    have hhc : g * (c ≫ P'.negative.inclusion.hom.hom) = h := by
      rw [show c ≫ P'.negative.inclusion.hom.hom = g⁻¹ * h from hc, mul_inv_cancel_left]
    let α := CharacterPairing.characterValue (p'.projection ≫ characterPullback r.torus χ) R c⁻¹
    have htt := L'.transition R g c z
    change prod.lift (g * (c ≫ P'.negative.inclusion.hom.hom))
      (linePoint R (α * z)) ≫ T' = prod.lift g (linePoint R z) ≫ T' at htt
    rw [hhc, ← hx, hxy, hy] at htt
    have hline : linePoint R (α * z) = linePoint R w := by
      have hh := L'.trivializes.hom_ext
        (k := prod.lift h (linePoint R (α * z))) (l := prod.lift h (linePoint R w))
        ((prod.lift_fst _ _).trans (prod.lift_fst _ _).symm) htt
      have hh' := congrArg (fun t : Points (G'.val.X ⨯ ℓ) R ↦
        t ≫ (prod.snd : G'.val.X ⨯ ℓ ⟶ ℓ)) hh
      rw [prod.lift_snd, prod.lift_snd] at hh'
      exact hh'
    let cG := c ≫ r.borel.hom.hom
    have hcb : cG ≫ P.negative.inclusion.hom.hom =
        (c ≫ P'.negative.inclusion.hom.hom) ≫ F := by
      rw [Category.assoc, ← forget_comp, r.borel_comm, forget_comp, ← Category.assoc]
    have hchar : α = CharacterPairing.characterValue (p.projection ≫ χ) R cG⁻¹ := by
      rw [show α = CharacterPairing.characterValue (r.borel ≫ p.projection ≫ χ) R c⁻¹
        from congrArg (fun ch ↦ CharacterPairing.characterValue ch R c⁻¹) hχ]
      change CharacterPairing.characterValue (characterPullback r.borel (p.projection ≫ χ)) R c⁻¹ = _
      rw [characterValue_pullback, GrpObj.inv_comp]
    have hmul : (g ≫ F) * (cG ≫ P.negative.inclusion.hom.hom) = h ≫ F := by
      rw [hcb, ← MonObj.mul_comp, hhc]
    rw [htransport R x g z hx, htransport R y h w hy, ← hline,
      ← hmul, hchar]
    exact (L.transition R (g ≫ F) cG z).symm
  obtain ⟨m, hm⟩ := descend T' v (by
    intro A x y hxy
    apply GrassmannianCharts.hom_ext_on_affines
    intro R t
    simpa only [Category.assoc] using hvdesc R (t ≫ x) (t ≫ y)
      (by simp only [Category.assoc, hxy]))
  have hbase : m ≫ L.projection = L'.projection ≫ e.hom := by
    apply (cancel_epi T').mp
    rw [← Category.assoc, hm, Category.assoc, L.trivializes.w.symm, ← Category.assoc,
      show b ≫ prod.fst = prod.fst ≫ F by simp [b],
      Category.assoc, ← he, ← Category.assoc, L'.trivializes.w, Category.assoc]
  have hprod := IsPullback.of_prod_fst_with_id F ℓ
  have hvpb : IsPullback prod.fst v (Q'.projection ≫ e.hom) L.projection := by
    rw [he]
    exact hprod.paste_vert L.trivializes
  have hvleft := hvpb.map (Over.forget _)
  haveI : Flat (Q'.projection ≫ e.hom).left := by
    change Flat (Q'.projection.left ≫ e.hom.left)
    infer_instance
  haveI : Surjective (Q'.projection ≫ e.hom).left := by
    change Surjective (Q'.projection.left ≫ e.hom.left)
    infer_instance
  haveI : QuasiCompact (Q'.projection ≫ e.hom).left := by
    change QuasiCompact (Q'.projection.left ≫ e.hom.left)
    infer_instance
  have hvflat : Flat v.left :=
    MorphismProperty.of_isPullback hvleft (inferInstanceAs (Flat (Q'.projection ≫ e.hom).left))
  have hvsurj : Surjective v.left :=
    MorphismProperty.of_isPullback hvleft (inferInstanceAs (Surjective (Q'.projection ≫ e.hom).left))
  have hvqc : QuasiCompact v.left :=
    MorphismProperty.of_isPullback hvleft (inferInstanceAs (QuasiCompact (Q'.projection ≫ e.hom).left))
  have hiso : IsIso m.left := by
    have houter : IsPullback ((𝟙 (G'.val.X ⨯ ℓ)) ≫ prod.fst) T'
        (Q'.projection ≫ e.hom) (m ≫ L.projection) := by
      rw [Category.id_comp, hbase]
      have hright : IsPullback (𝟙 G'.val.X) Q'.projection (Q'.projection ≫ e.hom) e.hom :=
        IsPullback.of_horiz_isIso ⟨by simp⟩
      simpa using L'.trivializes.paste_horiz hright
    have hleft : IsPullback (𝟙 (G'.val.X ⨯ ℓ)) T' v m :=
      houter.of_right (by rw [Category.id_comp, hm]) hvpb
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u}) (hleft.map (Over.forget _))
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨hvsurj, hvflat⟩, hvqc⟩
      (by change IsIso (𝟙 _); infer_instance)
  letI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map m) := hiso
  letI : IsIso m := isIso_of_reflects_iso m (Over.forget _)
  have hqeq : a'.smul ≫ e.hom = (F ⊗ₘ e.hom) ≫ a.smul := by
    letI := whiskerLeft_epi (X := G'.val.X) Q'.projection
    apply (cancel_epi (G'.val.X ◁ Q'.projection)).mp
    calc
      (G'.val.X ◁ Q'.projection) ≫ a'.smul ≫ e.hom
          = μ[G'.val.X] ≫ Q'.projection ≫ e.hom := by
            rw [← Category.assoc, ← Category.assoc, ha', MonoidalCategory.id_tensorHom]
      _ = (F ⊗ₘ F) ≫ μ[G.val.X] ≫ Q.projection := by
            rw [he, ← Category.assoc, IsMonHom.mul_hom F, Category.assoc]
      _ = (G'.val.X ◁ Q'.projection) ≫ (F ⊗ₘ e.hom) ≫ a.smul := by
            simp only [ha, ← MonoidalCategory.id_tensorHom, ← Category.assoc,
              MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, he]
            rfl
  refine ⟨e, m, he, hqeq, IsPullback.of_horiz_isIso ⟨hbase⟩, hm, ?_⟩
  letI := whiskerLeft_epi (X := G'.val.X) T'
  apply (cancel_epi (G'.val.X ◁ T')).mp
  apply GrassmannianCharts.hom_ext_on_affines
  intro R x
  let h := x ≫ fst _ _
  let t := x ≫ snd _ _
  let g := t ≫ prod.fst
  obtain ⟨z, hz⟩ := affineLine_point_surjective R (t ≫ prod.snd)
  have ht : t = prod.lift g (linePoint R z) :=
    prod.hom_ext (prod.lift_fst _ _).symm (hz.symm.trans (prod.lift_snd _ _).symm)
  have hx : x ≫ (G'.val.X ◁ T') = lift h (t ≫ T') := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [h, t]
  simp only [← Category.assoc]
  rw [hx, ht, L'.leftTranslation, Category.assoc, hm, lift_map]
  have hz' : prod.lift (h * g) (linePoint R z) ≫ v =
      prod.lift ((h * g) ≫ F) (linePoint R z) ≫ L.trivialization :=
    htransport R _ _ _ rfl
  have hg' : prod.lift g (linePoint R z) ≫ v =
      prod.lift (g ≫ F) (linePoint R z) ≫ L.trivialization :=
    htransport R _ _ _ rfl
  rw [show (prod.lift g (linePoint R z) ≫ T') ≫ m =
      prod.lift g (linePoint R z) ≫ v by rw [Category.assoc, hm],
    hg', L.leftTranslation, hz', MonObj.mul_comp]

private theorem torus_inverse_image
    {G' G : AffineAlgebraicGroup k} {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val) (hf : IsCentralIsogeny f) (r : Restrictions f P' P) :
    IsPullback P'.torus.inclusion.hom.hom r.torus.hom.hom f.hom.hom P.torus.inclusion.hom.hom := by
  letI := hf.1
  letI := r.torus_surjective
  letI : Flat r.torus.hom.hom.left := flat_of_surjective_torus_map r.torus P.split r.torus_surjective
  letI : IsFinite r.torus.hom.hom.left :=
    Classification.CentralIsogenies.finiteTorusRestriction hf.1
      ⟨r.torus_comm, inferInstance, r.torus_surjective⟩
  obtain ⟨N, hN, hz⟩ := hf.2.2.2
  obtain ⟨j, hj⟩ :=
    Classification.CentralIsogenies.kernel_le_maximalTorus RootData.SchemeCentre.schemeCentre
      G' P'.reductive P'.torus P'.split P'.maximal N hz
  exact subgroup_inverse_image f r.torus r.torus_comm hN j hj

private theorem normalizes_of_normalizes_image
    {G H : GroupScheme k} {T : ClosedSubgroup G} {S : ClosedSubgroup H}
    {f : G ⟶ H} {fT : T.group ⟶ S.group}
    (hp : IsPullback T.inclusion.hom.hom fT.hom.hom f.hom.hom S.inclusion.hom.hom)
    {Y : SchemeOver k} (g : Y ⟶ G.X) (hg : Normalizes S.inclusion (g ≫ f.hom.hom)) :
    Normalizes T.inclusion g := by
  let F := f.hom.hom
  let t := T.inclusion.hom.hom
  let s := S.inclusion.hom.hom
  have transport {a : Y ⟶ G.X} (ha : ConjugateLe S.inclusion (a ≫ F)) :
      ConjugateLe T.inclusion a := by
    apply (conjugateLe_iff T.inclusion a).2
    intro A u b
    obtain ⟨c, hc⟩ := (conjugateLe_iff S.inclusion (a ≫ F)).1 ha A u (b ≫ fT.hom.hom)
    let v := (u ≫ a) * (b ≫ t) * (u ≫ a)⁻¹
    have h : v ≫ F = c ≫ s := by
      change ((u ≫ a) * (b ≫ t) * (u ≫ a)⁻¹) ≫ F = _
      have hb : (b ≫ t) ≫ F = (b ≫ fT.hom.hom) ≫ s := by
        rw [Category.assoc, show t ≫ F = fT.hom.hom ≫ s from hp.w, Category.assoc]
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hb]
      simpa only [Category.assoc] using hc.symm
    exact ⟨hp.lift v c h, hp.lift_fst _ _ _⟩
  obtain ⟨hpos, hneg⟩ := (normalizesIff k S.inclusion S.isClosedImmersion Y _).1 hg
  have hn : ConjugateLe S.inclusion (g⁻¹ ≫ F) := by
    rw [GrpObj.inv_comp]
    exact hneg
  exact (normalizesIff k T.inclusion T.isClosedImmersion Y g).2 ⟨transport hpos, transport hn⟩

private theorem normalizer_inverse_image
    {G' G : AffineAlgebraicGroup k} {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    (f : G'.val ⟶ G.val) (hf : IsCentralIsogeny f) (r : Restrictions f P' P)
    (W' : WeylQuotient P'.torus) (W : WeylQuotient P.torus) :
    ∃ n : W'.normalizer.group ⟶ W.normalizer.group,
      IsPullback W'.normalizer.inclusion.hom.hom n.hom.hom
        f.hom.hom W.normalizer.inclusion.hom.hom := by
  let N' := W'.normalizer
  let N := W.normalizer
  letI : IsClosedImmersion N'.inclusion.hom.hom.left := N'.isClosedImmersion
  letI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  letI : Mono N'.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsAffine N'.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup N').property.1
  letI : IsAffine P'.torus.group.X.left :=
    (Unipotent.closedSubgroupAlgebraicGroup P'.torus).property.1
  letI : IsAffine P.torus.group.X.left :=
    (Unipotent.closedSubgroupAlgebraicGroup P.torus).property.1
  letI := r.torus_surjective
  letI := flat_of_surjective_torus_map r.torus P.split r.torus_surjective
  have hn' := (W'.represents _ N'.inclusion.hom.hom).2 ⟨𝟙 _, Category.id_comp _⟩
  have hn : Normalizes P.torus.inclusion (N'.inclusion.hom.hom ≫ f.hom.hom) :=
    pushforwardNormalizes P'.torus P.torus f r.torus (𝟙 N'.group.X)
      N'.inclusion.hom.hom _ r.torus_comm (Category.id_comp _) hn'
  obtain ⟨b, hb⟩ := (W.represents _ _).1 hn
  letI := isMonHom_of_comp_closed b (N'.inclusion ≫ f) N.inclusion hb
  let n : N'.group ⟶ N.group := Grp.homMk b
  refine ⟨n, ?_⟩
  have ht := torus_inverse_image f hf r
  have he (c : PullbackCone f.hom.hom N.inclusion.hom.hom) :
      ∃ u : c.pt ⟶ N'.group.X, u ≫ N'.inclusion.hom.hom = c.fst := by
    have hc : Normalizes P.torus.inclusion (c.fst ≫ f.hom.hom) := by
      rw [c.condition]
      exact (W.represents _ _).2 ⟨c.snd, rfl⟩
    exact (W'.represents _ _).1 (normalizes_of_normalizes_image ht c.fst hc)
  choose a ha using he
  refine IsPullback.of_isLimit' ⟨hb.symm⟩
    (PullbackCone.IsLimit.mk hb.symm a ha (fun c ↦ ?_) (fun c m hm _ ↦ ?_))
  · change a c ≫ b = c.snd
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hb, ← Category.assoc, ha, c.condition]
  · exact (cancel_mono N'.inclusion.hom.hom).mp (hm.trans (ha c).symm)

private theorem monoid_hom_of_comp_epi {G H I : GroupScheme k} (p : G ⟶ H)
    (e : H.X ⟶ I.X) [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    (q : G ⟶ I) (hq : p.hom.hom ≫ e = q.hom.hom) : IsMonHom e := by
  let v := p.hom.hom
  letI : Epi v := over_epi v
  letI : Epi (H.X ◁ v) := whiskerLeft_epi v
  have hp := (whiskerRight_isPullback (Y := G.X) v).flip.map (Over.forget _)
  letI : Flat (v ▷ G.X).left :=
    MorphismProperty.of_isPullback hp (inferInstanceAs (Flat v.left))
  letI : Surjective (v ▷ G.X).left :=
    MorphismProperty.of_isPullback hp (inferInstanceAs (Surjective v.left))
  letI : Epi (v ▷ G.X) := over_epi _
  haveI : Epi (v ⊗ₘ v) := by
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  refine ⟨?_, ?_⟩
  · calc
      η[H.X] ≫ e = η[G.X] ≫ (v ≫ e) := by
        rw [← Category.assoc, IsMonHom.one_hom v]
      _ = η[I.X] := by rw [show v ≫ e = q.hom.hom from hq, IsMonHom.one_hom]
  · apply (cancel_epi (v ⊗ₘ v)).mp
    calc
      (v ⊗ₘ v) ≫ μ[H.X] ≫ e = μ[G.X] ≫ q.hom.hom := by
        rw [← Category.assoc, ← IsMonHom.mul_hom v, Category.assoc, show v ≫ e = q.hom.hom from hq]
      _ = (v ⊗ₘ v) ≫ (e ⊗ₘ e) ≫ μ[I.X] := by
        rw [IsMonHom.mul_hom, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
          show v ≫ e = q.hom.hom from hq]

private theorem weyl_character_action
    {G' G : AffineAlgebraicGroup k} {P' : OppositeBorelPair G'} {P : OppositeBorelPair G}
    {f : G'.val ⟶ G.val} (r : Restrictions f P' P)
    (W' : WeylQuotient P'.torus) (W : WeylQuotient P.torus)
    (n : W'.normalizer.group ⟶ W.normalizer.group) (e : W'.scheme.val ≅ W.scheme.val)
    (hn : n ≫ W.normalizer.inclusion = W'.normalizer.inclusion ≫ f)
    (he : W'.projection ≫ e.hom = n ≫ W.projection)
    (D' : SplitImage P'.torus.inclusion W'.normalizer.inclusion W'.projection)
    (D : SplitImage P.torus.inclusion W.normalizer.inclusion W.projection)
    (w' : D'.labels) (w : D.labels)
    (hw : D'.constantGroup.sectionPoint w' ≫ e.hom.hom.hom = D.constantGroup.sectionPoint w)
    (χ : CharacterDescent.Character P.torus.group) :
    characterPullback r.torus (w.val χ) = w'.val (characterPullback r.torus χ) := by
  let K := 𝟙_ (SchemeOver k)
  let T' : ClosedSubgroup W'.normalizer.group := ⟨_, W'.torusInclusion, W'.torusClosed⟩
  let s := D'.constantGroup.sectionPoint w'
  have ht := fibreTorsor (G := Unipotent.closedSubgroupAlgebraicGroup W'.normalizer)
    (W := W'.scheme) T' W'.projection W'.quotient s
  obtain ⟨g, hg⟩ := splitFibrePoint (G := Unipotent.closedSubgroupAlgebraicGroup W'.normalizer)
    (W := W'.scheme) T' P'.split W'.projection s ht
  have hq : (g ≫ n.hom.hom) ≫ W.projection.hom.hom = D.constantGroup.sectionPoint w := by
    rw [Category.assoc, ← forget_comp, ← he, forget_comp, ← Category.assoc, hg]
    exact hw
  have hunit : toUnit K = 𝟙 K := Subsingleton.elim _ _
  have c' := D'.conjugates K g w' (by rwa [hunit, Category.id_comp])
  have c := D.conjugates K (g ≫ n.hom.hom) w (by rwa [hunit, Category.id_comp])
  let g' := g ≫ W'.normalizer.inclusion.hom.hom
  let g₁ := (g ≫ n.hom.hom) ≫ W.normalizer.inclusion.hom.hom
  let t' := P'.torus.inclusion.hom.hom
  let t := P.torus.inclusion.hom.hom
  let fT := r.torus.hom.hom
  let F := f.hom.hom
  have hg₁ : g₁ = g' ≫ F := by
    change (g ≫ n.hom.hom) ≫ W.normalizer.inclusion.hom.hom =
      (g ≫ W'.normalizer.inclusion.hom.hom) ≫ f.hom.hom
    rw [Category.assoc, ← forget_comp, hn, forget_comp, ← Category.assoc]
  have hT : fT ≫ t = t' ≫ F :=
    congrArg (fun a : P'.torus.group ⟶ G.val ↦ a.hom.hom) r.torus_comm
  let a := toUnit P'.torus.group.X ≫ g'
  let b := toUnit P'.torus.group.X ≫ g₁
  have hc' : (D'.conjugation w').hom.hom.hom ≫ t' = a * t' * a⁻¹ := by
    simpa only [forget_comp, Category.id_comp] using
      apply_conjugateFamily_eq P'.torus.inclusion g' (D'.conjugation w') c' (toUnit _) (𝟙 _)
  have hc : fT ≫ (D.conjugation w).hom.hom.hom ≫ t = b * (fT ≫ t) * b⁻¹ := by
    simpa only [forget_comp] using
      apply_conjugateFamily_eq P.torus.inclusion g₁ (D.conjugation w) c (toUnit _) fT
  have hconj : r.torus ≫ (D.conjugation w).hom = (D'.conjugation w').hom ≫ r.torus := by
    apply Grp.hom_ext
    letI : IsClosedImmersion t.left := P.torus.isClosedImmersion
    letI : Mono t := Over.mono_of_mono_left t
    apply (cancel_mono t).mp
    change (fT ≫ (D.conjugation w).hom.hom.hom) ≫ t =
      ((D'.conjugation w').hom.hom.hom ≫ fT) ≫ t
    rw [Category.assoc, hc, Category.assoc, hT, ← Category.assoc, hc']
    have hb : b = a ≫ F := by simp only [b, a, hg₁, Category.assoc]
    rw [hb, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have hinv : r.torus ≫ (D.conjugation w).inv = (D'.conjugation w').inv ≫ r.torus := by
    rw [← cancel_mono (D.conjugation w).hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.assoc, hconj, Iso.inv_hom_id_assoc]
  rw [D.characterAction, D'.characterAction]
  change r.torus ≫ (D.conjugation w).inv ≫ χ =
    (D'.conjugation w').inv ≫ r.torus ≫ χ
  rw [← Category.assoc, hinv, Category.assoc]

/-- The central isogeny identifies the roots and Weyl group schemes, with
their compatible actions on characters. -/
theorem rootAndWeylComparison : RootAndWeylComparison.{u} := by
  intro k _ G' G P' P f hf r
  obtain ⟨hi, _, hbij, _⟩ := Classification.CentralIsogenies.centralIsogenyComparison
    G' G P'.reductive P.reductive P'.torus P.torus P'.split P'.maximal P.split P.maximal
    f r.torus hf r.torus_comm r.torus_surjective
  refine ⟨hi, hbij, ?_⟩
  intro W' W
  obtain ⟨n, hn⟩ := normalizer_inverse_image f hf r W' W
  let N' := W'.normalizer
  let N := W.normalizer
  letI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hn' : n ≫ N.inclusion = N'.inclusion ≫ f := Grp.hom_ext _ _ hn.w.symm
  have htr : W'.torusInclusion ≫ n = r.torus ≫ W.torusInclusion := by
    apply Grp.hom_ext
    apply (cancel_mono N.inclusion.hom.hom).mp
    repeat rw [← forget_comp]
    rw [Category.assoc, hn', ← Category.assoc, W'.torus_comm,
      Category.assoc, W.torus_comm, r.torus_comm]
  let F := n.hom.hom
  have hp := hn.map (Over.forget _)
  letI : Flat F.left := MorphismProperty.of_isPullback hp hf.2.1
  letI : Surjective F.left := MorphismProperty.of_isPullback hp hf.2.2.1
  letI : IsFinite F.left := MorphismProperty.of_isPullback hp hf.1
  letI : LocallyOfFinitePresentation F.left := group_hom_finitePresentation
    (Unipotent.closedSubgroupAlgebraicGroup N') (Unipotent.closedSubgroupAlgebraicGroup N) n
  let S' : ClosedSubgroup N'.group := ⟨_, W'.torusInclusion, W'.torusClosed⟩
  let q := n ≫ W.projection
  letI : Flat W.projection.hom.hom.left := W.quotient.2.1
  letI : Surjective W.projection.hom.hom.left := W.quotient.2.2.1
  letI : LocallyOfFinitePresentation W.projection.hom.hom.left := W.quotient.2.2.2.1
  letI : Flat q.hom.hom.left := inferInstanceAs (Flat (F.left ≫ W.projection.hom.hom.left))
  letI : Surjective q.hom.hom.left :=
    inferInstanceAs (Surjective (F.left ≫ W.projection.hom.hom.left))
  letI : LocallyOfFinitePresentation q.hom.hom.left :=
    inferInstanceAs (LocallyOfFinitePresentation (F.left ≫ W.projection.hom.hom.left))
  have htor := torus_inverse_image f hf r
  have hmatch (T : SchemeOver k) (g h : T ⟶ N'.group.X) :
      g ≫ q.hom.hom = h ≫ q.hom.hom ↔ g⁻¹ * h ∈ SubgroupSections S' T := by
    change (g ≫ F ≫ W.projection.hom.hom = h ≫ F ≫ W.projection.hom.hom) ↔ _
    rw [← Category.assoc g, ← Category.assoc h, schemeKernel_eq_iff W.quotient.1,
      ← GrpObj.inv_comp, ← MonObj.mul_comp]
    constructor
    · rintro ⟨t, ht⟩
      have ht' : ((g⁻¹ * h) ≫ N'.inclusion.hom.hom) ≫ f.hom.hom =
          t ≫ P.torus.inclusion.hom.hom := by
        rw [Category.assoc, hn.w, ← Category.assoc, ← ht, Category.assoc, ← forget_comp,
          W.torus_comm]
      let t' := htor.lift _ _ ht'
      refine ⟨t', ?_⟩
      change t' ≫ W'.torusInclusion.hom.hom = g⁻¹ * h
      letI : IsClosedImmersion N'.inclusion.hom.hom.left := N'.isClosedImmersion
      letI : Mono N'.inclusion.hom.hom := Over.mono_of_mono_left _
      apply (cancel_mono N'.inclusion.hom.hom).mp
      rw [Category.assoc, ← forget_comp, W'.torus_comm]
      exact htor.lift_fst _ _ _
    · rintro ⟨t', ht'⟩
      refine ⟨t' ≫ r.torus.hom.hom, ?_⟩
      change (t' ≫ r.torus.hom.hom) ≫ W.torusInclusion.hom.hom = _
      rw [Category.assoc, ← forget_comp, ← htr, forget_comp, ← Category.assoc,
        show t' ≫ W'.torusInclusion.hom.hom = g⁻¹ * h from ht']
  obtain ⟨θ, hθ⟩ := represent_of_fppf S' q.hom.hom hmatch
  obtain ⟨θ', hθ'⟩ := W'.quotient.2.2.2.2
  let Y := (fppfOver k).uliftYoneda
  let e := (fppfOver k).fullyFaithfulUliftYoneda.preimageIso (θ'.symm ≪≫ θ)
  have he : W'.projection.hom.hom ≫ e.hom = q.hom.hom := by
    apply Y.map_injective
    rw [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, ← hθ']
    change (rightQuotientProjection S' ≫ θ'.hom) ≫ θ'.inv ≫ θ.hom = _
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hθ
  letI : Flat W'.projection.hom.hom.left := W'.quotient.2.1
  letI : Surjective W'.projection.hom.hom.left := W'.quotient.2.2.1
  letI := monoid_hom_of_comp_epi W'.projection e.hom q he
  let E : W'.scheme.val ≅ W.scheme.val :=
    Grp.mkIso e (IsMonHom.one_hom (f := e.hom)) (IsMonHom.mul_hom (f := e.hom))
  have hproj : W'.projection ≫ E.hom = n ≫ W.projection := Grp.hom_ext _ _ he
  exact ⟨n, E, hn', htr, hproj, weyl_character_action r W' W n E hn' hproj⟩

end

end LinearAlgebraicGroups.Representation.IsogenyFlagComparison
