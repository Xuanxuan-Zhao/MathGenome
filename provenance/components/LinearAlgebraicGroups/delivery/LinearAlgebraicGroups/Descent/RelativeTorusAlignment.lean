import Specs.LinearAlgebraicGroups.Descent.RelativeTorusAlignment
import LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.Relative.LeviConjugacy
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.RelativeTorusAlignment

open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup)
open Specs.RelativeTorusAlignment
open Specs.ParabolicFamilyTransporter
open Relative.ParabolicFamilyTransporter
open Specs.Fppf (schemeTopology IsFppf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {H B : GroupScheme k}

private theorem fppf_mem {V U : SchemeOver k} (a : V ⟶ U) (ha : IsFppf a.left)
    {J : Sieve U} (h : J a) : J ∈ schemeTopology k U := by
  obtain ⟨hf, hs, hl⟩ := ha
  rw [GrothendieckTopology.mem_over_iff]
  apply Scheme.fppfTopology.superset_covering
    ((Sieve.generate_le_iff _ _).mpr (fun _ _ hb ↦ ?_))
    (Precoverage.generate_mem_toGrothendieck a.left.singleton_mem_fppfPrecoverage)
  cases hb
  exact ⟨V, a, 𝟙 V.left, h, by simp⟩

private theorem openCover_mem {S : SchemeOver k} (U : S.left.OpenCover) :
    Sieve.ofArrows (fun i => Over.mk (U.f i ≫ S.hom))
      (fun i => (Over.homMk (U.f i) : Over.mk (U.f i ≫ S.hom) ⟶ S)) ∈ schemeTopology k S := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
    U.mem_grothendieckTopology

private abbrev restrict {S V : SchemeOver k} (b : V ⟶ S)
    (f : relativePoints B S ≅ relativePoints B S) :
    relativePoints B V ≅ relativePoints B V :=
  Functor.isoWhiskerLeft (Over.map b).op f

private theorem alignment_affineLocal (i : H ⟶ B)
    (h : ∀ (R : TestAlgebra k) (f : relativePoints B ((testSpec k).obj (op R)) ≅
      relativePoints B ((testSpec k).obj (op R))),
      alignmentSieve i f ∈ schemeTopology k ((testSpec k).obj (op R)))
    {S : SchemeOver k} (f : relativePoints B S ≅ relativePoints B S) :
    alignmentSieve i f ∈ schemeTopology k S := by
  let C := S.left.affineCover
  apply (schemeTopology k).transitive (openCover_mem C)
  intro U b hb
  obtain ⟨W, v, p, hp, rfl⟩ := hb
  obtain ⟨j⟩ := hp
  let V : SchemeOver k := Over.mk (C.f j ≫ S.hom)
  let a : V ⟶ S := Over.homMk (C.f j)
  suffices ha : (alignmentSieve i f).pullback a ∈ schemeTopology k V by
    simpa only [Sieve.pullback_comp] using (schemeTopology k).pullback_stable v ha
  have hV : IsAffine V.left := inferInstanceAs (IsAffine (S.left.affineCover.X j))
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hV
  change (testSpec k).obj R ≅ V at e
  have hR := h R.unop (restrict (e.hom ≫ a) f)
  have hEq : (alignmentSieve i f).pullback (e.hom ≫ a) =
      alignmentSieve i (restrict (e.hom ≫ a) f) := by
    ext W w
    change Aligns i f (w ≫ e.hom ≫ a) ↔ Aligns i (restrict (e.hom ≫ a) f) w
    simp only [Aligns, evaluate_map_comp]
    rfl
  have hh : (alignmentSieve i f).pullback (e.hom ≫ a) ∈ schemeTopology k _ := hEq.symm ▸ hR
  have h' := (schemeTopology k).pullback_stable e.inv hh
  rwa [← Sieve.pullback_comp, Iso.inv_hom_id_assoc] at h'

open private relativePoint relativePointHom relativePoint_natural relativePoint_comp
  factors_relative_iff
  from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

private def sliceObjectIso {S : SchemeOver k} (U : Over S) :
    (Over.map S.hom).obj (S.iteratedSliceForward.obj U) ≅ U.left :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ U.left.hom = U.hom.left ≫ S.hom
    rw [Category.id_comp, Over.w U.hom])

private def scalarPoint {G : GroupScheme k} {S : SchemeOver k} {U : Over S}
    (z : S.iteratedSliceForward.obj U ⟶ (relativeGroup G S).X) : U.left ⟶ G.X :=
  (sliceObjectIso U).inv ≫ relativePoint z

private theorem scalarPoint_comp {G : GroupScheme k} {S : SchemeOver k} {U V : Over S}
    (a : U ⟶ V) (z : S.iteratedSliceForward.obj V ⟶ (relativeGroup G S).X) :
    scalarPoint (S.iteratedSliceForward.map a ≫ z) = a.left ≫ scalarPoint z := by
  rw [scalarPoint, scalarPoint, relativePoint_comp, ← Category.assoc, ← Category.assoc]
  congr 1

private def scalarPointEquiv (G : GroupScheme k) {S : SchemeOver k} (U : Over S) :
    (S.iteratedSliceForward.obj U ⟶ (relativeGroup G S).X) ≃* (U.left ⟶ G.X) := by
  let p := relativePointHom (G := G) (T := S) (S.iteratedSliceForward.obj U)
  let q : ((Over.map S.hom).obj (S.iteratedSliceForward.obj U) ⟶ G.X) →*
      (U.left ⟶ G.X) :=
    ⟨⟨((sliceObjectIso U).inv ≫ ·), MonObj.comp_one _⟩, MonObj.comp_mul _⟩
  refine MulEquiv.ofBijective (q.comp p) ((?_ : Function.Bijective q).comp ?_)
  · exact ((Iso.homCongr (sliceObjectIso U) (Iso.refl G.X))).bijective
  · exact ((Over.mapPullbackAdj S.hom).homEquiv _ G.X).symm.bijective

private def scalarPointIso (G : GroupScheme k) (S : SchemeOver k) :
    S.iteratedSliceForward.op ⋙ yonedaGrp.obj (relativeGroup G S) ≅ relativePoints G S :=
  NatIso.ofComponents (fun U ↦ (scalarPointEquiv G U.unop).toGrpIso) (by
    intro U V a
    apply GrpCat.ext
    intro z
    simp only [ConcreteCategory.comp_apply]
    change scalarPoint (S.iteratedSliceForward.map a.unop ≫ z) =
      a.unop.left ≫ scalarPoint z
    exact scalarPoint_comp a.unop z)

private theorem scalarPoint_natural {G J : GroupScheme k} (i : G ⟶ J) (S : SchemeOver k)
    (U : Over S) (z : S.iteratedSliceForward.obj U ⟶ (relativeGroup G S).X) :
    scalarPoint (z ≫ ((Over.pullback S.hom).mapGrp.map i).hom.hom) =
      scalarPoint z ≫ i.hom.hom := by
  change (sliceObjectIso U).inv ≫ relativePoint (z ≫ (Over.pullback S.hom).map i.hom.hom) =
    ((sliceObjectIso U).inv ≫ relativePoint z) ≫ i.hom.hom
  rw [relativePoint_natural, Category.assoc]

private def representedAut {S : SchemeOver k}
    (f : relativePoints B S ≅ relativePoints B S) :
    relativeGroup B S ≅ relativeGroup B S :=
  (yonedaGrpFullyFaithful.comp (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ GrpCat).obj S.iteratedSliceEquiv.op.functor))).preimageIso
    (scalarPointIso B S ≪≫ f ≪≫ (scalarPointIso B S).symm)

private theorem representedAut_hom {S : SchemeOver k}
    (f : relativePoints B S ≅ relativePoints B S) (U : Over S)
    (z : S.iteratedSliceForward.obj U ⟶ (relativeGroup B S).X) :
    scalarPoint (z ≫ (representedAut f).hom.hom.hom) =
      evaluate f.hom U (scalarPoint z) := by
  let F := yonedaGrpFullyFaithful.comp (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ GrpCat).obj S.iteratedSliceEquiv.op.functor))
  have hf := congrArg (fun n ↦ n.app (op U))
    (F.map_preimage (scalarPointIso B S ≪≫ f ≪≫ (scalarPointIso B S).symm).hom)
  have h := ConcreteCategory.congr_hom hf z
  change z ≫ (representedAut f).hom.hom.hom =
    (scalarPointIso B S).inv.app (op U) (evaluate f.hom U (scalarPoint z)) at h
  have eq := congrArg (fun p ↦ scalarPoint (U := U) p) h
  have cancel := ConcreteCategory.congr_hom
    (Iso.inv_hom_id_app (scalarPointIso B S) (op U)) (evaluate f.hom U (scalarPoint z))
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at cancel
  change scalarPoint ((scalarPointIso B S).inv.app (op U)
    (evaluate f.hom U (scalarPoint z))) = _ at cancel
  exact eq.trans cancel

private def imageFamily (P : ClosedSubgroup B) {S : SchemeOver k} (hP : Smooth P.group.X.hom)
    (f : relativePoints B S ≅ relativePoints B S) : Family B S := by
  refine ⟨relativeGroup P.group S, (Over.pullback S.hom).mapGrp.map P.inclusion ≫
    (representedAut f).hom, ?_, ?_⟩
  · let q := P.inclusion.hom.hom
    let b := ((Over.pullback S.hom).map q).left
    have hp : IsPullback (pullback.fst P.group.X.hom S.hom)
        (pullback.snd P.group.X.hom S.hom) (q.left ≫ B.X.hom) S.hom := by
      rw [Over.w q]
      exact IsPullback.of_hasPullback _ _
    have h₁ : b ≫ pullback.fst B.X.hom S.hom = pullback.fst P.group.X.hom S.hom ≫ q.left :=
      pullback.lift_fst _ _ _
    have h₂ : b ≫ pullback.snd B.X.hom S.hom = pullback.snd P.group.X.hom S.hom :=
      pullback.lift_snd _ _ _
    have pb := (IsPullback.of_bot (h₂.symm ▸ hp) h₁.symm
      (IsPullback.of_hasPullback B.X.hom S.hom)).flip
    have hc : IsClosedImmersion ((Over.pullback S.hom).map P.inclusion.hom.hom).left :=
      MorphismProperty.of_isPullback pb.flip P.isClosedImmersion
    have : IsIso (representedAut f).hom.hom.hom.left :=
      (Grp.forget _ ⋙ Over.forget _).map_isIso (representedAut f).hom
    change IsClosedImmersion (b ≫ (representedAut f).hom.hom.hom.left)
    exact MorphismProperty.comp_mem _ _ _ hc inferInstance
  · exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback P.group.X.hom S.hom) hP

open Specs.Pinning (SplitBorelPair)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics
open private restrictSubgroup transportSubgroup maximal_of_square
  solvable_maximal_torus_iff
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private centralizes_iff_in_ambient centralizes_opposite_iff map_hasLimit
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private centralizes_of_opposite_limits from LinearAlgebraicGroups.RootData.RootGroups
open private centralizes_hasLimit subgroupInclusionFactors pointHom affine_subgroup
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers

/-- Inside the Borel, extendibility in the opposite cocharacter direction forces
centralization, since the positive-direction limit already exists. -/
private theorem torus_is_opposite_limit (P : SplitBorelPair k)
    (i : P.T.group ⟶ P.B.group) (hi : i ≫ P.B.inclusion = P.T.inclusion) :
    ∃ (c : Cocharacter P.B.group) (E : LimitDecomposition c),
      SameSubgroup (restrictSubgroup P.T P.B i hi) E.parabolic := by
  let B := closedSubgroupAlgebraicGroup P.B
  let T := restrictSubgroup P.T P.B i hi
  obtain ⟨c, D, hc, hB, _⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  have hT :=
    (RootData.BorelsAndChambers.regularCocharacterBorel P.G P.reductive
      P.T P.split P.maximal c hc D).1
  let d := c ≫ i
  have hd : d ≫ P.B.inclusion = c ≫ P.T.inclusion := by
    rw [Category.assoc, hi]
  have hd' : oppositeCocharacter d ≫ P.B.inclusion =
      oppositeCocharacter (c ≫ P.T.inclusion) := by
    dsimp only [oppositeCocharacter]
    rw [Category.assoc, hd]
  obtain ⟨E⟩ := existsLimitDecomposition B (oppositeCocharacter d)
  refine ⟨oppositeCocharacter d, E, ?_, ?_⟩
  · apply subgroupInclusionFactors (affine_subgroup B.property.1 T) E.parabolic T.inclusion
    intro R t
    apply (E.parabolic_points R _).mp
    let g := pointHom T.inclusion R t
    have hcentG : Centralizes (c ≫ P.T.inclusion) (g ≫ P.B.inclusion.hom.hom) := by
      obtain ⟨j, hj⟩ := hT.2
      apply (D.centralizer_points _ _).mpr
      refine ⟨t ≫ j.hom.hom, ?_⟩
      change t ≫ j.hom.hom ≫ D.centralizer.inclusion.hom.hom =
        (t ≫ i.hom.hom) ≫ P.B.inclusion.hom.hom
      have hj' : j.hom.hom ≫ D.centralizer.inclusion.hom.hom = P.T.inclusion.hom.hom :=
        congrArg (fun f : P.T.group ⟶ P.G.val ↦ f.hom.hom) hj
      have hi' : i.hom.hom ≫ P.B.inclusion.hom.hom = P.T.inclusion.hom.hom :=
        congrArg (fun f : P.T.group ⟶ P.G.val ↦ f.hom.hom) hi
      rw [Category.assoc, hj', hi']
    rw [← hd] at hcentG
    have hcent := (centralizes_iff_in_ambient P.B d g).mp hcentG
    exact ⟨g, centralizes_hasLimit _ ((centralizes_opposite_iff d g).mpr hcent)⟩
  · apply subgroupInclusionFactors (affine_subgroup B.property.1 E.parabolic) T E.parabolic.inclusion
    intro R p
    let b := pointHom E.parabolic.inclusion R p
    let g : GroupPoints P.G.val R := b ≫ P.B.inclusion.hom.hom
    obtain ⟨j, hj⟩ := hB.1
    have hpos : HasExtension (c ≫ P.T.inclusion) g := by
      apply (D.parabolic_points R g).mpr
      exact ⟨b ≫ j.hom.hom, by
        change (b ≫ j.hom.hom) ≫ D.parabolic.inclusion.hom.hom = g
        have h : j.hom.hom ≫ D.parabolic.inclusion.hom.hom = P.B.inclusion.hom.hom :=
          congrArg (fun f : P.B.group ⟶ P.G.val ↦ f.hom.hom) hj
        rw [Category.assoc, h]⟩
    obtain ⟨z, hz⟩ := (E.parabolic_points R b).mpr ⟨p, rfl⟩
    have hneg : HasExtension (oppositeCocharacter (c ≫ P.T.inclusion)) g := by
      rw [← hd']
      exact ⟨_, map_hasLimit P.B.inclusion (oppositeCocharacter d) hz⟩
    obtain ⟨y, hy⟩ := (D.centralizer_points _ g).mp
      (centralizes_of_opposite_limits P.G.property.1 _ g hpos hneg)
    obtain ⟨j', hj'⟩ := hT.1
    refine ⟨y ≫ j'.hom.hom, ?_⟩
    have : Mono P.B.inclusion.hom.hom := mono_over _ P.B.isClosedImmersion
    apply (cancel_mono P.B.inclusion.hom.hom).mp
    change ((y ≫ j'.hom.hom) ≫ i.hom.hom) ≫ P.B.inclusion.hom.hom = g
    have hi' : i.hom.hom ≫ P.B.inclusion.hom.hom = P.T.inclusion.hom.hom :=
      congrArg (fun f : P.T.group ⟶ P.G.val ↦ f.hom.hom) hi
    have hj'' : j'.hom.hom ≫ P.T.inclusion.hom.hom = D.centralizer.inclusion.hom.hom :=
      congrArg (fun f : D.centralizer.group ⟶ P.G.val ↦ f.hom.hom) hj'
    rw [Category.assoc _ i.hom.hom, Category.assoc, hi', hj'']
    exact hy

open private reductionMap conjugacy_lifts_for_limit_parabolic
  from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

/-- The infinitesimal transporter argument applies to limit subgroups of a
smooth affine group, with geometric conjugacy supplied separately. -/
private theorem smooth_limit_transporter (G : Specs.AffineAlgebraicGroup k)
    (hG : Smooth G.val.X.hom) {c : Cocharacter G.val} (D : LimitDecomposition c)
    (R : TestAlgebra k) (Q : Family G.val ((testSpec k).obj (op R)))
    (hQ : SameGeometricType D.parabolic Q) :
    ∃ (Z : SchemeOver k) (p : Z ⟶ (testSpec k).obj (op R)) (g : Z ⟶ G.val.X),
      IsFppf p.left ∧ Conjugates D.parabolic Q p g := by
  let S := (testSpec k).obj (op R)
  obtain ⟨Z, j, hj, hrep, hsurj, hfp, _, _⟩ := closedTransporter G D.parabolic R Q hQ
  let p := j ≫ snd G.val.X S
  let g := j ≫ fst G.val.X S
  have hj_eq : lift g p = j := lift_comp_fst_snd _
  have hGa := G.property.1
  have hSa : IsAffine S.left := inferInstanceAs (IsAffine (Spec (.of R)))
  have hprod : IsAffine (G.val.X ⊗ S).left := by
    rw [Over.tensorObj_left]
    infer_instance
  have hZa : IsAffine Z.left := isAffine_of_isAffineHom j.left
  have hsm : Smooth p.left := by
    apply smooth_of_squareZeroLifting p.left
    intro A I hI a z hz
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ S.hom)
    let : Algebra k A := φ.hom.toAlgebra
    let C : TestAlgebra k := CommAlgCat.of k A
    let V := (testSpec k).obj (op C)
    let V₀ := (testSpec k).obj (op (CommAlgCat.of k (A ⧸ I)))
    let r : V₀ ⟶ V := reductionMap C I
    let b : V ⟶ S := Over.homMk a hφ.symm
    have hrz : z ≫ Z.hom = V₀.hom := by
      rw [← Over.w p, ← Category.assoc, ← hz, Category.assoc, ← hφ]
      exact (Spec.map_comp φ (CommRingCat.ofHom (Ideal.Quotient.mk I))).symm
    let w : V₀ ⟶ Z := Over.homMk z hrz
    have hw : w ≫ p = r ≫ b := Over.OverMorphism.ext hz.symm
    have hc : Conjugates D.parabolic Q (r ≫ b) (w ≫ g) := (hrep _ _ _).mpr
      ⟨w, by rw [← hw, ← comp_lift, hj_eq]⟩
    obtain ⟨x, hx, hxr⟩ := conjugacy_lifts_for_limit_parabolic G hG c D Q b I hI (w ≫ g) hc
    obtain ⟨y, hy⟩ := (hrep _ _ _).mp hx
    have hyp : y ≫ p = b := by simp only [p, ← Category.assoc, hy, lift_snd]
    have hjm : Mono j := mono_over j hj
    have hyr : r ≫ y = w := (cancel_mono j).mp (by
      rw [Category.assoc, hy, comp_lift, hxr, ← hw, ← comp_lift, hj_eq])
    exact ⟨y.left, congrArg (·.left) hyp, congrArg (·.left) hyr⟩
  have : Smooth p.left := hsm
  exact ⟨Z, p, g, ⟨inferInstance, hsurj, hfp⟩, (hrep _ _ _).mpr ⟨𝟙 _, by simp [hj_eq]⟩⟩

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup IsSchemeKernel)
open Specs.GeometricRadicals (IsMaximalTorus IsSplitTorus)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup IsUnipotent)

open private subgroupOf_mutual_iso
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private pushSubgroup transported_kernel
  from LinearAlgebraicGroups.Relative.LeviConjugacy
open private baseChangeKernelSquare baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private maximal_of_iso_projection
  from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private splitTorus_baseChange kBorel_smooth_connected
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private rationalSections from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private unipotent_sections_solvable torus_commutative solvable_of_schemeKernel
  from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent

private theorem borel_smooth_connected (P : SplitBorelPair k) :
    Smooth P.B.group.X.hom ∧ GeometricallyConnected P.B.group.X.hom := by
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected P.G P.B P.borel
  have : ConnectedSpace (closedSubgroupAlgebraicGroup P.B).val.X.left := hc
  exact ⟨hs, geometricallyConnected_of_connected (closedSubgroupAlgebraicGroup P.B)⟩

private def extendSubgroup {G : GroupScheme k} (K : Type u) [Field K] [Algebra k K]
    (T : ClosedSubgroup G) : ClosedSubgroup ((groupBaseChange k K).obj G) :=
  ⟨_, (groupBaseChange k K).map T.inclusion, by
    exact MorphismProperty.of_isPullback
      (baseChangeMapPullback (K := K) T.inclusion.hom.hom).flip T.isClosedImmersion⟩

/-- The regular limit projection exhibits a torus quotient with unipotent kernel
on each geometric fibre, and identifies the specified torus with that quotient. -/
private theorem geometric_borel_torus (P : SplitBorelPair k)
    (i : P.T.group ⟶ P.B.group) (hi : i ≫ P.B.inclusion = P.T.inclusion)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K] :
    let G := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup P.B)
    Smooth G.val.X.hom ∧ ConnectedSpace G.val.X.left ∧ Specs.SchemeDerivedGroup.IsSolvable G.val ∧
      IsMaximalTorus (G := G.val) (extendSubgroup K (restrictSubgroup P.T P.B i hi)) := by
  dsimp only
  let F := groupBaseChange k K
  let B := closedSubgroupAlgebraicGroup P.B
  let G := baseChangedAlgebraicGroup K B
  let T := restrictSubgroup P.T P.B i hi
  let T' := extendSubgroup K T
  obtain ⟨c, D, hc, hB, _⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  have hT := (RootData.BorelsAndChambers.regularCocharacterBorel P.G P.reductive
    P.T P.split P.maximal c hc D).1
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso hB.1 hB.2
  obtain ⟨d, hd⟩ := subgroupOf_mutual_iso hT.2 hT.1
  have : Mono D.parabolic.inclusion.hom.hom :=
    mono_over _ D.parabolic.isClosedImmersion
  have : Mono D.parabolic.inclusion := (Grp.forget _).mono_of_mono_map
    (show Mono D.parabolic.inclusion.hom.hom from inferInstance)
  have hd' : i ≫ e.hom = d.hom ≫ D.sectionMap := (cancel_mono D.parabolic.inclusion).mp (by
    rw [Category.assoc, Category.assoc, he, D.section_in_G, hi, hd])
  let C := closedSubgroupAlgebraicGroup D.centralizer
  let C' := baseChangedAlgebraicGroup K C
  let q : B.val ⟶ C.val := e.hom ≫ D.limit
  have hqi : i ≫ q = d.hom := by
    rw [← Category.assoc, hd', Category.assoc, D.section_limit, Category.comp_id]
  have hCT : IsSplitTorus C.val := by
    obtain ⟨r, ⟨f⟩⟩ := P.split
    exact ⟨r, ⟨d.symm ≪≫ f⟩⟩
  have hC' : IsSplitTorus C'.val := splitTorus_baseChange hCT
  let q' : G.val ⟶ C'.val := F.map q
  let U₀ := contractingSubgroup D
  let U : ClosedSubgroup B.val := pushSubgroup U₀ e.symm
  have hk : IsSchemeKernel q U := transported_kernel e (Iso.refl _) (by
    change 𝟙 _ ≫ U₀.inclusion = (U₀.inclusion ≫ e.inv) ≫ e.hom
    simp) D.isKernel
  let U' : ClosedSubgroup G.val := extendSubgroup K U
  have hk' : IsSchemeKernel q' U' := baseChangeKernelSquare q U.inclusion hk
  have : Smooth P.G.val.X.hom := P.reductive.1
  have hUn : IsUnipotent (closedSubgroupAlgebraicGroup U) :=
    contractingSubgroupUnipotent P.G (c ≫ P.T.inclusion) D
  have hUn' : IsUnipotent (closedSubgroupAlgebraicGroup U') :=
    (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension
      (K := K) (closedSubgroupAlgebraicGroup U)).mpr hUn
  obtain ⟨hBs, hBc⟩ := borel_smooth_connected P
  have hs : Smooth G.val.X.hom := MorphismProperty.pullback_snd _ _ hBs
  have : GeometricallyConnected B.val.X.hom := hBc
  have : GeometricallyConnected G.val.X.hom :=
    MorphismProperty.pullback_snd _ _ hBc
  have : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  have : Group.IsSolvable (rationalSections U'.group) :=
    unipotent_sections_solvable (closedSubgroupAlgebraicGroup U') hUn'
  have : IsCommMonObj C'.val.X := torus_commutative C' (isTorus_of_split hC')
  have : Group.IsSolvable (rationalSections C'.val) := inferInstance
  have hqi' : T'.inclusion ≫ q' = (F.mapIso d).hom := by
    change F.map i ≫ F.map q = F.map d.hom
    rw [← F.map_comp, hqi]
  have : IsIso (T'.inclusion ≫ q') := hqi' ▸ (inferInstance : IsIso (F.mapIso d).hom)
  exact ⟨hs, inferInstance, solvable_of_schemeKernel (G := G) (Q := C') q' hk' hs inferInstance,
    (solvable_maximal_torus_iff G T').mp
      (maximal_of_iso_projection (D := C') hk' hUn' hC' T')⟩

open private overBase familyAmbient_left from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

private theorem imageFamily_points (P : ClosedSubgroup B) {S V : SchemeOver k}
    (hP : Smooth P.group.X.hom) (f : relativePoints B S ≅ relativePoints B S)
    (a : V ⟶ S) (z : V ⟶ B.X) :
    (∃ y : V ⟶ (imageFamily P hP f).overField,
      y ≫ (imageFamily P hP f).ambient = lift z a) ↔
      ∃ t : V ⟶ P.group.X, evaluate f.hom (Over.mk a) (t ≫ P.inclusion.hom.hom) = z := by
  let Q := imageFamily P hP f
  let U := Over.mk a
  let A := S.iteratedSliceForward.obj U
  let e := sliceObjectIso U
  let w := (scalarPointEquiv B U).symm z
  have hw : scalarPoint w = z := (scalarPointEquiv B U).apply_symm_apply z
  have heb : e.inv ≫ overBase S A = a := Over.OverMorphism.ext rfl
  have hl : e.inv ≫ lift (relativePoint w) (overBase S A) = lift z a := by
    rw [comp_lift, heb]
    change lift (scalarPoint w) a = lift z a
    rw [hw]
  have hr : e.hom ≫ lift z a = lift (relativePoint w) (overBase S A) := by
    rw [← hl, Iso.hom_inv_id_assoc]
  have hp := factors_relative_iff Q.inclusion.hom.hom (familyAmbient_left Q) (p := w)
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hp.mpr ⟨e.hom ≫ y, by rw [Category.assoc, hy, hr]⟩
    refine ⟨scalarPoint t, ?_⟩
    have h := congrArg (fun p ↦ scalarPoint (U := U) p) ht
    change scalarPoint ((t ≫ ((Over.pullback S.hom).mapGrp.map P.inclusion).hom.hom) ≫
      (representedAut f).hom.hom.hom) = scalarPoint w at h
    rw [representedAut_hom, scalarPoint_natural, hw] at h
    exact h
  · rintro ⟨t, ht⟩
    let t' := (scalarPointEquiv P.group U).symm t
    have ht' : scalarPoint t' = t := (scalarPointEquiv P.group U).apply_symm_apply t
    have htw : t' ≫ Q.inclusion.hom.hom = w := by
      apply (scalarPointEquiv B U).injective
      change scalarPoint ((t' ≫ ((Over.pullback S.hom).mapGrp.map P.inclusion).hom.hom) ≫
        (representedAut f).hom.hom.hom) = scalarPoint w
      rw [representedAut_hom, scalarPoint_natural, ht', hw]
      exact ht
    obtain ⟨y, hy⟩ := hp.mp ⟨t', htw⟩
    exact ⟨e.inv ≫ y, by rw [Category.assoc, hy, hl]⟩

private def conjugation {V : SchemeOver k} (g : V ⟶ B.X) :
    relativePoints B V ⟶ relativePoints B V where
  app U := GrpCat.ofHom ((MulAut.conj (U.unop.hom ≫ g)).toMonoidHom)
  naturality := by
    intro U W a
    apply GrpCat.ext
    intro x
    change U.unop.left ⟶ B.X at x
    change (W.unop.hom ≫ g) * (a.unop.left ≫ x) * (W.unop.hom ≫ g)⁻¹ =
      a.unop.left ≫ ((U.unop.hom ≫ g) * x * (U.unop.hom ≫ g)⁻¹)
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, Over.w]

/-- Equal images of two monic maps of group-valued functors give an isomorphism
of their sources, by uniqueness of the comparison on each test. -/
private theorem iso_of_equal_ranges {C : Type (u + 1)} [Category.{u} C]
    {F Y : C ⥤ GrpCat.{u}} (α β : F ⟶ Y)
    (hα : ∀ U, Function.Injective (α.app U))
    (hβ : ∀ U, Function.Injective (β.app U))
    (h : ∀ U z, (∃ x, α.app U x = z) ↔ ∃ x, β.app U x = z) :
    ∃ t : F ≅ F, t.hom ≫ β = α := by
  classical
  have hfact (U : C) (x : F.obj U) : ∃ y, β.app U y = α.app U x :=
    (h U (α.app U x)).mp ⟨x, rfl⟩
  let v (U : C) (x : F.obj U) : F.obj U := (hfact U x).choose
  have hv (U : C) (x : F.obj U) : β.app U (v U x) = α.app U x := (hfact U x).choose_spec
  let e (U : C) : F.obj U ≃* F.obj U := MulEquiv.ofBijective
    (show F.obj U →* F.obj U from
      { toFun := v U
        map_one' := hβ U (by simp only [hv, map_one])
        map_mul' x y := hβ U (by simp only [hv, map_mul]) })
    ⟨fun x y exy ↦ hα U ((hv U x).symm.trans ((congrArg (β.app U) exy).trans (hv U y))),
      fun y ↦ by
        obtain ⟨x, hx⟩ := (h U (β.app U y)).mpr ⟨y, rfl⟩
        exact ⟨x, hβ U ((hv U x).trans hx)⟩⟩
  refine ⟨NatIso.ofComponents (fun U ↦ (e U).toGrpIso) ?_, ?_⟩
  · intro U W a
    apply GrpCat.ext
    intro x
    change v W (F.map a x) = F.map a (v U x)
    apply hβ W
    rw [hv]
    have h₁ := ConcreteCategory.congr_hom (α.naturality a) x
    have h₂ := ConcreteCategory.congr_hom (β.naturality a) (v U x)
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    exact h₁.trans ((congrArg (fun z ↦ Y.map a z) (hv U x).symm).trans h₂.symm)
  · ext U x
    exact hv U x

private theorem aligns_of_conjugates (P : ClosedSubgroup B) {S V : SchemeOver k}
    (hP : Smooth P.group.X.hom) (f : relativePoints B S ≅ relativePoints B S)
    (b : V ⟶ S) (g : V ⟶ B.X) (hg : Conjugates P (imageFamily P hP f) b g) :
    Aligns P.inclusion f b := by
  let i := Functor.whiskerLeft (Over.forget V).op (yonedaGrp.map P.inclusion)
  let α := i ≫ (restrict b f).hom
  let β := i ≫ conjugation g
  have hm : Mono P.inclusion.hom.hom := mono_over _ P.isClosedImmersion
  have hi (U : (Over V)ᵒᵖ) : Function.Injective (i.app U) :=
    fun _ _ h ↦ (cancel_mono P.inclusion.hom.hom).mp h
  have hα (U : (Over V)ᵒᵖ) : Function.Injective (α.app U) :=
    (ConcreteCategory.bijective_of_isIso ((restrict b f).hom.app U)).injective.comp (hi U)
  have hβ (U : (Over V)ᵒᵖ) : Function.Injective (β.app U) :=
    (MulAut.conj (U.unop.hom ≫ g)).injective.comp (hi U)
  obtain ⟨t, ht⟩ := iso_of_equal_ranges α β hα hβ (by
    intro U
    obtain ⟨W, w, hw⟩ := Over.mk_surjective U.unop
    rw [← op_unop U, ← hw]
    intro z
    change W ⟶ B.X at z
    exact ((imageFamily_points P hP f (w ≫ b) z).symm.trans
      ((conjugates_iff_factorizations.mp hg) W w z)))
  refine ⟨g⁻¹, t, fun U x ↦ ?_⟩
  have eq := NatTrans.congr_app ht (op U)
  have h := congrArg (fun m : (relativePoints P.group V).obj (op U) ⟶
    (relativePoints B V).obj (op U) ↦ m x) eq
  let y : U.left ⟶ B.X := evaluate f.hom ((Over.map b).obj U) (x ≫ P.inclusion.hom.hom)
  change (U.hom ≫ g) * (evaluate t.hom U x ≫ P.inclusion.hom.hom) * (U.hom ≫ g)⁻¹ = y at h
  change (U.hom ≫ g⁻¹) * y * (U.hom ≫ g⁻¹)⁻¹ = _
  rw [← h, GrpObj.comp_inv]
  group

open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open private solvable_tori_conjugate from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem scalarPoint_constant {G : GroupScheme k} {S V : SchemeOver k}
    (a : V ⟶ S) (g : 𝟙_ (Over S.left) ⟶ (relativeGroup G S).X) :
    scalarPoint (U := Over.mk a) (toUnit _ ≫ g) =
      a ≫ scalarPoint (U := Over.mk (𝟙 S)) (toUnit _ ≫ g) := by
  let f : Over.mk a ⟶ Over.mk (𝟙 S) := Over.homMk a
  have h := scalarPoint_comp f (toUnit _ ≫ g)
  change scalarPoint (S.iteratedSliceForward.map f ≫ toUnit _ ≫ g) = _
  simp only [← Category.assoc, comp_toUnit] at h
  exact h

/-- Transport a conjugacy over a field to the relative image family, tested on
all schemes over that field. -/
private theorem imageFamily_conjugates {S V : SchemeOver k} (P : ClosedSubgroup B)
    (hP : Smooth P.group.X.hom) (f : relativePoints B S ≅ relativePoints B S) (a : V ⟶ S)
    (g : 𝟙_ (Over V.left) ⟶ (relativeGroup B V).X)
    (e : relativeGroup P.group V ≅ relativeGroup P.group V)
    (he :
      let i := (Over.pullback V.hom).mapGrp.map P.inclusion
      (e.hom ≫ i ≫ (representedAut (restrict a f)).hom).hom.hom =
        (toUnit _ ≫ g) * i.hom.hom * (toUnit _ ≫ g)⁻¹) :
    Conjugates P (imageFamily P hP f) a
      (scalarPoint (U := Over.mk (𝟙 V)) (toUnit _ ≫ g)) := by
  apply conjugates_iff_factorizations.mpr
  intro W v z
  rw [imageFamily_points]
  let U := Over.mk v
  let i := (Over.pullback V.hom).mapGrp.map P.inclusion
  let gg : W ⟶ B.X := v ≫ scalarPoint (U := Over.mk (𝟙 V)) (toUnit _ ≫ g)
  let F := representedAut (restrict a f)
  have he' (x : V.iteratedSliceForward.obj U ⟶ (relativeGroup P.group V).X) :
      evaluate f.hom (Over.mk (v ≫ a)) (scalarPoint (U := U) x ≫ P.inclusion.hom.hom) =
        gg * (show W ⟶ B.X from scalarPoint (U := U) (x ≫ e.inv.hom.hom) ≫
          P.inclusion.hom.hom) * gg⁻¹ := by
    let y := x ≫ e.inv.hom.hom
    let g₀ : V.iteratedSliceForward.obj U ⟶ (relativeGroup B V).X := toUnit _ ≫ g
    have hd : y ≫ e.hom.hom.hom = x := by
      let j := (Grp.forget (Over V.left)).mapIso e
      change (x ≫ j.inv) ≫ j.hom = x
      rw [Category.assoc, j.inv_hom_id]
      exact Category.comp_id x
    have hc : (x ≫ i.hom.hom) ≫ F.hom.hom.hom =
        g₀ * (y ≫ i.hom.hom) * g₀⁻¹ := calc
      _ = y ≫ (e.hom ≫ i ≫ F.hom).hom.hom := by
        change (x ≫ i.hom.hom) ≫ F.hom.hom.hom =
          y ≫ e.hom.hom.hom ≫ i.hom.hom ≫ F.hom.hom.hom
        rw [← Category.assoc y, hd, Category.assoc]
      _ = _ := by
        rw [he]
        simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit]
        rfl
    have h' := congrArg (fun p ↦ (scalarPointEquiv B U) p) hc
    rw [map_mul, map_mul, map_inv] at h'
    change scalarPoint (U := U) ((x ≫ i.hom.hom) ≫ F.hom.hom.hom) =
      scalarPoint (U := U) g₀ * scalarPoint (U := U) (y ≫ i.hom.hom) *
        (scalarPoint (U := U) g₀)⁻¹ at h'
    rw [representedAut_hom, scalarPoint_natural, scalarPoint_natural] at h'
    have hg₀ : scalarPoint (U := U) g₀ = gg := scalarPoint_constant v g
    rw [hg₀] at h'
    exact h'
  constructor
  · rintro ⟨t, ht⟩
    let x := (scalarPointEquiv P.group U).symm t
    have hx : scalarPoint (U := U) x = t := (scalarPointEquiv P.group U).apply_symm_apply t
    have h := he' x
    rw [hx] at h
    exact ⟨scalarPoint (U := U) (x ≫ e.inv.hom.hom), h.symm.trans ht⟩
  · rintro ⟨t, ht⟩
    let y := (scalarPointEquiv P.group U).symm t
    have hy : scalarPoint (U := U) y = t := (scalarPointEquiv P.group U).apply_symm_apply t
    let x := y ≫ e.hom.hom.hom
    have hx : x ≫ e.inv.hom.hom = y := by
      let j := (Grp.forget (Over V.left)).mapIso e
      change (y ≫ j.hom) ≫ j.inv = y
      rw [Category.assoc, j.hom_inv_id]
      exact Category.comp_id y
    exact ⟨scalarPoint (U := U) x, (he' x).trans (by rwa [hx, hy])⟩

set_option maxHeartbeats 500000 in
private theorem imageFamily_geometricType (P : SplitBorelPair k)
    (i : P.T.group ⟶ P.B.group) (hi : i ≫ P.B.inclusion = P.T.inclusion)
    {S : SchemeOver k} (hP : Smooth P.T.group.X.hom)
    (f : relativePoints P.B.group S ≅ relativePoints P.B.group S) :
    SameGeometricType (restrictSubgroup P.T P.B i hi)
      (imageFamily (restrictSubgroup P.T P.B i hi) hP f) := by
  intro K _ _ _ a
  let V := (testSpec k).obj (op (CommAlgCat.of k K))
  let G₀ := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup P.B)
  let G : AffineAlgebraicGroup K := ⟨relativeGroup P.B.group V, G₀.property⟩
  let T₀ := extendSubgroup K (restrictSubgroup P.T P.B i hi)
  let iV := (Over.pullback V.hom).mapGrp.map i
  let T : ClosedSubgroup G.val := ⟨relativeGroup P.T.group V, iV, T₀.isClosedImmersion⟩
  let b : G.val ≅ G.val := representedAut (restrict a f)
  let T' := transportSubgroup b T
  obtain ⟨hs, hc, hv, ht₀⟩ := geometric_borel_torus P i hi K
  have ht : IsMaximalTorus T := ht₀
  have ht' : IsMaximalTorus T' := maximal_of_square b T T' (Iso.refl _) (by
    change 𝟙 _ ≫ (T.inclusion ≫ b.hom) = _
    rw [Category.id_comp]) ht
  obtain ⟨g, e, he⟩ := solvable_tori_conjugate GeometricTorusSplitting.splitting
    GeometricTorusSplitting.conjugacy G hs hc hv T T' ht ht'
  refine ⟨_, imageFamily_conjugates (restrictSubgroup P.T P.B i hi) hP f a g e ?_⟩
  dsimp only [ConjugatesSubgroups] at he
  rw [show T'.inclusion = T.inclusion ≫ b.hom from rfl] at he
  exact he

open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme
open private conjugates_of_sameSubgroup from LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter

/-- The relative Borel automorphism can be made to preserve the specified
maximal torus by conjugation on an fppf covering sieve. -/
theorem relativeTorusAlignment : Statement.{u} := by
  intro k _ P i hi S f
  apply alignment_affineLocal i _ f
  intro R a
  let B := closedSubgroupAlgebraicGroup P.B
  let T := restrictSubgroup P.T P.B i hi
  have hT : Smooth T.group.X.hom := splitTorusSmooth P.split
  let Q := imageFamily T hT a
  obtain ⟨c, E, hE⟩ := torus_is_opposite_limit P i hi
  have hQ : SameGeometricType T Q := imageFamily_geometricType P i hi hT a
  have hQE : SameGeometricType E.parabolic Q := by
    intro K _ _ _ b
    obtain ⟨g, hg⟩ := hQ K b
    exact ⟨g, conjugates_of_sameSubgroup hE hg⟩
  obtain ⟨Z, p, g, hp, hg⟩ := smooth_limit_transporter B (borel_smooth_connected P).1 E R Q hQE
  apply fppf_mem p hp
  exact aligns_of_conjugates T hT a p g (conjugates_of_sameSubgroup ⟨hE.2, hE.1⟩ hg)

end

end LinearAlgebraicGroups.Descent.RelativeTorusAlignment
