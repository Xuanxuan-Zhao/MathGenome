import Specs.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Unramified.Field

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

private theorem isReduced_of_etale_over_domain (R A : Type u)
    [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    _root_.IsReduced A := by
  -- Flatness embeds the algebra in its étale generic fibre.
  let K := FractionRing R
  have : _root_.IsReduced (K ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Module.Flat.tensorProduct_mk_injective R A K)

private theorem isReduced_of_smooth_algebra (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : _root_.IsReduced A := by
  constructor
  intro a ha
  apply eq_zero_of_localization
  intro p hp
  let : p.IsPrime := hp.isPrime
  obtain ⟨s, hs, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth k p
  have hstd' : (algebraMap k (Localization.Away s)).IsStandardSmooth := by
    rwa [RingHom.isStandardSmooth_algebraMap]
  obtain ⟨n, φ, -, hφ⟩ := hstd'.exists_etale_mvPolynomial
  let := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) k) (Localization.Away s) := hφ
  have : _root_.IsReduced (Localization.Away s) :=
    isReduced_of_etale_over_domain (MvPolynomial (Fin n) k) _
  have hunit : IsUnit (algebraMap A (Localization.AtPrime p) s) :=
    IsLocalization.map_units _ (⟨s, hs⟩ : p.primeCompl)
  let lift : Localization.Away s →+* Localization.AtPrime p := IsLocalization.Away.lift s hunit
  have hlift (a : A) : lift (algebraMap A (Localization.Away s) a) =
      algebraMap A (Localization.AtPrime p) a := IsLocalization.Away.lift_eq s hunit a
  have he := congrArg lift (ha.map (algebraMap A (Localization.Away s))).eq_zero
  simpa only [hlift, map_zero] using he

private theorem isReduced_of_smooth_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : IsReduced X := by
  refine @IsReduced.of_openCover X X.affineCover ?_
  intro i
  let h := X.affineCover.f i ≫ f
  let φ := Spec.preimage h
  have hs : Smooth (Spec.map φ) := by
    have hmap : Spec.map φ = h := Spec.map_preimage h
    exact hmap.symm ▸ inferInstanceAs (Smooth (X.affineCover.f i ≫ f))
  have hφ : φ.hom.Smooth := HasRingHomProperty.Spec_iff.mp hs
  let := φ.hom.toAlgebra
  have : Algebra.Smooth k _ := hφ
  exact (affine_isReduced_iff _).mpr (isReduced_of_smooth_algebra k _)

private theorem geometricallyReduced_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ g Y fst snd h
  let : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  exact isReduced_of_smooth_over_field snd

private theorem smooth_smoothLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  exact iff_of_true x.property trivial

private theorem mem_smoothLocus_pullback {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] {x : ↥(pullback f g : Scheme.{u})}
    (hx : pullback.fst f g x ∈ f.smoothLocus) :
    x ∈ (pullback.snd f g).smoothLocus := by
  let U := f.smoothLocus
  let V := pullback.fst f g ⁻¹ᵁ U
  let e : V.toScheme ≅ pullback (U.ι ≫ f) g :=
    (pullbackRestrictIsoRestrict (pullback.fst f g) U).symm ≪≫
      pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g U.ι
  have he : e.hom ≫ pullback.snd (U.ι ≫ f) g = V.ι ≫ pullback.snd f g := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      pullbackSymmetry_hom_comp_snd_assoc]
    exact pullbackRestrictIsoRestrict_inv_fst_assoc _ _ _
  have : Smooth (U.ι ≫ f) := smooth_smoothLocus f
  have hv : Smooth (V.ι ≫ pullback.snd f g) := by
    rw [← he]
    infer_instance
  have h := (V.ι ≫ pullback.snd f g).smoothLocus_eq_top
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at h
  have hmem : (⟨x, hx⟩ : V) ∈ (⊤ : V.toScheme.Opens) := trivial
  rw [← h] at hmem
  exact hmem

private theorem smooth_of_smooth_after_fieldExtension {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : Smooth (pullback.snd f (fieldSpecMap k K))) : Smooth f := by
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := fieldSpecMap k K)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact h

/-- Translation takes the smooth locus at the identity to the smooth locus at a rational point. -/
theorem smoothAtRationalPoint : Specs.SmoothAtRationalPoint.{u} := by
  intro k _ G _ p
  let t := GrpObj.mulRight p
  have ht : η[G.X] ≫ t.hom = p := by
    simp only [t, GrpObj.mulRight, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, toUnit_unit]
    simpa only [Category.id_comp] using MonObj.lift_comp_one_left (𝟙 (𝟙_ (SchemeOver k))) p
  have hp : t.hom.left (groupIdentityPoint G) = p.left (IsLocalRing.closedPoint k) := by
    exact congrArg (fun a : 𝟙_ (SchemeOver k) ⟶ G.X ↦ a.left (IsLocalRing.closedPoint k)) ht
  change p.left (IsLocalRing.closedPoint k) ∈ G.X.hom.smoothLocus ↔
    groupIdentityPoint G ∈ G.X.hom.smoothLocus
  rw [← hp, ← t.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq]
  simp only [t.hom.w]

private theorem smooth_of_identity_over_algClosed {k : Type u} [Field k] [IsAlgClosed k]
    (G : Specs.GroupScheme k) [LocallyOfFiniteType G.X.hom] (h : SmoothAtIdentity G) :
    Smooth G.X.hom := by
  have := LocallyOfFiniteType.jacobsonSpace G.X.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints H
    G.X.hom.smoothLocus.2.isClosed_compl.isLocallyClosed
  let p : 𝟙_ (SchemeOver k) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom x hxc) (pointOfClosedPoint_comp G.X.hom x hxc)
  have hp := (smoothAtRationalPoint k G p).mpr h
  change p.left (IsLocalRing.closedPoint k) ∈ G.X.hom.smoothLocus at hp
  have he : p.left (IsLocalRing.closedPoint k) = x := pointOfClosedPoint_apply _ _ _ _
  exact hx (he ▸ hp)

private theorem identitySection_comp {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : Specs.GroupScheme k) :
    groupIdentitySection ((groupBaseChange k K).obj G) ≫
      pullback.fst G.X.hom (fieldSpecMap k K) = fieldSpecMap k K ≫ groupIdentitySection G := by
  change ((Functor.LaxMonoidal.ε (baseChange k K) ≫ (baseChange k K).map η[G.X]).left) ≫
      pullback.fst G.X.hom (fieldSpecMap k K) = _
  have he := Over.w (Functor.LaxMonoidal.ε (baseChange k K))
  change (Functor.LaxMonoidal.ε (baseChange k K)).left ≫
    pullback.snd (𝟙 _) (fieldSpecMap k K) = 𝟙 _ at he
  simp only [Over.comp_left, Category.assoc, baseChange, Over.pullback_map_left, pullback.lift_fst]
  simp only [Over.tensorUnit_hom]
  rw [← Category.assoc,
    show pullback.fst (𝟙 _) (fieldSpecMap k K) =
      pullback.snd (𝟙 _) (fieldSpecMap k K) ≫ fieldSpecMap k K by
        simpa only [Category.comp_id] using pullback.condition (f := 𝟙 _) (g := fieldSpecMap k K),
    ← Category.assoc, he, Category.id_comp]

private theorem smoothAtIdentity_pullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : Specs.GroupScheme k) [LocallyOfFiniteType G.X.hom] (h : SmoothAtIdentity G) :
    SmoothAtIdentity ((groupBaseChange k K).obj G) := by
  have he := congrArg (fun f : Spec (CommRingCat.of K) ⟶ G.X.left ↦
    f (IsLocalRing.closedPoint K)) (identitySection_comp (K := K) G)
  change pullback.fst G.X.hom (fieldSpecMap k K) (groupIdentityPoint ((groupBaseChange k K).obj G)) =
    groupIdentitySection G (fieldSpecMap k K (IsLocalRing.closedPoint K)) at he
  rw [Subsingleton.elim (fieldSpecMap k K (IsLocalRing.closedPoint K))
    (IsLocalRing.closedPoint k)] at he
  have hmem : groupIdentityPoint G ∈ G.X.hom.smoothLocus := h
  exact mem_smoothLocus_pullback G.X.hom (fieldSpecMap k K) (he.symm ▸ hmem)

private instance locallyOfFiniteType_groupBaseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] (G : Specs.GroupScheme k) [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType ((groupBaseChange k K).obj G).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (fieldSpecMap k K)))

private theorem smooth_of_identity {k : Type u} [Field k] (G : Specs.GroupScheme k)
    [LocallyOfFiniteType G.X.hom] (h : SmoothAtIdentity G) : Smooth G.X.hom := by
  let K := AlgebraicClosure k
  have hK := smooth_of_identity_over_algClosed ((groupBaseChange k K).obj G)
    (smoothAtIdentity_pullback (K := K) G h)
  exact smooth_of_smooth_after_fieldExtension G.X.hom hK

private theorem smoothAtIdentity_of_smooth {k : Type u} [Field k] (G : Specs.GroupScheme k)
    [LocallyOfFiniteType G.X.hom] (h : Smooth G.X.hom) : SmoothAtIdentity G := by
  let := h
  change groupIdentityPoint G ∈ G.X.hom.smoothLocus
  rw [G.X.hom.smoothLocus_eq_top]
  trivial

/-- Smoothness, geometric reducedness and smoothness at the identity are equivalent. -/
theorem groupSmoothnessCriteria : Specs.GroupSmoothnessCriteria.{u} := by
  intro k _ G _
  refine ⟨⟨fun h ↦ geometricallyReduced_of_smooth G.X.hom, ?_⟩,
    ⟨smoothAtIdentity_of_smooth G, smooth_of_identity G⟩⟩
  intro h
  let : GrpObj (Over.mk G.X.hom) := G.grp
  exact AlgebraicGeometry.smooth_of_grpObj G.X.hom

/-- The criterion restricted to finite-type affine group schemes. -/
theorem affineGroupSmoothnessCriteria : Specs.AffineGroupSmoothnessCriteria.{u} := by
  intro k _ G
  let := G.2.2.1
  exact groupSmoothnessCriteria k G.1

/-- The identity is smooth over the ground field exactly when it is smooth after scalar extension. -/
theorem smoothAtIdentityBaseChange : Specs.SmoothAtIdentityBaseChange.{u} := by
  intro k K _ _ _ G _
  refine ⟨fun h ↦ smoothAtIdentity_of_smooth G ?_, smoothAtIdentity_pullback G⟩
  exact smooth_of_smooth_after_fieldExtension G.X.hom (smooth_of_identity _ h)

/-- At any geometric point of a scalar extension, smoothness is equivalent to smoothness
at the original identity. -/
theorem smoothAtGeometricPoint : Specs.SmoothAtGeometricPoint.{u} := by
  intro k Ω _ _ _ _ G _ p
  exact (smoothAtRationalPoint Ω ((groupBaseChange k Ω).obj G) p).trans
    (smoothAtIdentityBaseChange k Ω G)

/-- A reduced group scheme locally of finite type over a perfect field is smooth. -/
theorem smoothOfReducedOverPerfectField : Specs.SmoothOfReducedOverPerfectField.{u} := by
  intro k _ _ G _ h
  let K := AlgebraicClosure k
  let g := fieldSpecMap k K
  let H := (groupBaseChange k K).obj G
  have : LocallyOfFiniteType H.X.hom := locallyOfFiniteType_groupBaseChange G
  have : Nonempty G.X.left := ⟨groupIdentityPoint G⟩
  obtain ⟨x, hx⟩ := G.X.hom.dense_smoothLocus_of_perfectField.nonempty
  obtain ⟨y, hy⟩ := (Surjective.surj (f := pullback.fst G.X.hom g)) x
  have hy' : y ∈ H.X.hom.smoothLocus :=
    mem_smoothLocus_pullback G.X.hom g (hy.symm ▸ hx)
  have : JacobsonSpace ↥H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hnonempty : (H.X.hom.smoothLocus : Set H.X.left).Nonempty := ⟨y, hy'⟩
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hnonempty H.X.hom.smoothLocus.2.isLocallyClosed
  let p : 𝟙_ (SchemeOver K) ⟶ H.X :=
    Over.homMk (pointOfClosedPoint H.X.hom z hzc) (pointOfClosedPoint_comp H.X.hom z hzc)
  have he : p.left (IsLocalRing.closedPoint K) = z := pointOfClosedPoint_apply _ _ _ _
  have hp : SmoothAtIdentity H := (smoothAtRationalPoint K H p).mp (he.symm ▸ hz)
  exact smooth_of_smooth_after_fieldExtension G.X.hom (smooth_of_identity_over_algClosed H hp)

/-- The residue field map at the rational identity is an isomorphism. -/
theorem identityResidueFieldOverBase : Specs.IdentityResidueFieldOverBase.{u} := by
  intro k _ G
  let e := groupIdentitySection G
  let z : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
  have h : e ≫ G.X.hom = 𝟙 _ := (η[G.X]).w
  let i := G.X.hom.residueFieldMap (e z)
  let r := e.residueFieldMap z
  have hz : G.X.hom (e z) = z :=
    congrArg (fun s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) ↦ s z) h
  let transport := (Spec (CommRingCat.of k)).residueFieldCongr hz
  have hc := Scheme.Hom.residueFieldMap_congr h z
  simp only [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_id] at hc
  have hc : i ≫ r = transport.hom ≫ 𝟙 _ := by
    with_unfolding_all exact hc
  have : IsIso (i ≫ r) := hc.symm ▸ inferInstanceAs (IsIso (transport.hom ≫ 𝟙 _))
  have : Mono r := ConcreteCategory.mono_of_injective r (RingHom.injective r.hom)
  have : IsIso i := ⟨r ≫ inv (i ≫ r), by
    rw [← Category.assoc, IsIso.hom_inv_id], by
    rw [← cancel_mono r]
    simp⟩
  change IsIso ((Scheme.Spec.residueFieldIsoOfField _).inv ≫ i)
  infer_instance

/-- The tangent dimension of a locally Noetherian scheme equals the embedding dimension
and bounds the local Krull dimension at every point. -/
theorem zariskiTangentDimension : Specs.ZariskiTangentDimension.{u} := by
  intro X _ x
  let A := X.presheaf.stalk x
  have h : Module.finrank (IsLocalRing.ResidueField A) (ZariskiTangentSpace X x) =
      (IsLocalRing.maximalIdeal A).spanFinrank := by
    rw [Subspace.dual_finrank_eq, IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ⟨h, h ▸ ringKrullDim_le_spanFinrank_maximalIdeal A⟩

/-- The tangent dimension at the identity equals its embedding dimension and bounds its
local Krull dimension. -/
theorem identityTangentDimension : Specs.IdentityTangentDimension.{u} := by
  intro k _ G _
  let E := IdentityResidueField G
  let V := IdentityTangentSpace G
  let : Algebra k E := (identityResidueRingHom G).toAlgebra
  let : Module k V := Module.compHom V (identityResidueRingHom G)
  have : IsScalarTower k E V := .of_algebraMap_smul fun _ _ ↦ rfl
  have h := identityResidueFieldOverBase k G
  let e : k ≃ₗ[k] E :=
    LinearEquiv.ofBijective (Algebra.linearMap k E) ((ConcreteCategory.isIso_iff_bijective _).mp h)
  have hE : Module.finrank k E = 1 := e.finrank_eq.symm.trans (CommSemiring.finrank_self k)
  have hV : Module.finrank k V = Module.finrank E V := by
    simpa only [hE, one_mul] using (Module.finrank_mul_finrank k E V).symm
  have := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  change Module.finrank k V = _ ∧ ringKrullDim _ ≤ (Module.finrank k V : WithBot ℕ∞)
  rw [hV]
  exact zariskiTangentDimension G.X.left (groupIdentityPoint G)

end

end LinearAlgebraicGroups
