import LinearAlgebraicGroups.Affine.GenericFreeness
import LinearAlgebraicGroups.Affine.HopfAlgebras
import Specs.LinearAlgebraicGroups.Affine.DominantMapOverReducedGroup
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

namespace LinearAlgebraicGroups

universe u

noncomputable section

/-- A nonempty reduced affine Noetherian scheme has a nonempty integral principal open. -/
private theorem exists_domain_away (A : Type u) [CommRing A] [Nontrivial A]
    [IsNoetherianRing A] [IsReduced A] : ∃ s : A, IsDomain (Localization.Away s) := by
  classical
  let X := PrimeSpectrum A
  let Z := irreducibleComponent (Classical.choice (inferInstance : Nonempty X))
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents _
  -- Remove the other components before choosing the basic open.
  let V : Set X := (⋃₀ (irreducibleComponents X \ {Z}))ᶜ
  have hV : IsOpen V := by
    rw [show V = (⋃₀ (irreducibleComponents X \ {Z}))ᶜ from rfl,
      Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hcl : closure V = Z :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents Z hZ
  have hne : V.Nonempty := by
    by_contra! hempty
    exact hZ.1.nonempty.ne_empty (by rw [← hcl, hempty, closure_empty])
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨s, rfl⟩, hsx, hsV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hV) x hx
  have hs : IsIrreducible (PrimeSpectrum.basicOpen s : Set X) :=
    hZ.1.2.subset_irreducible ⟨x, hsx⟩ (PrimeSpectrum.basicOpen s).2
      Set.Subset.rfl (hsV.trans (hcl ▸ subset_closure))
  have he := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away s) s
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away s) s
  have hi : IrreducibleSpace (PrimeSpectrum (Localization.Away s)) := by
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible Set.univ
    have heq : PrimeSpectrum.comap (algebraMap A (Localization.Away s)) ⁻¹'
        (PrimeSpectrum.basicOpen s : Set X) = Set.univ := by
      rw [← hr]
      exact Set.eq_univ_of_forall fun x ↦ Set.mem_range_self x
    rw [← heq]
    exact hs.preimage he (by rw [hr, Set.inter_self]; exact hs.nonempty)
  let : IrreducibleSpace ↥(Spec (CommRingCat.of (Localization.Away s))) := hi
  exact ⟨s, (affine_isIntegral_iff (CommRingCat.of (Localization.Away s))).mp
    (isIntegral_of_irreducibleSpace_of_isReduced _)⟩

private abbrev awaySpec {A : Type u} [CommRing A] (s : A) :
    Spec (CommRingCat.of (Localization.Away s)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))

private abbrev awayMapSpec {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (s : A) :
    Spec (CommRingCat.of (Localization.Away (f s))) ⟶
      Spec (CommRingCat.of (Localization.Away s)) :=
  Spec.map (CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away s)
    (Localization.Away (f s)) f s))

private theorem awayMapSpec_isPullback {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (s : A) :
    IsPullback (awaySpec (f s)) (awayMapSpec f s)
      (Spec.map (CommRingCat.ofHom f)) (awaySpec s) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) s,
      Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) (f s)]
    exact PrimeSpectrum.comap_basicOpen f s

private theorem exists_faithfullyFlat_chart {A B : Type u} [CommRing A] [CommRing B]
    [Nontrivial A] [IsNoetherianRing A] [IsReduced A] [Algebra A B] [Algebra.FiniteType A B]
    (hf : Function.Injective (algebraMap A B)) :
    ∃ (V W : Scheme.{u}) (j : V ⟶ Spec (CommRingCat.of A))
      (i : W ⟶ Spec (CommRingCat.of B)) (g : W ⟶ V),
      Nonempty V ∧ IsOpenImmersion j ∧
      IsPullback i g (Spec.map (CommRingCat.ofHom (algebraMap A B))) j ∧
      Flat g ∧ Surjective g := by
  obtain ⟨s, hs⟩ := exists_domain_away A
  let f := algebraMap A B
  let A' := Localization.Away s
  let B' := Localization.Away (f s)
  let : Algebra A' B' := localizationAlgebra (Submonoid.powers s) B
  have hf' : algebraMap A' B' = IsLocalization.Away.map A' B' f s := rfl
  have hf't : Algebra.FiniteType A' B' := by
    rw [← RingHom.finiteType_algebraMap, hf']
    exact RingHom.localization_away_map_finiteType A B A' B' f s
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hf'i : Function.Injective (algebraMap A' B') := by
    rw [hf', IsLocalization.Away.map_injective_iff]
    intro a ha
    exact ⟨0, by simpa using hf (ha.trans f.map_zero.symm)⟩
  obtain ⟨t, ht, I, hI, ⟨b⟩⟩ := genericFreeness_of_injective hf'i
  let : Algebra (Localization.Away t) (Localization.Away (algebraMap A' B' t)) :=
    localizationAlgebra (Submonoid.powers t) B'
  have hdom := Localization.Away.isDomain ht
  have : Nontrivial (Localization.Away (algebraMap A' B' t)) := by
    let v := b (Classical.choice hI)
    exact ⟨⟨v, 0, b.ne_zero _⟩⟩
  have := Module.Free.of_basis b
  have hff : (algebraMap (Localization.Away t)
    (Localization.Away (algebraMap A' B' t))).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hfg : Flat (awayMapSpec (algebraMap A' B') t) ∧
      Surjective (awayMapSpec (algebraMap A' B') t) :=
    (flat_and_surjective_SpecMap_iff _).mpr hff
  refine ⟨_, _, awaySpec t ≫ awaySpec s, awaySpec (algebraMap A' B' t) ≫ awaySpec (f s),
    awayMapSpec (algebraMap A' B') t, inferInstance, inferInstance, ?_, hfg⟩
  exact ((awayMapSpec_isPullback (algebraMap A' B') t).flip.paste_vert
    (awayMapSpec_isPullback f s).flip).flip

private theorem mulRight_natural {k : Type u} [Field k] {G H : Specs.GroupScheme k}
    (f : G ⟶ H) (p : 𝟙_ (SchemeOver k) ⟶ G.X) :
    (GrpObj.mulRight p).hom ≫ f.hom.hom =
      f.hom.hom ≫ (GrpObj.mulRight (p ≫ f.hom.hom)).hom := by
  simp [GrpObj.mulRight, IsMonHom.mul_hom, lift_map_assoc, comp_lift_assoc,
    comp_toUnit_assoc]

private theorem point_comp_mulRight {k : Type u} [Field k] {G : Specs.GroupScheme k}
    (p q : 𝟙_ (SchemeOver k) ⟶ G.X) :
    p ≫ (GrpObj.mulRight q).hom = p * q := by
  simp [GrpObj.mulRight, CategoryTheory.Hom.mul_def, comp_lift_assoc, comp_toUnit_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty faithfully flat chart spreads to a dense homomorphism of group schemes
over an algebraically closed field. -/
private theorem flat_and_surjective_of_chart {k : Type u} [Field k] [IsAlgClosed k]
    {G H : Specs.GroupScheme k} [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (f : G ⟶ H) (hd : DenseRange f.hom.hom.left)
    {V W : Scheme.{u}} [Nonempty V] (j : V ⟶ H.X.left) [IsOpenImmersion j]
    (i : W ⟶ G.X.left) (g : W ⟶ V) (hg : IsPullback i g f.hom.hom.left j)
    (hflat : Flat g) (hsurj : Surjective g) :
    Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
  let q := f.hom.hom.left
  let Q := f.hom.hom
  let e := IsLocalRing.closedPoint k
  let P := 𝟙_ (SchemeOver k) ⟶ G.X
  let tX (x : P) := (GrpObj.mulRight x).hom.left
  let tY (x : P) := (GrpObj.mulRight (x ≫ Q)).hom.left
  have hG : JacobsonSpace ↥G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have hH : JacobsonSpace ↥H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hclosed : Dense (closedPoints G.X.left) := dense_iff_closure_eq.mpr closure_closedPoints
  -- The morphism has dense image even when restricted to rational points of the source.
  have hpoints : DenseRange (fun p : P ↦ q (p.left e)) := by
    refine (hd.dense_image q.continuous hclosed).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    change IsClosed {x} at hx
    refine ⟨Over.homMk (pointOfClosedPoint G.X.hom x hx)
      (pointOfClosedPoint_comp G.X.hom x hx), ?_⟩
    change q (pointOfClosedPoint G.X.hom x hx e) = q x
    exact congrArg q (pointOfClosedPoint_apply G.X.hom x hx e)
  have hclosedCover (y : H.X.left) (hy : IsClosed {y}) :
      ∃ x : P, ∃ v : V, (j ≫ tY x) v = y := by
    let p : 𝟙_ (SchemeOver k) ⟶ H.X :=
      Over.homMk (pointOfClosedPoint H.X.hom y hy) (pointOfClosedPoint_comp H.X.hom y hy)
    have hp : p.left e = y := pointOfClosedPoint_apply _ _ _ _
    -- Pull the chart back by z ↦ (z * p⁻¹)⁻¹.
    let a : H.X ⟶ H.X := (GrpObj.mulRight p⁻¹).hom ≫ ι[H.X]
    have : IsIso a := by dsimp [a]; infer_instance
    have hsurja : Function.Surjective a.left :=
      ((Over.forget _).mapIso (asIso a)).hom.surjective
    have hopen : IsOpen (a.left ⁻¹' Set.range j) :=
      (IsOpenImmersion.isOpen_range j).preimage a.left.continuous
    have hne : (a.left ⁻¹' Set.range j).Nonempty := by
      obtain ⟨z, hz⟩ := hsurja (j (Classical.choice ‹Nonempty V›))
      exact ⟨z, _, hz.symm⟩
    obtain ⟨_, hz, ⟨x, rfl⟩⟩ := hpoints.inter_open_nonempty _ hopen hne
    have ha : (x ≫ Q) ≫ a = p * (x ≫ Q)⁻¹ := by
      rw [show a = (GrpObj.mulRight p⁻¹).hom ≫ ι[H.X] from rfl, ← Category.assoc,
        point_comp_mulRight, GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id,
        mul_inv_rev, inv_inv]
    have htrans : ((x ≫ Q) ≫ a) ≫ (GrpObj.mulRight (x ≫ Q)).hom = p := by
      rw [point_comp_mulRight, ha, mul_assoc, inv_mul_cancel, mul_one]
    obtain ⟨v, hv⟩ := hz
    refine ⟨x, v, ?_⟩
    have heq := congrArg (fun b : 𝟙_ (SchemeOver k) ⟶ H.X ↦ b.left e) htrans
    change tY x (a.left (q (x.left e))) = p.left e at heq
    change tY x (j v) = y
    rw [hv, heq, hp]
  let U (x : P) := (j ≫ tY x).opensRange
  have hopen (x : P) : IsOpenImmersion (j ≫ tY x) := by
    dsimp [tY]
    infer_instance
  have hcover (y : H.X.left) : ∃ x : P, ∃ v : V, (j ≫ tY x) v = y := by
    by_contra! hy
    have hne : (⋃ x, (U x : Set H.X.left))ᶜ.Nonempty := by
      refine ⟨y, ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      exact fun ⟨x, v, hv⟩ ↦ hy x v hv
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hne
      (isOpen_iUnion fun x ↦ (U x).2).isClosed_compl.isLocallyClosed
    obtain ⟨x, v, hv⟩ := hclosedCover z hzc
    exact hz (Set.mem_iUnion.mpr ⟨x, v, hv⟩)
  -- Equivariance transports the original pullback square to each member of the cover.
  let C : H.X.left.OpenCover :=
    Scheme.Cover.mkOfCovers P (fun _ ↦ V) (fun x ↦ j ≫ tY x) hcover hopen
  have hsquare (x : P) : IsPullback (i ≫ tX x) g q (j ≫ tY x) := by
    have hc : tX x ≫ q = q ≫ tY x :=
      congrArg (fun h : G.X ⟶ H.X ↦ h.left) (mulRight_natural f x)
    have hpb : IsPullback (tX x) q q (tY x) := by
      have : IsIso (tX x) := by dsimp [tX]; infer_instance
      have : IsIso (tY x) := by dsimp [tY]; infer_instance
      exact IsPullback.of_horiz_isIso ⟨hc⟩
    exact hg.paste_horiz hpb
  have hlocal (x : C.I₀) : Flat (C.pullbackHom q x) ∧ Surjective (C.pullbackHom q x) := by
    let sq := hsquare x
    change Flat (pullback.snd q (j ≫ tY x)) ∧ Surjective (pullback.snd q (j ≫ tY x))
    exact ⟨(MorphismProperty.cancel_left_of_respectsIso @AlgebraicGeometry.Flat.{u}
        sq.isoPullback.hom _).mp (sq.isoPullback_hom_snd.symm ▸ hflat),
      (MorphismProperty.cancel_left_of_respectsIso @Surjective sq.isoPullback.hom _).mp
      (sq.isoPullback_hom_snd.symm ▸ hsurj)⟩
  exact ⟨IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.Flat.{u}) C
      (fun x ↦ (hlocal x).1),
    IsZariskiLocalAtTarget.of_openCover C (fun x ↦ (hlocal x).2)⟩

/-- An injective morphism of finite-type commutative Hopf algebras over an algebraically
closed field is faithfully flat when its domain is reduced. -/
theorem faithfullyFlatOfInjectiveHopfOfReduced : Specs.FaithfullyFlatOfInjectiveHopfOfReduced.{u} := by
  intro k _ _ A B _ _ _ f hf
  let G := (hopfSpec (CommRingCat.of k)).obj (op B)
  let H := (hopfSpec (CommRingCat.of k)).obj (op A)
  let q : G ⟶ H := (hopfSpec (CommRingCat.of k)).map f.op
  have hq : q.hom.hom.left = Spec.map (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) :=
    (hopfSpecMorphism k f).1
  have hG : LocallyOfFiniteType G.X.hom :=
    (hopfSpec_locallyOfFiniteType_iff k B).mpr inferInstance
  have hH : LocallyOfFiniteType H.X.hom :=
    (hopfSpec_locallyOfFiniteType_iff k A).mpr inferInstance
  have hd : DenseRange q.hom.hom.left := by
    rw [hq]
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    change RingHom.ker f.hom.toAlgHom.toRingHom ≤ nilradical A
    rw [(RingHom.injective_iff_ker_eq_bot f.hom.toAlgHom.toRingHom).mp hf]
    exact bot_le
  let : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : Algebra A B := f.hom.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' f.hom.toAlgHom.comp_algebraMap.symm
  have : Algebra.FiniteType A B := .of_restrictScalars_finiteType k A B
  obtain ⟨V, W, j, i, g, hV, hj, hpb, hg, hgs⟩ := exists_faithfullyFlat_chart hf
  apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f.hom.toAlgHom.toRingHom)).mp
  rw [← hq]
  have hj' : IsOpenImmersion (Y := H.X.left) j := hj
  exact flat_and_surjective_of_chart q hd j i g (hq ▸ hpb) hg hgs

end
end LinearAlgebraicGroups
