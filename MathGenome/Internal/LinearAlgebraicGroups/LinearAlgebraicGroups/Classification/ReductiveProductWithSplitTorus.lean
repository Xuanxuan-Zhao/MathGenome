import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus

open _root_.LinearAlgebraicGroups.Specs
  (AffineAlgebraicGroup ClosedSubgroup GroupScheme IsNormalSubgroup subgroupConjugation)
open Specs.GeometricRadicals
open Specs.IntegralCentralQuotient
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup)

noncomputable section

open private splitFibreOfFreeLattice from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private torus_smooth_connected_solvable from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private torus_multiplicativeType from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private isTorus_iff_coordinates torus_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private splitTorus_baseChange geometricallyMaximal_of_maximal_split
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private isMonHom_of_comp_closed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private normalSubgroup_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

private abbrev integralTorus (M : Type u) [CommGroup M] :=
  HopfSpectrum IntegralRing.{u} (MonoidAlgebra IntegralRing.{u} M)

private theorem tensorClosedImmersion {S : Scheme.{u}} {U V A B : Over S}
    (f : U ⟶ A) (g : V ⟶ B) [IsClosedImmersion f.left] [IsClosedImmersion g.left] :
    IsClosedImmersion (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left, pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

private def affineProduct {k : Type u} [Field k] (G D : AffineAlgebraicGroup k) :
    AffineAlgebraicGroup k := by
  letI := G.property.1
  letI := D.property.1
  letI := G.property.2.1
  letI := D.property.2.1
  letI := G.property.2.2
  letI := D.property.2.2
  refine ⟨G.val ⊗ D.val, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsAffine (pullback G.val.X.hom D.val.X.hom))
  · change LocallyOfFiniteType (G.val.X ⊗ D.val.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  · change QuasiCompact (G.val.X ⊗ D.val.X).hom
    rw [Over.tensorObj_hom]
    infer_instance

section GeometricFibre

variable {k : Type u} [Field k]

/-- A normal subgroup of the product whose second projection is trivial
embeds as a closed normal subgroup of the first factor. -/
private theorem firstProjection_normal {G D : AffineAlgebraicGroup k}
    {N : GroupScheme k} (i : N ⟶ G.val ⊗ D.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hn : IsNormalSubgroup i)
    (hz : i ≫ snd G.val D.val = 0) :
    IsClosedImmersion (i ≫ fst G.val D.val).hom.hom.left ∧
      IsNormalSubgroup (i ≫ fst G.val D.val) := by
  let π := fst G.val D.val
  let s := lift (𝟙 G.val) (0 : G.val ⟶ D.val)
  have hs : s ≫ π = 𝟙 G.val := lift_fst _ _
  have hfac : (i ≫ π) ≫ s = i := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [s, π]
    · simp [s, hz]
  constructor
  · let := G.property.1
    let : IsSeparated s.hom.hom.left := inferInstance
    let : IsClosedImmersion ((i ≫ π).hom.hom.left ≫ s.hom.hom.left) := by
      change IsClosedImmersion (((i ≫ π) ≫ s).hom.hom.left)
      rw [hfac]
      exact hi
    exact IsClosedImmersion.of_comp _ s.hom.hom.left
  · let x := fst G.val.X N.X
    let y := snd G.val.X N.X
    obtain ⟨c, hc⟩ := normalSubgroup_conjugate_sections hn (x ≫ s.hom.hom) y
    refine ⟨c, ?_⟩
    change c ≫ i.hom.hom ≫ π.hom.hom = subgroupConjugation (i ≫ π)
    rw [← Category.assoc, hc]
    have hs' : s.hom.hom ≫ π.hom.hom = 𝟙 G.val.X :=
      congrArg (fun f : G.val ⟶ G.val => f.hom.hom) hs
    simp only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      hs', Category.comp_id, x, y]
    rfl

private theorem reductiveProduct [IsAlgClosed k] (G D : AffineAlgebraicGroup k)
    (hG : IsReductive G) (hD : IsSplitTorus D.val) : IsReductive (affineProduct G D) := by
  let P := affineProduct G D
  let := hG.2.1
  have hGc : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  obtain ⟨hDs, hDc, _⟩ := torus_smooth_connected_solvable D (lattice_torus_of_split hD)
  obtain ⟨hPs, hPc, _⟩ :=
    WordDomainGeometry.smoothConnectedGroupProduct G D hG.1 hGc hDs hDc
  let : ConnectedSpace P.val.X.left := hPc
  refine ⟨hPs, geometricallyConnected_of_connected P, ?_⟩
  -- Compute the radical over the algebraic closure used in IsReductive.
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := GeometricGroup G
  let D' := baseChangedAlgebraicGroup K D
  let e : (GeometricGroup P).val ≅ G'.val ⊗ D'.val :=
    (Functor.Monoidal.μIso F G.val D.val).symm
  let N := geometricUnipotentRadical P
  have hN := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest P
  let i := N.inclusion ≫ e.hom
  have hi : IsClosedImmersion i.hom.hom.left := by
    let := N.isClosedImmersion
    let : IsIso e.hom.hom.hom.left :=
      (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso e.hom
    change IsClosedImmersion (N.inclusion.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  have hn : IsNormalSubgroup i := by
    apply normalSubgroup_of_iso e.symm (Iso.refl N.group) (i := N.inclusion)
    · change (N.inclusion ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ N.inclusion
      simp
    · exact hN.1.2.2
  have hD' : IsTorus D'.val := lattice_torus_of_split (splitTorus_baseChange (K := K) hD)
  have hz : i ≫ snd G'.val D'.val = 0 :=
    Unipotent.homFromUnipotentToMultiplicativeType
      (closedSubgroupAlgebraicGroup N) D' _ hN.2.1
      (torus_multiplicativeType ((isTorus_iff_coordinates D').mp hD'))
  obtain ⟨hc, hnormal⟩ := firstProjection_normal (G := G') (D := D') i hi hn hz
  let J : ClosedSubgroup G'.val := ⟨N.group, i ≫ fst G'.val D'.val, hc⟩
  obtain ⟨j, hj⟩ :=
    (LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G).2.2
      J ⟨hN.1.1, hN.1.2.1, hnormal⟩ hN.2.1
  obtain ⟨trivial⟩ := hG.2.2
  have hjz : j = 0 := ((Grp.isZero_trivial (SchemeOver K)).of_iso trivial).eq_zero_of_tgt j
  have hJz : J.inclusion = 0 := by rw [← hj, hjz, zero_comp]
  let := J.isClosedImmersion
  let : Mono J.inclusion := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mono_of_mono_map
    (show Mono J.inclusion.hom.hom.left from inferInstance)
  exact ⟨(IsZero.of_mono_eq_zero J.inclusion hJz).iso (Grp.isZero_trivial _)⟩

private theorem maximalProduct {G D : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val)
    (hcentral : Specs.SubtorusCentralizer.IsCentralizer T T)
    (hc : IsClosedImmersion (T.inclusion ⊗ₘ 𝟙 D.val).hom.hom.left)
    (hT : IsTorus (T.group ⊗ D.val)) :
    IsMaximalTorus (⟨_, T.inclusion ⊗ₘ 𝟙 D.val, hc⟩ : ClosedSubgroup (G.val ⊗ D.val)) := by
  refine ⟨hT, ?_⟩
  intro S hS hTS
  obtain ⟨a, ha⟩ := hTS
  change a ≫ S.inclusion = T.inclusion ⊗ₘ 𝟙 D.val at ha
  -- Inside the larger torus, use the first factor at the identity of D.
  let s := lift (𝟙 T.group) (0 : T.group ⟶ D.val)
  let p := S.inclusion ≫ fst G.val D.val
  let q := S.inclusion ≫ snd G.val D.val
  have hsp : (s ≫ a) ≫ p = T.inclusion := by
    dsimp only [p]
    rw [Category.assoc, ← Category.assoc a S.inclusion, ha, tensorHom_fst, ← Category.assoc]
    simp [s]
  let : IsCommMonObj S.group.X := torus_commutative
    (closedSubgroupAlgebraicGroup (G := affineProduct G D) S) hS
  have hcomm : Centralizes T.inclusion p.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U x y
    let z := y ≫ (s ≫ a).hom.hom
    have hxy : Commute x z := show x * z = z * x from mul_comm x z
    have hproj := hxy.map (IsMonHom.monoidHom p.hom.hom U)
    change Commute (x ≫ p.hom.hom) ((y ≫ (s ≫ a).hom.hom) ≫ p.hom.hom) at hproj
    have hsp' : (s ≫ a).hom.hom ≫ p.hom.hom = T.inclusion.hom.hom :=
      congrArg (fun f : T.group ⟶ G.val => f.hom.hom) hsp
    rwa [Category.assoc, hsp'] at hproj
  obtain ⟨v, hv⟩ := (hcentral _ _).mp hcomm
  let := T.isClosedImmersion
  let := isMonHom_of_comp_closed v p T.inclusion hv
  let r : S.group ⟶ T.group := Grp.homMk v
  have hr : r ≫ T.inclusion = p := Grp.hom_ext _ _ hv
  refine ⟨lift r q, ?_⟩
  change lift r q ≫ (T.inclusion ⊗ₘ 𝟙 D.val) = S.inclusion
  apply CartesianMonoidalCategory.hom_ext
  · simp [hr, p]
  · simp [q]

end GeometricFibre

section IntegralTori

open Algebra.TensorProduct

variable {K : Type u} [CommRing K]

/-- The coordinate equivalence for a product of diagonalizable groups. -/
private def productGroupAlgebra (X Y : Type u) [CommGroup X] [CommGroup Y] :
    MonoidAlgebra K X ⊗[K] MonoidAlgebra K Y ≃ₐ[K] MonoidAlgebra K (X × Y) := by
  let a := (MonoidAlgebra.mapDomainBialgHom K (MonoidHom.inl X Y)).toAlgHom
  let b := (MonoidAlgebra.mapDomainBialgHom K (MonoidHom.inr X Y)).toAlgHom
  let l : MonoidAlgebra K X →ₐ[K] MonoidAlgebra K X ⊗[K] MonoidAlgebra K Y := includeLeft
  let r : MonoidAlgebra K Y →ₐ[K] MonoidAlgebra K X ⊗[K] MonoidAlgebra K Y := includeRight
  let f := Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)
  let g := MonoidAlgebra.lift K _ (X × Y)
    ((l.toMonoidHom.comp
      ((MonoidAlgebra.of K X).comp (MonoidHom.fst X Y))) *
      (r.toMonoidHom.comp ((MonoidAlgebra.of K Y).comp (MonoidHom.snd X Y))))
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply (MonoidAlgebra.lift K _ (X × Y)).symm.injective
    apply MonoidHom.ext
    rintro ⟨x, y⟩
    change f (g (MonoidAlgebra.of K (X × Y) (x, y))) = MonoidAlgebra.of K (X × Y) (x, y)
    rw [MonoidAlgebra.lift_of]
    change f (l (MonoidAlgebra.of K X x) *
      r (MonoidAlgebra.of K Y y)) = _
    have hx : f (l (MonoidAlgebra.of K X x)) =
        MonoidAlgebra.of K (X × Y) (x, 1) := by
      simp [l, f, a, MonoidAlgebra.of_apply]
    have hy : f (r (MonoidAlgebra.of K Y y)) =
        MonoidAlgebra.of K (X × Y) (1, y) := by
      simp [r, f, b, MonoidAlgebra.of_apply]
    rw [map_mul, hx, hy, ← map_mul]
    congr 1
    simp
  · apply Algebra.TensorProduct.ext
    · apply (MonoidAlgebra.lift K _ X).symm.injective
      apply MonoidHom.ext
      intro x
      change g (f (l (MonoidAlgebra.of K X x))) = l (MonoidAlgebra.of K X x)
      simp [l, r, f, a, g, MonoidAlgebra.of_apply, ← MonoidAlgebra.one_def]
    · apply (MonoidAlgebra.lift K _ Y).symm.injective
      apply MonoidHom.ext
      intro y
      change g (f (r (MonoidAlgebra.of K Y y))) = r (MonoidAlgebra.of K Y y)
      simp [l, r, f, b, g, MonoidAlgebra.of_apply, ← MonoidAlgebra.one_def]

private def productTorusMap (X Y : Type u) [CommGroup X] [CommGroup Y] :
    integralTorus (X × Y) ⟶ integralTorus X ⊗ integralTorus Y :=
  lift (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} (MonoidHom.inl X Y)))
    (spectrumOfHopfHom (MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} (MonoidHom.inr X Y)))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
private theorem productTorusMap_isIso (X Y : Type u) [CommGroup X] [CommGroup Y] :
    IsIso (productTorusMap X Y) := by
  let B := MonoidAlgebra IntegralRing.{u} X
  let C := MonoidAlgebra IntegralRing.{u} Y
  let E := MonoidAlgebra IntegralRing.{u} (X × Y)
  let a : B →ₐc[IntegralRing.{u}] E := MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} (MonoidHom.inl X Y)
  let b : C →ₐc[IntegralRing.{u}] E := MonoidAlgebra.mapDomainBialgHom IntegralRing.{u} (MonoidHom.inr X Y)
  let f : B ⊗[IntegralRing.{u}] C ≃ₐ[IntegralRing.{u}] E := productGroupAlgebra X Y
  let j := productTorusMap X Y
  let i : (integralTorus (X × Y)).X.left ≅ ((integralTorus X).X ⊗ (integralTorus Y).X).left :=
    Scheme.Spec.mapIso f.toRingEquiv.toCommRingCatIso.op ≪≫ (pullbackSpecIso IntegralRing.{u} B C).symm
  have hi : i.hom = j.hom.hom.left := by
    apply pullback.hom_ext
    · have h : j.hom.hom.left ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom a.toAlgHom.toRingHom) := by
        change (lift (spectrumOfHopfHom a).hom.hom (spectrumOfHopfHom b).hom.hom).left ≫ _ = _
        exact congrArg Over.Hom.left (lift_fst (spectrumOfHopfHom a).hom.hom
          (spectrumOfHopfHom b).hom.hom)
      have k : i.hom = Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
          (pullbackSpecIso IntegralRing.{u} B C).inv := rfl
      rw [h, k, Category.assoc]
      change Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
        (pullbackSpecIso IntegralRing.{u} B C).inv ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing.{u} B)))
            (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing.{u} C))) = _
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      apply congrArg (fun q : B →+* E => Spec.map (CommRingCat.ofHom q))
      apply RingHom.ext
      intro x
      change f (x ⊗ₜ[IntegralRing.{u}] (1 : C)) = a x
      change a x * b 1 = a x
      rw [map_one, mul_one]
    · have h : j.hom.hom.left ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom b.toAlgHom.toRingHom) := by
        change (lift (spectrumOfHopfHom a).hom.hom (spectrumOfHopfHom b).hom.hom).left ≫ _ = _
        exact congrArg Over.Hom.left (lift_snd (spectrumOfHopfHom a).hom.hom
          (spectrumOfHopfHom b).hom.hom)
      have k : i.hom = Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
          (pullbackSpecIso IntegralRing.{u} B C).inv := rfl
      rw [h, k, Category.assoc]
      change Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫
        (pullbackSpecIso IntegralRing.{u} B C).inv ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing.{u} B)))
            (Spec.map (CommRingCat.ofHom (algebraMap IntegralRing.{u} C))) = _
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      apply congrArg (fun q : C →+* E => Spec.map (CommRingCat.ofHom q))
      apply RingHom.ext
      intro y
      change f ((1 : B) ⊗ₜ[IntegralRing.{u}] y) = b y
      change a 1 * b y = b y
      rw [map_one, one_mul]
  let e : (integralTorus (X × Y)).X ≅ (integralTorus X).X ⊗ (integralTorus Y).X :=
    Over.isoMk i (hi ▸ Over.w j.hom.hom)
  have h : e.hom = j.hom.hom := Over.OverMorphism.ext hi
  let : IsMonHom e.hom := h ▸ j.hom.isMonHom_hom
  let e' : integralTorus (X × Y) ≅ integralTorus X ⊗ integralTorus Y := Grp.mkIso' e
  have eq : e'.hom = productTorusMap X Y := Grp.hom_ext _ _ h
  exact eq ▸ e'.isIso_hom

private def productTorusIso (X Y : Type u) [CommGroup X] [CommGroup Y] :
    integralTorus (X × Y) ≅ integralTorus X ⊗ integralTorus Y :=
  let := productTorusMap_isIso X Y
  asIso (productTorusMap X Y)

end IntegralTori

private theorem maximalOfSourceIso {k : Type u} [Field k] {A U V : GroupScheme k}
    (e : U ≅ V) (j : V ⟶ A) (hj : IsClosedImmersion j.hom.hom.left)
    (h : IsMaximalTorus (⟨_, j, hj⟩ : ClosedSubgroup A)) :
    ∃ hc : IsClosedImmersion (e.hom ≫ j).hom.hom.left,
      IsMaximalTorus (⟨_, e.hom ≫ j, hc⟩ : ClosedSubgroup A) := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsIso e.hom.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso e.hom
  refine ⟨inferInstanceAs (IsClosedImmersion (e.hom.hom.hom.left ≫ j.hom.hom.left)),
    torus_of_iso e.symm h.1, ?_⟩
  intro S hS hUS
  obtain ⟨a, ha⟩ := hUS
  change a ≫ S.inclusion = e.hom ≫ j at ha
  have hVS : IsSubgroupOf (⟨_, j, hj⟩ : ClosedSubgroup A) S :=
    ⟨e.inv ≫ a, by rw [Category.assoc, ha, e.inv_hom_id_assoc]⟩
  obtain ⟨b, hb⟩ := h.2 S hS hVS
  refine ⟨b ≫ e.inv, ?_⟩
  change (b ≫ e.inv) ≫ e.hom ≫ j = S.inclusion
  rw [Category.assoc, e.inv_hom_id_assoc]
  exact hb

/-- A split torus factor preserves reductivity and extends the marked maximal torus
in every geometric fibre of an integral group scheme. -/
theorem reductiveFibresTensorSplitTorus :
    Specs.ReductiveProductWithSplitTorus.Statement.{u} := by
  intro X M _ _ _ _ _ _ G t h K _ _ _
  let F := fibreGroup K (R := IntegralRing.{u})
  let U := integralTorus X
  let V := integralTorus M
  obtain ⟨H, eH, hTc, hHr, hTm⟩ := h K
  let T : ClosedSubgroup H.val := ⟨F.obj U, F.map t ≫ eH.hom, hTc⟩
  have htSplit : IsSplitTorus T.group := splitFibreOfFreeLattice K X
  have htGeom := geometricallyMaximal_of_maximal_split H T hTm htSplit
  have hct := Reductive.TorusCentralizer.maximalTorusCentralizer H hHr T hTm.1 htGeom
  obtain ⟨r, ⟨eD⟩⟩ := splitFibreOfFreeLattice (R := IntegralRing.{u}) K M
  let D := Specs.StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin r))
  have hdSplit : IsSplitTorus D.val := ⟨r, ⟨Iso.refl _⟩⟩
  let e : F.obj (G ⊗ V) ≅ (affineProduct H D).val :=
    (Functor.Monoidal.μIso F G V).symm ≪≫ MonoidalCategory.tensorIso eH eD
  let d : F.obj (U ⊗ V) ≅ T.group ⊗ D.val :=
    (Functor.Monoidal.μIso F U V).symm ≪≫ MonoidalCategory.tensorIso (Iso.refl _) eD
  let : Module.Free ℤ (Additive (X × M)) :=
    inferInstanceAs (Module.Free ℤ (Additive X × Additive M))
  let : Module.Finite ℤ (Additive (X × M)) :=
    inferInstanceAs (Module.Finite ℤ (Additive X × Additive M))
  have hTd : IsTorus (T.group ⊗ D.val) :=
    torus_of_iso (F.mapIso (productTorusIso X M) ≪≫ d)
      (lattice_torus_of_split (splitFibreOfFreeLattice (R := IntegralRing.{u}) K (X × M)))
  let j := T.inclusion ⊗ₘ 𝟙 D.val
  let := T.isClosedImmersion
  have hj : IsClosedImmersion j.hom.hom.left :=
    tensorClosedImmersion T.inclusion.hom.hom (𝟙 D.val.X)
  have hmax := maximalProduct (G := H) (D := D) T hct hj hTd
  have hcomp : F.map (t ⊗ₘ 𝟙 V) ≫ e.hom = d.hom ≫ j := by
    change F.map (t ⊗ₘ 𝟙 V) ≫
        Functor.OplaxMonoidal.δ F G V ≫ (eH.hom ⊗ₘ eD.hom) =
      (Functor.OplaxMonoidal.δ F U V ≫ (𝟙 (F.obj U) ⊗ₘ eD.hom)) ≫
        ((F.map t ≫ eH.hom) ⊗ₘ 𝟙 D.val)
    rw [← Functor.OplaxMonoidal.δ_natural_assoc, Category.assoc,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, F.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  refine ⟨affineProduct H D, e, ?_⟩
  rw [hcomp]
  obtain ⟨hc, hm⟩ := maximalOfSourceIso d j hj hmax
  exact ⟨hc, reductiveProduct H D hHr hdSplit, hm⟩

end

end LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
