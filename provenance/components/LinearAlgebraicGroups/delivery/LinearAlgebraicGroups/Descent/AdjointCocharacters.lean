import Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Reductive.CentralDerived
import LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Reductive.SubtorusCentralizer
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.Localization
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra
open scoped TensorProduct BigOperators CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.AdjointCocharacters

open _root_.LinearAlgebraicGroups.Specs Specs.AdjointCocharacters
open Specs.CharacterDescent (GeometricCharacters MultiplicativeTypeHopf)
open Specs.GeometricRadicals (IsTorus)
open Specs.SmoothnessAndIsogenies (pullbackCharacter)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

/-- The rational dual used for a torus is the scalar extension of the
integral cocharacter lattice, with its usual evaluation on characters. -/
theorem rationalCocharacterComparison {K : Type u} [Field K] [Algebra k K] [IsSepClosure k K]
    (A : HopfAlgebraCategory k) (hA : Specs.CharacterDescent.IsTorus A) :
    ∃ e : (ℚ ⊗[ℤ] Module.Dual ℤ (Additive (GeometricCharacters K A))) ≃ₗ[ℚ]
        RationalCocharacters K A,
      ∀ a v χ, e (a ⊗ₜ[ℤ] v) (1 ⊗ₜ[ℤ] Additive.ofMul χ) =
        a * (v (Additive.ofMul χ) : ℚ) := by
  have hM := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A hA
  obtain ⟨r, ⟨latticeEquiv⟩⟩ :=
    ((LinearAlgebraicGroups.CharacterDescent.torusAndSplitCriteria (K := K) A hM).1).mp hA
  let coordinates : Additive (Specs.CharacterDescent.StandardLattice.{u} r) ≃+ (Fin r → ℤ) :=
    { toFun := fun x i ↦ (x.toMul i).down.toAdd
      invFun := fun x ↦ Additive.ofMul (fun i ↦ ULift.up (Multiplicative.ofAdd (x i)))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let latticeCoordinates : Additive (GeometricCharacters K A) ≃ₗ[ℤ] (Fin r → ℤ) :=
    (latticeEquiv.toAdditive.trans coordinates).toIntLinearEquiv
  letI : Module.Free ℤ (Additive (GeometricCharacters K A)) :=
    Module.Free.of_equiv latticeCoordinates.symm
  letI : Module.Finite ℤ (Additive (GeometricCharacters K A)) :=
    Module.Finite.of_surjective latticeCoordinates.symm.toLinearMap latticeCoordinates.symm.surjective
  let baseChange := TensorProduct.isBaseChange ℤ (Additive (GeometricCharacters K A)) ℚ
  exact ⟨baseChange.toDualBaseChange,
    fun a v χ ↦ baseChange.toDualBaseChange_tmul a v (Additive.ofMul χ)⟩

private abbrev rationalCharacterMap (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    RationalCharacters K A →ₗ[ℚ] RationalCharacters K B :=
  ((pullbackCharacter K f).toAdditive.toIntLinearMap).baseChange ℚ

private theorem rationalCharacterMap_injective
    {K : Type u} [Field K] [Algebra k K] {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hf : Function.Injective (pullbackCharacter K f)) :
    Function.Injective (rationalCharacterMap K f) := by
  letI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hf

private theorem rationalCharacterMap_surjective
    {K : Type u} [Field K] [Algebra k K] {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    [Finite (GeometricCharacters K B ⧸ (pullbackCharacter K f).range)] :
    Function.Surjective (rationalCharacterMap K f) := by
  let L := (pullbackCharacter K f).range
  let n := Nat.card (GeometricCharacters K B ⧸ L)
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let m := rationalCharacterMap K f
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact (LinearMap.range m).add_mem hx hy
  | tmul a y =>
      let b : GeometricCharacters K B := Additive.toMul y
      have hb : b ^ n ∈ L := by
        apply (QuotientGroup.eq_one_iff _).mp
        rw [QuotientGroup.mk_pow]
        exact pow_card_eq_one'
      obtain ⟨z, hz⟩ := hb
      refine ⟨(a / (n : ℚ)) ⊗ₜ[ℤ] Additive.ofMul z, ?_⟩
      change (a / (n : ℚ)) ⊗ₜ[ℤ] (Additive.ofMul (pullbackCharacter K f z)) = a ⊗ₜ[ℤ] y
      rw [hz]
      change (a / (n : ℚ)) ⊗ₜ[ℤ] (n • y) = a ⊗ₜ[ℤ] y
      rw [← Nat.cast_smul_eq_nsmul ℤ, ← TensorProduct.smul_tmul, Nat.cast_smul_eq_nsmul]
      simp [nsmul_eq_mul, mul_div_cancel₀, hn]

private theorem rationalInvariantMap
    {K : Type u} [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hA : Specs.CharacterDescent.IsMultiplicativeType A)
    (hB : Specs.CharacterDescent.IsMultiplicativeType B)
    (hf : Function.Surjective (rationalCocharacterMap K f)) :
    (rationalCocharacterInvariants K B).map (rationalCocharacterMap K f) =
      rationalCocharacterInvariants K A := by
  let m := rationalCocharacterMap K f
  let F := LinearAlgebraicGroups.CharacterDescent.geometricCharacterFunctor (k := k) K
  let B' : MultiplicativeTypeHopf k :=
    ⟨⟨B, (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties B hB).1⟩, hB⟩
  obtain ⟨E, hE, hN, ρ, hρ⟩ :=
    LinearAlgebraicGroups.CharacterDescent.factorsThroughFiniteGalois (F.obj B')
  letI := hE
  letI := hN
  letI : Fintype (Gal(E/k)) := Fintype.ofFinite _
  let r : Gal(K/k) →* Gal(E/k) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective (K₁ := E) K
  let j (C : HopfAlgebraCategory k) (x : GeometricCharacters K C) :
      RationalCharacters K C := 1 ⊗ₜ[ℤ] Additive.ofMul x
  let bAct (σ : Gal(K/k)) (x : GeometricCharacters K B) :=
    (LinearAlgebraicGroups.CharacterDescent.geometricAction K B σ).asHom x
  have hact (σ : Gal(K/k)) (x : GeometricCharacters K B) :
      ρ (r σ) x = bAct σ x := (hρ σ x).symm
  have hval (σ : Gal(K/k)) (x : GeometricCharacters K B) :
      (bAct σ x).val = (LinearAlgebraicGroups.Descent.SemilinearAction.scalarExtension (K := K) B).act σ x.val :=
    rfl
  have heqv := LinearAlgebraicGroups.SmoothnessAndIsogenies.characterPullbackEquivariant
    (K := K) f hA hB
  have hm (v : RationalCocharacters K B) (x : GeometricCharacters K A) :
      m v (j A x) = v (j B (pullbackCharacter K f x)) := rfl
  apply le_antisymm
  · rintro w ⟨v, hv, rfl⟩ σ x y hxy
    change m v (j A y) = m v (j A x)
    rw [hm, hm]
    exact hv σ _ _ (heqv σ x y hxy)
  · intro w hw
    obtain ⟨v, hv⟩ := hf w
    let act (τ : Gal(E/k)) : RationalCharacters K B →ₗ[ℚ] RationalCharacters K B :=
      ((ρ τ).toMonoidHom.toAdditive.toIntLinearMap).baseChange ℚ
    let v' : RationalCocharacters K B :=
      (Fintype.card (Gal(E/k)) : ℚ)⁻¹ • ∑ τ : Gal(E/k), v.comp (act τ)
    have hv' (x : GeometricCharacters K B) :
        v' (j B x) = (Fintype.card (Gal(E/k)) : ℚ)⁻¹ *
          ∑ τ : Gal(E/k), v (j B (ρ τ x)) := by
      simp only [v', LinearMap.smul_apply, smul_eq_mul, LinearMap.sum_apply]
      rfl
    refine ⟨v', ?_, ?_⟩
    · intro σ x y hxy
      change v' (j B y) = v' (j B x)
      have hy : ρ (r σ) x = y := GroupLike.val_injective ((congrArg GroupLike.val
        (hact σ x)).trans ((hval σ x).trans hxy))
      rw [hv', hv', ← hy]
      congr 1
      let e : Gal(E/k) ≃ Gal(E/k) := Equiv.mulRight (r σ)
      calc
        ∑ τ : Gal(E/k), v (j B (ρ τ (ρ (r σ) x))) =
            ∑ τ : Gal(E/k), v (j B (ρ (e τ) x)) := by
              apply Finset.sum_congr rfl
              intro τ _
              change v (j B (ρ τ (ρ (r σ) x))) = v (j B (ρ (τ * r σ) x))
              rw [map_mul]
              rfl
        _ = ∑ τ : Gal(E/k), v (j B (ρ τ x)) :=
          e.sum_comp (fun τ : Gal(E/k) ↦ v (j B (ρ τ x)))
    · apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | add t s ht hs => simp only [map_add, ht, hs]
      | tmul a t =>
          have h (x : GeometricCharacters K A) :
              m v' (j A x) = w (j A x) := by
            rw [hm, hv']
            have hterm (τ : Gal(E/k)) :
                v (j B (ρ τ (pullbackCharacter K f x))) = w (j A x) := by
              obtain ⟨σ, rfl⟩ := hr τ
              let y := (LinearAlgebraicGroups.CharacterDescent.geometricAction K A σ).asHom x
              have hy : (LinearAlgebraicGroups.Descent.SemilinearAction.scalarExtension (K := K) A).act σ x.val =
                  y.val := rfl
              rw [hact σ]
              have hc : bAct σ (pullbackCharacter K f x) = pullbackCharacter K f y :=
                GroupLike.val_injective ((hval σ _).trans (heqv σ x y hy))
              rw [hc, ← hm, hv]
              exact hw σ x y hy
            simp_rw [hterm]
            have hn : (Fintype.card (Gal(E/k)) : ℚ) ≠ 0 :=
              Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
            simp [nsmul_eq_mul, hn]
          rw [TensorProduct.tmul_eq_smul_one_tmul]
          simp only [map_smul]
          exact congrArg (fun z : ℚ ↦ a • z) (h (Additive.toMul t))

private theorem coordinatePresentationMap {G H : AffineAlgebraicGroup k} (f : G.val ⟶ H.val) :
    specGroupMap (Specs.AdjointCocharacters.coordinateHopfMap f) =
      (Specs.AdjointCocharacters.coordinateHopfIso G).hom ≫ f ≫ (Specs.AdjointCocharacters.coordinateHopfIso H).inv := by
  exact (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _


private theorem coordinatePresentationTorus (G : AffineAlgebraicGroup k)
    (hG : IsTorus G.val) : Specs.CharacterDescent.IsTorus (Specs.AdjointCocharacters.coordinateHopf G) := by
  apply (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes _).mpr
  obtain ⟨E, hE, hkE, hsep, r, ⟨e⟩⟩ := hG
  letI := hE
  letI := hkE
  exact ⟨E, hE, hkE, hsep, r,
    ⟨(groupBaseChange k E).mapIso (Specs.AdjointCocharacters.coordinateHopfIso G) ≪≫ e⟩⟩

private theorem coordinatePresentationSurjective {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (hf : Surjective f.hom.hom.left) :
    Surjective (specGroupMap (Specs.AdjointCocharacters.coordinateHopfMap f)).hom.hom.left := by
  rw [coordinatePresentationMap]
  let U : GroupScheme k ⥤ Scheme := Grp.forget _ ⋙ Over.forget _
  letI : IsIso (U.map (Specs.AdjointCocharacters.coordinateHopfIso G).hom) := U.map_isIso _
  letI : IsIso (U.map (Specs.AdjointCocharacters.coordinateHopfIso H).inv) := U.map_isIso _
  change Surjective (U.map ((Specs.AdjointCocharacters.coordinateHopfIso G).hom ≫ f ≫ (Specs.AdjointCocharacters.coordinateHopfIso H).inv))
  rw [Functor.map_comp, Functor.map_comp]
  letI : Surjective (U.map f) := hf
  infer_instance

open private injectivePullbackIff reducedOfSmoothHopf
  from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies

private theorem pullbackCharacter_injective_of_surjective
    {K : Type u} [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hA : Specs.CharacterDescent.IsTorus A) (hB : Specs.CharacterDescent.IsTorus B)
    (hf : Surjective (specGroupMap f).hom.hom.left) :
    Function.Injective (pullbackCharacter K f) := by
  have hA' := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A hA
  have hB' := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType B hB
  apply (injectivePullbackIff (K := K) f hA' hB').mpr
  have : _root_.IsReduced A := reducedOfSmoothHopf A
    ((LinearAlgebraicGroups.SmoothnessAndIsogenies.smoothConnectedMultiplicativeType A).mp hA).2.1
  let r := f.hom.toAlgHom.toRingHom
  have hd : DenseRange (PrimeSpectrum.comap r) := hf.surj.denseRange
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical r).mp hd
  rw [nilradical_eq_zero] at hker
  exact (RingHom.injective_iff_ker_eq_bot r).mpr (le_bot_iff.mp hker)

theorem rationalCocharacterSurjectivity : RationalCocharacterSurjectivity.{u} := by
  intro k _ G Q Z q hG hq T' hT' hmax T p hp
  let S := closedSubgroupAlgebraicGroup T
  let S' := closedSubgroupAlgebraicGroup T'
  let f := Specs.AdjointCocharacters.coordinateHopfMap (G := S) (H := S') p
  let K := SeparableClosure k
  have hA := coordinatePresentationTorus S' hT'
  have hB := coordinatePresentationTorus S hp.2.1.1
  have hi := pullbackCharacter_injective_of_surjective (K := K) f hA hB
    (coordinatePresentationSurjective (G := S) (H := S') p hp.2.2.2.2)
  have hs : Function.Surjective (rationalCocharacterMap K f) :=
    LinearMap.dualMap_surjective_of_injective (rationalCharacterMap_injective f hi)
  exact ⟨hs, rationalInvariantMap f
    (LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType _ hA)
    (LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType _ hB) hs⟩

open Specs.CentralTorus (IsSchemeCentre)
open Specs.GeometricRadicals (IsMaximalTorus IsReductive GeometricGroup
  baseChangedSubgroup geometricUnipotentRadical)
open Specs.SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open private isMonHom_of_comp_closed schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private geometricCharacterFunctor_full geometricCharacterFunctor_faithful
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private kernel_of_preimage from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent

private theorem coordinatePresentationFiniteKernel {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (Z : ClosedSubgroup G.val) (hz : IsSchemeKernel f Z)
    (hfin : IsFinite Z.group.X.hom) :
    ∃ N : ClosedSubgroup (specGroup (Specs.AdjointCocharacters.coordinateHopf G)),
      IsSchemeKernel (specGroupMap (Specs.AdjointCocharacters.coordinateHopfMap f)) N ∧ IsFinite N.group.X.hom := by
  let eG := Specs.AdjointCocharacters.coordinateHopfIso G
  let eH := Specs.AdjointCocharacters.coordinateHopfIso H
  let U := Grp.forget (SchemeOver k)
  let V := U ⋙ Over.forget (Spec (CommRingCat.of k))
  let j := Z.inclusion ≫ eG.inv
  letI : IsIso eG.inv.hom.hom.left := V.map_isIso eG.inv
  have hj : IsClosedImmersion j.hom.hom.left := by
    letI := Z.isClosedImmersion
    change IsClosedImmersion (Z.inclusion.hom.hom.left ≫ eG.inv.hom.hom.left)
    exact IsClosedImmersion.comp Z.inclusion.hom.hom.left eG.inv.hom.hom.left
  refine ⟨⟨Z.group, j, hj⟩, ?_, hfin⟩
  refine hz.of_iso' (Iso.refl _) (U.mapIso eG) (Iso.refl _) (U.mapIso eH) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    change U.map Z.inclusion = U.map j ≫ U.map eG.hom
    rw [← U.map_comp]
    exact congrArg U.map (show Z.inclusion = j ≫ eG.hom by simp [j])
  · simp
  · change eG.hom.hom.hom ≫ f.hom.hom =
      (specGroupMap (Specs.AdjointCocharacters.coordinateHopfMap f)).hom.hom ≫ eH.hom.hom.hom
    rw [coordinatePresentationMap]
    exact congrArg U.map (show eG.hom ≫ f = (eG.hom ≫ f ≫ eH.inv) ≫ eH.hom by simp)
  · change (𝟙 _) ≫ η[H.val.X] = η[(specGroup (Specs.AdjointCocharacters.coordinateHopf H)).X] ≫ eH.hom.hom.hom
    rw [Category.id_comp, IsMonHom.one_hom]

theorem semisimpleRationalCocharacterIso : SemisimpleRationalCocharacterIso.{u} := by
  intro k _ G Q Z q hG hss hq T' hT' hmax T p hp
  let S := closedSubgroupAlgebraicGroup T
  let S' := closedSubgroupAlgebraicGroup T'
  let f := Specs.AdjointCocharacters.coordinateHopfMap (G := S) (H := S') p
  let K := SeparableClosure k
  have hfin : IsFinite Z.group.X.hom :=
    (LinearAlgebraicGroups.Reductive.CentralDerived.semisimpleIffFiniteCentre G hG Z hq.1).mp hss
  obtain ⟨j, hj, _, hker⟩ := kernel_of_preimage hq.2.1
    (IsPullback.of_map_of_faithful (Grp.forget (SchemeOver k)) hp.1)
  obtain ⟨N, hN, hNfin⟩ := coordinatePresentationFiniteKernel
    (G := S) (H := S') p ⟨Z.group, j, hj⟩ hker hfin
  have hA := coordinatePresentationTorus S' hT'
  have hB := coordinatePresentationTorus S hp.2.1.1
  obtain ⟨hi, hindex⟩ := (LinearAlgebraicGroups.SmoothnessAndIsogenies.torusIsogenyCriterion
    (K := K) f hA hB).mp
    ⟨coordinatePresentationSurjective (G := S) (H := S') p hp.2.2.2.2, N, hN, hNfin⟩
  letI := hindex
  obtain ⟨hs, hfix⟩ := rationalCocharacterSurjectivity Z q hG hq T' hT' hmax T p hp
  have hd : Function.Injective (rationalCocharacterMap K f) :=
    LinearMap.dualMap_injective_of_surjective (rationalCharacterMap_surjective f)
  exact ⟨⟨hd, hs⟩, hfix⟩

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsSmoothConnectedNormal)
open Specs.Unipotent (IsUnipotent)
open LinearAlgebraicGroups.EquivariantUnipotentSeries
  (ReducedIdentityComponent exists_smooth_identity_component smooth_identity_component_normal)

open private preimageSubgroup preimage_isNormal trivial_of_subsingleton_points torus_isMultiplicativeType
  from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private centre_baseChange centre_le_of_selfCentralizer commute_from_centre
  from LinearAlgebraicGroups.Reductive.CentralTorus
open private normalOfCentral normalSolvableTorus connectedOfGeometricallyConnected torusOfSurjectiveMap
  subgroupIso
  from LinearAlgebraicGroups.Reductive.CentralDerived
open private rationalSections solvable_iff_sections factor_closed
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private quotient_smooth_connected torus_after_algClosed_extension
  torus_descends_from_algebraic_closure image_of_geometric_torus
  from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private torus_commutative solvable_of_schemeKernel unipotent_sections_solvable
  from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private baseChangeMapPullback baseChangeKernelSquare
  from LinearAlgebraicGroups.Affine.Components
open private geometricallyConnected_of_connected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private torus_smooth_connected_solvable
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private schemeKernel_exists from LinearAlgebraicGroups.Affine.SchemeImageQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem underlyingPullback {X Y Z W : GroupScheme k}
    {a : W ⟶ X} {b : W ⟶ Y} {p : X ⟶ Z} {q : Y ⟶ Z} (h : IsPullback a b p q) :
    IsPullback a.hom.hom b.hom.hom p.hom.hom q.hom.hom :=
  h.map (Grp.forget (SchemeOver k))

private theorem schemePullback {X Y Z W : GroupScheme k}
    {a : W ⟶ X} {b : W ⟶ Y} {p : X ⟶ Z} {q : Y ⟶ Z} (h : IsPullback a b p q) :
    IsPullback a.hom.hom.left b.hom.hom.left p.hom.hom.left q.hom.hom.left :=
  (underlyingPullback h).map (Over.forget (Spec (CommRingCat.of k)))

/-- The reduced identity component is open on points. Its image in a connected
fppf quotient is open, and scheme-image factorization makes that image closed. -/
private theorem component_surjects [IsAlgClosed k] (P S : AffineAlgebraicGroup k)
    (p : P.val ⟶ S.val) (D : ReducedIdentityComponent P)
    (hc : ConnectedSpace S.val.X.left)
    (hf : Flat p.hom.hom.left) (hl : LocallyOfFinitePresentation p.hom.hom.left) :
    Surjective (D.subgroup.inclusion ≫ p).hom.hom.left := by
  letI := hc
  letI := hf
  letI := hl
  let f := D.subgroup.inclusion ≫ p
  have hopen : IsOpen (Set.range f.hom.hom.left) := by
    rw [show (f.hom.hom.left : D.subgroup.group.X.left → S.val.X.left) =
      p.hom.hom.left ∘ D.subgroup.inclusion.hom.hom.left from rfl, Set.range_comp]
    exact p.hom.hom.left.isOpenMap _ D.open_range
  obtain ⟨I, r, i, hi, _, _⟩ :=
    LinearAlgebraicGroups.schemeImageFactorization (closedSubgroupAlgebraicGroup D.subgroup) S f
  have he : Set.range f.hom.hom.left = Set.range i.hom.hom.left := by
    rw [← hi.1]
    change Set.range (i.hom.hom.left ∘ r.hom.hom.left) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr hi.2.2.1.1, Set.image_univ]
  have hclosed := hi.2.2.2.2.2.isClosedEmbedding.isClosed_range
  have hn : (Set.range f.hom.hom.left).Nonempty :=
    ⟨_, ⟨η[D.subgroup.group.X].left (IsLocalRing.closedPoint k), rfl⟩⟩
  exact ⟨Set.range_eq_univ.mp
    ((show IsClopen (Set.range f.hom.hom.left) from ⟨by rw [he]; exact hclosed, hopen⟩).eq_univ hn)⟩

/-- A smooth connected subgroup whose image is solvable and whose kernel lies in
the centre is solvable. The kernel may be nonreduced. -/
private theorem solvable_of_central_kernel [IsAlgClosed k]
    {G Q A S : AffineAlgebraicGroup k} {Z : ClosedSubgroup G.val}
    {q : G.val ⟶ Q.val} (hz : IsSchemeKernel q Z) (hc : IsSchemeCentre Z)
    (j : A.val ⟶ G.val) (hj : IsClosedImmersion j.hom.hom.left)
    (f : A.val ⟶ S.val) (i : S.val ⟶ Q.val) (he : j ≫ q = f ≫ i)
    (hsA : Smooth A.val.X.hom) (hcA : ConnectedSpace A.val.X.left)
    [Group.IsSolvable (rationalSections S.val)] : IsSolvable A.val := by
  letI := S.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  have hNq : (N.inclusion ≫ j) ≫ q = 0 := by
    rw [Category.assoc, he, ← Category.assoc,
      (Grp.hom_ext _ _ hN.w : N.inclusion ≫ f = 0), zero_comp]
  obtain ⟨a, ha⟩ : ∃ a : N.group.X ⟶ Z.group.X,
      a ≫ Z.inclusion.hom.hom = (N.inclusion ≫ j).hom.hom :=
    (schemeKernel_sections hz (N.inclusion ≫ j).hom.hom).mpr
      (congrArg (fun b : N.group ⟶ Q.val ↦ b.hom.hom) hNq)
  have hcent := (hc Z.group.X Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  letI := hj
  letI := N.isClosedImmersion
  letI : Mono (N.inclusion ≫ j).hom.hom.left :=
    inferInstanceAs (Mono (N.inclusion.hom.hom.left ≫ j.hom.hom.left))
  letI : Mono (N.inclusion ≫ j).hom.hom := Over.mono_of_mono_left _
  letI : Group.IsSolvable (rationalSections N.group) := Group.isSolvable_of_comm (by
    intro x y
    apply (cancel_mono (N.inclusion ≫ j).hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp, ← ha, ← Category.assoc x a]
    exact (commute_from_centre hcent (x ≫ a) (y ≫ a ≫ Z.inclusion.hom.hom)).eq)
  exact solvable_of_schemeKernel f hN hsA hcA

private theorem reductive_of_central_quotient {G Q : AffineAlgebraicGroup k}
    {Z : ClosedSubgroup G.val} {q : G.val ⟶ Q.val} (hg : IsReductive G)
    (hz : IsSchemeKernel q Z) (hc : IsSchemeCentre Z)
    (hf : Flat q.hom.hom.left) (hs : Surjective q.hom.hom.left)
    (hl : LocallyOfFinitePresentation q.hom.hom.left) : IsReductive Q := by
  obtain ⟨hsQ, hcQ⟩ := quotient_smooth_connected q hf hs hg.1
    (connectedOfGeometricallyConnected G hg.2.1)
  letI := hcQ
  refine ⟨hsQ, geometricallyConnected_of_connected Q, ?_⟩
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let G' := GeometricGroup G
  let Q' := GeometricGroup Q
  let q' := F.map q
  let R := geometricUnipotentRadical Q
  let S := closedSubgroupAlgebraicGroup R
  have hg' : IsReductive G' :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
      (K := K) G hg.1 hg.2.1).mpr hg
  obtain ⟨hz', hc'⟩ := centre_baseChange hc K
  let Z' := baseChangedSubgroup K Z hz'
  have hker : IsSchemeKernel q' Z' := baseChangeKernelSquare q Z.inclusion hz
  have hb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  have hf' : Flat q'.hom.hom.left := MorphismProperty.of_isPullback hb hf
  have hl' : LocallyOfFinitePresentation q'.hom.hom.left := MorphismProperty.of_isPullback hb hl
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest Q
  obtain ⟨P, p, hp⟩ := preimageSubgroup (G := G') (Q := Q') q' R
  let A := closedSubgroupAlgebraicGroup P
  obtain ⟨D⟩ := exists_smooth_identity_component A
  let B := closedSubgroupAlgebraicGroup D.subgroup
  let V := subgroupOfSubgroup P D.subgroup
  let f := D.subgroup.inclusion ≫ p
  have hp' := schemePullback hp
  have hfs : Surjective f.hom.hom.left :=
    component_surjects A S p D hR.1.2.1
      (MorphismProperty.of_isPullback hp' hf') (MorphismProperty.of_isPullback hp' hl')
  have hV : IsSmoothConnectedNormal (G := G') V :=
    ⟨D.smooth, D.connected, smooth_identity_component_normal hg'.1
      (connectedOfGeometricallyConnected G' hg'.2.1) P (preimage_isNormal hp hR.1.2.2) D⟩
  letI : Group.IsSolvable (rationalSections S.val) := unipotent_sections_solvable S hR.2.1
  have hVsol : IsSolvable V.group := solvable_of_central_kernel (A := B) (S := S) hker hc'
    V.inclusion V.isClosedImmersion f R.inclusion (by
      change (D.subgroup.inclusion ≫ P.inclusion) ≫ q' =
        (D.subgroup.inclusion ≫ p) ≫ R.inclusion
      simp only [Category.assoc, hp.w]) D.smooth D.connected
  have ht : IsTorus B.val := normalSolvableTorus G' hg' V hV hVsol
  have hf0 : f = 0 := LinearAlgebraicGroups.Unipotent.homFromMultiplicativeTypeToUnipotent
    B S f (torus_isMultiplicativeType B ht) hR.2.1
  have hconst (x : B.val.X.left) :
      f.hom.hom.left x = η[S.val.X].left (IsLocalRing.closedPoint K) := by
    rw [hf0]
    change η[S.val.X].left (B.val.X.hom x) = _
    rw [Subsingleton.elim (B.val.X.hom x) (IsLocalRing.closedPoint K)]
  letI : Subsingleton S.val.X.left := ⟨fun x y ↦ by
    obtain ⟨a, rfl⟩ := hfs.1 x
    obtain ⟨b, rfl⟩ := hfs.1 y
    exact (hconst a).trans (hconst b).symm⟩
  letI : Smooth S.val.X.hom := hR.1.1
  letI := isReduced_of_smooth_over_field S.val.X.hom
  exact trivial_of_subsingleton_points S

theorem adjointQuotientExists : AdjointQuotientExists.{u} := by
  intro k _ G hg
  let H : ClosedSubgroup G.val := ⟨G.val, 𝟙 G.val, by
    change IsClosedImmersion (𝟙 G.val.X.left)
    infer_instance⟩
  obtain ⟨Z, hc⟩ := LinearAlgebraicGroups.centralizerScheme k G H
  have hc : IsSchemeCentre Z := hc
  have hn : IsNormalSubgroup Z.inclusion :=
    normalOfCentral Z ((hc _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨_, _, Q, q, _, _, hk, hi, _, hrep⟩ :=
    LinearAlgebraicGroups.normalAffineQuotient G Z hn
  exact ⟨Z, Q, q, ⟨hc, hk, hrep, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩,
    reductive_of_central_quotient hg hk hc hi.2.1 hi.2.2.1 hi.2.2.2.1⟩

open private centre_splits from LinearAlgebraicGroups.Reductive.CentralTorus
open private isIso_of_trivial_kernel from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private torus_of_split split_of_torus from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates exists_maximal_torus_over inclusion_mono subgroup_trans torus_of_iso
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private geometricallyMaximal_of_maximal_split maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private factors_of_range_subset from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private descends from LinearAlgebraicGroups.Reductive.BorelProper
open private trivial_of_zero_inclusion from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private flatOfSurjectiveHom from LinearAlgebraicGroups.Reductive.CentralDerived
open private subgroup_baseChange_iff extendSubgroup
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange

private theorem full_preimage_of_surjective_subgroup {G Q : AffineAlgebraicGroup k}
    {q : G.val ⟶ Q.val} {Z P S : ClosedSubgroup G.val} {T : ClosedSubgroup Q.val}
    {p : P.group ⟶ T.group} {r : S.group ⟶ T.group}
    (hz : IsSchemeKernel q Z) (hZ : IsSubgroupOf Z S)
    (hr : S.inclusion ≫ q = r ≫ T.inclusion) (hp : P.inclusion ≫ q = p ≫ T.inclusion)
    (hf : Flat r.hom.hom.left) (hs : Surjective r.hom.hom.left)
    (hl : LocallyOfFinitePresentation r.hom.hom.left) : IsSubgroupOf P S := by
  let W := pullback p.hom.hom r.hom.hom
  let a : W ⟶ P.group.X := pullback.fst p.hom.hom r.hom.hom
  let b : W ⟶ S.group.X := pullback.snd p.hom.hom r.hom.hom
  let v := a ≫ P.inclusion.hom.hom
  let w := b ≫ S.inclusion.hom.hom
  have hpb : IsPullback a.left b.left p.hom.hom.left r.hom.hom.left :=
    (IsPullback.of_hasPullback p.hom.hom r.hom.hom).map (Over.forget _)
  letI : Flat a.left := MorphismProperty.of_isPullback hpb.flip hf
  letI : Surjective a.left := MorphismProperty.of_isPullback hpb.flip hs
  letI : LocallyOfFinitePresentation a.left := MorphismProperty.of_isPullback hpb.flip hl
  have he : v ≫ q.hom.hom = w ≫ q.hom.hom := by
    change a ≫ P.inclusion.hom.hom ≫ q.hom.hom = b ≫ S.inclusion.hom.hom ≫ q.hom.hom
    rw [show P.inclusion.hom.hom ≫ q.hom.hom = p.hom.hom ≫ T.inclusion.hom.hom
          from congrArg (Grp.forget (SchemeOver k)).map hp,
        show S.inclusion.hom.hom ≫ q.hom.hom = r.hom.hom ≫ T.inclusion.hom.hom
          from congrArg (Grp.forget (SchemeOver k)).map hr,
        ← pullback.condition_assoc]
  obtain ⟨z, hzv⟩ : ∃ z : W ⟶ Z.group.X, z ≫ Z.inclusion.hom.hom = v * w⁻¹ :=
    (schemeKernel_sections hz (v * w⁻¹)).mpr (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, he, mul_inv_cancel])
  obtain ⟨j, hj⟩ := hZ
  let t := (z ≫ j.hom.hom) * b
  have ht : t ≫ S.inclusion.hom.hom = a ≫ P.inclusion.hom.hom := by
    rw [MonObj.mul_comp, Category.assoc,
      show j.hom.hom ≫ S.inclusion.hom.hom = Z.inclusion.hom.hom
        from congrArg (Grp.forget (SchemeOver k)).map hj, hzv]
    exact inv_mul_cancel_right v w
  letI := S.isClosedImmersion
  letI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  obtain ⟨c, hc⟩ := descends a t (by
    intro Y x y hxy
    apply (cancel_mono S.inclusion.hom.hom).mp
    calc
      (x ≫ t) ≫ S.inclusion.hom.hom = (x ≫ a) ≫ P.inclusion.hom.hom := by
        simp only [Category.assoc, ht]
      _ = (y ≫ a) ≫ P.inclusion.hom.hom := by rw [hxy]
      _ = (y ≫ t) ≫ S.inclusion.hom.hom := by simp only [Category.assoc, ht])
  letI : Epi a := (Over.forget _).epi_of_epi_map (Flat.epi_of_flat_of_surjective a.left)
  have hci : c ≫ S.inclusion.hom.hom = P.inclusion.hom.hom :=
    (cancel_epi a).mp (by rw [← Category.assoc, hc, ht])
  letI := isMonHom_of_comp_closed c P.inclusion S.inclusion hci
  exact ⟨Grp.homMk c, Grp.hom_ext _ _ hci⟩

private theorem geometric_preimage_maximal [IsAlgClosed k]
    {G Q : AffineAlgebraicGroup k} {Z P : ClosedSubgroup G.val} {T : ClosedSubgroup Q.val}
    {q : G.val ⟶ Q.val} {p : P.group ⟶ T.group} (hg : IsReductive G)
    (hz : IsSchemeKernel q Z) (hc : IsSchemeCentre Z)
    (hp : IsPullback P.inclusion.hom.hom p.hom.hom q.hom.hom T.inclusion.hom.hom)
    (hf : Flat p.hom.hom.left) (hl : LocallyOfFinitePresentation p.hom.hom.left)
    (hT : IsMaximalTorus T) : IsMaximalTorus P := by
  let A := closedSubgroupAlgebraicGroup P
  let B := closedSubgroupAlgebraicGroup T
  obtain ⟨D⟩ := exists_smooth_identity_component A
  let C := closedSubgroupAlgebraicGroup D.subgroup
  let j : D.subgroup.group ⟶ G.val := D.subgroup.inclusion ≫ P.inclusion
  let f : D.subgroup.group ⟶ T.group := D.subgroup.inclusion ≫ p
  have hj : IsClosedImmersion j.hom.hom.left := (subgroupOfSubgroup P D.subgroup).isClosedImmersion
  have he : j ≫ q = f ≫ T.inclusion := by
    simp only [j, f, Category.assoc, (Grp.hom_ext _ _ hp.w : P.inclusion ≫ q = p ≫ T.inclusion)]
  obtain ⟨hsB, hcB, hsolB⟩ :=
    torus_smooth_connected_solvable B hT.1
  letI : Group.IsSolvable (rationalSections B.val) := (solvable_iff_sections B hsB hcB).mp hsolB
  have hfs : Surjective f.hom.hom.left := component_surjects A B p D hcB hf hl
  have hsol := solvable_of_central_kernel (A := C) (S := B) hz hc j hj f T.inclusion he
    D.smooth D.connected
  obtain ⟨U, J, s, hU, hs, hJ, _⟩ :=
    LinearAlgebraicGroups.GeometricTorusSplitting.splitting C D.smooth D.connected hsol
  let V := closedSubgroupAlgebraicGroup U
  have hUu : IsUnipotent V := hU.2.2.2.1
  have hmultZ : (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage
      (closedSubgroupAlgebraicGroup Z) :=
    (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeGroupCriterion _).mpr
      (centre_splits LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists
        LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer G hg Z hc)
  have h0 := LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
    V B (U.inclusion ≫ f) hUu (torus_isMultiplicativeType B hT.1)
  have hkill : (U.inclusion ≫ j) ≫ q = 0 := by
    rw [Category.assoc, he, ← Category.assoc, h0, zero_comp]
  obtain ⟨l, hle⟩ := (schemeKernel_sections hz (U.inclusion ≫ j).hom.hom).mpr
    (congrArg (Grp.forget (SchemeOver k)).map hkill)
  letI := Z.isClosedImmersion
  letI := isMonHom_of_comp_closed l (U.inclusion ≫ j) Z.inclusion hle
  let v : U.group ⟶ Z.group := Grp.homMk l
  have hv : v ≫ Z.inclusion = U.inclusion ≫ j := Grp.hom_ext _ _ hle
  have hv0 := LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType
    V (closedSubgroupAlgebraicGroup Z) v hUu hmultZ
  letI := hj
  letI : Mono j.hom.hom.left := inferInstance
  letI : Mono j.hom.hom := Over.mono_of_mono_left _
  letI : Mono j := (Grp.forget (SchemeOver k)).mono_of_mono_map ‹Mono j.hom.hom›
  have hUi : U.inclusion = 0 := (cancel_mono j).mp (by rw [← hv, hv0, zero_comp, zero_comp])
  letI := isIso_of_trivial_kernel s U hs (trivial_of_zero_inclusion U hUi)
  have hC : IsTorus C.val := torus_of_iso (asIso s).symm
    ((isTorus_iff_coordinates J).mpr (torus_of_split hJ))
  let E := subgroupOfSubgroup P D.subgroup
  obtain ⟨S, hS, g, hgS⟩ : ∃ S : ClosedSubgroup G.val, IsMaximalTorus S ∧
      ∃ g : D.subgroup.group ⟶ S.group, g ≫ S.inclusion = j :=
    exists_maximal_torus_over G E hC
  obtain ⟨I, b, hI, hb⟩ : ∃ (I : ClosedSubgroup Q.val) (b : S.group ⟶ I.group),
      IsTorus I.group ∧ b ≫ I.inclusion = S.inclusion ≫ q :=
    image_of_geometric_torus (G := closedSubgroupAlgebraicGroup S) (Q := Q)
      (S.inclusion ≫ q) hS.1
  have hTI : IsSubgroupOf T I := by
    letI : Smooth T.group.X.hom := hsB
    letI := isReduced_of_smooth_over_field T.group.X.hom
    have hcomm : f ≫ T.inclusion = (g ≫ b) ≫ I.inclusion := by
      rw [Category.assoc g b I.inclusion, hb, ← Category.assoc g S.inclusion q, hgS]
      exact he.symm
    obtain ⟨i, hi⟩ := factors_of_range_subset T.inclusion.hom.hom I.inclusion.hom.hom
      I.isClosedImmersion (by
        rintro _ ⟨y, rfl⟩
        obtain ⟨x, rfl⟩ := hfs.1 y
        exact ⟨(g ≫ b).hom.hom.left x,
          (congrArg (fun a : D.subgroup.group ⟶ Q.val ↦ a.hom.hom.left x) hcomm).symm⟩)
    letI := I.isClosedImmersion
    letI := isMonHom_of_comp_closed i T.inclusion I.inclusion hi
    exact ⟨Grp.homMk i, Grp.hom_ext _ _ hi⟩
  obtain ⟨l, hli⟩ := hT.2 I hI hTI
  let r : S.group ⟶ T.group := b ≫ l
  have hr : S.inclusion ≫ q = r ≫ T.inclusion := by
    change S.inclusion ≫ q = (b ≫ l) ≫ T.inclusion
    rw [Category.assoc, hli, hb]
  letI := inclusion_mono T
  have hfr : f = g ≫ r := (cancel_mono T.inclusion).mp (by
    rw [Category.assoc g r T.inclusion, ← hr, ← Category.assoc g S.inclusion q, hgS]
    exact he.symm)
  have hsurj : Surjective r.hom.hom.left := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ := hfs.1 y
    exact ⟨g.hom.hom.left x,
      (congrArg (fun a : D.subgroup.group ⟶ T.group ↦ a.hom.hom.left x) hfr).symm.trans hx⟩⟩
  have hflat := flatOfSurjectiveHom (A := closedSubgroupAlgebraicGroup S) (B := B) r hsB hsurj
  letI : LocallyOfFiniteType T.group.X.hom := B.property.2.1
  have hfp : LocallyOfFinitePresentation r.hom.hom.left := by
    letI := LocallyOfFiniteType.isLocallyNoetherian T.group.X.hom
    haveI : LocallyOfFiniteType (r.hom.hom.left ≫ T.group.X.hom) := by
      rw [Over.w r.hom.hom]
      exact (closedSubgroupAlgebraicGroup S).property.2.1
    letI := locallyOfFiniteType_of_comp r.hom.hom.left T.group.X.hom
    infer_instance
  have hmaxS := geometricallyMaximal_of_maximal_split G S hS
    (split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup S)).mp hS.1))
  have hZS := centre_le_of_selfCentralizer hc
    (LinearAlgebraicGroups.Reductive.TorusCentralizer.maximalTorusCentralizer G hg S hS.1 hmaxS)
  have hPS := full_preimage_of_surjective_subgroup hz hZS hr
    (Grp.hom_ext _ _ hp.w) hflat hsurj hfp
  have hSP : IsSubgroupOf S P := by
    let a := hp.lift S.inclusion.hom.hom r.hom.hom (congrArg (Grp.forget (SchemeOver k)).map hr)
    have ha : a ≫ P.inclusion.hom.hom = S.inclusion.hom.hom := hp.lift_fst _ _ _
    letI := P.isClosedImmersion
    letI := isMonHom_of_comp_closed a S.inclusion P.inclusion ha
    exact ⟨Grp.homMk a, Grp.hom_ext _ _ ha⟩
  obtain ⟨e, _⟩ := subgroupIso hSP hPS
  exact ⟨torus_of_iso e hS.1, fun D hD hPD ↦
    subgroup_trans (hS.2 D hD (subgroup_trans hSP hPD)) hSP⟩

theorem maximalTorusPreimage : MaximalTorusPreimage.{u} := by
  intro k _ G Q Z q hg hq T hT hmax
  obtain ⟨P, p, hp⟩ := preimageSubgroup (G := G) (Q := Q) q T
  have hpover := underlyingPullback hp
  have hp' := schemePullback hp
  have hpf : Flat p.hom.hom.left := MorphismProperty.of_isPullback hp' hq.2.2.2.1
  have hps : Surjective p.hom.hom.left := MorphismProperty.of_isPullback hp' hq.2.2.2.2.1
  have hpl : LocallyOfFinitePresentation p.hom.hom.left :=
    MorphismProperty.of_isPullback hp' hq.2.2.2.2.2
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨hZ, hcentre⟩ := centre_baseChange hq.1 K
  let Z' := baseChangedSubgroup K Z hZ
  let G' := GeometricGroup G
  let Q' := GeometricGroup Q
  let P' := extendSubgroup K P
  let T' := extendSubgroup K T
  have hT' : IsMaximalTorus T' := hmax.choose_spec
  let q' := F.map q
  let p' := F.map p
  have hg' := (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := K) G hg.1 hg.2.1).mpr hg
  have hker : IsSchemeKernel q' Z' := baseChangeKernelSquare q Z.inclusion hq.2.1
  have hpb : IsPullback P'.inclusion.hom.hom p'.hom.hom q'.hom.hom T'.inclusion.hom.hom :=
    hpover.map (baseChange k K)
  have hbase := (baseChangeMapPullback (K := K) p.hom.hom).flip
  have hP' := geometric_preimage_maximal (G := G') (Q := Q') (P := P') (T := T') hg' hker
    hcentre hpb (MorphismProperty.of_isPullback hbase hpf) (MorphismProperty.of_isPullback hbase hpl) hT'
  have hPm : IsGeometricallyMaximal P := ⟨P'.isClosedImmersion, hP'⟩
  have hPt := torus_descends_from_algebraic_closure (closedSubgroupAlgebraicGroup P) hP'.1
  exact ⟨P, p, hpover,
    maximalTorus_of_geometricallyMaximal G P hPt hPm, hPm, hpf, hps⟩

open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)
open LinearAlgebraicGroups.CharacterDescent
  (geometricAction geometricCharacterFunctor baseChangeCharacterMap baseChangeCharacterMap_bijective
    extendedHopfFunctor monomialCharacterEquiv)
open Specs.CharacterDescent
  (Cocharacter IsMultiplicativeType)
open private monomialCharacter splitBaseChange from
  LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private specGroupMap_comp
  from LinearAlgebraicGroups.Affine.ClosedSubgroups

private def evaluation {K : Type u} [Field K] [Algebra k K]
    {A : HopfAlgebraCategory k} (v : RationalCocharacters K A) :
    GeometricCharacters K A →* Multiplicative ℚ where
  toFun x := Multiplicative.ofAdd (v (1 ⊗ₜ[ℤ] Additive.ofMul x))
  map_one' := by change v (1 ⊗ₜ[ℤ] (0 : Additive (GeometricCharacters K A))) = 0; simp
  map_mul' x y := by
    change v (1 ⊗ₜ[ℤ] (Additive.ofMul x + Additive.ofMul y)) =
      v (1 ⊗ₜ[ℤ] Additive.ofMul x) + v (1 ⊗ₜ[ℤ] Additive.ofMul y)
    rw [TensorProduct.tmul_add, map_add]

private theorem integral_multiple {M : Type u} [CommGroup M] [Group.FG M]
    (g : M →* Multiplicative ℚ) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (v : M →* Multiplicative ℤ),
      ∀ x, ((v x).toAdd : ℚ) = n * (g x).toAdd := by
  classical
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG M)
  let t := hfin.toFinset
  let n := ∏ x ∈ t, (g x).toAdd.den
  have hn : 0 < n := Finset.prod_pos (fun x _ ↦ (g x).toAdd.pos)
  let a : Multiplicative ℤ →* Multiplicative ℚ := (Int.castAddHom ℚ).toMultiplicative
  have ha : Function.Injective a := fun x y h ↦ Int.cast_injective
    (show (x.toAdd : ℚ) = (y.toAdd : ℚ) from h)
  let f := (powMonoidHom n).comp g
  have hv (x : M) : f x ∈ a.range := by
    have hh : Subgroup.closure s ≤ a.range.comap f := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      have hxt : x ∈ t := hfin.mem_toFinset.mpr hx
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun x ↦ (g x).toAdd.den) hxt
      change n = (g x).toAdd.den * m at hm
      change f x ∈ a.range
      refine ⟨Multiplicative.ofAdd ((m : ℤ) * (g x).toAdd.num), ?_⟩
      change (((m : ℤ) * (g x).toAdd.num : ℤ) : ℚ) = n * (g x).toAdd
      rw [hm, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, mul_comm ((g x).toAdd.den : ℚ),
        mul_assoc, Rat.den_mul_eq_num]
    exact hh (hs.symm ▸ Subgroup.mem_top x)
  let e : Multiplicative ℤ ≃* a.range :=
    MulEquiv.ofBijective (a.codRestrict a.range (fun x ↦ ⟨x, rfl⟩)) ⟨fun _ _ h ↦
      ha (congrArg Subtype.val h), fun y ↦ by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x, Subtype.ext hx⟩⟩
  let v := e.symm.toMonoidHom.comp (f.codRestrict a.range hv)
  refine ⟨n, hn, v, fun x ↦ ?_⟩
  exact congrArg (fun y : a.range ↦ y.val.toAdd) (e.apply_symm_apply ⟨f x, hv x⟩)

private abbrev gmCoordinates (k : Type u) [Field k] :=
  groupAlgebra k IntegerCharacters.{u}

private theorem gmDiagonalizable : Specs.CharacterDescent.IsDiagonalizable (gmCoordinates k) :=
  ⟨⟨CommGrpCat.of IntegerCharacters.{u}, inferInstance⟩, ⟨Iso.refl _⟩⟩

private theorem gmMultiplicativeType :
    IsMultiplicativeType (gmCoordinates k) :=
  ⟨k, inferInstance, inferInstance, inferInstance, splitBaseChange (K := k) _ gmDiagonalizable⟩

private def gmCharacterEquiv (K : Type u) [Field K] [Algebra k K] :
    IntegerCharacters.{u} ≃* GeometricCharacters K (gmCoordinates k) :=
  (monomialCharacterEquiv k).trans (MulEquiv.ofBijective
    (baseChangeCharacterMap K _) (baseChangeCharacterMap_bijective K _ gmDiagonalizable))

private theorem gmCharacter_fixed (K : Type u) [Field K] [Algebra k K]
    (σ : Gal(K/k)) (x : GeometricCharacters K (gmCoordinates k)) :
    (geometricAction K (gmCoordinates k) σ).asHom x = x := by
  obtain ⟨a, rfl⟩ := (gmCharacterEquiv (k := k) K).surjective x
  apply GroupLike.val_injective
  change σ 1 ⊗ₜ[k] (monomialCharacter k a).val = (1 : K) ⊗ₜ[k] (monomialCharacter k a).val
  rw [map_one]

private theorem pullbackCharacter_comp (K : Type u) [Field K] [Algebra k K]
    {A B C : HopfAlgebraCategory k} (f : A ⟶ B) (g : B ⟶ C)
    (x : GeometricCharacters K A) :
    pullbackCharacter K (f ≫ g) x = pullbackCharacter K g (pullbackCharacter K f x) := by
  apply GroupLike.val_injective
  change ((extendedHopfFunctor K).map (f ≫ g)).hom x.val = _
  rw [Functor.map_comp]
  rfl

private theorem gmCharacter_power (K : Type u) [Field K] [Algebra k K]
    (n : ℕ) (x : GeometricCharacters K (gmCoordinates k)) :
    pullbackCharacter K (groupAlgebraMap k (powMonoidHom n)) x = x ^ n := by
  obtain ⟨a, rfl⟩ := (gmCharacterEquiv (k := k) K).surjective x
  rw [← map_pow]
  apply GroupLike.val_injective
  change (1 : K) ⊗ₜ[k] (groupAlgebraMap k (powMonoidHom n)).hom
    (MonoidAlgebra.of k IntegerCharacters a) = (1 : K) ⊗ₜ[k]
      MonoidAlgebra.of k IntegerCharacters (a ^ n)
  simp [groupAlgebraMap, MonoidAlgebra.of_apply]

set_option backward.isDefEq.respectTransparency true in
/-- A surjective torus map lifts a positive multiple of every cocharacter.
Rational invariant lifting is followed by clearing denominators in a set of
lattice generators and descending the resulting integral character map. -/
private theorem lift_of_surjective_tori
    {K : Type u} [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} {f : A ⟶ B}
    (hA : Specs.CharacterDescent.IsTorus A) (hB : Specs.CharacterDescent.IsTorus B)
    (hf : Function.Injective (pullbackCharacter K f))
    (c : A ⟶ gmCoordinates k) :
    ∃ (n : ℕ), 0 < n ∧ ∃ (d : B ⟶ gmCoordinates k),
      f ≫ d = c ≫ groupAlgebraMap k (powMonoidHom n) := by
  let F := geometricCharacterFunctor (k := k) K
  letI : F.Full := geometricCharacterFunctor_full K
  letI : F.Faithful := geometricCharacterFunctor_faithful K
  let hAm := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType _ hA
  let hBm := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType _ hB
  let mk (C : HopfAlgebraCategory k) (h : IsMultiplicativeType C) : MultiplicativeTypeHopf k :=
    ⟨⟨C, (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties C h).1⟩, h⟩
  let B' := mk B hBm
  let Gm := mk (gmCoordinates k) gmMultiplicativeType
  letI : Group.FG (GeometricCharacters K B) := (F.obj B').property.1
  let e : GeometricCharacters K (gmCoordinates k) ≃* Multiplicative ℤ :=
    (gmCharacterEquiv (k := k) K).symm.trans MulEquiv.ulift
  let c₀ : GeometricCharacters K A →* Multiplicative ℤ := e.toMonoidHom.comp (pullbackCharacter K c)
  let integral : Module.Dual ℤ (Additive (GeometricCharacters K A)) :=
    c₀.toAdditive.toIntLinearMap
  let w : RationalCocharacters K A := integral.baseChange ℚ
  have hw_eval (x : GeometricCharacters K A) :
      w (1 ⊗ₜ[ℤ] Additive.ofMul x) = ((c₀ x).toAdd : ℚ) := by
    calc
      w (1 ⊗ₜ[ℤ] Additive.ofMul x) = integral (Additive.ofMul x) • (1 : ℚ) :=
        Module.Dual.baseChange_apply_tmul ℚ integral 1 (Additive.ofMul x)
      _ = _ := by
        change (c₀ x).toAdd • (1 : ℚ) = _
        simp [zsmul_eq_mul]
  have hw : w ∈ rationalCocharacterInvariants K A := by
    intro σ x y hxy
    rw [hw_eval, hw_eval]
    have h := LinearAlgebraicGroups.SmoothnessAndIsogenies.characterPullbackEquivariant
      (K := K) c hAm gmMultiplicativeType σ x y hxy
    have h' : (geometricAction K (gmCoordinates k) σ).asHom (pullbackCharacter K c x) =
        pullbackCharacter K c y := GroupLike.val_injective h
    rw [gmCharacter_fixed] at h'
    change ((e (pullbackCharacter K c y)).toAdd : ℚ) = ((e (pullbackCharacter K c x)).toAdd : ℚ)
    rw [h']
  have hs : Function.Surjective (rationalCocharacterMap K f) :=
    LinearMap.dualMap_surjective_of_injective (rationalCharacterMap_injective f hf)
  have hinv := rationalInvariantMap f hAm hBm hs
  rw [← hinv] at hw
  obtain ⟨v, hv, he⟩ := hw
  obtain ⟨n, hn, d₀, hd⟩ := integral_multiple (evaluation v)
  let d := e.symm.toMonoidHom.comp d₀
  let g : F.obj B' ⟶ F.obj Gm := ObjectProperty.homMk
    { hom := CommGrpCat.ofHom d
      comm := by
        intro σ
        apply CommGrpCat.ext
        intro x
        change GeometricCharacters K B at x
        let y := (geometricAction K B σ).asHom x
        change d y = (geometricAction K (gmCoordinates k) σ).asHom (d x)
        rw [gmCharacter_fixed]
        change e.symm (d₀ y) = e.symm (d₀ x)
        congr 1
        change (d₀ y).toAdd = (d₀ x).toAdd
        apply (Int.cast_injective (α := ℚ))
        rw [hd, hd]
        exact congrArg (fun a : ℚ ↦ (n : ℚ) * a) (hv σ x y rfl) }
  let d' := F.preimage g
  have hge (x : GeometricCharacters K B) : pullbackCharacter K d'.hom.hom x = d x :=
    congrArg (fun s : F.obj B' ⟶ F.obj Gm ↦ s.hom.hom.hom x) (F.map_preimage g)
  let A' := mk A hAm
  let f' : A' ⟶ B' := ObjectProperty.homMk (InducedCategory.homMk f)
  let c' : A' ⟶ Gm := ObjectProperty.homMk (InducedCategory.homMk c)
  let pow' : Gm ⟶ Gm := ObjectProperty.homMk (InducedCategory.homMk
    (groupAlgebraMap k (powMonoidHom n)))
  have heq : f' ≫ d' = c' ≫ pow' := by
    apply F.map_injective
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply CommGrpCat.ext
    intro x
    change GeometricCharacters K A at x
    change pullbackCharacter K (f ≫ d'.hom.hom) x =
      pullbackCharacter K (c ≫ groupAlgebraMap k (powMonoidHom n)) x
    rw [pullbackCharacter_comp, pullbackCharacter_comp, hge, gmCharacter_power]
    apply e.injective
    rw [map_pow]
    change e (e.symm (d₀ (pullbackCharacter K f x))) = (e (pullbackCharacter K c x)) ^ n
    rw [e.apply_symm_apply]
    change (d₀ (pullbackCharacter K f x)).toAdd = ((e (pullbackCharacter K c x)) ^ n).toAdd
    apply (Int.cast_injective (α := ℚ))
    rw [hd]
    change (n : ℚ) * v (1 ⊗ₜ[ℤ] Additive.ofMul (pullbackCharacter K f x)) =
      ((n • (c₀ x).toAdd : ℤ) : ℚ)
    have hx := LinearMap.congr_fun he ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul x)
    change v (1 ⊗ₜ[ℤ] Additive.ofMul (pullbackCharacter K f x)) =
      w (1 ⊗ₜ[ℤ] Additive.ofMul x) at hx
    rw [hx, hw_eval]
    simp
  exact ⟨n, hn, d'.hom.hom,
    congrArg (fun a : A' ⟶ Gm ↦ a.hom.hom) heq⟩

open Specs.DiagonalizableGroups (diagonalGroup)
open private torus_in_centralizer from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private factor_torus_through_centralizer from LinearAlgebraicGroups.Reductive.MaximalToriExist
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

private theorem torusInMaximalTorus {Q : AffineAlgebraicGroup k}
    (hsQ : Smooth Q.val.X.hom) (hcQ : ConnectedSpace Q.val.X.left)
    (S : ClosedSubgroup Q.val) (hS : IsTorus S.group) :
    ∃ T : ClosedSubgroup Q.val, IsTorus T.group ∧ IsGeometricallyMaximal T ∧ IsSubgroupOf S T := by
  letI := hsQ
  letI := hcQ
  obtain ⟨C, hC, hsC, hcC⟩ := LinearAlgebraicGroups.CocharacterDynamics.connectedTorusCentralizer Q S hS
  let A := closedSubgroupAlgebraicGroup C
  obtain ⟨T, hT, hTm, hMax⟩ := LinearAlgebraicGroups.MaximalToriExist.geometricallyMaximalTorusExists
    A hsC (connectedOfGeometricallyConnected A hcC)
  obtain ⟨j, hj, hji, _⟩ := torus_in_centralizer (G := Q)
    (torus_commutative (closedSubgroupAlgebraicGroup S) hS) hC
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Q' := GeometricGroup Q
  let A' := GeometricGroup A
  let T' := extendSubgroup K T
  let S' := extendSubgroup K S
  let cj := extendSubgroup K C
  obtain ⟨_, hC'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K S.inclusion C hC
  have hC' : RepresentsSubgroup cj (fun _ g ↦ Centralizes S'.inclusion g) := hC'
  have hS' : IsTorus S'.group := torus_after_algClosed_extension K (closedSubgroupAlgebraicGroup S) hS
  have hsA' : Smooth A'.val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback A.val.X.hom (fieldSpecMap k K)) hsC
  have hcA' : ConnectedSpace A'.val.X.left := by
    letI : GeometricallyConnected A.val.X.hom := hcC
    exact pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace K
      (fieldSpecMap k K)
  have hMax' : IsMaximalTorus T' := hMax
  obtain ⟨B, hB, _, _, _, _, i, hi, U, p, hipt, hp, hU⟩ :=
    LinearAlgebraicGroups.TorusFreeUnipotent.maximalTorusCentralizer A' hsA' hcA' T' hMax'
  have hj' : IsClosedImmersion (F.map j).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) j.hom.hom).flip hj
  let J : ClosedSubgroup A'.val := ⟨S'.group, F.map j, hj'⟩
  have hJc : J.inclusion ≫ cj.inclusion = S'.inclusion := by
    change F.map j ≫ F.map C.inclusion = F.map S.inclusion
    rw [← F.map_comp, hji]
  have hcen : Centralizes T'.inclusion J.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y x y
    have hc := (hC' Y (y ≫ T'.inclusion.hom.hom ≫ cj.inclusion.hom.hom)).mpr
      ⟨y ≫ T'.inclusion.hom.hom, Category.assoc _ _ _⟩
    have h := (centralizes_iff _ _).mp hc Y (𝟙 _) x
    letI := cj.isClosedImmersion
    haveI : Mono cj.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono cj.inclusion.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc,
      show J.inclusion.hom.hom ≫ cj.inclusion.hom.hom = S'.inclusion.hom.hom
        from congrArg (Grp.forget (SchemeOver K)).map hJc]
    simpa only [Category.id_comp] using h.symm.eq
  obtain ⟨a, ha⟩ := (hB _ _).mp hcen
  letI := B.isClosedImmersion
  letI := isMonHom_of_comp_closed a J.inclusion B.inclusion ha
  let l : J.group ⟶ B.group := Grp.homMk a
  have hzero : l ≫ p = 0 := LinearAlgebraicGroups.Unipotent.homFromMultiplicativeTypeToUnipotent
    (closedSubgroupAlgebraicGroup J) U (l ≫ p)
    (torus_isMultiplicativeType (closedSubgroupAlgebraicGroup J) hS') hU
  let I : ClosedSubgroup B.group := ⟨T'.group, i, hi⟩
  obtain ⟨v, hv⟩ := (schemeKernel_sections (N := I) hp.1 a).mpr
    (congrArg (Grp.forget (SchemeOver K)).map hzero)
  letI := hi
  letI := isMonHom_of_comp_closed v l i hv
  let t : J.group ⟶ T'.group := Grp.homMk v
  have ht : t ≫ i = l := Grp.hom_ext _ _ hv
  have hJT : t ≫ T'.inclusion = J.inclusion := by
    rw [← hipt, ← Category.assoc, ht]
    exact Grp.hom_ext _ _ ha
  let T₀ := subgroupOfSubgroup C T
  let L := extendSubgroup K T₀
  have hL : T'.inclusion ≫ cj.inclusion = L.inclusion := (F.map_comp _ _).symm
  have hSL : IsSubgroupOf S' L := ⟨t, by rw [← hL, ← Category.assoc, hJT, hJc]⟩
  have hST := (subgroup_baseChange_iff (K := K) S T₀).mp hSL
  refine ⟨T₀, hT, ⟨L.isClosedImmersion, ?_⟩, hST⟩
  refine ⟨hMax'.1, fun D hD hLD ↦ ?_⟩
  change IsSubgroupOf L D at hLD
  obtain ⟨b, hb⟩ := factor_torus_through_centralizer (C := cj) hC'
    (torus_commutative (closedSubgroupAlgebraicGroup (G := Q') D) hD) (subgroup_trans hSL hLD)
  let D' : ClosedSubgroup A'.val := ⟨D.group, b, factor_closed hb⟩
  have hTD' : IsSubgroupOf T' D' := by
    obtain ⟨d, hd⟩ := hLD
    letI := inclusion_mono cj
    exact ⟨d, (cancel_mono cj.inclusion).mp (by
      change (d ≫ b) ≫ cj.inclusion = T'.inclusion ≫ cj.inclusion
      rw [Category.assoc, hb, hd, hL])⟩
  obtain ⟨c, hc⟩ := hMax'.2 D' hD hTD'
  exact ⟨c, by
    change c ≫ L.inclusion = D.inclusion
    rw [← hL, ← Category.assoc, hc]
    exact hb⟩

private theorem cocharacterInMaximalTorus {Q : AffineAlgebraicGroup k} (hQ : IsReductive Q)
    (c : Cocharacter Q.val) :
    ∃ (T : ClosedSubgroup Q.val) (d : Cocharacter T.group),
      IsTorus T.group ∧ IsGeometricallyMaximal T ∧ d ≫ T.inclusion = c := by
  let A := diagonalGroup k IntegerCharacters.{u}
  have hg : Specs.CharacterDescent.IsTorus (gmCoordinates k) := by
    apply ((LinearAlgebraicGroups.CharacterDescent.torusAndSplitCriteria
      (K := SeparableClosure k) _ gmMultiplicativeType).1).mpr
    exact ⟨1, ⟨(gmCharacterEquiv (k := k) (SeparableClosure k)).symm.trans
      (MulEquiv.piUnique (fun _ : Fin 1 ↦ IntegerCharacters.{u})).symm⟩⟩
  have htA : IsTorus A.val := (LinearAlgebraicGroups.CharacterDescent.torusOnSchemes _).mp hg
  obtain ⟨_, hsA, hcA⟩ :=
    (LinearAlgebraicGroups.SmoothnessAndIsogenies.smoothConnectedMultiplicativeType _).mp hg
  obtain ⟨I, p, i, h, _, _⟩ := LinearAlgebraicGroups.schemeImageFactorization A Q c
  let S : ClosedSubgroup Q.val := ⟨I.val, i, h.2.2.2.2.2⟩
  have hS := torusOfSurjectiveMap A I p htA
    (quotient_smooth_connected p h.2.1 h.2.2.1 hsA hcA).1 h.2.2.1
  obtain ⟨T, ht, hm, ⟨j, hj⟩⟩ := torusInMaximalTorus hQ.1
    (connectedOfGeometricallyConnected Q hQ.2.1) S hS
  exact ⟨T, p ≫ j, ht, hm, by rw [Category.assoc, hj]; exact h.1⟩

theorem adjointCocharacterLift : AdjointCocharacterLift.{u} := by
  intro k _ G Q Z q hg hq c
  have hQ := reductive_of_central_quotient hg hq.2.1 hq.1 hq.2.2.2.1
    hq.2.2.2.2.1 hq.2.2.2.2.2
  obtain ⟨T', c', ht, hm, hc⟩ := cocharacterInMaximalTorus hQ c
  obtain ⟨T, p, hp⟩ := maximalTorusPreimage Z q hg hq T' ht hm
  let A := closedSubgroupAlgebraicGroup T'
  let B := closedSubgroupAlgebraicGroup T
  let eA := Specs.AdjointCocharacters.coordinateHopfIso A
  let eB := Specs.AdjointCocharacters.coordinateHopfIso B
  let f := Specs.AdjointCocharacters.coordinateHopfMap (G := B) (H := A) p
  let FF := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : Specs.AdjointCocharacters.coordinateHopf A ⟶ gmCoordinates k := (FF.preimage (c' ≫ eA.inv)).unop
  have ha : specGroupMap a = c' ≫ eA.inv := FF.map_preimage _
  have hAt := coordinatePresentationTorus A ht
  have hBt := coordinatePresentationTorus B hp.2.1.1
  have hfi := pullbackCharacter_injective_of_surjective
    (K := SeparableClosure k) f hAt hBt
    (coordinatePresentationSurjective (G := B) (H := A) p hp.2.2.2.2)
  obtain ⟨n, hn, b, hb⟩ := lift_of_surjective_tori (K := SeparableClosure k) hAt hBt hfi a
  refine ⟨n, hn, specGroupMap b ≫ eB.hom ≫ T.inclusion, ?_⟩
  have hm₀ : specGroupMap b ≫ eB.hom ≫ p = powerOnGm k n ≫ c' := by
    apply (cancel_mono eA.inv).mp
    have he := congrArg specGroupMap hb
    rw [specGroupMap_comp, specGroupMap_comp, ha, coordinatePresentationMap] at he
    simpa only [Category.assoc, eA, eB, powerOnGm] using he
  have hpw : T.inclusion ≫ q = p ≫ T'.inclusion := Grp.hom_ext _ _ hp.1.w
  calc
    _ = (specGroupMap b ≫ eB.hom ≫ p) ≫ T'.inclusion := by
      simp only [Category.assoc, hpw]
    _ = _ := by rw [hm₀, Category.assoc, hc]

end

end LinearAlgebraicGroups.Descent.AdjointCocharacters
