import Specs.LinearAlgebraicGroups.Reductive.MaximalToriExist
import Specs.LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
import LinearAlgebraicGroups.Descent.FiniteFieldFlags
import LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Idempotents

import LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.MaximalToriExist

open _root_.LinearAlgebraicGroups.Specs
open Algebra.TensorProduct (includeLeft includeRight)
open Specs.GeometricRadicals (IsTorus IsMaximalTorus IsTrivialSubgroup
  GeometricGroup baseChangedSubgroup identitySubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)
open Specs.DiagonalizableGroups (groupAlgebra diagonalGroup)
open Specs.CharacterDescent (StandardLattice)
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private torus_smooth_connected_solvable from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private exists_maximal_torus_over isTorus_iff_coordinates inclusion_mono torus_of_iso
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private trivial_isSplitTorus isTorus_of_split isSplitTorus_of_torus torusHopf_split
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private torus_in_centralizer torus_commutative torus_of_torus_extension
  from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private baseChangeMapPullback baseChangeKernelSquare
  from LinearAlgebraicGroups.Affine.Components
open private represented_quotient_of_kernel
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private isReduced_of_smooth_over_field smooth_of_smooth_after_fieldExtension
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_closed from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private groupPresentation isMonHom_of_comp_closed schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private reducedImage imageTorus
  from LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel

open private groupLikeIso groupAlgebraOfCharacters
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option autoImplicit false
set_option linter.style.haveILetI false

private theorem groupLike_map_coefficients {K L R A : Type*}
    [Field K] [Field L] [CommRing R] [CommRing A] [Algebra K L] [Algebra K R]
    [Bialgebra K A] (φ : L →ₐ[K] R) {x : L ⊗[K] A}
    (hx : IsGroupLikeElem L x) :
    IsGroupLikeElem R (Algebra.TensorProduct.map φ (AlgHom.id K A) x) := by
  let f := Algebra.TensorProduct.map φ (AlgHom.id K A)
  have hφ : f.toRingHom.comp (algebraMap L (L ⊗[K] A)) =
      (algebraMap R (R ⊗[K] A)).comp φ.toRingHom := by
    ext l
    change f (l ⊗ₜ[K] (1 : A)) = φ l ⊗ₜ[K] (1 : A)
    rfl
  let g := Algebra.TensorProduct.mapRingHom φ.toRingHom f.toRingHom f.toRingHom hφ hφ
  have hc (z : L ⊗[K] A) : counit (R := R) (f z) = φ (counit (R := L) z) := by
    induction z with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul l a =>
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.counit_tmul,
        CommSemiring.counit_apply, Algebra.smul_def, map_mul, AlgHom.commutes]
  have hd (z : L ⊗[K] A) : comul (R := R) (f z) = g (comul (R := L) z) := by
    induction z with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul l a =>
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        TensorProduct.comul_tmul, CommSemiring.comul_apply]
      generalize comul (R := K) a = t
      induction t with
      | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
      | tmul a b =>
        simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, g,
          Algebra.TensorProduct.mapRingHom_tmul, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, f, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  exact ⟨by rw [hc, hx.counit_eq_one, map_one],
    by rw [hd, hx.comul_eq_tmul_self, Algebra.TensorProduct.mapRingHom_tmul]; rfl⟩

private theorem groupLike_coordinate_isIdempotent {R B Index : Type*}
    [CommRing R] [AddCommGroup B] [Module R B] [Coalgebra R B]
    (b : Module.Basis Index R B) (hb : ∀ i, IsGroupLikeElem R (b i))
    {x : B} (hx : IsGroupLikeElem R x) (i : Index) :
    IsIdempotentElem (b.coord i x) := by
  classical
  let c := (TensorProduct.lid R R).toLinearMap.comp
    (TensorProduct.map (b.coord i) (b.coord i))
  have he : c.comp (comul (R := R)) = b.coord i := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, hb j |>.comul_eq_tmul_self]
    change (TensorProduct.lid R R) ((b.coord i (b j)) ⊗ₜ[R] (b.coord i (b j))) = b.coord i (b j)
    simp only [TensorProduct.lid_tmul, smul_eq_mul, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply]
    split_ifs <;> simp
  have hh := LinearMap.congr_fun he x
  rw [LinearMap.comp_apply, hx.comul_eq_tmul_self] at hh
  simpa [c, IsIdempotentElem] using hh

/-- Along a purely inseparable extension, group-like elements descend whenever
the extended coalgebra has a basis of group-like elements. -/
private theorem groupLike_descends_purelyInseparable {K L A Index : Type*}
    [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
    [CommRing A] [Bialgebra K A]
    (b : Module.Basis Index L (L ⊗[K] A)) (hb : ∀ i, IsGroupLikeElem L (b i))
    {x : L ⊗[K] A} (hx : IsGroupLikeElem L x) :
    ∃ a : A, (1 : L) ⊗ₜ[K] a = x := by
  let R := L ⊗[K] L
  let f : L →ₐ[K] R := includeLeft
  let g : L →ₐ[K] R := includeRight
  let multiply : R →ₐ[K] L := Algebra.TensorProduct.lmul' K
  let F := Algebra.TensorProduct.map f (AlgHom.id K A)
  let G := Algebra.TensorProduct.map g (AlgHom.id K A)
  let M := Algebra.TensorProduct.map multiply (AlgHom.id K A)
  let c := Algebra.TensorProduct.cancelBaseChange K L R R A
  let d := (b.baseChange R).map c.toLinearEquiv
  have hF (i : Index) : d i = F (b i) := by
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
    change c ((1 : R) ⊗ₜ[L] b i) = F (b i)
    generalize b i = y
    induction y with
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul l a =>
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul]
      simp only [AlgHom.id_apply, f]
      congr 1
      rw [Algebra.smul_def, mul_one]
      rfl
  have hd (i : Index) : IsGroupLikeElem R (d i) :=
    hF i ▸ groupLike_map_coefficients f (hb i)
  have hmultiplyL (l : L) : multiply (algebraMap L R l) = l := by
    change l * 1 = l
    exact mul_one l
  have hmultiplyR (l : L) : multiply (g l) = l := by
    change 1 * l = l
    exact one_mul l
  have hmultiply (z : R) (hz : multiply z = 0) : IsNilpotent z := by
    obtain ⟨n, _, t, ht⟩ :=
      IsPurelyInseparable.exists_pow_mem_range_tensorProduct (k := K) z
    have ht0 : t = 0 := by rw [← hmultiplyL t, ht, map_pow, hz, zero_pow (by omega)]
    exact ⟨n, by rw [← ht, ht0, map_zero]⟩
  have hMF (y : L ⊗[K] A) : M (F y) = y := by
    induction y with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul l a =>
      change multiply (algebraMap L R l) ⊗ₜ[K] a = l ⊗ₜ[K] a
      rw [hmultiplyL]
  have hMG (y : L ⊗[K] A) : M (G y) = y := by
    induction y with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul l a =>
      change multiply (g l) ⊗ₜ[K] a = l ⊗ₜ[K] a
      rw [hmultiplyR]
  have hMc (z : R) (y : L ⊗[K] A) : M (c (z ⊗ₜ[L] y)) = multiply z • y := by
    induction y with
    | add y w hy hw => simp only [TensorProduct.tmul_add, map_add, smul_add, hy, hw]
    | tmul l a =>
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.smul_def, map_mul, TensorProduct.smul_tmul']
      rw [hmultiplyL, smul_eq_mul, mul_comm l]
  have hcoord (z : R ⊗[K] A) (i : Index) : multiply (d.coord i z) = b.coord i (M z) := by
    obtain ⟨w, rfl⟩ := c.surjective z
    induction w with
    | add w y hw hy => simp only [map_add, hw, hy]
    | tmul z y =>
      rw [hMc z y, map_smul, Module.Basis.coord_apply, Module.Basis.map_repr,
        LinearEquiv.trans_apply]
      change multiply (((b.baseChange R).repr (c.symm (c (z ⊗ₜ[L] y)))) i) = multiply z • b.coord i y
      rw [AlgEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul,
        Algebra.smul_def, map_mul, hmultiplyL, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  have he : F x = G x := by
    apply d.repr.injective
    ext i
    change d.coord i (F x) = d.coord i (G x)
    apply eq_of_isNilpotent_sub_of_isIdempotentElem
      (groupLike_coordinate_isIdempotent d hd (groupLike_map_coefficients f hx) i)
      (groupLike_coordinate_isIdempotent d hd (groupLike_map_coefficients g hx) i)
    apply hmultiply
    rw [map_sub, hcoord, hcoord, hMF, hMG, sub_self]
  obtain ⟨functional, hfunctional⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  let r : R →ₗ[K] L := (TensorProduct.lid K L).toLinearMap.comp
    (TensorProduct.map functional (LinearMap.id : L →ₗ[K] L))
  let p : L ⊗[K] A →ₗ[K] A := (TensorProduct.lid K A).toLinearMap.comp
    (TensorProduct.map functional (LinearMap.id : A →ₗ[K] A))
  let P := TensorProduct.map r (LinearMap.id : A →ₗ[K] A)
  have hPF (y : L ⊗[K] A) : P (F y) = (1 : L) ⊗ₜ[K] p y := by
    induction y with
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
    | tmul l a =>
      change r (l ⊗ₜ[K] (1 : L)) ⊗ₜ[K] a = (1 : L) ⊗ₜ[K] p (l ⊗ₜ[K] a)
      have hr : r (l ⊗ₜ[K] (1 : L)) = functional l • (1 : L) := by
        change TensorProduct.lid K L ((TensorProduct.map functional
          (LinearMap.id : L →ₗ[K] L)) (l ⊗ₜ[K] (1 : L))) = _
        rw [TensorProduct.map_tmul]
        rfl
      have hp : p (l ⊗ₜ[K] a) = functional l • a := by
        change TensorProduct.lid K A ((TensorProduct.map functional
          (LinearMap.id : A →ₗ[K] A)) (l ⊗ₜ[K] a)) = _
        rw [TensorProduct.map_tmul]
        rfl
      rw [hr, hp, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hPG (y : L ⊗[K] A) : P (G y) = y := by
    induction y with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul l a =>
      change r ((1 : L) ⊗ₜ[K] l) ⊗ₜ[K] a = l ⊗ₜ[K] a
      have hr : r ((1 : L) ⊗ₜ[K] l) = l := by
        change TensorProduct.lid K L ((TensorProduct.map functional
          (LinearMap.id : L →ₗ[K] L)) ((1 : L) ⊗ₜ[K] l)) = _
        rw [TensorProduct.map_tmul]
        change functional 1 • l = l
        rw [hfunctional, one_smul]
      rw [hr]
  exact ⟨p x, (hPF x).symm.trans ((congrArg P he).trans (hPG x))⟩

private def splitHopf_descends_purelyInseparable {k L : Type u} [Field k] [Field L] [Algebra k L]
    [IsPurelyInseparable k L] (A : HopfAlgebraCategory k) (r : ℕ)
    (e : groupAlgebra L (StandardLattice.{u} r) ≅ extendedHopf L A) :
    groupAlgebra k (StandardLattice.{u} r) ≅ A := by
  let b : Module.Basis (StandardLattice.{u} r) L (L ⊗[k] A) :=
    (MonoidAlgebra.basis (StandardLattice.{u} r) L).map
      (CommHopfAlgCat.ofIso e).toAlgEquiv.toLinearEquiv
  have hb (m : StandardLattice.{u} r) : IsGroupLikeElem L (b m) := by
    change IsGroupLikeElem L (e.hom.hom (MonoidAlgebra.single m 1))
    exact (MonoidAlgebra.isGroupLikeElem_single_one (R := L) (A := L) m).map e.hom.hom
  let W := Submodule.span k (Set.range (GroupLike.val (R := k) (A := A)))
  have hW : W.baseChange L = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    obtain ⟨a, ha⟩ := groupLike_descends_purelyInseparable b hb (hb m)
    have hgl : IsGroupLikeElem k a :=
      (CharacterDescent.isGroupLikeElem_tmul_one_iff L A a).mp (ha ▸ hb m)
    rw [← ha]
    exact Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.subset_span ⟨⟨a, hgl⟩, rfl⟩)
  have hsur : Function.Surjective (W.subtype.lTensor L) := by
    apply LinearMap.range_eq_top.mp
    ext z
    change (∃ w, W.subtype.lTensor L w = z) ↔ z ∈ (⊤ : Submodule k (L ⊗[k] A))
    rw [show (∃ w, W.subtype.lTensor L w = z) ↔ z ∈ W.baseChange L from Iff.rfl, hW]
    exact ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  have hspan : W = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨w, hw⟩ :=
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k L W.subtype).mp hsur a
    exact hw ▸ w.property
  have hbij : Function.Bijective (CharacterDescent.baseChangeCharacterMap L A) := by
    refine ⟨CharacterDescent.baseChangeCharacterMap_injective L A, ?_⟩
    intro x
    obtain ⟨a, ha⟩ := groupLike_descends_purelyInseparable b hb x.2
    refine ⟨⟨a, (CharacterDescent.isGroupLikeElem_tmul_one_iff L A a).mp (ha ▸ x.2)⟩, ?_⟩
    exact GroupLike.val_injective ha
  let chars := ((CharacterDescent.monomialCharacterEquiv L).trans (groupLikeIso e)).trans
    (MulEquiv.ofBijective (CharacterDescent.baseChangeCharacterMap L A) hbij).symm
  exact CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k chars) ≪≫
    groupAlgebraOfCharacters A hspan

private theorem torus_descends_from_algebraic_closure {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (h : IsTorus (GeometricGroup G).val) : IsTorus G.val := by
  let L := AlgebraicClosure k
  let K := SeparableClosure k
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := k) K
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  have ht : Specs.CharacterDescent.IsTorus (extendedHopf L A) :=
    (GeometricRadicals.torusCoordinateComparison (extendedHopf L A)).mp
      (torus_of_iso ((groupBaseChange k L).mapIso e.symm ≪≫ (extendedGroupIso L A).symm) h)
  obtain ⟨r, ⟨i⟩⟩ := torusHopf_split _ ht
  let j := splitHopf_descends_purelyInseparable (extendedHopf K A) r
    (i ≪≫ (CharacterDescent.extendedHopfTower (K := K) L A).symm)
  exact torus_of_iso e ((GeometricRadicals.torusCoordinateComparison A).mpr
    ⟨K, inferInstance, inferInstance, inferInstance, r, ⟨j⟩⟩)

variable {k : Type u} [Field k]

private theorem rational_maximal_exists (G : AffineAlgebraicGroup k) :
    ∃ T : ClosedSubgroup G.val, IsMaximalTorus T := by
  obtain ⟨T, hT, _⟩ :=
    exists_maximal_torus_over G (identitySubgroup G) (isTorus_of_split trivial_isSplitTorus)
  exact ⟨T, hT⟩

private theorem torus_after_algClosed_extension (K : Type u) [Field K] [Algebra k K]
    [IsAlgClosed K] (G : AffineAlgebraicGroup k) (hG : IsTorus G.val) :
    IsTorus ((groupBaseChange k K).obj G.val) := by
  obtain ⟨A, ⟨e⟩, E, _, _, _, r, ⟨t⟩⟩ := (isTorus_iff_coordinates G).mp hG
  let a : E →ₐ[k] K := IsAlgClosed.lift
  letI : Algebra E K := a.toRingHom.toAlgebra
  letI : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let t' : groupAlgebra K (StandardLattice.{u} r) ≅ extendedHopf K A :=
    (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange E K _)).symm ≪≫
      (CharacterDescent.extendedHopfFunctor K).mapIso t ≪≫
      CharacterDescent.extendedHopfTower (K := E) K A
  obtain ⟨j⟩ := CharacterDescent.standardSplitTorus (k := K) r
  exact isTorus_of_split ⟨r, ⟨(groupBaseChange k K).mapIso e.symm ≪≫
    (extendedGroupIso K A).symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso t'.op ≪≫ j⟩⟩

private theorem quotient_smooth_connected {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) (hf : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Smooth Q.val.X.hom ∧ ConnectedSpace Q.val.X.left := by
  let K := AlgebraicClosure k
  let q' := (groupBaseChange k K).map q
  have pb := baseChangeMapPullback (K := K) q.hom.hom
  have hf' : Flat q'.hom.hom.left := MorphismProperty.of_isPullback pb.flip hf
  have hsurj' : Surjective q'.hom.hom.left := MorphismProperty.of_isPullback pb.flip hsurj
  have hs' : Smooth (GeometricGroup G).val.X.hom :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hs
  letI := G.property.1
  letI := Q.property.1
  letI := (GeometricGroup G).property.1
  letI := (GeometricGroup Q).property.1
  letI := (GeometricGroup Q).property.2.1
  letI := hs'
  letI := hc
  have hred : IsReduced (GeometricGroup Q).val.X.left :=
    reducedImage (G := GeometricGroup G) (D := GeometricGroup Q) q'
      (isReduced_of_smooth_over_field (GeometricGroup G).val.X.hom) hf' hsurj'
  have hsq := smoothOfReducedOverPerfectField K (GeometricGroup Q).val hred
  exact ⟨smooth_of_smooth_after_fieldExtension (k := k) (K := K) Q.val.X.hom hsq,
    hsurj.1.connectedSpace q.hom.hom.left.continuous⟩

private theorem image_of_geometric_torus [IsAlgClosed k] {G Q : AffineAlgebraicGroup k}
    (f : G.val ⟶ Q.val) (hG : IsTorus G.val) :
    ∃ (D : ClosedSubgroup Q.val) (p : G.val ⟶ D.group),
      IsTorus D.group ∧ p ≫ D.inclusion = f := by
  obtain ⟨I, p, i, hfact, _, _⟩ := schemeImageFactorization G Q f
  obtain ⟨r, ⟨e⟩⟩ := isSplitTorus_of_torus G hG
  obtain ⟨d⟩ := CharacterDescent.standardSplitTorus (k := k) r
  let a : (diagonalGroup k (StandardLattice.{u} r)).val ≅ G.val := d ≪≫ e.symm
  letI : IsIso a.hom.hom.hom.left :=
    ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map_isIso a.hom
  letI := hfact.2.1
  letI := hfact.2.2.1
  have hff : Flat (a.hom ≫ p).hom.hom.left ∧ Surjective (a.hom ≫ p).hom.hom.left :=
    ⟨Flat.comp a.hom.hom.hom.left p.hom.hom.left,
      inferInstanceAs (Surjective (a.hom.hom.hom.left ≫ p.hom.hom.left))⟩
  obtain ⟨N, ⟨b, _⟩, _⟩ := (DiagonalizableGroups.diagonalFaithfullyFlatQuotients
    k (StandardLattice.{u} r) ⟨I.val, I.property.1⟩ (a.hom ≫ p)).mp hff
  letI := DiagonalizableGroups.subgroupFG N
  obtain ⟨hs, hc, _⟩ := torus_smooth_connected_solvable G hG
  obtain ⟨hI, _⟩ := imageTorus (G := G) (D := I) p hfact.2.1 hfact.2.2.1 hs hc
    ⟨⟨CommGrpCat.of N, inferInstance⟩, ⟨b⟩⟩ SmoothnessAndIsogenies.smoothConnectedMultiplicativeType
  exact ⟨⟨I.val, i, hfact.2.2.2.2.2⟩, p, (isTorus_iff_coordinates I).mpr hI, hfact.1⟩

private theorem factor_torus_through_centralizer {G : GroupScheme k}
    {T C S : ClosedSubgroup G}
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes T.inclusion g))
    (hS : IsCommMonObj S.group.X) (hTS : IsSubgroupOf T S) :
    ∃ l : S.group ⟶ C.group, l ≫ C.inclusion = S.inclusion := by
  obtain ⟨f, hf⟩ := hTS
  letI := hS
  have hcent : Centralizes T.inclusion S.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U x y
    have hy : T.inclusion.hom.hom = f.hom.hom ≫ S.inclusion.hom.hom :=
      (congrArg (fun a : T.group ⟶ G ↦ a.hom.hom) hf).symm
    rw [hy, ← Category.assoc y]
    exact (show Commute x (y ≫ f.hom.hom) from mul_comm _ _).map
      (IsMonHom.monoidHom S.inclusion.hom.hom U)
  obtain ⟨g, hg⟩ := (hC _ _).mp hcent
  letI := C.isClosedImmersion
  letI := isMonHom_of_comp_closed g S.inclusion C.inclusion hg
  exact ⟨Grp.homMk g, Grp.hom_ext _ _ hg⟩

private theorem geometric_quotient_torus
    {G Q : AffineAlgebraicGroup k} (T C : ClosedSubgroup G.val)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes T.inclusion g))
    (j : T.group ⟶ C.group) (hjc : IsClosedImmersion j.hom.hom.left)
    (hj : j ≫ C.inclusion = T.inclusion) (q : C.group ⟶ Q.val)
    (hk : IsSchemeKernel q (⟨T.group, j, hjc⟩ : ClosedSubgroup C.group))
    (ht : IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left)
    (S : ClosedSubgroup (GeometricGroup G).val) (hS : IsTorus S.group)
    (hTS : IsSubgroupOf (baseChangedSubgroup (AlgebraicClosure k) T ht) S)
    (hST : ¬ IsSubgroupOf S (baseChangedSubgroup (AlgebraicClosure k) T ht)) :
    ∃ D : ClosedSubgroup (GeometricGroup Q).val, IsTorus D.group ∧ ¬ IsTrivialSubgroup D := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨hc, hC'⟩ := centralizerSchemeBaseChange k K T.inclusion C hC
  let C' := baseChangedSubgroup K C hc
  let T' := baseChangedSubgroup K T ht
  have hC'' : RepresentsSubgroup C' (fun _ g ↦ Centralizes T'.inclusion g) := hC'
  obtain ⟨l, hl⟩ := factor_torus_through_centralizer hC''
    (torus_commutative (closedSubgroupAlgebraicGroup S) hS) hTS
  obtain ⟨D, p, hD, hp⟩ := image_of_geometric_torus
    (G := closedSubgroupAlgebraicGroup S) (Q := GeometricGroup Q) (l ≫ F.map q) hS
  refine ⟨D, hD, ?_⟩
  rintro ⟨e⟩
  have hp0 : p = 0 := (IsZero.of_iso (Grp.isZero_trivial _) e).eq_of_tgt p 0
  have hz : l ≫ F.map q = 0 := by rw [← hp, hp0, zero_comp]
  let hN := MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) j.hom.hom).flip hjc
  let N : ClosedSubgroup C'.group := ⟨_, F.map j, hN⟩
  have hker : IsSchemeKernel (F.map q) N := baseChangeKernelSquare q j hk
  have hz' : l.hom.hom ≫ (F.map q).hom.hom = 1 :=
    congrArg (fun f : S.group ⟶ (GeometricGroup Q).val ↦ f.hom.hom) hz
  obtain ⟨v, hv⟩ := (schemeKernel_sections hker l.hom.hom).mpr hz'
  letI : IsClosedImmersion N.inclusion.hom.hom.left := hN
  letI := isMonHom_of_comp_closed v l N.inclusion hv
  let f : S.group ⟶ T'.group := Grp.homMk v
  have hf : f ≫ F.map j = l := Grp.hom_ext _ _ hv
  have hcomp : F.map j ≫ C'.inclusion = T'.inclusion := by
    change F.map j ≫ F.map C.inclusion = F.map T.inclusion
    rw [← F.map_comp, hj]
  apply hST
  exact ⟨f, by rw [← hcomp, ← Category.assoc, hf, hl]⟩

private theorem torus_of_extension {G Q : AffineAlgebraicGroup k}
    {N : ClosedSubgroup G.val} (q : G.val ⟶ Q.val) (hk : IsSchemeKernel q N)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (hfp : LocallyOfFinitePresentation q.hom.hom.left)
    (hN : IsTorus N.group) (hQ : IsTorus Q.val) : IsTorus G.val := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let p := F.map q
  have pb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  let h := baseChangeClosedSubgroup k K N.inclusion N.isClosedImmersion
  let T := baseChangedSubgroup K N h
  have hp : IsFppfGroupQuotient (G := GeometricGroup G) (Q := GeometricGroup Q) T p :=
    represented_quotient_of_kernel (G := GeometricGroup G) (Q := GeometricGroup Q) p T
      (baseChangeKernelSquare q N.inclusion hk) (MorphismProperty.of_isPullback pb hflat)
      (MorphismProperty.of_isPullback pb hsurj) (MorphismProperty.of_isPullback pb hfp)
  exact torus_descends_from_algebraic_closure G
    (torus_of_torus_extension (G := GeometricGroup G) (Q := GeometricGroup Q) p hp
      (torus_after_algClosed_extension K (closedSubgroupAlgebraicGroup N) hN)
      (torus_after_algClosed_extension K Q hQ))

/-- A torus in the quotient pulls back to a torus containing the original torus.
Maximality then forces the quotient torus's inclusion to be zero. -/
private theorem rational_quotient_torus_trivial
    {G Q : AffineAlgebraicGroup k} (T C : ClosedSubgroup G.val) (hT : IsMaximalTorus T)
    (j : T.group ⟶ C.group) (hjc : IsClosedImmersion j.hom.hom.left)
    (hj : j ≫ C.inclusion = T.inclusion) (q : C.group ⟶ Q.val)
    (hq : IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup C) ⟨_, j, hjc⟩ q)
    (S : ClosedSubgroup Q.val) (hS : IsTorus S.group) : IsTrivialSubgroup S := by
  let P := pullback q S.inclusion
  let i : P ⟶ C.group := pullback.fst q S.inclusion
  let p : P ⟶ S.group := pullback.snd q S.inclusion
  have square : IsPullback i.hom.hom p.hom.hom q.hom.hom S.inclusion.hom.hom :=
    (IsPullback.of_hasPullback q S.inclusion).map (Grp.forget (SchemeOver k))
  have pb := square.map (Over.forget _)
  let R : ClosedSubgroup C.group :=
    ⟨P, i, MorphismProperty.of_isPullback pb.flip S.isClosedImmersion⟩
  let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup C) R
  let D := Specs.GeometricBorelConjugacy.subgroupOfSubgroup C R
  have hjq : j ≫ q = 0 := Grp.hom_ext _ _ hq.1.w
  let f : T.group ⟶ P := pullback.lift j (0 : T.group ⟶ S.group) (by
    simpa only [zero_comp] using hjq)
  have hfi : f ≫ i = j := pullback.lift_fst ..
  have hfp : f ≫ p = 0 := pullback.lift_snd ..
  let N : ClosedSubgroup A.val := ⟨_, f, factor_closed (H := ⟨T.group, j, hjc⟩) (N := R) hfi⟩
  have hker : IsSchemeKernel p N := by
    have hwhole : IsPullback (f.hom.hom ≫ i.hom.hom) (toUnit T.group.X)
        q.hom.hom (η[S.group.X] ≫ S.inclusion.hom.hom) := by
      rw [show f.hom.hom ≫ i.hom.hom = j.hom.hom from
        congrArg (fun a : T.group ⟶ C.group ↦ a.hom.hom) hfi, IsMonHom.one_hom]
      exact hq.1
    exact hwhole.of_right (congrArg (fun a : T.group ⟶ S.group ↦ a.hom.hom) hfp) square
  have hflat : Flat p.hom.hom.left := MorphismProperty.of_isPullback pb hq.2.1
  have hsurj : Surjective p.hom.hom.left := MorphismProperty.of_isPullback pb hq.2.2.1
  have hA : IsTorus A.val :=
    torus_of_extension (G := A) (Q := closedSubgroupAlgebraicGroup S) p hker hflat hsurj
      (MorphismProperty.of_isPullback pb hq.2.2.2.1) hT.1 hS
  have hTD : f ≫ D.inclusion = T.inclusion := by
    change f ≫ i ≫ C.inclusion = T.inclusion
    rw [← Category.assoc, hfi, hj]
  obtain ⟨r, hr⟩ := hT.2 D hA ⟨f, hTD⟩
  letI := inclusion_mono C
  have hri : r ≫ j = i := by
    apply (cancel_mono C.inclusion).mp
    rw [Category.assoc, hj]
    exact hr
  have hz : p ≫ S.inclusion = 0 := by
    calc
      p ≫ S.inclusion = i ≫ q := (pullback.condition (f := q) (g := S.inclusion)).symm
      _ = 0 := by rw [← hri, Category.assoc, hjq, comp_zero]
  letI := hflat
  letI := hsurj
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
  haveI : Epi p := F.epi_of_epi_map (f := p) (Flat.epi_of_flat_of_surjective p.hom.hom.left)
  have hs0 : S.inclusion = 0 := (cancel_epi p).mp (by simpa only [comp_zero] using hz)
  letI := inclusion_mono S
  exact ⟨(IsZero.of_mono_eq_zero S.inclusion hs0).iso (Grp.isZero_trivial _)⟩

private theorem infinite_field [Infinite k]
    (nontrivial : Specs.NontrivialRationalTorus.ExistsNontrivialTorus.{u})
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧
      ∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h) := by
  classical
  letI := hs
  letI := hc
  obtain ⟨T, hT⟩ := rational_maximal_exists G
  let K := AlgebraicClosure k
  let ht := MorphismProperty.of_isPullback
    (baseChangeMapPullback (K := K) T.inclusion.hom.hom).flip T.isClosedImmersion
  refine ⟨T, hT.1, ht, torus_after_algClosed_extension K (closedSubgroupAlgebraicGroup T) hT.1, ?_⟩
  intro S hS hTS
  by_contra hST
  obtain ⟨C, hC, hsC, hgC⟩ := CocharacterDynamics.connectedTorusCentralizer G T hT.1
  obtain ⟨j, hjc, hj, hn⟩ := torus_in_centralizer (G := G)
    (torus_commutative (closedSubgroupAlgebraicGroup T) hT.1) hC
  let A := closedSubgroupAlgebraicGroup C
  let N : ClosedSubgroup C.group := ⟨T.group, j, hjc⟩
  obtain ⟨_, _, Q, q, _, _, hk, hf, _, hquot⟩ := normalAffineQuotient A N hn
  have hq : IsFppfGroupQuotient (G := A) (Q := Q) N q :=
    ⟨hk, hf.2.1, hf.2.2.1, hf.2.2.2.1, hquot⟩
  letI := hgC
  have hcC : ConnectedSpace C.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C.group.X.hom)
  obtain ⟨hsQ, hcQ⟩ := quotient_smooth_connected (G := A) (Q := Q) q hq.2.1 hq.2.2.1 hsC hcC
  obtain ⟨D, hD, hDnt⟩ := nontrivial k Q hsQ hcQ
    (geometric_quotient_torus (G := G) (Q := Q) T C hC j hjc hj q hk ht S hS hTS hST)
  exact hDnt (rational_quotient_torus_trivial (G := G) (Q := Q) T C hT j hjc hj q hq D hD)

/-- The nontrivial rational torus theorem promotes rational maximality to
geometric maximality over infinite fields. Over finite fields use Lang descent. -/
theorem geometricallyMaximalTorusExists_conditional
    (nontrivial : Specs.NontrivialRationalTorus.ExistsNontrivialTorus.{u}) :
    Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u} := by
  classical
  intro k _ G hs hc
  rcases finite_or_infinite k with hfinite | hinfinite
  · letI := hfinite
    letI : Fintype k := Fintype.ofFinite k
    exact Descent.FiniteFieldFlags.geometricallyMaximalTorusExists G hs hc
  · letI := hinfinite
    exact infinite_field nontrivial G hs hc

end

end LinearAlgebraicGroups.MaximalToriExist

universe v8_closure_52a0603143ed6162_u0
theorem _root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists» : _root_.«LinearAlgebraicGroups».«Specs».«MaximalToriExist».«GeometricallyMaximalTorusExists».{v8_closure_52a0603143ed6162_u0} :=
  @_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists_conditional».{v8_closure_52a0603143ed6162_u0} (@_root_.«LinearAlgebraicGroups».«NontrivialRationalTorus».«existsNontrivialTorus».{v8_closure_52a0603143ed6162_u0})
