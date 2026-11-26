import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RankOneDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TypeAOneLattices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.RankOneDescent

open _root_.LinearAlgebraicGroups.Specs Specs.RankOneDescent
open Specs.AbstractPairing (IsAttachedCoroot Root)
open Specs.BorelsAndChambers (IsPositiveSystem subgroupRoots)
open Specs.CentralIsogenies (characterPullback)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (pairing powerMorphism)
open Specs.DiagonalizableGroups (rootsOfUnityPoints)
open Specs.GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open Specs.GeneralLinearCentralIsogeny (pointMap)
open Specs.InducedNonvanishing (Dominant)
open Specs.RootWeightAction (Representation SimpleRoot act actLinear extendVector mem_weightSpace
  weightSpace)
open Specs.SimpleClassification (SocleModel)
open Specs.SpecialLinearDatum (RootIndices)
open Specs.StandardGroups (multiplicativePoints)
open Specs.TypeAOneLattices (ScalarQuotient firstIndex)
open Specs.Unipotent (Index)

noncomputable section

set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private sourceMark ratioMark gm_ratio_maps dual_generators sourceMark_matrix marked_pairing
  marked_character_value signedRootIndex signedRoot_character signedRoot_coroot power_one power_comp
  gm_forward_coordinate
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TypeAOneLattices
open private quotientRepresentsImage fppfYoneda_locallySurjective schemeKernel_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private quotient_desc from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private generates_of_simple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private torusPoint_weights charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private weightProjection sum_projections projection_mem
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition

variable {k : Type u} [Field k] {G S P M : AffineAlgebraicGroup k}
variable {g : MatrixPoints G 2} {s : SpecialMatrixPoints S 2}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

private theorem descends_iff_trivial_kernel {I : Type u} [Fintype I] [DecidableEq I]
    (f : S.val ⟶ P.val) (hf : Specs.CentralIsogenies.IsCentralIsogeny f)
    {N : ClosedSubgroup S.val} (hN : IsSchemeKernel f N) (ρ : Representation S.val I) :
    Descends f ρ ↔
      ∀ (R : TestAlgebra k) (x : Points N.group.X R),
        ρ.app R (pointMap N.inclusion R x) = 1 := by
  constructor
  · rintro ⟨σ, rfl⟩ R x
    have hx := (schemeKernel_sections hN (pointMap N.inclusion R x)).mp ⟨x, rfl⟩
    change σ.app R (pointMap N.inclusion R x ≫ f.hom.hom) = 1
    rw [hx]
    exact map_one (σ.app R).hom
  · intro hρ
    let L := LinearAlgebraicGroups.StandardGroups.generalLinearGroup k I
    let e := LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso k I
    obtain ⟨φ, hφ⟩ := (groupHomComparison k S.val L.val S.property.1).2 (ρ ≫ e.inv)
    change (groupPointsFunctor k).map φ = ρ ≫ e.inv at hφ
    have hφ' : (groupPointsFunctor k).map φ ≫ e.hom = ρ := by
      rw [hφ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have htriv : ∀ (R : TestAlgebra k) (x : Points N.group.X R),
        pointMap (N.inclusion ≫ φ) R x = 1 := by
      intro R x
      apply (e.app R).groupIsoToMulEquiv.injective
      have he := congrArg (fun ν : Representation S.val I => ν.app R (pointMap N.inclusion R x)) hφ'
      change e.hom.app R ((pointMap N.inclusion R x) ≫ φ.hom.hom) =
        ρ.app R (pointMap N.inclusion R x) at he
      rw [map_one, hρ R x] at *
      exact he
    have hNaff : IsAffine N.group.X.left :=
      (Specs.Unipotent.closedSubgroupAlgebraicGroup N).property.1
    have hφN : (N.inclusion ≫ φ).hom.hom = 1 := by
      apply hom_ext_of_points hNaff
      intro R x
      exact (htriv R x).trans (MonObj.comp_one x).symm
    obtain ⟨H, q, i, hq, _, _⟩ := schemeImageFactorization S P f
    obtain ⟨j, hj, _⟩ := schemeImageUniqueness S P f q i f (𝟙 P.val)
      hq.1 (Category.comp_id _) hq.2.1 hq.2.2.1 hq.2.2.2.2.2
      hf.2.1 hf.2.2.1 (by change IsClosedImmersion (𝟙 P.val.X.left); infer_instance)
    letI := hq.2.1
    letI := hq.2.2.1
    letI := hq.2.2.2.1
    obtain ⟨ψ, hψ, _⟩ := quotient_desc H N q (quotientRepresentsImage hq hN)
      (fppfYoneda_locallySurjective q.hom.hom) φ (by
        rintro T _ ⟨x, rfl⟩
        change (x ≫ N.inclusion.hom.hom) ≫ φ.hom.hom = 1
        rw [Category.assoc, ← Grp.comp_hom_hom, hφN, MonObj.comp_one])
    refine ⟨(groupPointsFunctor k).map (j.inv ≫ ψ) ≫ e.hom, ?_⟩
    rw [← Category.assoc, ← (groupPointsFunctor k).map_comp, ← hj.1,
      Category.assoc, j.hom_inv_id_assoc, hψ, hφ']

private theorem square_root_inv {R : Type*} [CommRing R] (z : rootsOfUnity 2 R) :
    (z.val : Rˣ)⁻¹ = z.val := by
  have hz := (mem_rootsOfUnity 2 z.val).mp z.property
  rw [pow_two] at hz
  exact inv_eq_of_mul_eq_one_right hz

private theorem square_root_even {R : Type*} [CommRing R] (z : rootsOfUnity 2 R)
    {m : ℤ} (hm : Even m) : z.val ^ m = 1 := by
  obtain ⟨j, hj⟩ := hm
  have hz := (mem_rootsOfUnity 2 z.val).mp z.property
  rw [show m = (2 : ℤ) * j by omega, zpow_mul, show z.val ^ (2 : ℤ) = 1 from hz, one_zpow]

private theorem square_root_odd {R : Type*} [CommRing R] (z : rootsOfUnity 2 R)
    {m : ℤ} (hm : Odd m) : z.val ^ m = z.val := by
  obtain ⟨j, rfl⟩ := hm
  rw [zpow_add, square_root_even z (by exact ⟨j, by omega⟩), zpow_one, one_mul]

private theorem square_root_generator_ne_one :
    squareRootGenerator.{u} k ≠ 1 := by
  intro h
  classical
  let i : ULift.{u} (Multiplicative (ZMod 2)) := ⟨Multiplicative.ofAdd 1⟩
  have hi : i ≠ 1 := by
    intro he
    have : (1 : ZMod 2) = 0 := congrArg (fun j => Multiplicative.toAdd j.down) he
    exact one_ne_zero this
  have h' := congrArg (MonoidAlgebra.coeff · i) h
  change MonoidAlgebra.coeff (MonoidAlgebra.single i (1 : k)) i =
    MonoidAlgebra.coeff (1 : MonoidAlgebra k _) i at h'
  rw [MonoidAlgebra.one_def] at h'
  simp [MonoidAlgebra.coeff_single, hi] at h'

private theorem square_root_geometric_points
    {N : ClosedSubgroup S.val}
    (r : (groupPointsFunctor k).obj N.group ≅ rootsOfUnityPoints k 2)
    [CharP k 2] :
    Subsingleton (Points N.group.X (CommAlgCat.of k (AlgebraicClosure k))) := by
  let K := AlgebraicClosure k
  letI : CharP K 2 := charP_of_injective_algebraMap (algebraMap k K).injective 2
  let R := CommAlgCat.of k K
  have h (z : rootsOfUnity 2 K) : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    have hz := (mem_rootsOfUnity' 2 z.val).mp z.property
    change (z.val : K) = 1
    have ht : ((z.val : K) - 1) ^ 2 = 0 := by
      rw [sub_pow_char (R := K) (p := 2) _ _, hz, one_pow, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero ht)
  exact ⟨fun x y => (r.app R).groupIsoToMulEquiv.injective ((h (r.hom.app R x)).trans
    (h (r.hom.app R y)).symm)⟩

private theorem matrix_borels (s : SpecialMatrixPoints S 2) :
    ∃ (B : MatrixBorels s) (Upos : ClosedSubgroup B.pair.positive.group),
      Nonempty (Specs.Pinning.AttachedDatum B.upper.pair) ∧
      Specs.GeometricRadicals.IsUnipotentRadical
        (Specs.Unipotent.closedSubgroupAlgebraicGroup B.pair.positive) Upos := by
  obtain ⟨T, L, W, B, D, _, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k 1 S s
  obtain ⟨comm, _, _, hBC, _, _, hRad⟩ :=
    RootData.BorelPositivity.borelPositivity S B.reductive T.subgroup T.split B.maximal
  letI := comm
  obtain ⟨f, hf, hb⟩ := hBC.1 B.limits.parabolic B.isBorel B.containsTorus
  have hneg : IsPositiveSystem T.subgroup (subgroupRoots T.subgroup B.limits.parabolic)ᶜ := by
    refine ⟨-f, fun α h => hf α (neg_eq_zero.mp h), ?_⟩
    ext α
    change α ∉ subgroupRoots T.subgroup B.limits.parabolic ↔ 0 < -f (Additive.ofMul α.val)
    rw [hb]
    change ¬ 0 < f (Additive.ofMul α.val) ↔ 0 < -f (Additive.ofMul α.val)
    rw [neg_pos]
    exact ⟨fun h => lt_of_le_of_ne (not_lt.mp h) (hf α), fun h => not_lt.mpr h.le⟩
  obtain ⟨Bneg, hBn, hTn, hn⟩ := hBC.2.1 _ hneg
  obtain ⟨Upos, _, _, hR, _⟩ := hRad B.limits.parabolic B.isBorel B.containsTorus
  exact ⟨⟨T, L, W, B, Bneg, hBn, hTn, hn⟩, Upos, ⟨D⟩, hR⟩

private theorem positive_root (B : MatrixBorels s) :
    let α := B.roots.indices (signedRootIndex 1)
    subgroupRoots B.pair.torus B.pair.positive = {α} ∧
      α.val = (sourceMark B.diagonal).inv ≫ powerMorphism 2 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · ext α
    obtain ⟨p, rfl⟩ := B.roots.indices.surjective α
    change B.roots.indices p ∈ subgroupRoots B.diagonal.subgroup B.upper.limits.parabolic ↔ _
    rw [B.upper.positive_iff, Set.mem_singleton_iff, B.roots.indices.injective.eq_iff]
    constructor
    · intro hp
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change p.val.1.val = 0
        have := p.val.2.isLt
        omega
      · change p.val.2.val = 1
        have := p.val.2.isLt
        omega
    · rintro rfl
      decide
  · simpa using signedRoot_character B.roots 1 (Or.inl rfl)

private theorem dominance_rank_one (B : MatrixBorels s)
    (D : Specs.Pinning.AttachedDatum B.upper.pair) (m : ℤ) :
    Dominant B.pair ((sourceMark B.diagonal).inv ≫ powerMorphism m) ↔ 0 ≤ m := by
  let e := sourceMark B.diagonal
  let α := B.roots.indices (signedRootIndex 1)
  have hα := positive_root B
  have hc : IsAttachedCoroot B.pair.torus α e.hom := by
    have hc' := signedRoot_coroot (B := B.upper) D 1 (Or.inl rfl)
    rwa [power_one, Category.id_comp] at hc'
  have hsimple : α ∈ subgroupRoots B.pair.torus B.pair.positive := by simp [hα.1, α]
  let root : SimpleRoot B.pair.torus B.pair.positive := ⟨α, hsimple, by
    intro beta hβ gamma hγ he
    have hb : beta = α := by simpa [hα.1, α] using hβ
    have hg : gamma = α := by simpa [hα.1, α] using hγ
    rw [hb, hg] at he
    have hn : α.val = 1 := (mul_left_cancel (he.symm.trans (mul_one α.val).symm))
    exact α.property.1 hn⟩
  have he (j n : ℤ) :
      pairing B.pair.torus.group (e.inv ≫ powerMorphism j) (powerMorphism n ≫ e.hom) = n * j :=
    marked_pairing e j n
  have hm : pairing B.pair.torus.group (e.inv ≫ powerMorphism m) e.hom = m := by
    simpa only [power_one, Category.id_comp, one_mul] using he m 1
  constructor
  · intro h
    exact hm ▸ h root e.hom hc
  · intro h β c hβ
    have hβα : β.val = α := by simpa [hα.1, α] using β.property.1
    have hpair : pairing B.pair.torus.group α.val c = 2 := by
      rw [← hβα]
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r, hr⟩ := hβ
      rw [← hr]
      exact r.root_pairing
    obtain ⟨j, hj, _⟩ := (dual_generators e).2.2 c
    rw [hj, hα.2, he] at hpair
    have hj' : j = 1 := by omega
    change 0 ≤ pairing B.pair.torus.group (e.inv ≫ powerMorphism m) c
    simpa only [hj, he, hj', one_mul] using h

private theorem kernel_point_on_diagonal (B : MatrixBorels s)
    {N : ClosedSubgroup S.val}
    (r : (groupPointsFunctor k).obj N.group ≅ rootsOfUnityPoints k 2)
    (hs : ∀ (R : TestAlgebra k) (x : Points N.group.X R),
      Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
        Matrix.GeneralLinearGroup.scalar (Index.{u} 2) (r.hom.app R x).val)
    (R : TestAlgebra k) (x : Points N.group.X R) :
    pointMap N.inclusion R x = pointMap B.pair.torus.inclusion R
      (CocharacterDynamics.cocharacterPoint (sourceMark B.diagonal).hom R (r.hom.app R x).val) := by
  let z : rootsOfUnity 2 R := r.hom.app R x
  apply (s.app R).groupIsoToMulEquiv.injective
  apply Subtype.ext
  have hl := congrArg Units.val (hs R x)
  change (s.hom.app R (pointMap N.inclusion R x)).val = Matrix.scalar (Index.{u} 2) (z.val : R) at hl
  change (s.hom.app R (pointMap N.inclusion R x)).val =
    (s.hom.app R (pointMap B.diagonal.subgroup.inclusion R
      (CocharacterDynamics.cocharacterPoint (sourceMark B.diagonal).hom R z.val))).val
  rw [hl, sourceMark_matrix, square_root_inv z]
  simp [Matrix.scalar]

private theorem weight_parity (B : MatrixBorels s)
    (D : Specs.Pinning.AttachedDatum B.upper.pair)
    {Upos : ClosedSubgroup B.pair.positive.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical
      (Specs.Unipotent.closedSubgroupAlgebraicGroup B.pair.positive) Upos)
    (m : ℤ) (L : SocleModel B.pair Upos ((sourceMark B.diagonal).inv ≫ powerMorphism m)) :
    ∀ j : ℤ, weightSpace L.socleAction B.pair.torus
        ((sourceMark B.diagonal).inv ≫ powerMorphism j) ≠ ⊥ → Even (m - j) := by
  classical
  let e := sourceMark B.diagonal
  let α := B.roots.indices (signedRootIndex 1)
  let χ : ℤ → Character B.pair.torus.group := fun n => e.inv ≫ powerMorphism n
  let v := L.socleBasis.equivFun L.highestVector
  have hC := CyclicHighestWeight.cyclicHighestWeight.{u}
  have hcy := generates_of_simple hC.1 L.socleAction L.A (pointIso L.groupIso)
    L.simple L.primitive.1
  obtain ⟨comm, _, hhighest⟩ := hC.2 S B.pair.reductive B.pair.torus B.pair.positive
    B.pair.split B.pair.maximal B.pair.positiveBorel B.pair.inPositive
  let _ := comm
  obtain ⟨_, hlower, _⟩ := (hhighest Upos hU L.socleAction (χ m) v L.primitive).2 hcy
  letI : IsCommMonObj B.upper.pair.T.group.X := D.comm
  let F : Additive (Character B.pair.torus.group) →ₗ[ℤ] ℤ :=
    D.datum.rootDatum.toLinearMap.flip (Additive.ofMul e.hom)
  have hF (n : ℤ) : F (Additive.ofMul (χ n)) = n := by
    change D.datum.rootDatum.toLinearMap (Additive.ofMul (χ n)) (Additive.ofMul e.hom) = n
    rw [D.datum.pairing_eq]
    simpa only [power_one, Category.id_comp, one_mul] using marked_pairing e n 1
  intro j hj
  by_cases he : χ j = χ m
  · have : j = m := by rw [← hF j, ← hF m, he]
    subst j
    simp
  · obtain ⟨c, hc⟩ := hlower (χ j) he hj
    have h := congrArg F hc
    change F (Additive.ofMul (χ m) - Additive.ofMul (χ j)) = _ at h
    rw [map_sub, hF, hF, Finsupp.sum, map_sum] at h
    have hterm (β : SimpleRoot B.pair.torus B.pair.positive) :
        F (c β • Additive.ofMul β.val.val) = 2 * (c β : ℤ) := by
      have hβα : β.val = α := by simpa [(positive_root B).1, α] using β.property.1
      rw [map_nsmul, hβα, (positive_root B).2, hF]
      simp [mul_comm]
    simp only [hterm, ← Finset.mul_sum] at h
    exact ⟨∑ β ∈ c.support, (c β : ℤ), h.trans (two_mul _)⟩

private theorem kernel_scalar_action (B : MatrixBorels s)
    {N : ClosedSubgroup S.val}
    (r : (groupPointsFunctor k).obj N.group ≅ rootsOfUnityPoints k 2)
    (hs : ∀ (R : TestAlgebra k) (x : Points N.group.X R),
      Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
        Matrix.GeneralLinearGroup.scalar (Index.{u} 2) (r.hom.app R x).val)
    {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation S.val I)
    (m : ℤ) (hp : ∀ j : ℤ, weightSpace ρ B.pair.torus
      ((sourceMark B.diagonal).inv ≫ powerMorphism j) ≠ ⊥ → Even (m - j))
    (R : TestAlgebra k) (x : Points N.group.X R) (v : I → R) :
    act ρ R (pointMap N.inclusion R x) v = (↑((r.hom.app R x).val ^ m) : R) • v := by
  classical
  let z : rootsOfUnity 2 R := r.hom.app R x
  let e := sourceMark B.diagonal
  let d : R := ↑(z.val ^ m)
  have weight_action (χ : Character B.pair.torus.group) (w : I → k)
      (hw : w ∈ weightSpace ρ B.pair.torus χ) :
      act ρ R (pointMap N.inclusion R x) (extendVector R w) = d • extendVector R w := by
    by_cases hz : w = 0
    · subst w
      have hzero : extendVector R (0 : I → k) = 0 := by
        exact (Specs.RootWeightAction.extendLinear (I := I) R).map_zero
      rw [hzero]
      simp [act]
    obtain ⟨j, rfl, _⟩ := (dual_generators e).2.1 χ
    have hn : weightSpace ρ B.pair.torus (e.inv ≫ powerMorphism j) ≠ ⊥ := by
      intro h
      exact hz ((Submodule.mem_bot k).mp (h ▸ hw))
    have he := square_root_even z (hp j hn)
    have hpow : z.val ^ j = z.val ^ m := by
      conv_rhs => rw [show m = (m - j) + j by omega, zpow_add, he, one_mul]
    rw [kernel_point_on_diagonal B r hs R x]
    change act ρ R (_ ≫ B.pair.torus.inclusion.hom.hom) _ = _
    rw [mem_weightSpace.mp hw, marked_character_value, hpow]
  obtain ⟨n, ⟨iT⟩⟩ := B.pair.split
  obtain ⟨iA⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
  let i := iA ≪≫ iT.symm
  letI : DecidableEq (StandardLattice.{u} n) := Classical.decEq _
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) n
  obtain ⟨c, hc⟩ := torusPoint_weights ρ i χ hχ
  have hbase (w : I → k) :
      act ρ R (pointMap N.inclusion R x) (extendVector R w) = d • extendVector R w := by
    obtain ⟨t, ht⟩ := sum_projections c w
    let ext := Specs.RootWeightAction.extendLinear (I := I) R
    let op := actLinear ρ R (pointMap N.inclusion R x)
    change op (ext w) = d • ext w
    rw [← ht, map_sum, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact weight_action ((charactersOfIso i) (χ b)) _ ((hc b).symm ▸ projection_mem c b w)
  have hop : actLinear ρ R (pointMap N.inclusion R x) = d • LinearMap.id := by
    apply (Pi.basisFun R I).ext
    intro j
    have he : extendVector R (Pi.single j (1 : k)) = Pi.single j (1 : R) := by
      funext l
      by_cases h : l = j <;> simp [extendVector, h]
    change act ρ R (pointMap N.inclusion R x) ((Pi.basisFun R I) j) =
      d • ((Pi.basisFun R I) j)
    rw [Pi.basisFun_apply, ← he]
    exact hbase (Pi.single j (1 : k))
  exact DFunLike.congr_fun hop v

private theorem universal_kernel_point {N : ClosedSubgroup S.val}
    (e : N.group ≅ specGroup (Specs.SmoothnessAndIsogenies.rootsOfUnityCoordinates k 2))
    (r₀ : (groupPointsFunctor k).obj
        (specGroup (Specs.SmoothnessAndIsogenies.rootsOfUnityCoordinates k 2)) ≅ rootsOfUnityPoints k 2)
    (hc : ∀ (R : TestAlgebra k)
        (φ : MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod 2))) →ₐ[k] R)
        (x : Points (specGroup (Specs.SmoothnessAndIsogenies.rootsOfUnityCoordinates k 2)).X R),
        x.left = Spec.map (CommRingCat.ofHom φ.toRingHom) →
        ((r₀.hom.app R x).val : R) = φ (squareRootGenerator k)) :
    let A := MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod 2)))
    let R := CommAlgCat.of k A
    let r := (groupPointsFunctor k).mapIso e ≪≫ r₀
    ∃ x : Points N.group.X R,
      (pointMap e.hom R x).left = 𝟙 _ ∧
      ((r.hom.app R x).val : A) = squareRootGenerator k ∧
      ∀ m : ℤ, Odd m → (((r.hom.app R x).val ^ m : Aˣ) : A) ≠ 1 := by
  dsimp only
  let A := MonoidAlgebra k (ULift.{u} (Multiplicative (ZMod 2)))
  let R := CommAlgCat.of k A
  let r := (groupPointsFunctor k).mapIso e ≪≫ r₀
  let t : Points (specGroup (Specs.SmoothnessAndIsogenies.rootsOfUnityCoordinates k 2)).X R :=
    𝟙 _
  let x : Points N.group.X R := pointMap e.inv R t
  have hx : pointMap e.hom R x = t :=
    (((groupPointsFunctor k).mapIso e).app R).groupIsoToMulEquiv.apply_symm_apply t
  have hcoord : ((r.hom.app R x).val : A) = squareRootGenerator k := by
    change ((r₀.hom.app R (pointMap e.hom R x)).val : A) = _
    rw [hx]
    exact hc R (AlgHom.id k A) t (by
      change 𝟙 _ = Spec.map (𝟙 (CommRingCat.of A))
      exact (Spec.map_id _).symm)
  refine ⟨x, congrArg Over.Hom.left hx, hcoord, fun m hm => ?_⟩
  change (((r.hom.app R x).val ^ m : Aˣ) : A) ≠ 1
  rw [square_root_odd _ hm, hcoord]
  exact square_root_generator_ne_one

private theorem even_descent (Q : ScalarQuotient g s a)
    (hf : Specs.CentralIsogenies.IsCentralIsogeny Q.map)
    {N : ClosedSubgroup S.val} (hN : IsSchemeKernel Q.map N)
    (r : (groupPointsFunctor k).obj N.group ≅ rootsOfUnityPoints k 2)
    {I : Type u} [Fintype I] [DecidableEq I] (ρ : Representation S.val I) (m : ℤ)
    (hI : Nonempty I)
    (hscalar : ∀ (R : TestAlgebra k) (x : Points N.group.X R) (v : I → R),
      act ρ R (pointMap N.inclusion R x) v = (↑((r.hom.app R x).val ^ m) : R) • v)
    (hodd : ∃ (R : TestAlgebra k) (x : Points N.group.X R),
      Odd m → (((r.hom.app R x).val ^ m : Rˣ) : R) ≠ 1) :
    Descends Q.map ρ ↔ Even m := by
  rw [descends_iff_trivial_kernel Q.map hf hN ρ]
  constructor
  · intro h
    by_contra hm
    obtain ⟨R, x, hx⟩ := hodd
    obtain ⟨i⟩ := hI
    have he := congrFun (hscalar R x (Pi.single i 1)) i
    simp [act, h R x] at he
    exact hx (Int.not_even_iff_odd.mp hm) he.symm
  · intro hm R x
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    have he := hscalar R x (Pi.single i 1)
    rw [square_root_even _ hm] at he
    change (ρ.app R (pointMap N.inclusion R x)).val.mulVec (Pi.single i 1) =
      ((1 : Rˣ) : R) • Pi.single i 1 at he
    change (ρ.app R (pointMap N.inclusion R x)).val.mulVec (Pi.single i 1) =
      (1 : Matrix I I R).mulVec (Pi.single i 1)
    rw [Matrix.one_mulVec]
    simpa only [Units.val_one, one_smul] using he

/-- The highest weight simple SL₂-module descends through the scalar quotient
if and only if its integer highest weight is even. -/
theorem rankOneDescent : Statement.{u} := by
  intro k _ G S M g s a
  obtain ⟨Q, hf, hkernel, _⟩ := Classification.TypeAOneLattices.matrixProjectiveIsogeny
    k 2 (by decide) G S M g s a
  obtain ⟨U⟩ := Classification.TypeAOneLattices.projectiveRatioTorus k G S M g s a Q
  obtain ⟨B, Upos, ⟨D⟩, hU⟩ := matrix_borels s
  obtain ⟨p, hp, _, hppt⟩ := Classification.TypeAOneLattices.rankOneTorusRestriction
    k G S M g s a Q U B.diagonal
  obtain ⟨N, eN, r₀, hN, _, hZ, hc, hs, _⟩ := hkernel
  let r := (groupPointsFunctor k).mapIso eN ≪≫ r₀
  let eS := sourceMark B.diagonal
  let eP := ratioMark Q U
  have hmarks := gm_ratio_maps Q U B.diagonal hppt
  have hgeneric := universal_kernel_point eN r₀ hc
  refine ⟨Q, B, U, Upos, eS, eP, p, N, eN, r, hf, hp, hU,
    dual_generators eS, dual_generators eP, sourceMark_matrix B.diagonal, ?_, ?_,
    ?_, hN, hZ, hs, hgeneric, square_root_geometric_points r, ?_⟩
  · intro R t
    exact gm_forward_coordinate (X := Specs.Unipotent.closedSubgroupAlgebraicGroup U.subgroup)
      ((groupPointsFunctor k).mapIso U.coordinate ≪≫ a) R t
  · intro j
    change p ≫ (eP.inv ≫ powerMorphism j) = _
    rw [← Category.assoc, hmarks, Category.assoc, power_comp]
  · refine ⟨B.roots.indices (signedRootIndex 1), (positive_root B).1, (positive_root B).2, ?_⟩
    have hc' := signedRoot_coroot (B := B.upper) D 1 (Or.inl rfl)
    rwa [power_one, Category.id_comp] at hc'
  · intro m
    have hd := dominance_rank_one B D m
    refine ⟨hd, ?_, ?_⟩
    · intro hm
      obtain ⟨L, _⟩ := (SimpleClassification.classification S B.pair Upos hU).2.2 _ (hd.mpr hm)
      exact ⟨L⟩
    · intro L
      have hpar := weight_parity B D hU m L
      have hscalar := kernel_scalar_action B r hs L.socleAction m hpar
      refine ⟨hpar, hscalar, even_descent Q hf hN r L.socleAction m ?_ hscalar ?_⟩
      · by_contra h
        haveI : IsEmpty L.J := not_nonempty_iff.mp h
        exact L.primitive.1 (funext fun j => isEmptyElim j)
      · obtain ⟨x, _, _, hx⟩ := hgeneric
        exact ⟨_, x, hx m⟩

/-- Specialize the result to the determinant-localization and determinant-one
coordinate models, with the usual multiplicative group for the scalars. -/
theorem rankOneDescentOverEveryField : OverEveryField.{u} := by
  intro k _
  let G := LinearAlgebraicGroups.StandardGroups.generalLinearGroup k (Index.{u} 2)
  let S := LinearAlgebraicGroups.StandardGroups.specialLinearGroup k (Index.{u} 2)
  let M := LinearAlgebraicGroups.StandardGroups.multiplicativeGroup k
  let g := LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso k (Index.{u} 2)
  let s := LinearAlgebraicGroups.StandardGroups.specialLinearGroupPointsIso k (Index.{u} 2)
  let a := LinearAlgebraicGroups.StandardGroups.multiplicativeGroupPointsIso k
  exact ⟨G, S, M, g, s, a, rankOneDescent k G S M g s a⟩

end
end LinearAlgebraicGroups.Representation.RankOneDescent
