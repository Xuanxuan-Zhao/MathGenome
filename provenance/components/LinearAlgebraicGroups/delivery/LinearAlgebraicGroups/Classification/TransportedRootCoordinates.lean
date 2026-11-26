import Specs.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
import LinearAlgebraicGroups.Classification.NormalizerComparison
import LinearAlgebraicGroups.RootData.RankOneFlag
import LinearAlgebraicGroups.RootData.SimpleRoots
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.TransportedRootCoordinates

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open CellHomomorphism (pullbackCharacters)
open Pinning (AttachedDatum PinnedGroup)
open RankTwoLifting (Compatible)
open RootGroups (AdditiveLine)
open Specs.TransportedRootCoordinates

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {A : AdditiveLine k}
    {P Q : PinnedGroup A} {D : AttachedDatum P.pair} {E : AttachedDatum Q.pair}
    {d : Root P.pair.T ≃ Root Q.pair.T} {τ : P.pair.T.group ⟶ Q.pair.T.group}

/-- The normalizer comparison premise supplies the scheme data for transport. -/
theorem normalizersOfComparison (comparison : Specs.NormalizerComparison.Statement.{u})
    (h : Compatible P Q D E d τ) : Nonempty (Normalizers P Q D E d τ) := by
  obtain ⟨N, M, j, l, f, hN, hM, hj, hl, ht, n, m, hn⟩ :=
    comparison P Q D E d τ h
  exact ⟨⟨N, M, j, l, f, hN, hM, hj, hl, ht, n, m, hn⟩⟩

/-- The compatible root bijection carries the saturated two-root span onto
the corresponding saturated span in the target character lattice. -/
theorem inSaturatedSpan_iff (h : Compatible P Q D E d τ) (a b r : Root P.pair.T) :
    InSaturatedSpan a.val b.val r.val ↔
      InSaturatedSpan (d a).val (d b).val (d r).val := by
  have hr (α : Root P.pair.T) : pullbackCharacters τ (d α).val = α.val := h.root α
  constructor
  · rintro ⟨m, i, j, hm, hij⟩
    refine ⟨m, i, j, hm, h.injective ?_⟩
    simpa only [map_mul, map_zpow, hr] using hij
  · rintro ⟨m, i, j, hm, hij⟩
    refine ⟨m, i, j, hm, ?_⟩
    simpa only [map_mul, map_zpow, hr] using congrArg (pullbackCharacters τ) hij

/-- Opposite roots are preserved by the compatible root bijection. -/
theorem map_opposite (h : Compatible P Q D E d τ) {a b : Root P.pair.T}
    (hab : b.val = a.val⁻¹) : (d b).val = (d a).val⁻¹ := by
  apply h.injective
  rw [map_inv]
  exact (h.root b).trans (hab.trans (congrArg Inv.inv (h.root a)).symm)

/-- The subsystem root bijection is the restriction of the global root bijection. -/
theorem exists_subsystem_root_equiv (h : Compatible P Q D E d τ)
    {a b : Root P.pair.T} (S : Subsystem P D a b) (T : Subsystem Q E (d a) (d b)) :
    ∃ δ : Root S.localGroup.pair.T ≃ Root T.localGroup.pair.T,
      ∀ r, T.roots (δ r) = d (S.roots r) := by
  classical
  have existsTarget (r : Root S.localGroup.pair.T) :
      ∃ s : Root T.localGroup.pair.T, T.roots s = d (S.roots r) := by
    have hsource : S.roots r ∈ Set.range S.roots := Set.mem_range_self r
    rw [S.root_range] at hsource
    have hs : d (S.roots r) ∈ Set.range T.roots := by
      rw [T.root_range]
      exact (inSaturatedSpan_iff h a b (S.roots r)).mp hsource
    exact hs
  let δ (r : Root S.localGroup.pair.T) := (existsTarget r).choose
  have hδ (r : Root S.localGroup.pair.T) : T.roots (δ r) = d (S.roots r) :=
    (existsTarget r).choose_spec
  have hinj : Function.Injective δ := by
    intro r s hrs
    exact S.roots.injective (d.injective ((hδ r).symm.trans
      ((congrArg T.roots hrs).trans (hδ s))))
  have hsurj : Function.Surjective δ := by
    intro s
    have ht : T.roots s ∈ Set.range T.roots := Set.mem_range_self s
    rw [T.root_range] at ht
    change InSaturatedSpan (d a).val (d b).val (T.roots s).val at ht
    have hs : d.symm (T.roots s) ∈ Set.range S.roots := by
      rw [S.root_range]
      apply (inSaturatedSpan_iff h a b (d.symm (T.roots s))).mpr
      simpa only [Equiv.apply_symm_apply] using ht
    obtain ⟨r, hr⟩ := hs
    refine ⟨r, T.roots.injective ?_⟩
    rw [hδ, hr, Equiv.apply_symm_apply]
  exact ⟨Equiv.ofBijective δ ⟨hinj, hsurj⟩, hδ⟩

section CommonKernel

open CharacterDescent (Character StandardLattice)
open DiagonalizableGroups (groupAlgebra groupAlgebraMap diagonalClosedInclusion)
open Specs.GeometricRadicals (IsSplitTorus IsTorus)
open Module Submodule

open private splitPresentation latticeCoordinates from LinearAlgebraicGroups.RootData.CharacterPairing
open private latticeCharacter latticeCharacter_comp latticeMap_comp lattice_torus_of_split
  torsionFree_of_diagonal_torus from LinearAlgebraicGroups.RootData.RankOneFlag
open private torus_of_iso from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {M : Type u} [CommGroup M]

private abbrev LatticeQuotient (L : Subgroup M) := Additive (M ⧸ L)

private def saturationProjection (L : Subgroup M) :
    M →* Multiplicative (LatticeQuotient L ⧸ torsion ℤ (LatticeQuotient L)) :=
  ((torsion ℤ (LatticeQuotient L)).mkQ.toAddMonoidHom.toMultiplicativeRight).comp
    (QuotientGroup.mk' L)

private theorem saturationProjection_surjective (L : Subgroup M) :
    Function.Surjective (saturationProjection L) :=
  (Submodule.mkQ_surjective _).comp QuotientGroup.mk_surjective

private theorem mem_saturation_iff (L : Subgroup M) (x : M) :
    x ∈ (saturationProjection L).ker ↔ ∃ n : ℤ, n ≠ 0 ∧ x ^ n ∈ L := by
  let p := QuotientGroup.mk' L
  let y : LatticeQuotient L := Additive.ofMul (p x)
  change Submodule.Quotient.mk y = (0 : LatticeQuotient L ⧸ torsion ℤ (LatticeQuotient L)) ↔ _
  rw [Submodule.Quotient.mk_eq_zero, mem_torsion_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, mem_nonZeroDivisors_iff_ne_zero.mp n.property, (QuotientGroup.eq_one_iff _).mp ?_⟩
    change p (x ^ (n : ℤ)) = 1
    rw [map_zpow]
    exact hn
  · rintro ⟨n, hn, hx⟩
    refine ⟨⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩, ?_⟩
    change p x ^ n = 1
    rw [← map_zpow]
    exact (QuotientGroup.eq_one_iff _).mpr hx

private theorem saturation_ker_le (L : Subgroup M) {N : Type u} [CommGroup N]
    [IsTorsionFree ℤ (Additive N)] (f : M →* N) (hf : L ≤ f.ker) :
    (saturationProjection L).ker ≤ f.ker := by
  intro x hx
  obtain ⟨n, hn, hxn⟩ := (mem_saturation_iff L x).mp hx
  have he : f (x ^ n) = 1 := hf hxn
  rw [map_zpow] at he
  have he' : n • (Additive.ofMul (f x) : Additive N) = 0 := he
  exact ((isTorsionFree_iff_smul_eq_zero.mp inferInstance) _ _ he').resolve_left hn

private theorem saturationQuotient_split [Group.FG M] (L : Subgroup M) :
    IsSplitTorus (specGroup (groupAlgebra k (M ⧸ (saturationProjection L).ker))) := by
  let V := LatticeQuotient L
  let W := V ⧸ torsion ℤ V
  letI : Module.Finite ℤ V := Module.Finite.iff_addGroup_fg.mpr
    (inferInstanceAs (AddGroup.FG V))
  let r := Module.finrank ℤ W
  let basis : Module.Basis (Fin r) ℤ W := Module.finBasis ℤ W
  let e : W ≃ₗ[ℤ] Additive (StandardLattice.{u} r) :=
    basis.equivFun.trans (latticeCoordinates r).symm
  let j : M ⧸ (saturationProjection L).ker ≃* StandardLattice.{u} r :=
    (QuotientGroup.quotientKerEquivOfSurjective _ (saturationProjection_surjective L)).trans
      e.toAddEquiv.toMultiplicative
  obtain ⟨t⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨(hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k j.symm)).op ≪≫ t⟩⟩

private theorem commonKernelInLattice {T : GroupScheme k} [Group.FG M]
    (i : specGroup (groupAlgebra k M) ≅ T) (a b : Character T) :
    Nonempty (KernelSubtorus a b) := by
  let c := latticeCharacter (k := k) M
  let x := c.symm (i.hom ≫ a)
  let y := c.symm (i.hom ≫ b)
  have hx : c x = i.hom ≫ a := c.apply_symm_apply _
  have hy : c y = i.hom ≫ b := c.apply_symm_apply _
  let L := Subgroup.closure ({x, y} : Set M)
  let N := (saturationProjection L).ker
  let j := diagonalClosedInclusion k N
  obtain ⟨hclosed, _⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalRestrictionKernelAndQuotient k M N
  letI := hclosed
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  haveI : IsIso i.hom.hom.hom.left := F.map_isIso i.hom
  let S : ClosedSubgroup T := ⟨_, j ≫ i.hom, IsClosedImmersion.comp _ _⟩
  have hS := saturationQuotient_split (k := k) L
  have annihilator (χ : Character T) :
      S.inclusion ≫ χ = 1 ↔ InSaturatedSpan a b χ := by
    let z := c.symm (i.hom ≫ χ)
    have hz : c z = i.hom ≫ χ := c.apply_symm_apply _
    change (j ≫ i.hom) ≫ χ = 1 ↔ _
    rw [Category.assoc, ← hz]
    change specGroupMap (groupAlgebraMap k (QuotientGroup.mk' N)) ≫
      latticeCharacter (k := k) M z = 1 ↔ _
    rw [latticeCharacter_comp, ← map_one (latticeCharacter (k := k) (M ⧸ N)),
      (latticeCharacter (k := k) (M ⧸ N)).injective.eq_iff,
      show (QuotientGroup.mk' N) z = 1 ↔ z ∈ N from QuotientGroup.eq_one_iff z]
    change z ∈ (saturationProjection L).ker ↔ InSaturatedSpan a b χ
    rw [mem_saturation_iff]
    have power_eq (m s t : ℤ) : z ^ m = x ^ s * y ^ t ↔ χ ^ m = a ^ s * b ^ t := by
      let f := pullbackCharacters i.hom
      have hf : Function.Injective f := by
        intro v w h
        exact (cancel_epi i.hom).mp h
      rw [← c.injective.eq_iff, map_zpow, map_mul, map_zpow, map_zpow, hz, hx, hy]
      change f χ ^ m = f a ^ s * f b ^ t ↔ _
      rw [← map_zpow, ← map_zpow, ← map_zpow, ← map_mul, hf.eq_iff]
    constructor
    · rintro ⟨m, hm, hmem⟩
      obtain ⟨s, t, he⟩ := Subgroup.mem_closure_pair.mp hmem
      exact ⟨m, s, t, hm, (power_eq m s t).mp he.symm⟩
    · rintro ⟨m, s, t, hm, he⟩
      exact ⟨m, hm, Subgroup.mem_closure_pair.mpr ⟨s, t, ((power_eq m s t).mpr he).symm⟩⟩
  refine ⟨⟨S, hS, lattice_torus_of_split hS,
    (annihilator a).mpr ⟨1, 1, 0, one_ne_zero, by simp⟩,
    (annihilator b).mpr ⟨1, 0, 1, one_ne_zero, by simp⟩, ?_, annihilator⟩⟩
  intro U hU hUa hUb
  haveI := U.isClosedImmersion
  haveI : IsIso i.inv.hom.hom.left := F.map_isIso i.inv
  have hUi : IsClosedImmersion (U.inclusion ≫ i.inv).hom.hom.left :=
    IsClosedImmersion.comp U.inclusion.hom.hom.left i.inv.hom.hom.left
  obtain ⟨K, ⟨d, hd⟩, _⟩ :=
    (LinearAlgebraicGroups.DiagonalizableGroups.diagonalClosedSubgroups k M U.group
      (U.inclusion ≫ i.inv)).mp hUi
  let p := QuotientGroup.mk' K
  letI := torsionFree_of_diagonal_torus (M ⧸ K) (torus_of_iso d hU)
  have kills (v : M) (χ : Character T) (hv : c v = i.hom ≫ χ)
      (hχ : U.inclusion ≫ χ = 1) : p v = 1 := by
    apply (latticeCharacter (k := k) (M ⧸ K)).injective
    rw [← latticeCharacter_comp, map_one, hv]
    change diagonalClosedInclusion k K ≫ i.hom ≫ χ = 1
    have hd' : diagonalClosedInclusion k K = d.inv ≫ U.inclusion ≫ i.inv := by
      rw [← hd, Iso.inv_hom_id_assoc]
    rw [hd', Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hχ]
    apply Grp.hom_ext
    exact MonObj.comp_one d.inv.hom.hom
  have hL : L ≤ p.ker := by
    change Subgroup.closure ({x, y} : Set M) ≤ p.ker
    rw [Subgroup.closure_le]
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact kills x a hx hUa
    · obtain rfl := Set.mem_singleton_iff.mp hv
      exact kills y b hy hUb
  let g := QuotientGroup.lift N p (saturation_ker_le L p hL)
  refine ⟨d.hom ≫ specGroupMap (groupAlgebraMap k g), ?_⟩
  have hgj : specGroupMap (groupAlgebraMap k g) ≫ j = diagonalClosedInclusion k K := by
    change specGroupMap (groupAlgebraMap k g) ≫
      specGroupMap (groupAlgebraMap k (QuotientGroup.mk' N)) = _
    rw [latticeMap_comp, show g.comp (QuotientGroup.mk' N) = p from MonoidHom.ext (fun _ => rfl)]
    rfl
  change (d.hom ≫ specGroupMap (groupAlgebraMap k g)) ≫ (j ≫ i.hom) = U.inclusion
  rw [Category.assoc, ← Category.assoc (specGroupMap (groupAlgebraMap k g)), hgj,
    ← Category.assoc, hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The two characters cut out a largest subtorus using the saturated lattice quotient. -/
theorem commonKernelSubtorus : CommonKernelSubtorus.{u} := by
  intro k _ T hT a b
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  letI : Module.Finite ℤ (Additive M) := Module.Finite.equiv (latticeCoordinates r).symm
  letI : Group.FG M := GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp inferInstance)
  exact commonKernelInLattice i a b

end

end CommonKernel

section NormalizerAction

open CharacterDescent (Character)
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

/-- The comparison homomorphism carries any root movement in the source
normalizer to the corresponding root movement in the target normalizer. -/
theorem movesCharacter_map (h : Compatible P Q D E d τ) (N : Normalizers P Q D E d τ)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) (a b : Root P.pair.T)
    (hab : MovesCharacter P.pair.T (z ≫ N.source.inclusion.hom.hom) a.val b.val) :
    MovesCharacter Q.pair.T (z ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom)
      (d a).val (d b).val := by
  obtain ⟨e, he, heab⟩ := hab
  let g := z ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom
  letI := E.comm
  obtain ⟨M, hM, _, hact⟩ := E.datum.normalizerAction
  have hnorm : Normalizes Q.pair.T.inclusion g :=
    (N.representsTarget _ _).mpr ⟨z ≫ N.hom.hom.hom, Category.assoc _ _ _⟩
  obtain ⟨q, hq⟩ := (hM _ _).mp hnorm
  obtain ⟨e', he', _, _⟩ := hact q
  have hg : (e'.hom ≫ Q.pair.T.inclusion).hom.hom =
      (toUnit Q.pair.T.group.X ≫ g) * Q.pair.T.inclusion.hom.hom *
        (toUnit Q.pair.T.group.X ≫ g)⁻¹ := by
    simpa only [Category.assoc, hq] using he'
  let F := Grp.forget (SchemeOver k)
  let p := toUnit P.pair.T.group.X ≫ z
  have hs : N.sourceTorus.hom.hom ≫ N.source.inclusion.hom.hom =
      P.pair.T.inclusion.hom.hom := F.congr_map N.sourceTorus_eq
  have ht : N.targetTorus.hom.hom ≫ N.target.inclusion.hom.hom =
      Q.pair.T.inclusion.hom.hom := F.congr_map N.targetTorus_eq
  have hh : N.sourceTorus.hom.hom ≫ N.hom.hom.hom =
      τ.hom.hom ≫ N.targetTorus.hom.hom := F.congr_map N.torus_comm
  have hsource : e.hom.hom.hom ≫ N.sourceTorus.hom.hom =
      p * N.sourceTorus.hom.hom * p⁻¹ := by
    letI := N.source.isClosedImmersion
    letI : Mono N.source.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono N.source.inclusion.hom.hom).mp
    rw [Category.assoc, hs, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hs]
    exact he
  have hτ : e.hom ≫ τ = τ ≫ e'.hom := by
    letI := Q.pair.T.isClosedImmersion
    letI : Mono Q.pair.T.inclusion.hom.hom := Over.mono_of_mono_left _
    apply Grp.hom_ext
    apply (cancel_mono Q.pair.T.inclusion.hom.hom).mp
    change (e.hom.hom.hom ≫ τ.hom.hom) ≫ Q.pair.T.inclusion.hom.hom =
      (τ.hom.hom ≫ e'.hom.hom.hom) ≫ Q.pair.T.inclusion.hom.hom
    rw [Category.assoc, Category.assoc, show e'.hom.hom.hom ≫ Q.pair.T.inclusion.hom.hom =
      (e'.hom ≫ Q.pair.T.inclusion).hom.hom from rfl, hg,
      MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc τ.hom.hom (toUnit _),
      comp_toUnit]
    have hmiddle : N.sourceTorus.hom.hom ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom =
        τ.hom.hom ≫ Q.pair.T.inclusion.hom.hom := by
      rw [← Category.assoc, hh, Category.assoc, ht]
    have heh := congrArg (fun l => l ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom) hsource
    rw [Category.assoc, ← Category.assoc N.sourceTorus.hom.hom, hh, Category.assoc, ht,
      MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp] at heh
    simpa only [p, g, Category.assoc, hmiddle] using heh
  have hinv : e.inv ≫ τ = τ ≫ e'.inv := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hτ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ⟨e', hg, h.injective ?_⟩
  change τ ≫ e'.inv ≫ (d a).val = τ ≫ (d b).val
  rw [← Category.assoc, ← hinv, Category.assoc, h.root a, h.root b, heab]

end NormalizerAction

section TransportUniqueness

open Pinning (SimpleRoot)
open RootGroups (rootPoint)
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false

private theorem rootMorphism_ext {G : GroupScheme k} {f g : A.group ⟶ G}
    (h : ∀ (R : TestAlgebra k) (a : R), rootPoint f R a = rootPoint g R a) :
    f = g := by
  apply Grp.hom_ext
  have hX := h (CommAlgCat.of k (Polynomial k)) Polynomial.X
  have heval : (Polynomial.aeval Polynomial.X : Polynomial k →ₐ[k] Polynomial k) =
      AlgHom.id k (Polynomial k) :=
    Polynomial.algHom_ext (Polynomial.aeval_X _)
  let R := CommAlgCat.of k (Polynomial k)
  let p : A.group.X ⟶ A.group.X :=
    (testSpec k).map (CommAlgCat.ofHom
      (Polynomial.aeval Polynomial.X : Polynomial k →ₐ[k] R)).op
  have hp : p = 𝟙 A.group.X := by
    have hId : CommAlgCat.ofHom
        (Polynomial.aeval Polynomial.X : Polynomial k →ₐ[k] R) = 𝟙 R :=
      congrArg CommAlgCat.ofHom heval
    exact ((testSpec k).congr_map (congrArg Quiver.Hom.op hId)).trans
      ((testSpec k).map_id (op R))
  change p ≫ f.hom.hom = p ≫ g.hom.hom at hX
  rwa [hp, Category.id_comp, Category.id_comp] at hX

/-- Once transports exist and agree, the resulting maps of root subgroup
schemes are uniquely determined. -/
theorem matchesTransports_unique (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e e' : RootIsomorphisms P Q d}
    (he : MatchesTransports N e) (he' : MatchesTransports N e') : e' = e := by
  funext a
  obtain ⟨i, z, hz⟩ := he.1 a
  have hi := (h.simple i.val).mp ((D.simple_iff i.val).mpr i.property)
  let j : SimpleRoot Q.pair := ⟨d i.val, (E.simple_iff _).mp hi⟩
  obtain ⟨x, hx, hxe⟩ := he.2 a i j rfl z hz
  obtain ⟨x', hx', hxe'⟩ := he'.2 a i j rfl z hz
  haveI := inclusion_mono (P.roots a).val
  have hxx : x' = x := by
    apply Iso.ext
    apply (cancel_mono (P.roots a).val.inclusion).mp
    exact rootMorphism_ext fun R s => (hx' R s).symm.trans (hx R s)
  subst x'
  haveI := inclusion_mono (Q.roots (d a)).val
  apply Iso.ext
  apply (cancel_epi x.hom).mp
  apply (cancel_mono (Q.roots (d a)).val.inclusion).mp
  exact rootMorphism_ext fun R s => (hxe' R s).symm.trans (hxe R s)

end TransportUniqueness

section WeylTransport

open scoped TensorProduct
noncomputable section

open RootPairing

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (R : RootPairing I ℤ X Y)

/-- The subgroup of the Weyl group generated by the two indicated reflections. -/
private def pairWeyl (i j : I) : Subgroup R.weylGroup :=
  Subgroup.closure ({weylGroup.ofIdx R i, weylGroup.ofIdx R j} : Set R.weylGroup)

private theorem pairWeyl_left (i j : I) : weylGroup.ofIdx R i ∈ pairWeyl R i j :=
  Subgroup.subset_closure (by simp)

private theorem pairWeyl_right (i j : I) : weylGroup.ofIdx R j ∈ pairWeyl R i j :=
  Subgroup.subset_closure (by simp)

private abbrev pairSpan (i j : I) : Submodule ℤ X :=
  Submodule.span ℤ ({R.root i, R.root j} : Set X)

private theorem pairWeyl_preserves_span {i j : I} {w : R.weylGroup}
    (hw : w ∈ pairWeyl R i j) :
    ∀ x ∈ pairSpan R i j, w • x ∈ pairSpan R i j := by
  let L := pairSpan R i j
  change ∀ x ∈ L, w • x ∈ L
  have hreflect (q : I) (hq : R.root q ∈ L) (x : X) (hx : x ∈ L) :
      weylGroup.ofIdx R q • x ∈ L := by
    rw [weylGroup.ofIdx_smul]
    change R.reflection q x ∈ L
    rw [RootPairing.reflection_apply]
    exact L.sub_mem hx (L.smul_mem _ hq)
  have hgen (v : R.weylGroup)
      (hv : v ∈ ({weylGroup.ofIdx R i, weylGroup.ofIdx R j} : Set R.weylGroup)) :
      ∀ x ∈ L, v • x ∈ L := by
    rcases Set.mem_insert_iff.mp hv with rfl | hj
    · exact hreflect i (Submodule.subset_span (by simp))
    · obtain rfl := Set.mem_singleton_iff.mp hj
      exact hreflect j (Submodule.subset_span (by simp))
  change w ∈ Subgroup.closure _ at hw
  induction hw using Subgroup.closure_induction'' with
  | mem v hv => exact hgen v hv
  | inv_mem v hv =>
      have h : v⁻¹ = v := by
        rcases Set.mem_insert_iff.mp hv with rfl | hj
        · exact Subtype.ext (RootPairing.Equiv.reflection_inv R i)
        · obtain rfl := Set.mem_singleton_iff.mp hj
          exact Subtype.ext (RootPairing.Equiv.reflection_inv R j)
      simpa only [h] using hgen v hv
  | one => simpa only [one_smul] using fun x (hx : x ∈ L) => hx
  | mul x y _ _ hx hy =>
      intro z hz
      rw [mul_smul]
      exact hx _ (hy _ hz)

private theorem pairCoefficients_sign (b : R.Base) {i j : b.support} (hij : i ≠ j)
    {a c : ℤ} {q : I} (h : a • R.root i.val + c • R.root j.val = R.root q) :
    (0 ≤ a ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ c ≤ 0) := by
  classical
  let coeff : b.support → ℤ := Pi.single i a + Pi.single j c
  have sum_single (l : b.support) (n : ℤ) :
      ∑ t : b.support, (Pi.single l n : b.support → ℤ) t • R.root t.val = n • R.root l.val := by
    rw [Finset.sum_eq_single l]
    · simp
    · intro t _ ht
      simp [Pi.single_eq_of_ne ht]
    · simp
  have hc : ∑ t : b.support, coeff t • R.root t.val = R.root q := by
    simp only [coeff, Pi.add_apply, add_smul, Finset.sum_add_distrib, sum_single, h]
  obtain ⟨d, _, hsign, hd⟩ := b.exists_root_eq_sum_int q
  have hsum : (∑ t : b.support, d t.val • R.root t.val) = R.root q :=
    (Finset.sum_finset_coe (fun t => d t • R.root t) b.support).trans hd.symm
  have he := Fintype.linearIndependent_iffₛ.mp b.linearIndepOn_root
    (fun t : b.support => d t.val) coeff (hsum.trans hc.symm)
  have hi : d i.val = a := (he i).trans (by simp [coeff, Pi.single_eq_of_ne hij])
  have hj : d j.val = c := (he j).trans (by simp [coeff, Pi.single_eq_of_ne hij.symm])
  rcases hsign with hd | hd
  · exact Or.inl ⟨hi ▸ hd.le i.val, hj ▸ hd.le j.val⟩
  · exact Or.inr ⟨hi ▸ hd.le i.val, hj ▸ hd.le j.val⟩

/-- If all roots are in the saturated span of two independent roots, then
the root system has semisimple rank two. The argument allows a larger
ambient weight lattice. -/
private theorem base_card_of_two_root_span (b : R.Base) (p q : I)
    (hind : LinearIndependent ℤ ![R.root p, R.root q])
    (hspan : ∀ i : I, ∃ m c d : ℤ, m ≠ 0 ∧
      m • R.root i = c • R.root p + d • R.root q) :
    b.support.card = 2 := by
  classical
  let W := ℚ ⊗[ℤ] X
  let s : X →ₗ[ℤ] W := TensorProduct.mk ℤ ℚ X 1
  let U := Submodule.span ℚ (Set.range (fun j : b.support => s (R.root j.val)))
  let V := Submodule.span ℚ ({s (R.root p), s (R.root q)} : Set W)
  have root_mem_U (i : I) : s (R.root i) ∈ U := by
    obtain ⟨c, _, _, hc⟩ := b.exists_root_eq_sum_int i
    rw [hc, map_sum]
    apply U.sum_mem
    intro j hj
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
    apply U.smul_mem
    exact Submodule.subset_span ⟨(⟨j, hj⟩ : b.support), rfl⟩
  have root_mem_V (i : I) : s (R.root i) ∈ V := by
    obtain ⟨m, c, d, hm, hi⟩ := hspan i
    apply (V.smul_mem_iff (Int.cast_ne_zero.mpr hm : (m : ℚ) ≠ 0)).mp
    have h := congrArg s hi
    simp only [map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at h
    rw [h]
    exact V.add_mem
      (V.smul_mem _ (Submodule.subset_span (by simp)))
      (V.smul_mem _ (Submodule.subset_span (by simp)))
  have hUV : U = V := by
    apply le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨j, rfl⟩
      exact root_mem_V j.val
    · intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact root_mem_U p
      · obtain rfl := Set.mem_singleton_iff.mp hx
        exact root_mem_U q
  have hU : Module.finrank ℚ U = b.support.card := by
    have h : LinearIndependent ℚ (fun j : b.support => s (R.root j.val)) :=
      Module.Flat.linearIndependent_one_tmul (S := ℚ) b.linearIndepOn_root
    change Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j : b.support => s (R.root j.val)))) = _
    rw [finrank_span_eq_card h, Fintype.card_coe]
  have hV : Module.finrank ℚ V = 2 := by
    have h := Module.Flat.linearIndependent_one_tmul (S := ℚ) hind
    have hrange : Set.range (fun j : Fin 2 => (1 : ℚ) ⊗ₜ[ℤ] ![R.root p, R.root q] j) =
        ({s (R.root p), s (R.root q)} : Set W) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two]
      exact or_congr eq_comm eq_comm
    rw [← show Submodule.span ℚ _ = V from congrArg (Submodule.span ℚ) hrange]
    simpa using finrank_span_eq_card h
  rw [hUV] at hU
  exact hU.symm.trans hV

open private exists_integralValues exists_shortest_word delete_of_signChange
  word_append word_cons word_nil reflection_conjugate reflected_value
  from LinearAlgebraicGroups.RootData.SimpleRoots

open Specs.SimpleRoots (wordLength wordProduct)

variable [Finite I] [R.IsReduced]

private theorem weylGeneratedByBase (b : R.Base) :
    Subgroup.closure (Set.range (fun i : b.support => weylGroup.ofIdx R i.val)) = ⊤ := by
  let W := Subgroup.closure (Set.range (fun i : b.support => weylGroup.ofIdx R i.val))
  have simple_mem (i : I) (hi : i ∈ b.support) : weylGroup.ofIdx R i ∈ W :=
    Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
  have reflection_mem (i : I) : weylGroup.ofIdx R i ∈ W := by
    refine b.induction_reflect i ?_ simple_mem ?_
    · intro j hj
      have he := reflection_conjugate R (weylGroup.ofIdx R j) j
      change weylGroup.ofIdx R (R.reflectionPerm j j) =
        weylGroup.ofIdx R j * weylGroup.ofIdx R j * (weylGroup.ofIdx R j)⁻¹ at he
      rw [he, mul_inv_cancel_right]
      exact hj
    · intro j l hj hl
      have he := reflection_conjugate R (weylGroup.ofIdx R l) j
      change weylGroup.ofIdx R (R.reflectionPerm l j) =
        weylGroup.ofIdx R l * weylGroup.ofIdx R j * (weylGroup.ofIdx R l)⁻¹ at he
      rw [he]
      exact W.mul_mem (W.mul_mem (simple_mem l hl) hj) (W.inv_mem (simple_mem l hl))
  apply top_unique
  rintro ⟨v, hv⟩ -
  induction hv using weylGroup.induction with
  | mem i => exact reflection_mem i
  | one => exact W.one_mem
  | mul g h hg hh ihg ihh => exact W.mul_mem ihg ihh

omit [Finite I] [R.IsReduced] in
private theorem exists_heightFunctional [Module.Free ℤ X] [Module.Finite ℤ X] (b : R.Base) :
    ∃ (f : X →ₗ[ℤ] ℤ) (m : ℤ), 0 < m ∧ ∀ i, f (R.root i) = m * b.height i := by
  obtain ⟨f, m, hm, hsimple⟩ := exists_integralValues b.linearIndepOn_root (fun _ => 1)
  refine ⟨f, m, hm, fun i => ?_⟩
  obtain ⟨c, _, _, hc⟩ := b.exists_root_eq_sum_int i
  rw [b.height_eq_sum hc, hc, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := hsimple ⟨j, hj⟩
  rw [map_zsmul, show f (R.root j) = m by simpa using h, smul_eq_mul, mul_comm]

private theorem shorter_of_negative (b : R.Base) (f : X →ₗ[ℤ] ℤ)
    (hf : ∀ i, f (R.root i) ≠ 0) (hb : ∀ i, b.IsPos i ↔ 0 < f (R.root i))
    (w : R.weylGroup) (i : b.support)
    (hi : f (R.root (R.weylGroupToPerm w i.val)) < 0) :
    wordLength R b (w * weylGroup.ofIdx R i.val) < wordLength R b w := by
  obtain ⟨l, hl, hlen, _⟩ := exists_shortest_word R b (weylGeneratedByBase R b) w
  obtain ⟨l', hl', hlen'⟩ := delete_of_signChange R b f hf hb l
    ((hb _).mp (b.isPos_of_mem_support i.property)) (hl.symm ▸ hi)
  rw [hl] at hl'
  have hle : wordLength R b (w * weylGroup.ofIdx R i.val) ≤ l'.length :=
    csInf_le' ⟨l', rfl, hl'⟩
  omega

private theorem exists_negative_simple (b : R.Base) (f : X →ₗ[ℤ] ℤ)
    (hf : ∀ i, f (R.root i) ≠ 0) (hb : ∀ i, b.IsPos i ↔ 0 < f (R.root i))
    (w : R.weylGroup) (hw : w ≠ 1) :
    ∃ i : b.support, f (R.root (R.weylGroupToPerm w i.val)) < 0 := by
  obtain ⟨l, hl, _, hmin⟩ := exists_shortest_word R b (weylGeneratedByBase R b) w
  revert hl hmin
  induction l using List.reverseRecOn with
  | nil => intro hl _; exact (hw hl.symm).elim
  | append_singleton ls i _ =>
    intro hl hmin
    have hval : w = wordProduct R b ls * weylGroup.ofIdx R i.val := by
      simpa only [word_append, word_cons, word_nil, mul_one] using hl.symm
    refine ⟨i, ?_⟩
    rw [hval, map_mul, Equiv.Perm.mul_apply]
    change f (R.root (R.weylGroupToPerm (wordProduct R b ls) (R.reflectionPerm i.val i.val))) < 0
    rw [reflected_value R f, neg_lt_zero]
    by_contra! hnonpos
    have hn := lt_of_le_of_ne hnonpos (hf _)
    obtain ⟨l', hl', hlen'⟩ := delete_of_signChange R b f hf hb ls
      ((hb _).mp (b.isPos_of_mem_support i.property)) hn
    have hle := hmin l' (hl'.trans hval.symm)
    simp only [List.length_append, List.length_singleton] at hle
    omega

/-- Tits's reduction of a Weyl element carrying one simple root to another.
A transport property stable under composition need only be checked inside
the subgroups generated by pairs of simple reflections. -/
private theorem weylInductionOnSimpleTransport [Module.Free ℤ X] [Module.Finite ℤ X]
    (b : R.Base) (F : R.weylGroup → b.support → b.support → Prop)
    (identity : ∀ i, F 1 i i)
    (localStep : ∀ (i j l : b.support) (w : R.weylGroup), i ≠ l → (j = i ∨ j = l) →
      w ∈ pairWeyl R i.val l.val → R.weylGroupToPerm w i.val = j.val → F w i j)
    (compose : ∀ (v w : R.weylGroup) (i j l : b.support),
      F v i j → F w j l → F (w * v) i l) :
    ∀ (w : R.weylGroup) (i j : b.support), R.weylGroupToPerm w i.val = j.val → F w i j := by
  classical
  obtain ⟨f, m, hm, hheight⟩ := exists_heightFunctional R b
  have hf (i : I) : f (R.root i) ≠ 0 :=
    hheight i ▸ mul_ne_zero hm.ne' (b.height_ne_zero i)
  have hb (i : I) : b.IsPos i ↔ 0 < f (R.root i) := by
    rw [b.isPos_iff, hheight, mul_pos_iff_of_pos_left hm]
  intro w
  induction w using (measure (wordLength R b)).wf.induction with
  | h w ih =>
    intro i j hwij
    by_cases hw : w = 1
    · subst w
      have hij : i = j := Subtype.ext (by simpa only [map_one, Equiv.Perm.one_apply] using hwij)
      subst j
      exact identity i
    obtain ⟨l, hl⟩ := exists_negative_simple R b f hf hb w hw
    have hil : i ≠ l := by
      rintro rfl
      rw [hwij] at hl
      exact (not_lt_of_gt ((hb _).mp (b.isPos_of_mem_support j.property))) hl
    let W := pairWeyl R i.val l.val
    let lengths : Set ℕ := {n | ∃ v ∈ W, wordLength R b (w * v) = n}
    have hlengths : lengths.Nonempty :=
      ⟨_, 1, W.one_mem, rfl⟩
    obtain ⟨v, hv, hvmin⟩ := Nat.sInf_mem hlengths
    let y := w * v
    have hmin (z : R.weylGroup) (hz : z ∈ W) :
        wordLength R b y ≤ wordLength R b (w * z) :=
      hvmin.trans_le (csInf_le' ⟨z, hz, rfl⟩)
    have hy_shorter : wordLength R b y < wordLength R b w :=
      (hmin _ (pairWeyl_right R i.val l.val)).trans_lt (shorter_of_negative R b f hf hb w l hl)
    have hypos (q : b.support) (hq : weylGroup.ofIdx R q.val ∈ W) :
        b.IsPos (R.weylGroupToPerm y q.val) := by
      apply (hb _).mpr
      by_contra! hn
      have ht := hmin _ (W.mul_mem hv hq)
      rw [← mul_assoc] at ht
      exact (not_lt_of_ge ht) (shorter_of_negative R b f hf hb y q (lt_of_le_of_ne hn (hf _)))
    let t := R.weylGroupToPerm v⁻¹ i.val
    have ht : R.root t ∈ pairSpan R i.val l.val := by
      rw [← R.weylGroup_apply_root]
      exact pairWeyl_preserves_span R (W.inv_mem hv) _ (Submodule.subset_span (by simp))
    obtain ⟨a, c, hcoeff⟩ := Submodule.mem_span_pair.mp ht
    have hsign := pairCoefficients_sign R b hil hcoeff
    have hyt : R.weylGroupToPerm y t = j.val := by
      change R.weylGroupToPerm y (R.weylGroupToPerm v⁻¹ i.val) = j.val
      rw [← Equiv.Perm.mul_apply, ← map_mul, show y * v⁻¹ = w from mul_inv_cancel_right w v, hwij]
    let ha := b.height (R.weylGroupToPerm y i.val)
    let hc := b.height (R.weylGroupToPerm y l.val)
    have ha1 : 1 ≤ ha := hypos i (pairWeyl_left R i.val l.val)
    have hc1 : 1 ≤ hc := hypos l (pairWeyl_right R i.val l.val)
    have hsum : a * ha + c * hc = 1 := by
      apply mul_left_cancel₀ hm.ne'
      have h := congrArg f (congrArg (y • ·) hcoeff)
      simp only [smul_add, smul_comm y a, smul_comm y c, R.weylGroup_apply_root, hyt,
        map_zsmul, map_add, smul_eq_mul, hheight, b.height_one_of_mem_support j.property] at h
      change a * (m * ha) + c * (m * hc) = m * 1 at h
      linear_combination h
    have hnonneg : 0 ≤ a ∧ 0 ≤ c := hsign.resolve_right fun ⟨h₁, h₂⟩ => by
      have e₁ := mul_nonpos_of_nonpos_of_nonneg h₁ (show 0 ≤ ha by omega)
      have e₂ := mul_nonpos_of_nonpos_of_nonneg h₂ (show 0 ≤ hc by omega)
      omega
    have hle : a + c ≤ 1 := by
      have e₁ := mul_le_mul_of_nonneg_left ha1 hnonneg.1
      have e₂ := mul_le_mul_of_nonneg_left hc1 hnonneg.2
      simp only [mul_one] at e₁ e₂
      omega
    have hsimple : t = i.val ∨ t = l.val := by
      by_cases hzero : a = 0
      · have hc' : c = 1 := by
          have : c ≠ 0 := by rintro rfl; simp [hzero] at hsum
          omega
        exact Or.inr (R.root.injective (by simpa only [hzero, hc', zero_smul,
          one_smul, zero_add] using hcoeff.symm))
      · have ha' : a = 1 := by omega
        have hc' : c = 0 := by omega
        exact Or.inl (R.root.injective (by simpa only [ha', hc', one_smul, zero_smul,
          add_zero] using hcoeff.symm))
    have finish (q : b.support) (hq : t = q.val) (hq' : q = i ∨ q = l) : F w i j := by
      have hfirst := localStep i q l v⁻¹ hil hq' (W.inv_mem hv) hq
      have hsecond := ih y hy_shorter q j (hq ▸ hyt)
      simpa only [y, mul_inv_cancel_right] using compose v⁻¹ y i q j hfirst hsecond
    exact hsimple.elim (fun h => finish i h (Or.inl rfl)) (fun h => finish l h (Or.inr rfl))

/-- The Weyl reduction lifts to a group of representatives. Arbitrary lifts
differ from the chosen lifts of the two-generator words by an element of the kernel. -/
private theorem representativeInductionOnSimpleTransport [Module.Free ℤ X] [Module.Finite ℤ X]
    (b : R.Base) {N : Type*} [Group N] (π : N →* R.weylGroup)
    (hsurj : Function.Surjective π) (n : b.support → N)
    (hn : ∀ i, π (n i) = weylGroup.ofIdx R i.val)
    (F : N → b.support → b.support → Prop)
    (kernel : ∀ t, π t = 1 → ∀ i, F t i i)
    (localStep : ∀ (i j l : b.support) (z : N), i ≠ l → (j = i ∨ j = l) →
      z ∈ Subgroup.closure ({n i, n l} : Set N) →
      R.weylGroupToPerm (π z) i.val = j.val → F z i j)
    (compose : ∀ (z w : N) (i j l : b.support), F z i j → F w j l → F (w * z) i l) :
    ∀ (z : N) (i j : b.support), R.weylGroupToPerm (π z) i.val = j.val → F z i j := by
  let L (w : R.weylGroup) (i j : b.support) := ∀ z, π z = w → F z i j
  have hidentity (i : b.support) : L 1 i i := fun t ht => kernel t ht i
  have hlocal (i j l : b.support) (w : R.weylGroup) (hil : i ≠ l)
      (hjl : j = i ∨ j = l) (hw : w ∈ pairWeyl R i.val l.val)
      (hmove : R.weylGroupToPerm w i.val = j.val) : L w i j := by
    intro z hz
    let M := Subgroup.closure ({n i, n l} : Set N)
    have hM : M.map π = pairWeyl R i.val l.val := by
      change (Subgroup.closure _).map π = Subgroup.closure _
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, hn, hn]
    rw [← hM] at hw
    obtain ⟨y, hM, hy⟩ := hw
    have hF := localStep i j l y hil hjl hM (hy.symm ▸ hmove)
    have ht : π (z * y⁻¹) = 1 := by rw [map_mul, map_inv, hz, hy, mul_inv_cancel]
    simpa only [inv_mul_cancel_right] using compose y (z * y⁻¹) i j j hF (kernel _ ht j)
  have hcomp (v w : R.weylGroup) (i j l : b.support)
      (hv : L v i j) (hw : L w j l) : L (w * v) i l := by
    intro z hz
    obtain ⟨y, hy⟩ := hsurj v
    have ht : π (z * y⁻¹) = w := by rw [map_mul, map_inv, hz, hy, mul_inv_cancel_right]
    simpa only [inv_mul_cancel_right] using compose y (z * y⁻¹) i j l (hv y hy) (hw _ ht)
  intro z i j h
  exact weylInductionOnSimpleTransport R b L hidentity hlocal hcomp (π z) i j h z rfl

end

end WeylTransport

section SubsystemCompatibility

open CharacterDescent (Character)
open Pinning (IsSimple)
open BorelsAndChambers (subgroupRoots)

set_option backward.isDefEq.respectTransparency false

private noncomputable def pullbackCharacterEquiv {G H : GroupScheme k} (e : G ≅ H) :
    Character H ≃* Character G where
  toFun := pullbackCharacters e.hom
  invFun := pullbackCharacters e.inv
  left_inv χ := by
    change e.inv ≫ e.hom ≫ χ = χ
    rw [e.inv_hom_id_assoc]
  right_inv χ := by
    change e.hom ≫ e.inv ≫ χ = χ
    rw [e.hom_inv_id_assoc]
  map_mul' := (pullbackCharacters e.hom).map_mul

/-- Passing through isomorphic full tori preserves finite-index injectivity
and preserves surjectivity of the character map when it holds. -/
private theorem pullbackToriCompatibility {G G' H H' : GroupScheme k}
    (e : G ≅ G') (f : H ≅ H') (l : G ⟶ H)
    (hinj : Function.Injective (pullbackCharacters l))
    (hfinite : Finite (Character G ⧸ (pullbackCharacters l).range)) :
    let l' := e.inv ≫ l ≫ f.hom
    Function.Injective (pullbackCharacters l') ∧
      Finite (Character G' ⧸ (pullbackCharacters l').range) ∧
      (Function.Surjective (pullbackCharacters l) → Function.Surjective (pullbackCharacters l')) := by
  dsimp only
  let l' := e.inv ≫ l ≫ f.hom
  let c := pullbackCharacterEquiv e.symm
  let c' := pullbackCharacterEquiv f
  have comp_eq (χ : Character H') :
      pullbackCharacters l' χ = c (pullbackCharacters l (c' χ)) := by
    change (e.inv ≫ l ≫ f.hom) ≫ χ = e.inv ≫ l ≫ f.hom ≫ χ
    simp only [Category.assoc]
  have hcompose : pullbackCharacters l' = c ∘ pullbackCharacters l ∘ c' := funext comp_eq
  refine ⟨hcompose ▸ c.injective.comp (hinj.comp c'.injective), ?_,
    fun hs => hcompose ▸ c.surjective.comp (hs.comp c'.surjective)⟩
  have hrange : ((pullbackCharacters l).range.map c.toMonoidHom) = (pullbackCharacters l').range := by
    ext χ
    constructor
    · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
      obtain ⟨θ, hθ⟩ := c'.surjective ψ
      refine ⟨θ, ?_⟩
      rw [comp_eq, hθ]
      rfl
    · rintro ⟨θ, rfl⟩
      exact ⟨pullbackCharacters l (c' θ), ⟨c' θ, rfl⟩, (comp_eq θ).symm⟩
  letI := hfinite
  exact Finite.of_equiv _ (QuotientGroup.congr _ _ c hrange).toEquiv

/-- Compatibility on the full tori and inherited coroots restricts to the
two centralizers whenever their chosen positive systems correspond. -/
private theorem subsystemCompatible (h : Compatible P Q D E d τ)
    {a b : Root P.pair.T} (S : Subsystem P D a b) (T : Subsystem Q E (d a) (d b))
    (δ : Root S.localGroup.pair.T ≃ Root T.localGroup.pair.T)
    (hδ : ∀ r, T.roots (δ r) = d (S.roots r))
    (hpos : ∀ r, r ∈ subgroupRoots S.localGroup.pair.T S.localGroup.pair.B ↔
      δ r ∈ subgroupRoots T.localGroup.pair.T T.localGroup.pair.B) :
    Compatible S.localGroup T.localGroup S.datum T.datum δ (S.torus.inv ≫ τ ≫ T.torus.hom) := by
  letI := D.comm
  letI := E.comm
  letI := S.datum.comm
  letI := T.datum.comm
  let τ' := S.torus.inv ≫ τ ≫ T.torus.hom
  obtain ⟨hinj, hindex, _⟩ := pullbackToriCompatibility
    S.torus T.torus τ h.injective h.finiteIndex
  have hroot (r : Root S.localGroup.pair.T) : τ' ≫ (δ r).val = r.val := by
    change (S.torus.inv ≫ τ ≫ T.torus.hom) ≫ (δ r).val = r.val
    simp only [Category.assoc, T.root_eq, hδ, h.root, ← S.root_eq r, Iso.inv_hom_id_assoc]
  have hroot' (r : Root S.localGroup.pair.T) : pullbackCharacters τ' (δ r).val = r.val :=
    hroot r
  have hcoroot (r : Root S.localGroup.pair.T) :
      Additive.toMul (S.datum.datum.rootDatum.coroot r) ≫ τ' =
        Additive.toMul (T.datum.datum.rootDatum.coroot (δ r)) := by
    rw [← S.coroot_eq r, ← T.coroot_eq (δ r), hδ]
    change (Additive.toMul (D.datum.rootDatum.coroot (S.roots r)) ≫ S.torus.hom) ≫
      S.torus.inv ≫ τ ≫ T.torus.hom = _
    rw [Category.assoc, S.torus.hom_inv_id_assoc, ← Category.assoc, h.coroot]
  refine ⟨hinj, hindex, hroot, hcoroot, fun r => ?_⟩
  rw [S.datum.simple_iff, T.datum.simple_iff]
  unfold IsSimple
  refine and_congr (hpos r) ⟨?_, ?_⟩
  · intro hr x hx y hy he
    obtain ⟨p, rfl⟩ := δ.surjective x
    obtain ⟨q, rfl⟩ := δ.surjective y
    apply hr p ((hpos p).mpr hx) q ((hpos q).mpr hy)
    simpa only [map_mul, hroot'] using congrArg (pullbackCharacters τ') he
  · intro hr x hx y hy he
    apply hr (δ x) ((hpos x).mp hx) (δ y) ((hpos y).mp hy)
    apply hinj
    change pullbackCharacters τ' (δ r).val = pullbackCharacters τ' ((δ x).val * (δ y).val)
    simpa only [map_mul, hroot'] using he

end SubsystemCompatibility

section SubsystemSimpleRoots

open Additive
open BorelsAndChambers (subgroupRoots)
open Pinning (IsSimple SimpleRoot)
open RootGroups (Proportional)

set_option backward.isDefEq.respectTransparency false

/-- Distinct simple roots have independent characters. -/
private theorem simpleRoots_nonproportional (D : AttachedDatum P.pair)
    (a b : SimpleRoot P.pair) (hab : a ≠ b) :
    ¬ Proportional a.val.val b.val.val := by
  letI := D.comm
  let i : D.base.support := ⟨a.val, (D.simple_iff a.val).mpr a.property⟩
  let j : D.base.support := ⟨b.val, (D.simple_iff b.val).mpr b.property⟩
  have hij : i ≠ j := fun h => hab (Subtype.ext (congrArg (fun z : D.base.support => z.val) h))
  have hind := D.base.linearIndependent_pair_of_ne hij
  rw [LinearIndependent.pair_iff] at hind
  rintro ⟨m, n, hm, _, he⟩
  have hv : m • D.datum.rootDatum.root i.val = n • D.datum.rootDatum.root j.val := by
    simpa only [D.datum.root_eq, ofMul_zpow] using congrArg ofMul he
  have hz : m • D.datum.rootDatum.root i.val + (-n) • D.datum.rootDatum.root j.val = 0 := by
    rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero]
    exact hv
  exact hm (hind _ _ hz).1

/-- The two ambient simple roots become exactly the simple roots of their
rank-two centralizer when the positive system is restricted. -/
private theorem subsystem_simple_pair (a b : SimpleRoot P.pair) (hab : a ≠ b)
    (S : Subsystem P D a.val b.val)
    (hpos : ∀ r, r ∈ subgroupRoots S.localGroup.pair.T S.localGroup.pair.B ↔
      S.roots r ∈ subgroupRoots P.pair.T P.pair.B) :
    ∃ i j : SimpleRoot S.localGroup.pair, S.roots i.val = a.val ∧ S.roots j.val = b.val ∧
      ∀ r : SimpleRoot S.localGroup.pair, r = i ∨ r = j := by
  classical
  have hs (p : SimpleRoot P.pair) (hp : InSaturatedSpan a.val.val b.val.val p.val.val) :
      ∃ r : SimpleRoot S.localGroup.pair, S.roots r.val = p.val := by
    have hmem : p.val ∈ Set.range S.roots := S.root_range ▸ hp
    obtain ⟨r, hr⟩ := hmem
    have hrpos : S.roots r ∈ subgroupRoots P.pair.T P.pair.B := hr ▸ p.property.1
    refine ⟨⟨r, (hpos _).mpr hrpos, fun x hx y hy hxy => ?_⟩, hr⟩
    apply p.property.2 (S.roots x) ((hpos _).mp hx) (S.roots y) ((hpos _).mp hy)
    have he := congrArg (pullbackCharacters S.torus.hom) hxy
    change pullbackCharacters S.torus.hom r.val = _ at he
    have hχ (q : Root S.localGroup.pair.T) :
        pullbackCharacters S.torus.hom q.val = (S.roots q).val := S.root_eq q
    simpa only [map_mul, hχ, hr] using he
  obtain ⟨i, hi⟩ := hs a ⟨1, 1, 0, one_ne_zero, by simp⟩
  obtain ⟨j, hj⟩ := hs b ⟨1, 0, 1, one_ne_zero, by simp⟩
  have hij : i.val ≠ j.val := by
    intro h
    apply hab
    apply Subtype.ext
    exact hi.symm.trans ((congrArg S.roots h).trans hj)
  letI := S.datum.comm
  have hsub : ({i.val, j.val} : Finset (Root S.localGroup.pair.T)) ⊆ S.datum.base.support := by
    intro r hr
    rcases (Finset.mem_insert.mp hr) with rfl | hr
    · exact (S.datum.simple_iff _).mpr i.property
    · obtain rfl := Finset.mem_singleton.mp hr
      exact (S.datum.simple_iff _).mpr j.property
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [S.rank, Finset.card_pair hij])
  refine ⟨i, j, hi, hj, fun r => ?_⟩
  have hr := (S.datum.simple_iff r.val).mpr r.property
  rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hr
  exact hr.imp Subtype.ext Subtype.ext

end SubsystemSimpleRoots

section RationalMovement

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CharacterDescent (Character)
open CharacterPairing (pairing)
open Pinning (SimpleRoot)
open Additive

set_option backward.isDefEq.respectTransparency false

private theorem movesCharacter_one {G : GroupScheme k} (T : ClosedSubgroup G) (a : Character T.group) :
    MovesCharacter T (1 : 𝟙_ (SchemeOver k) ⟶ G.X) a a := by
  refine ⟨Iso.refl _, ?_, Category.id_comp _⟩
  rw [Iso.refl_hom, Category.id_comp, MonObj.comp_one, one_mul, inv_one, mul_one]

private theorem movesCharacter_mul {G : GroupScheme k} {T : ClosedSubgroup G}
    {n m : 𝟙_ (SchemeOver k) ⟶ G.X} {a b c : Character T.group}
    (hn : MovesCharacter T n a b) (hm : MovesCharacter T m b c) :
    MovesCharacter T (m * n) a c := by
  obtain ⟨e, he, heab⟩ := hn
  obtain ⟨f, hf, hfbc⟩ := hm
  refine ⟨e ≪≫ f, ?_, by rw [Iso.trans_inv, Category.assoc, heab, hfbc]⟩
  let i := T.inclusion.hom.hom
  let u := toUnit T.group.X ≫ n
  let v := toUnit T.group.X ≫ m
  change e.hom.hom.hom ≫ (f.hom ≫ T.inclusion).hom.hom =
    (toUnit T.group.X ≫ (m * n)) * i * (toUnit T.group.X ≫ (m * n))⁻¹
  rw [hf, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc _ (toUnit _),
    comp_toUnit, show e.hom.hom.hom ≫ i = u * i * u⁻¹ from he, MonObj.comp_mul]
  change v * (u * i * u⁻¹) * v⁻¹ = (v * u) * i * (v * u)⁻¹
  group

private theorem movesCharacter_invCharacter {G : GroupScheme k} {T : ClosedSubgroup G}
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} {a b : Character T.group} (h : MovesCharacter T n a b) :
    MovesCharacter T n a⁻¹ b⁻¹ := by
  obtain ⟨e, he, heab⟩ := h
  refine ⟨e, he, ?_⟩
  change pullbackCharacters e.inv a⁻¹ = b⁻¹
  rw [map_inv, show pullbackCharacters e.inv a = b from heab]


private theorem movesCharacter_inverse {G : GroupScheme k} {T : ClosedSubgroup G}
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} {a b : Character T.group} (h : MovesCharacter T n a b) :
    MovesCharacter T n⁻¹ b a := by
  obtain ⟨e, he, heab⟩ := h
  refine ⟨e.symm, ?_, ?_⟩
  · let F := Grp.forget (SchemeOver k)
    apply (cancel_epi (F.mapIso e).hom).mp
    let j := T.inclusion.hom.hom
    let g := toUnit T.group.X ≫ n
    change e.hom.hom.hom ≫ (e.inv.hom.hom ≫ j) =
      e.hom.hom.hom ≫ ((toUnit T.group.X ≫ n⁻¹) * j * (toUnit T.group.X ≫ n⁻¹)⁻¹)
    rw [← Category.assoc, show e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ from F.congr_map e.hom_inv_id,
      Category.id_comp, GrpObj.comp_inv, inv_inv, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      ← Category.assoc _ (toUnit _), comp_toUnit,
      show e.hom.hom.hom ≫ j = g * j * g⁻¹ from he]
    change j = g⁻¹ * (g * j * g⁻¹) * g
    group
  · change e.hom ≫ b = a
    rw [← heab, Iso.hom_inv_id_assoc]

private theorem simpleRepresentative_moves (N : Normalizers P Q D E d τ)
    (i : SimpleRoot P.pair) (a : Root P.pair.T) :
    letI := D.comm
    MovesCharacter P.pair.T (N.sourceSimple i).reflection.representative a.val
      (D.datum.rootDatum.reflectionPerm i.val a).val := by
  letI := D.comm
  let r := (N.sourceSimple i).reflection
  refine ⟨r.conjugation, r.conjugates, ?_⟩
  have hpair : pairing P.pair.T.group a.val r.coroot = D.datum.rootDatum.pairing a i.val := by
    rw [show r.coroot = toMul (D.datum.rootDatum.coroot i.val) from (N.sourceSimple i).coroot_eq]
    rw [← D.datum.pairing_eq, ← D.datum.root_eq]
    rfl
  have hr := D.datum.rootDatum.reflection_apply_root (i := i.val) (j := a)
  rw [← D.datum.rootDatum.root_reflectionPerm] at hr
  apply ofMul.injective
  rw [r.reflection, ofMul_mul, ofMul_zpow, neg_smul, ← sub_eq_add_neg, hpair,
    ← D.datum.root_eq a, ← D.datum.root_eq i.val, ← hr, D.datum.root_eq]

/-- Reflections in the linked simple representatives reach every root
from one of the simple pins. -/
private theorem exists_transportingRepresentative (N : Normalizers P Q D E d τ)
    (a : Root P.pair.T) :
    ∃ (i : SimpleRoot P.pair) (n : 𝟙_ (SchemeOver k) ⟶ N.source.group.X),
      MovesCharacter P.pair.T (n ≫ N.source.inclusion.hom.hom) i.val.val a.val := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  classical
  have hrep (i : SimpleRoot P.pair) :=
    (N.representsSource _ _).mp (N.sourceSimple i).reflection.normalizes
  choose n hn using hrep
  have step (i : SimpleRoot P.pair) (r : Root P.pair.T) :
      MovesCharacter P.pair.T (n i ≫ N.source.inclusion.hom.hom) r.val
        (D.datum.rootDatum.reflectionPerm i.val r).val := by
    rw [hn i]
    exact simpleRepresentative_moves N i r
  have opposite (r : Root P.pair.T) :
      (D.datum.rootDatum.reflectionPerm r r).val = r.val⁻¹ := by
    have hr := (D.datum.rootDatum.root_eq_neg_iff (i := D.datum.rootDatum.reflectionPerm r r)
      (j := r)).mpr rfl
    rwa [D.datum.root_eq, D.datum.root_eq] at hr
  refine D.base.induction_reflect a (p := fun r =>
    ∃ (i : SimpleRoot P.pair) (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X),
      MovesCharacter P.pair.T (z ≫ N.source.inclusion.hom.hom) i.val.val r.val) ?_ ?_ ?_
  · intro r hr
    obtain ⟨i, z, hz⟩ := hr
    have h₁ := step i i.val
    have h₂ := movesCharacter_invCharacter hz
    rw [opposite i.val] at h₁
    rw [opposite]
    exact ⟨i, z * n i, by
      rw [MonObj.mul_comp]
      exact movesCharacter_mul h₁ h₂⟩
  · intro r hr
    refine ⟨⟨r, (D.simple_iff r).mp hr⟩, 1, ?_⟩
    rw [MonObj.one_comp]
    exact movesCharacter_one P.pair.T r.val
  · intro r s hr hs
    obtain ⟨i, z, hz⟩ := hr
    let j : SimpleRoot P.pair := ⟨s, (D.simple_iff s).mp hs⟩
    refine ⟨i, n j * z, ?_⟩
    rw [MonObj.mul_comp]
    exact movesCharacter_mul hz (step j r)

end RationalMovement

section RationalEquivariance

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open Pinning (SimpleRoot)
open RootGroups (rootPoint)

set_option backward.isDefEq.respectTransparency false

private theorem transport_after_mul {G : GroupScheme k} {z w : 𝟙_ (SchemeOver k) ⟶ G.X}
    {x y q : A.group ⟶ G} (hw : TransportsCoordinate w x y)
    (hzw : TransportsCoordinate (z * w) x q) : TransportsCoordinate z y q := by
  intro R t
  have h₁ := hw R t
  have h₂ := hzw R t
  dsimp only at h₁ h₂ ⊢
  rw [← h₁, ← h₂, MonObj.comp_mul]
  group

/-- Once the transports agree, precomposing the chosen chamber transport
by a normalizer action compares the two rational conjugation maps. -/
private theorem matchesTransports_rational (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) (e : RootIsomorphisms P Q d)
    (he : MatchesTransports N e) (a b : Root P.pair.T)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X)
    (hz : MovesCharacter P.pair.T (z ≫ N.source.inclusion.hom.hom) a.val b.val) :
    ∃ (x : A.group ≅ (P.roots a).val.group) (y : A.group ≅ (P.roots b).val.group),
      TransportsCoordinate (z ≫ N.source.inclusion.hom.hom)
        (x.hom ≫ (P.roots a).val.inclusion) (y.hom ≫ (P.roots b).val.inclusion) ∧
      TransportsCoordinate (z ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom)
        ((x ≪≫ e a).hom ≫ (Q.roots (d a)).val.inclusion)
        ((y ≪≫ e b).hom ≫ (Q.roots (d b)).val.inclusion) := by
  obtain ⟨i, w, hw⟩ := he.1 a
  have hi := (h.simple i.val).mp ((D.simple_iff i.val).mpr i.property)
  let j : SimpleRoot Q.pair := ⟨d i.val, (E.simple_iff _).mp hi⟩
  obtain ⟨x, hx, hxe⟩ := he.2 a i j rfl w hw
  have hzw : MovesCharacter P.pair.T ((z * w) ≫ N.source.inclusion.hom.hom) i.val.val b.val := by
    rw [MonObj.mul_comp]
    exact movesCharacter_mul hw hz
  obtain ⟨y, hy, hye⟩ := he.2 b i j rfl (z * w) hzw
  refine ⟨x, y, transport_after_mul hx ?_, transport_after_mul hxe ?_⟩
  · simpa only [MonObj.mul_comp] using hy
  · let f := N.hom ≫ N.target.inclusion
    change TransportsCoordinate ((z ≫ f.hom.hom) * (w ≫ f.hom.hom)) _ _
    change TransportsCoordinate ((z * w) ≫ f.hom.hom) _ _ at hye
    simpa only [MonObj.mul_comp] using hye

end RationalEquivariance

section NormalizerFibres

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AbstractPairing (Datum)
open DatumAndWeyl (Identification)

/-- Two families in the same scheme quotient fibre differ by a family in
the scheme kernel. This also applies over nonreduced bases. -/
private theorem eq_mul_of_same_quotient {H G : GroupScheme k} {K : ClosedSubgroup H}
    {f : H ⟶ G} (hf : IsSchemeKernel f K) {Z : SchemeOver k}
    (z w : Z ⟶ H.X) (h : z ≫ f.hom.hom = w ≫ f.hom.hom) :
    ∃ t : Z ⟶ K.group.X, z = (t ≫ K.inclusion.hom.hom) * w := by
  let d := z * w⁻¹
  have hk : d ≫ f.hom.hom = toUnit Z ≫ η[G.X] := by
    change (z * w⁻¹) ≫ f.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]
  refine ⟨hf.lift d (toUnit Z) hk, ?_⟩
  rw [hf.lift_fst]
  change z = (z * w⁻¹) * w
  group

/-- A normalizer family of constant Weyl label is a torus family times
any rational representative of that label. -/
private theorem normalizer_family_factor {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (I : Identification D) {Z : SchemeOver k}
    (z : Z ⟶ I.normalizer.group.X)
    (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X)
    (hz : z ≫ I.quotient.hom.hom = toUnit Z ≫ n ≫ I.quotient.hom.hom) :
    ∃ t : Z ⟶ T.group.X, z = (t ≫ I.torusInclusion.hom.hom) * (toUnit Z ≫ n) :=
  eq_mul_of_same_quotient (f := I.quotient) I.isQuotient.1 z (toUnit Z ≫ n)
    (hz.trans (Category.assoc _ _ _).symm)

end NormalizerFibres

section CentralizerRoots

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots adjointWeightVectors)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Pinning (SplitBorelPair)
open SubtorusCentralizer (IsCentralizer)
open Unipotent (closedSubgroupAlgebraicGroup)

open private lattice_torus_of_split maximal_torus_in_intermediate_group
  character_eq_of_common_weight_vector from LinearAlgebraicGroups.RootData.RankOneFlag
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private restrictSubgroup inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private zeroWeightVectors_iff_centralizes from LinearAlgebraicGroups.RootData.CharacterPairing
open private differential_injective map_weightVector weightVector_of_map
  from LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option backward.isDefEq.respectTransparency false

private theorem commonKernelCentralizer (P : SplitBorelPair k) {a b : Character P.T.group}
    (S : KernelSubtorus a b) :
    ∃ (C : ClosedSubgroup P.G.val) (j : P.T.group ⟶ C.group)
      (hj : j ≫ C.inclusion = P.T.inclusion),
      IsCentralizer (subgroupOfSubgroup P.T S.subgroup) C ∧
      IsReductive (closedSubgroupAlgebraicGroup C) ∧
      RankOneFlag.IsGeometricallyMaximal (restrictSubgroup P.T C j hj) := by
  let S' := subgroupOfSubgroup P.T S.subgroup
  obtain ⟨C, hC, hred⟩ :=
    Reductive.SubtorusCentralizer.centralizerReductive P.G P.reductive P.T S'
      (lattice_torus_of_split P.split) S.torus ⟨S.subgroup.inclusion, rfl⟩ P.maximal
  obtain ⟨hcomm, _⟩ := RootData.CharacterPairing.perfectCharacterPairing P.T.group P.split
  letI := hcomm
  have hcentral : Centralizes S'.inclusion P.T.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Z t s
    exact (show Commute t (s ≫ S.subgroup.inclusion.hom.hom) from mul_comm _ _).map
      (IsMonHom.monoidHom P.T.inclusion.hom.hom Z)
  obtain ⟨i, hi⟩ := (hC _ _).mp hcentral
  obtain ⟨j, hj⟩ := factor_group_through_subgroup C P.T.inclusion i hi
  exact ⟨C, j, hj, hC, hred, maximal_torus_in_intermediate_group hj P.maximal⟩

set_option maxHeartbeats 800000 in
private theorem centralizer_absoluteRoots (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) {S : ClosedSubgroup T.group} (hS : IsSplitTorus S.group)
    {C : ClosedSubgroup G.val} (hC : IsCentralizer (subgroupOfSubgroup T S) C)
    {j : T.group ⟶ C.group} (hj : j ≫ C.inclusion = T.inclusion)
    (χ : Character T.group) :
    χ ∈ absoluteRoots (restrictSubgroup T C j hj) ↔
      χ ∈ absoluteRoots T ∧ S.inclusion ≫ χ = 1 := by
  let B := restrictSubgroup T C j hj
  let S' := subgroupOfSubgroup T S
  letI := C.isClosedImmersion
  letI : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : IsAffine G.val.X.left := G.property.1
  have hSaff : IsAffine S'.group.X.left := by
    letI := S'.isClosedImmersion
    exact isAffine_of_isAffineHom S'.inclusion.hom.hom.left
  have hT : B.inclusion ≫ C.inclusion = (Iso.refl T.group).hom ≫ T.inclusion :=
    hj.trans (Category.id_comp _).symm
  have hid : (Iso.refl T.group).hom ≫ χ = χ := Category.id_comp _
  have hinj := differential_injective C.inclusion
  have restrictWeight {v : Lie k G.val} (hv : v ∈ adjointWeightVectors T χ) :
      v ∈ adjointWeightVectors S' (S.inclusion ≫ χ) := by
    intro R s
    exact hv R (s ≫ S.inclusion.hom.hom)
  change χ ∈ absoluteRoots B ↔ _
  constructor
  · rintro ⟨hne, v, hv, hvne⟩
    let u := mapPointKernel C.inclusion v
    have hu : u ∈ adjointWeightVectors T χ :=
      map_weightVector (T := B) (S := T) C.inclusion (Iso.refl T.group) hT
        (χ := χ) (v := v)
        ((congrArg (fun ψ : Character T.group => v ∈ adjointWeightVectors B ψ) hid).mpr hv)
    have hune : u ≠ 0 := by
      intro he
      apply hvne
      apply hinj
      exact he.trans (map_zero _).symm
    have hcentral : Centralizes S'.inclusion u.toMul.val :=
      (hC _ _).mpr ⟨v.toMul.val, rfl⟩
    have hzero := (zeroWeightVectors_iff_centralizes S' hSaff u).mpr hcentral
    exact ⟨⟨hne, u, hu, hune⟩,
      character_eq_of_common_weight_vector G S' hS hune (restrictWeight hu) hzero⟩
  · rintro ⟨⟨hne, v, hv, hvne⟩, hχ⟩
    have hzero := restrictWeight hv
    rw [hχ] at hzero
    obtain ⟨z, hz⟩ := (hC _ _).mp ((zeroWeightVectors_iff_centralizes S' hSaff v).mp hzero)
    have hzreduce : reduceTangentPoints C.group z = 1 := by
      apply (cancel_mono C.inclusion.hom.hom).mp
      change ((testSpec k).map (dualReduction k).op ≫ z) ≫ C.inclusion.hom.hom =
        (1 : GroupPoints C.group (CommAlgCat.of k k)) ≫ C.inclusion.hom.hom
      rw [Category.assoc, hz, MonObj.one_comp]
      exact v.toMul.property
    let w : Lie k C.group := ⟨z, hzreduce⟩
    have hw : mapPointKernel C.inclusion w = v := Subtype.ext hz
    have hwne : w ≠ 0 := by
      intro hwzero
      apply hvne
      rw [← hw, hwzero, map_zero]
    refine ⟨hne, w, ?_, hwne⟩
    have hv' := weightVector_of_map (T := B) (S := T) C.inclusion (Iso.refl T.group).hom hT
      (v := w) (χ := χ) (hw.symm ▸ hv)
    exact (congrArg (fun ψ : Character T.group => w ∈ adjointWeightVectors B ψ) hid).mp hv'

end CentralizerRoots

section ConjugationTransport

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open Pinning (RootCoordinate)
open RootGroups (HasScalarAction IsRootSubgroup rootPoint)

open private conjugation conjugationIso conjugation_apply
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupIso_of_same from LinearAlgebraicGroups.RootData.RankOneFlag
open _root_.LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private rootPoint_eq rootPoint_comp tangent_weight_of_scalarAction
  normalizes_of_point_conjugation from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false

private theorem scalarAction_map {G H : GroupScheme k} {T : ClosedSubgroup G}
    {S : ClosedSubgroup H} (e : T.group ≅ S.group)
    {f : G ⟶ H} (hef : T.inclusion ≫ f = e.hom ≫ S.inclusion)
    {α : Character T.group} {β : Character S.group} (hα : e.inv ≫ α = β)
    {x : A.group ⟶ G} (hx : HasScalarAction T α x) :
    HasScalarAction S β (x ≫ f) := by
  intro R t u
  let s : GroupPoints T.group R := t ≫ e.inv.hom.hom
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 S.group.X :=
    (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
  have htorus : (s ≫ T.inclusion.hom.hom) ≫ f.hom.hom = t ≫ S.inclusion.hom.hom := by
    rw [Category.assoc, show T.inclusion.hom.hom ≫ f.hom.hom =
      e.hom.hom.hom ≫ S.inclusion.hom.hom from (Grp.forget _).congr_map hef]
    change (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom ≫ S.inclusion.hom.hom = _
    rw [Category.assoc, ← Category.assoc e.inv.hom.hom, he, Category.id_comp]
  have hval : characterValue α R s = characterValue β R t := by
    have hs : s ≫ α.hom.hom = t ≫ (e.inv ≫ α).hom.hom :=
      Category.assoc t e.inv.hom.hom α.hom.hom
    unfold characterValue
    rw [← hα, hs]
  have h := congrArg (fun p : GroupPoints G R => p ≫ f.hom.hom) (hx R s u)
  dsimp only at h
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, htorus, hval,
    ← rootPoint_comp, ← rootPoint_comp] at h
  exact h

private theorem rootSubgroup_of_coordinate {G : GroupScheme k} {T U : ClosedSubgroup G}
    {α : Character T.group} (x : RootCoordinate A T U α)
    (hu : Smooth U.group.X.hom) (hs : RankOneFlag.IsSplitAdditive U.group) :
    IsRootSubgroup T U α := by
  refine ⟨hu, hs, ?_, tangent_weight_of_scalarAction T U α A x.val x.property⟩
  apply normalizes_of_point_conjugation
  intro R t p
  let q : GroupPoints A.group R := p ≫ x.val.inv.hom.hom
  obtain ⟨u, hu⟩ := (additivePoints A R).surjective q
  have hp : (additivePoints A R u) ≫ x.val.hom.hom.hom = p := by
    rw [hu]
    change (p ≫ x.val.inv.hom.hom) ≫ x.val.hom.hom.hom = p
    rw [Category.assoc, show x.val.inv.hom.hom ≫ x.val.hom.hom.hom = 𝟙 _ from
      (Grp.forget (SchemeOver k)).congr_map x.val.inv_hom_id, Category.comp_id]
  let v := characterValue α R t * u
  refine ⟨additivePoints A R v ≫ x.val.hom.hom.hom, ?_⟩
  have h := x.property R t u
  dsimp only at h
  rw [rootPoint_eq, rootPoint_eq] at h
  simpa only [Grp.comp_hom_hom, ← Category.assoc, hp] using h.symm

private theorem pullback_conjugation {G : GroupScheme k} (T : ClosedSubgroup G)
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} (e : T.group ≅ T.group)
    (he : (e.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ n) * T.inclusion.hom.hom * (toUnit T.group.X ≫ n)⁻¹) :
    T.inclusion ≫ (conjugationIso n).hom = e.hom ≫ T.inclusion := by
  apply Grp.hom_ext
  change T.inclusion.hom.hom ≫ (conjugationIso n).hom.hom.hom = _
  rw [show (conjugationIso n).hom.hom.hom = (conjugation n).hom.hom from rfl,
    conjugation_apply]
  exact he.symm

/-- A rational normalizer representative carries an equivariant root
coordinate isomorphically to the root with the moved character. -/
private theorem exists_transportedRootCoordinate (P : PinnedGroup A) (a b : Root P.pair.T)
    {n : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X}
    (hm : MovesCharacter P.pair.T n a.val b.val)
    (x : RootCoordinate A P.pair.T (P.roots a).val a.val) :
    ∃ y : RootCoordinate A P.pair.T (P.roots b).val b.val,
      TransportsCoordinate n (x.val.hom ≫ (P.roots a).val.inclusion)
        (y.val.hom ≫ (P.roots b).val.inclusion) := by
  obtain ⟨e, he, heab⟩ := hm
  let C := conjugationIso n
  let U := (P.roots a).val
  let V := transportSubgroup C U
  have hV : HasScalarAction P.pair.T b.val (x.val.hom ≫ V.inclusion) := by
    change HasScalarAction P.pair.T b.val (x.val.hom ≫ U.inclusion ≫ C.hom)
    rw [← Category.assoc]
    exact scalarAction_map e (pullback_conjugation _ e he) heab x.property
  have hU : IsRootSubgroup P.pair.T U a.val := (P.roots a).property
  have hVroot := rootSubgroup_of_coordinate (⟨x.val, hV⟩ :
    RootCoordinate A P.pair.T V b.val) hU.1 hU.2.1
  obtain ⟨W, _, _, _, _, hW⟩ := ((RootData.RootGroups.rootSubgroups
    P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal).2 b.val b.property).2.2
  obtain ⟨f, hf⟩ := subgroupIso_of_same (hW V hVroot)
  obtain ⟨g, hg⟩ := subgroupIso_of_same (hW (P.roots b).val (P.roots b).property)
  let y := x.val ≪≫ f.symm ≪≫ g
  have hy : y.hom ≫ (P.roots b).val.inclusion = x.val.hom ≫ V.inclusion := by
    simp only [y, Iso.trans_hom, Iso.symm_hom, Category.assoc, hg, ← hf, Iso.inv_hom_id_assoc]
  refine ⟨⟨y, by rw [hy]; exact hV⟩, ?_⟩
  intro R u
  rw [hy]
  change _ = rootPoint ((x.val.hom ≫ U.inclusion) ≫ C.hom) R u
  rw [rootPoint_comp]
  exact (conjugation_apply n (rootPoint (x.val.hom ≫ U.inclusion) R u)).symm

end ConjugationTransport

section RootInCentralizer

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Pinning (RootCoordinate)
open RootGroups (HasScalarAction IsRootSubgroup rootPoint)
open SubtorusCentralizer (IsCentralizer)

open private centralizes_iff_affine from LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private factor_group_through_subgroup from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open _root_.LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private rootPoint_eq rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private characterValue_one from LinearAlgebraicGroups.RootData.CharacterPairing
open private restrictSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false

/-- A scalar-equivariant root map factors through the centralizer when its
character restricts trivially to the given subtorus. -/
private theorem rootCoordinate_factorsCentralizer {G : GroupScheme k}
    (T : ClosedSubgroup G) (S : ClosedSubgroup T.group)
    {C : ClosedSubgroup G} (hC : IsCentralizer (subgroupOfSubgroup T S) C)
    {χ : Character T.group} (hχ : S.inclusion ≫ χ = 1)
    {x : A.group ⟶ G} (hx : HasScalarAction T χ x) :
    ∃ f : A.group ⟶ C.group, f ≫ C.inclusion = x := by
  let S' := subgroupOfSubgroup T S
  have hcentral : Centralizes S'.inclusion x.hom.hom := by
    apply (centralizes_iff_affine _ _).mpr
    intro R p s
    obtain ⟨b, rfl⟩ := (additivePoints A R).surjective p
    let t : GroupPoints T.group R := s ≫ S.inclusion.hom.hom
    have hvalue : characterValue χ R t = 1 := by
      change characterValue (S.inclusion ≫ χ) R s = _
      rw [hχ, characterValue_one]
    have h := hx R t b
    rw [hvalue, one_mul] at h
    change Commute (additivePoints A R b ≫ x.hom.hom) (t ≫ T.inclusion.hom.hom)
    rw [← rootPoint_eq]
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  obtain ⟨i, hi⟩ := (hC _ _).mp hcentral
  exact factor_group_through_subgroup C x i hi

/-- Restriction along a subgroup inclusion carrying the full torus reflects
the scalar action. -/
private theorem scalarAction_of_inclusion {G : GroupScheme k} {T C : ClosedSubgroup G}
    {j : T.group ⟶ C.group} (hj : j ≫ C.inclusion = T.inclusion)
    {χ : Character T.group} {x : A.group ⟶ C.group}
    (hx : HasScalarAction T χ (x ≫ C.inclusion)) :
    HasScalarAction (restrictSubgroup T C j hj) χ x := by
  intro R t u
  letI := C.isClosedImmersion
  letI : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono C.inclusion.hom.hom).mp
  let g : GroupPoints C.group R := t ≫ j.hom.hom
  have hg : g ≫ C.inclusion.hom.hom = t ≫ T.inclusion.hom.hom := by
    change (t ≫ j.hom.hom) ≫ C.inclusion.hom.hom = _
    rw [Category.assoc, show j.hom.hom ≫ C.inclusion.hom.hom = T.inclusion.hom.hom from
      (Grp.forget _).congr_map hj]
  change (g * rootPoint x R u * g⁻¹) ≫ C.inclusion.hom.hom =
    rootPoint x R (characterValue χ R t * u) ≫ C.inclusion.hom.hom
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hg,
    ← rootPoint_comp, ← rootPoint_comp]
  exact hx R t u

private theorem rootCoordinate_restrict {G : GroupScheme k} {T : ClosedSubgroup G}
    (S : ClosedSubgroup T.group) {C : ClosedSubgroup G} {j : T.group ⟶ C.group}
    (hj : j ≫ C.inclusion = T.inclusion)
    (hC : IsCentralizer (subgroupOfSubgroup T S) C)
    {χ : Character T.group} {U : ClosedSubgroup G} (hχ : S.inclusion ≫ χ = 1)
    (x : RootCoordinate A T U χ) (hU : IsRootSubgroup T U χ) :
    ∃ (i : U.group ⟶ C.group) (hi : i ≫ C.inclusion = U.inclusion),
      let V := restrictSubgroup U C i hi
      IsRootSubgroup (restrictSubgroup T C j hj) V χ ∧
      HasScalarAction (restrictSubgroup T C j hj) χ (x.val.hom ≫ V.inclusion) := by
  obtain ⟨f, hf⟩ := rootCoordinate_factorsCentralizer T S hC hχ x.property
  let i := x.val.inv ≫ f
  have hi : i ≫ C.inclusion = U.inclusion := by
    simp only [i, Category.assoc, hf, Iso.inv_hom_id_assoc]
  have hinc : (x.val.hom ≫ i) ≫ C.inclusion = x.val.hom ≫ U.inclusion := by
    rw [Category.assoc, hi]
  have hscalar := scalarAction_of_inclusion hj (x := x.val.hom ≫ i) (by
    rw [hinc]
    exact x.property)
  exact ⟨i, hi, rootSubgroup_of_coordinate ⟨x.val, hscalar⟩ hU.1 hU.2.1, hscalar⟩

end RootInCentralizer

section CorootUniqueness

open CategoryTheory.MonoidalCategory
open AbstractPairing (Datum)
open CharacterDescent (Character)
open CharacterPairing (pairing)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (CorootReflection)

open private root_determines_coroot latticeAction quotientLabel quotientLabel_conjugates
  pointConj constantPoint conjugation_unique from LinearAlgebraicGroups.RootData.AbstractPairing
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing

set_option backward.isDefEq.respectTransparency false

/-- A linked rank-one reflection on the full torus has the coroot of the
actual datum. Use the finite normalizer action to compare its reflection to
the linked reflection witnessing the attached coroot. -/
private theorem coroot_eq_of_reflection {G : AffineAlgebraicGroup k} (hG : IsReductive G)
    {T : ClosedSubgroup G.val} (hsplit : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) [IsCommMonObj T.group.X]
    (D : Datum T) (a : Root T) {x y : A.group ⟶ G.val}
    (r : CorootReflection T a.val x y) :
    r.coroot = Additive.toMul (D.rootDatum.coroot a) := by
  letI := D.freeCharacters
  obtain ⟨N, _, _, W, q, hN, _, _, _, _, _, hsplitW⟩ :=
    Reductive.WeylScheme.weylScheme G hG T (isTorus_of_split hsplit) hmax
  obtain ⟨⟨I⟩, _⟩ := hsplitW hsplit
  letI := I.finite
  let ρ := latticeAction I
  let B := D.rootDatum.toLinearMap
  have reflect {L : AdditiveLine k} {p q : L.group ⟶ G.val}
      (s : CorootReflection T a.val p q) :
      ∃ w, ∀ v : Additive (Character T.group),
        ρ w v = v - B v (Additive.ofMul s.coroot) • Additive.ofMul a.val := by
    obtain ⟨n, hn⟩ := (hN _ _).mp s.normalizes
    let w := quotientLabel I n
    have he : s.conjugation = I.conjugation w := by
      apply conjugation_unique T
      exact s.conjugates.trans (by
        simpa only [w, hn, pointConj, constantPoint] using (quotientLabel_conjugates I n).symm)
    refine ⟨w, fun v => ?_⟩
    let χ : Character T.group := Additive.toMul v
    change Additive.ofMul (w.val χ) =
      Additive.ofMul χ - D.rootDatum.toLinearMap (Additive.ofMul χ) (Additive.ofMul s.coroot) •
        Additive.ofMul a.val
    rw [I.characterAction, ← he, s.reflection, D.pairing_eq, sub_eq_add_neg, ← neg_smul]
    rfl
  have hp {L : AdditiveLine k} {p q : L.group ⟶ G.val}
      (s : CorootReflection T a.val p q) : B (Additive.ofMul a.val) (Additive.ofMul s.coroot) = 2 :=
    (D.pairing_eq a.val s.coroot).trans s.root_pairing
  obtain ⟨C, c, _, _, P, M, _, Q, F, J, L, xp, xn, _, _, _, _, s, hs⟩ := D.attached a
  obtain ⟨w, hw⟩ := reflect r
  obtain ⟨v, hv⟩ := reflect s
  exact (Additive.ofMul.injective (root_determines_coroot ρ B (hp r) (hp s) hw hv)).trans hs

end CorootUniqueness
section CentralizerCoroots

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open AbstractPairing (Datum)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots)
open RootGroups (CorootReflection rankOneWord)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open Unipotent (closedSubgroupAlgebraicGroup)

open private normalizes_of_conjugates_self restrictSubgroup
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private rankOneWord_comp from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false

private theorem reflection_of_fullTorusInclusion {G : GroupScheme k} {T C : ClosedSubgroup G}
    {j : T.group ⟶ C.group} (hj : j ≫ C.inclusion = T.inclusion)
    {χ : Character T.group} {x y : A.group ⟶ C.group}
    (r : CorootReflection (restrictSubgroup T C j hj) χ x y) :
    ∃ s : CorootReflection T χ (x ≫ C.inclusion) (y ≫ C.inclusion),
      s.coroot = r.coroot := by
  let F := Grp.forget (SchemeOver k)
  let f := C.inclusion.hom.hom
  let n := r.representative ≫ f
  have htorus : j.hom.hom ≫ f = T.inclusion.hom.hom := F.congr_map hj
  have hn : (r.conjugation.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ n) * T.inclusion.hom.hom * (toUnit T.group.X ≫ n)⁻¹ := by
    have h := congrArg (fun p : T.group.X ⟶ C.group.X => p ≫ f) r.conjugates
    change (r.conjugation.hom.hom.hom ≫ j.hom.hom) ≫ f =
      ((toUnit T.group.X ≫ r.representative) * j.hom.hom *
        (toUnit T.group.X ≫ r.representative)⁻¹) ≫ f at h
    rw [Category.assoc, htorus, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
      Category.assoc] at h
    change r.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom = _
    simpa only [n, Category.assoc, htorus] using h
  refine ⟨⟨r.coroot, n, normalizes_of_conjugates_self T ⟨r.conjugation, hn⟩, ?_, ?_,
    r.conjugation, hn, r.reflection, r.root_pairing⟩, rfl⟩
  · have h := congrArg (fun p => p ≫ f) r.representative_word
    simpa only [n, f, Category.assoc, rankOneWord_comp] using h
  · intro R u
    have h := congrArg (fun p : GroupPoints C.group R => p ≫ f) (r.coroot_word R u)
    change (cocharacterPoint r.coroot R u ≫ j.hom.hom) ≫ f =
      (rankOneWord x y R u * (rankOneWord x y R 1)⁻¹) ≫ f at h
    rw [Category.assoc, htorus, MonObj.mul_comp, GrpObj.inv_comp] at h
    simpa only [f, rankOneWord_comp] using h

/-- The coroot in the centralizer is the same cocharacter of the full
torus, since the local linked root word acts as a linked word in the ambient group. -/
private theorem centralizer_coroot {G : AffineAlgebraicGroup k} (hG : Specs.GeometricRadicals.IsReductive G)
    {T C : ClosedSubgroup G.val} (hsplit : Specs.GeometricRadicals.IsSplitTorus T.group)
    (hmax : RankOneFlag.IsGeometricallyMaximal T) {j : T.group ⟶ C.group}
    (hj : j ≫ C.inclusion = T.inclusion) [IsCommMonObj T.group.X]
    [IsCommMonObj (restrictSubgroup T C j hj).group.X] (D : Datum T)
    (E : Datum (G := closedSubgroupAlgebraicGroup C) (restrictSubgroup T C j hj))
    (a : Root (G := closedSubgroupAlgebraicGroup C) (restrictSubgroup T C j hj))
    (ha : a.val ∈ absoluteRoots T) :
    Additive.toMul (E.rootDatum.coroot a) = Additive.toMul (D.rootDatum.coroot ⟨a.val, ha⟩) := by
  obtain ⟨L, c, _, _, P, M, _, Q, K, B, A', x, y, _, _, _, _, r, hr⟩ := E.attached a
  obtain ⟨s, hs⟩ := reflection_of_fullTorusInclusion (A := A') hj r
  exact hr.symm.trans (hs.symm.trans (coroot_eq_of_reflection hG hsplit hmax D ⟨a.val, ha⟩ s))

end CentralizerCoroots

section TransportComposition

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open Pinning (SimpleRoot)
open RootGroups (rootPoint)

open _root_.LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false

private theorem transport_compose {G : GroupScheme k} {z w : 𝟙_ (SchemeOver k) ⟶ G.X}
    {x y q : A.group ⟶ G} (hw : TransportsCoordinate w x y)
    (hz : TransportsCoordinate z y q) : TransportsCoordinate (z * w) x q := by
  intro R t
  have h₁ := hw R t
  have h₂ := hz R t
  dsimp only at h₁ h₂ ⊢
  rw [← h₂, ← h₁, MonObj.comp_mul]
  group

private theorem transport_precompose {G : GroupScheme k} {z : 𝟙_ (SchemeOver k) ⟶ G.X}
    {x y : A.group ⟶ G} (h : TransportsCoordinate z x y) (p : A.group ⟶ A.group) :
    TransportsCoordinate z (p ≫ x) (p ≫ y) := by
  intro R t
  obtain ⟨u, hu⟩ := (additivePoints A R).surjective
    ((additivePoints A R t) ≫ p.hom.hom)
  have h' := h R u
  dsimp only at h'
  simpa only [rootPoint_eq, hu, Grp.comp_hom_hom, Category.assoc] using h'

private def correspondingSimple (h : Compatible P Q D E d τ) (i : SimpleRoot P.pair) :
    SimpleRoot Q.pair :=
  ⟨d i.val, (E.simple_iff _).mp ((h.simple _).mp ((D.simple_iff _).mpr i.property))⟩

private noncomputable def comparedSimplePin (h : Compatible P Q D E d τ)
    (i : SimpleRoot P.pair) :
    (P.roots i.val).val.group ≅ (Q.roots (d i.val)).val.group :=
  (P.pin i).val.symm ≪≫ (Q.pin (correspondingSimple h i)).val

/-- Agreement for transports between simple pins suffices for agreement of
every transport from a simple pin to an arbitrary root. -/
private theorem exists_comparisonFromSimpleTransports
    (h : Compatible P Q D E d τ) (N : Normalizers P Q D E d τ)
    (hSimple : ∀ (i j : SimpleRoot P.pair) (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X),
      MovesCharacter P.pair.T (z ≫ N.source.inclusion.hom.hom) i.val.val j.val.val →
        ∃ x : A.group ≅ (P.roots j.val).val.group,
          TransportsCoordinate (z ≫ N.source.inclusion.hom.hom)
            ((P.pin i).val.hom ≫ (P.roots i.val).val.inclusion)
            (x.hom ≫ (P.roots j.val).val.inclusion) ∧
          TransportsCoordinate (z ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom)
            ((Q.pin (correspondingSimple h i)).val.hom ≫ (Q.roots (d i.val)).val.inclusion)
            ((x ≪≫ comparedSimplePin h j).hom ≫ (Q.roots (d j.val)).val.inclusion)) :
    ∃ e : RootIsomorphisms P Q d, MatchesTransports N e := by
  classical
  choose i n hn using exists_transportingRepresentative N
  have xexists (a : Root P.pair.T) :=
    exists_transportedRootCoordinate P (i a).val a (hn a) (P.pin (i a))
  have yexists (a : Root P.pair.T) :=
    exists_transportedRootCoordinate Q (d (i a).val) (d a)
      (movesCharacter_map h N (n a) (i a).val a (hn a)) (Q.pin (correspondingSimple h (i a)))
  choose x hx using xexists
  choose y hy using yexists
  let e : RootIsomorphisms P Q d := fun a => (x a).val.symm ≪≫ (y a).val
  refine ⟨e, fun a => ⟨i a, n a, hn a⟩, ?_⟩
  intro a p q hp z hz
  have hq : q = correspondingSimple h p := Subtype.ext hp.symm
  subst q
  let w := (n a)⁻¹ * z
  have hw : MovesCharacter P.pair.T (w ≫ N.source.inclusion.hom.hom) p.val.val (i a).val.val := by
    change MovesCharacter _ (((n a)⁻¹ * z) ≫ _) _ _
    rw [MonObj.mul_comp, GrpObj.inv_comp]
    exact movesCharacter_mul hz (movesCharacter_inverse (hn a))
  obtain ⟨v, hv, hv'⟩ := hSimple p (i a) w hw
  let r := v ≪≫ (P.pin (i a)).val.symm
  have hr : r.hom ≫ (P.pin (i a)).val.hom = v.hom := by
    simp only [r, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have src := transport_precompose (hx a) r.hom
  have trg := transport_precompose (hy a) r.hom
  have Hs : TransportsCoordinate (n a ≫ N.source.inclusion.hom.hom)
      (v.hom ≫ (P.roots (i a).val).val.inclusion) ((r ≪≫ (x a).val).hom ≫ (P.roots a).val.inclusion) := by
    simpa only [Iso.trans_hom, Category.assoc, ← hr] using src
  have Ht : TransportsCoordinate (n a ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom)
      ((v ≪≫ comparedSimplePin h (i a)).hom ≫ (Q.roots (d (i a).val)).val.inclusion)
      ((r ≪≫ (y a).val).hom ≫ (Q.roots (d a)).val.inclusion) := by
    simpa only [r, comparedSimplePin, Iso.trans_hom, Iso.symm_hom, Category.assoc] using trg
  have hzw : n a * w = z := by
    dsimp only [w]
    group
  refine ⟨r ≪≫ (x a).val, ?_, ?_⟩
  · simpa only [← MonObj.mul_comp, hzw] using transport_compose hv Hs
  · have hxy : ((r ≪≫ (x a).val) ≪≫ e a).hom = (r ≪≫ (y a).val).hom := by
      simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [hxy]
    let f := N.hom ≫ N.target.inclusion
    have hmul : ((n a ≫ f.hom.hom) * (w ≫ f.hom.hom)) = z ≫ f.hom.hom := by
      rw [← MonObj.mul_comp, hzw]
    have he := transport_compose hv' Ht
    change TransportsCoordinate ((n a ≫ f.hom.hom) * (w ≫ f.hom.hom)) _ _ at he
    rw [hmul] at he
    exact he

end TransportComposition

section SubsystemConstruction

open AbstractPairing (Datum)
open BorelsAndChambers (IsRegular IsPositiveSystem subgroupRoots positiveRoots)
open CharacterDescent (Character)
open CharacterPairing (absoluteRoots pairing)
open Pinning (IsSimple RootCoordinate SimpleRoot SplitBorelPair)
open RootGroups (Proportional)
open Unipotent (closedSubgroupAlgebraicGroup)

open private restrictSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open Additive

set_option backward.isDefEq.respectTransparency false

private theorem base_card_of_saturated_characters {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (D : Datum T)
    (b : D.rootDatum.Base) (a c : Root T) (hac : ¬ Proportional a.val c.val)
    (hspan : ∀ r : Root T, InSaturatedSpan a.val c.val r.val) :
    b.support.card = 2 := by
  letI := D.reduced
  have hpos : a ≠ c := by
    rintro rfl
    exact hac ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩
  have hneg : D.rootDatum.root a ≠ -D.rootDatum.root c := by
    rw [D.root_eq, D.root_eq]
    intro h
    have he : a.val = c.val⁻¹ := h
    exact hac ⟨1, -1, one_ne_zero, neg_ne_zero.mpr one_ne_zero, by simp only [zpow_one, zpow_neg, he]⟩
  apply base_card_of_two_root_span D.rootDatum b a c
    (RootPairing.IsReduced.linearIndependent D.rootDatum hpos hneg)
  intro r
  obtain ⟨m, p, q, hm, h⟩ := hspan r
  refine ⟨m, p, q, hm, ?_⟩
  simpa only [D.root_eq, ofMul_mul, ofMul_zpow] using congrArg ofMul h

set_option maxHeartbeats 1000000 in
/-- For any independent pair, the centralizer has the inherited full torus,
roots, and coroots. Its positive system is the restriction of the given
Borel's, and its simple pins may be prescribed on the ambient root groups. -/
private theorem exists_subsystem (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (a b : Root P.pair.T) (hab : ¬ Proportional a.val b.val)
    (coords : ∀ r : Root P.pair.T, RootCoordinate A P.pair.T (P.roots r).val r.val)
    (kernel : KernelSubtorus a.val b.val) :
    ∃ S : Subsystem P D a b,
      (∀ r, r ∈ subgroupRoots S.localGroup.pair.T S.localGroup.pair.B ↔
        S.roots r ∈ subgroupRoots P.pair.T P.pair.B) ∧
      ∀ i : SimpleRoot S.localGroup.pair,
        ((S.localGroup.pin i).val.hom ≫ (S.localGroup.roots i.val).val.inclusion) ≫
          S.groupIso.hom ≫ S.closed.inclusion =
        (coords (S.roots i.val)).val.hom ≫ (P.roots (S.roots i.val)).val.inclusion := by
  classical
  obtain ⟨C, j, hj, hC, hred, hmax⟩ := commonKernelCentralizer P.pair kernel
  let H := closedSubgroupAlgebraicGroup C
  let T : ClosedSubgroup H.val := restrictSubgroup P.pair.T C j hj
  have hroots (χ : Character P.pair.T.group) :
      χ ∈ absoluteRoots T ↔ χ ∈ absoluteRoots P.pair.T ∧
        kernel.subgroup.inclusion ≫ χ = 1 :=
    centralizer_absoluteRoots P.pair.G P.pair.T kernel.split hC hj χ
  let ambientRoot : Root T ↪ Root P.pair.T :=
    ⟨fun r => ⟨r.val, ((hroots r.val).mp r.property).1⟩,
      fun r s h => Subtype.ext (congrArg (fun q : Root P.pair.T => q.val) h)⟩
  have hχ (r : Root T) : kernel.subgroup.inclusion ≫ (ambientRoot r).val = 1 :=
    ((hroots r.val).mp r.property).2
  obtain ⟨c, _, hc, _, hB⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.pair.G P.pair.reductive P.pair.T
      P.pair.split P.pair.maximal).1 P.pair.B P.pair.borel P.pair.containsTorus
  have hregular : IsRegular T c := fun r => hc (ambientRoot r)
  have hsystem : IsPositiveSystem T (positiveRoots T c) :=
    (RootData.BorelsAndChambers.positiveSystemsFromCocharacters H hred T P.pair.split hmax
      (positiveRoots T c)).mpr ⟨c, hregular, rfl⟩
  obtain ⟨B, hBloc, hTB, hBroot, _⟩ :=
    ((RootData.BorelsAndChambers.borelsThroughT H hred T P.pair.split hmax).2 _).mp hsystem
  let localPair : SplitBorelPair k := ⟨H, hred, T, P.pair.split, hmax, B, hBloc, hTB⟩
  have hrestriction (r : Root T) :=
    rootCoordinate_restrict kernel.subgroup hj hC (hχ r) (coords (ambientRoot r)) (P.roots (ambientRoot r)).property
  choose i hi hp using hrestriction
  let groups : OrderedRootProducts.RootSubgroupFamily localPair.T := fun r =>
    ⟨restrictSubgroup (P.roots (ambientRoot r)).val C (i r) (hi r), (hp r).1⟩
  let localPinned : PinnedGroup A :=
    ⟨localPair, groups, fun r => ⟨(coords (ambientRoot r.val)).val, (hp r.val).2⟩⟩
  obtain ⟨hcomm, ⟨localDatum⟩⟩ := RootData.AbstractPairing.abstractPairing H hred T P.pair.split hmax
  letI := hcomm
  letI := localDatum.finiteRoots
  letI := localDatum.freeCharacters
  letI := localDatum.finiteCharacters
  letI := localDatum.reduced
  let f := Specs.SimpleRoots.evaluate localDatum c
  have hf (r : Root T) : f (localDatum.rootDatum.root r) = pairing T.group r.val c := by
    change localDatum.rootDatum.toLinearMap (localDatum.rootDatum.root r) (Additive.ofMul c) = _
    rw [localDatum.root_eq, localDatum.pairing_eq]
  obtain ⟨localBase, hbase⟩ := RootData.SimpleRoots.baseFor localDatum.rootDatum f
    (fun r => (hf r).symm ▸ hregular r)
  have hpositive : Specs.SimpleRoots.positive localDatum.rootDatum f = subgroupRoots T B := by
    rw [hBroot]
    ext r
    change 0 < f (localDatum.rootDatum.root r) ↔ 0 < pairing T.group r.val c
    rw [hf]
  let E : AttachedDatum localPair := ⟨hcomm, localDatum, localBase, fun r => by
    rw [hbase.simple_iff, hpositive]
    unfold IsSimple
    simp only [localDatum.root_eq]
    rfl⟩
  letI := D.comm
  letI := E.comm
  have hrank : E.base.support.card = 2 := by
    let a' : Root T := ⟨a.val, (hroots a.val).mpr ⟨a.property, kernel.left_trivial⟩⟩
    let b' : Root T := ⟨b.val, (hroots b.val).mpr ⟨b.property, kernel.right_trivial⟩⟩
    exact base_card_of_saturated_characters E.datum E.base a' b' hab
      (fun r => (kernel.annihilator _).mp (hχ r))
  have hrange : Set.range ambientRoot = {r | InSaturatedSpan a.val b.val r.val} := by
    ext r
    constructor
    · rintro ⟨p, rfl⟩
      exact (kernel.annihilator _).mp (hχ p)
    · intro h
      let p : Root T := ⟨r.val,
        (hroots r.val).mpr ⟨r.property, (kernel.annihilator _).mpr h⟩⟩
      exact ⟨p, Subtype.ext rfl⟩
  let S : Subsystem P D a b :=
    { kernel := kernel
      localGroup := localPinned
      closed := C
      groupIso := Iso.refl _
      centralizes := hC
      torus := Iso.refl _
      torus_comm := by
        change 𝟙 _ ≫ j ≫ 𝟙 _ ≫ C.inclusion = P.pair.T.inclusion
        simpa only [Category.id_comp] using hj
      datum := E
      rank := hrank
      roots := ambientRoot
      root_eq := fun r => Category.id_comp _
      root_range := hrange
      coroot_eq := fun r => by
        change Additive.toMul (D.datum.rootDatum.coroot (ambientRoot r)) ≫ 𝟙 _ =
          Additive.toMul (E.datum.rootDatum.coroot r)
        rw [Category.comp_id]
        exact (centralizer_coroot P.pair.reductive P.pair.split P.pair.maximal
          hj D.datum E.datum r (ambientRoot r).property).symm
      positive := fun r => (hbase.positive_iff r).trans (by rw [hpositive])
      rootIso := fun _ => Iso.refl _
      root_comm := fun r => by
        change i r ≫ 𝟙 _ ≫ C.inclusion = 𝟙 _ ≫ (P.roots (ambientRoot r)).val.inclusion
        simpa only [Category.id_comp] using hi r }
  refine ⟨S, ?_, ?_⟩
  · intro r
    change r ∈ subgroupRoots T B ↔ ambientRoot r ∈ subgroupRoots P.pair.T P.pair.B
    rw [hBroot, hB]
    rfl
  · intro r
    change ((coords (ambientRoot r.val)).val.hom ≫ i r.val) ≫ 𝟙 _ ≫ C.inclusion =
      (coords (ambientRoot r.val)).val.hom ≫ (P.roots (ambientRoot r.val)).val.inclusion
    rw [Category.id_comp, Category.assoc, hi r.val]

end SubsystemConstruction

section NormalizerWeylAction

open CategoryTheory.MonoidalCategory
open AbstractPairing (Datum)
open BorelNormalizer (InducesTorusConjugation)
open CharacterDescent (Character)
open DatumAndWeyl (Identification)
open Pinning (SplitBorelPair)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)

open private representative_label from LinearAlgebraicGroups.Classification.NormalizerComparison
open private rationalSectionsEquiv labelConjugation inducedConjugation_unique
  from LinearAlgebraicGroups.RootData.DatumAndWeyl

set_option backward.isDefEq.respectTransparency false

/-- The rank-one attachment determines the coroots, so the constructed
Weyl-group identification applies to every presentation of the actual datum. -/
private theorem actualDatum_unique {G : AffineAlgebraicGroup k} (hG : IsReductive G)
    {T : ClosedSubgroup G.val} (hsplit : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    [IsCommMonObj T.group.X] (D E : Datum T) : D = E := by
  letI := D.finiteRoots
  have hcoroot (r : Root T) : D.rootDatum.coroot r = E.rootDatum.coroot r := by
    obtain ⟨C, c, _, _, P, M, _, Q, F, L, B, x, y, _, _, _, _, s, hs⟩ := D.attached r
    exact Additive.toMul.injective (hs.symm.trans (coroot_eq_of_reflection hG hsplit hmax E r s))
  have h : D.rootDatum = E.rootDatum := by
    apply RootPairing.ext
    · ext χ c
      exact (D.pairing_eq (Additive.toMul χ) (Additive.toMul c)).trans
        (E.pairing_eq (Additive.toMul χ) (Additive.toMul c)).symm
    · apply Function.Embedding.ext
      intro r
      exact (D.root_eq r).trans (E.root_eq r).symm
    · exact congrArg (fun f : Root T ↪ _ => Set.range f) (Function.Embedding.ext hcoroot)
  cases D
  cases E
  cases h
  rfl

private theorem exists_weylIdentification (P : SplitBorelPair k) (D : AttachedDatum P) :
    letI := D.comm
    Nonempty (Identification D.datum) := by
  letI := D.comm
  obtain ⟨hcomm, E, hE⟩ := RootData.DatumAndWeyl.datumAndWeyl
    P.G P.reductive P.T P.split P.maximal
  have h := actualDatum_unique P.reductive P.split P.maximal E D.datum
  exact h ▸ hE

/-- Every rational normalizer point has a Weyl label. Its movement of roots
is the underlying Weyl permutation on the given root indices. -/
private theorem rationalWeylLabel {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (I : Identification D) :
    ∃ L : (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) →* D.rootDatum.weylGroup,
      ∀ n, n ≫ I.quotient.hom.hom = I.image.constantGroup.sectionPoint (I.labelEquiv (L n)) ∧
        ∀ a b : Root T,
          MovesCharacter T (n ≫ I.normalizer.inclusion.hom.hom) a.val b.val ↔
            D.rootDatum.weylGroupToPerm (L n) a = b := by
  obtain ⟨sectionEquiv, hsection⟩ := rationalSectionsEquiv I.image.constantGroup
  let q := IsMonHom.monoidHom I.quotient.hom.hom (𝟙_ (SchemeOver k))
  let L := I.labelEquiv.symm.toMonoidHom.comp (sectionEquiv.symm.toMonoidHom.comp q)
  have hlabel (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) :
      n ≫ I.quotient.hom.hom = I.image.constantGroup.sectionPoint (I.labelEquiv (L n)) := by
    rw [← hsection]
    change q n = sectionEquiv (I.labelEquiv (I.labelEquiv.symm (sectionEquiv.symm (q n))))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine ⟨L, fun n => ⟨hlabel n, fun a b => ?_⟩⟩
  let e := I.image.conjugation (I.labelEquiv (L n))
  have he : InducesTorusConjugation T (n ≫ I.normalizer.inclusion.hom.hom) e :=
    labelConjugation I.image (I.labelEquiv (L n)) n (hlabel n)
  have hchar : (L n).val.weightEquiv (Additive.ofMul a.val) = Additive.ofMul (e.inv ≫ a.val) :=
    (I.characterAction _ _).trans (congrArg Additive.ofMul (I.image.characterAction _ _))
  have hroot : (L n).val.weightEquiv (Additive.ofMul a.val) =
      Additive.ofMul (D.rootDatum.weylGroupToPerm (L n) a).val := by
    rw [← D.root_eq, ← D.root_eq]
    exact D.rootDatum.weylGroup_apply_root (L n) a
  constructor
  · rintro ⟨f, hf, hfab⟩
    have hfe := inducedConjugation_unique (show InducesTorusConjugation T _ f from hf) he
    apply Subtype.ext
    apply Additive.ofMul.injective
    rw [← hroot, hchar, ← hfe, hfab]
  · intro h
    refine ⟨e, he, Additive.ofMul.injective ?_⟩
    rw [← hchar, hroot, h]


open private subgroupIso_of_same subgroup_inclusion_of_represents
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

/-- The Weyl labels on the given comparison normalizer act on the actual
roots. The identity label consists of the rational points of its torus. -/
private theorem source_normalizer_labels (N : Normalizers P Q D E d τ) :
    letI := D.comm
    ∃ π : (𝟙_ (SchemeOver k) ⟶ N.source.group.X) →* D.datum.rootDatum.weylGroup,
      (∀ z a b, MovesCharacter P.pair.T (z ≫ N.source.inclusion.hom.hom) a.val b.val ↔
        D.datum.rootDatum.weylGroupToPerm (π z) a = b) ∧
      (∀ z, π z = 1 → ∃ t : 𝟙_ (SchemeOver k) ⟶ P.pair.T.group.X,
        t ≫ N.sourceTorus.hom.hom = z) ∧
      ∀ (i : Pinning.SimpleRoot P.pair) z,
        z ≫ N.source.inclusion.hom.hom = (N.sourceSimple i).reflection.representative →
        π z = RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val := by
  letI := D.comm
  obtain ⟨I⟩ := exists_weylIdentification P.pair D
  obtain ⟨e, he⟩ := subgroupIso_of_same
    ⟨subgroup_inclusion_of_represents N.representsSource I.representsNormalizer (fun _ _ h => h),
      subgroup_inclusion_of_represents I.representsNormalizer N.representsSource (fun _ _ h => h)⟩
  obtain ⟨L, hL⟩ := rationalWeylLabel I
  let F := Grp.forget (SchemeOver k)
  let M := IsMonHom.monoidHom e.hom.hom.hom (𝟙_ (SchemeOver k))
  have hambient (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) :
      M z ≫ I.normalizer.inclusion.hom.hom = z ≫ N.source.inclusion.hom.hom := by
    change (z ≫ e.hom.hom.hom) ≫ I.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, show e.hom.hom.hom ≫ I.normalizer.inclusion.hom.hom =
      N.source.inclusion.hom.hom from F.congr_map he]
  refine ⟨L.comp M, fun z a b => ?_, fun z hz => ?_, fun i z hz => ?_⟩
  · have h := (hL (M z)).2 a b
    rw [hambient z] at h
    exact h
  · have hq := (hL (M z)).1
    change L (M z) = 1 at hz
    rw [hz, map_one, map_one] at hq
    obtain ⟨t, ht⟩ := normalizer_family_factor I (M z) 1 (by
      rw [hq, MonObj.one_comp, MonObj.comp_one])
    rw [MonObj.comp_one, mul_one] at ht
    refine ⟨t, ?_⟩
    letI := N.source.isClosedImmersion
    letI : Mono N.source.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono N.source.inclusion.hom.hom).mp
    rw [Category.assoc, show N.sourceTorus.hom.hom ≫ N.source.inclusion.hom.hom =
      P.pair.T.inclusion.hom.hom from F.congr_map N.sourceTorus_eq, ← hambient z, ht,
      Category.assoc, show I.torusInclusion.hom.hom ≫ I.normalizer.inclusion.hom.hom =
        P.pair.T.inclusion.hom.hom from F.congr_map I.inclusion_eq]

  · apply I.labelEquiv.injective
    exact representative_label D I i (N.sourceSimple i) (M z) ((hambient z).trans hz)
      (I.labelEquiv (L (M z))) (hL (M z)).1

end NormalizerWeylAction

noncomputable section


section ChamberIndependence

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AdjointRepresentation (GroupPoints)
open CharacterPairing (characterValue)
open Pinning (SimpleRoot)
open RootGroups (rootPoint)
open RootPairing

open _root_.LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private rootPoint_comp rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private sectionMap sectionMap_comp PinnedLevi simpleRootOfIndex
  lift_pinning_to_levi levi_rank compatible_levis match_levi_representative compatibleSimpleRoots
  from LinearAlgebraicGroups.Classification.NormalizerComparison
open private PinnedLevi.pinned PinnedLevi.rootIndex PinnedLevi.simple_iff PinnedLevi.torus
  PinnedLevi.datum PinnedLevi.inclusion PinnedLevi.pin_eq PinnedLevi.mono
  from LinearAlgebraicGroups.Classification.NormalizerComparison

set_option backward.isDefEq.respectTransparency false

private abbrev pinMap {P : PinnedGroup A} (i : SimpleRoot P.pair) : A.group ⟶ P.pair.G.val :=
  (P.pin i).val.hom ≫ (P.roots i.val).val.inclusion

private abbrev sourcePoint (N : Normalizers P Q D E d τ)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) :=
  sectionMap N.source.inclusion _ z

private abbrev targetPoint (N : Normalizers P Q D E d τ)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) :=
  sectionMap (N.hom ≫ N.target.inclusion) _ z

private theorem sourcePoint_mul (N : Normalizers P Q D E d τ)
    (z w : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) :
    sourcePoint N (z * w) = sourcePoint N z * sourcePoint N w :=
  map_mul (sectionMap N.source.inclusion _) z w

private theorem targetPoint_mul (N : Normalizers P Q D E d τ)
    (z w : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) :
    targetPoint N (z * w) = targetPoint N z * targetPoint N w :=
  map_mul (sectionMap (N.hom ≫ N.target.inclusion) _) z w

private theorem sourcePoint_one (N : Normalizers P Q D E d τ) : sourcePoint N 1 = 1 :=
  map_one (sectionMap N.source.inclusion _)

private theorem targetPoint_one (N : Normalizers P Q D E d τ) : targetPoint N 1 = 1 :=
  map_one (sectionMap (N.hom ≫ N.target.inclusion) _)

private theorem sourcePoint_inv (N : Normalizers P Q D E d τ)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) : sourcePoint N z⁻¹ = (sourcePoint N z)⁻¹ :=
  map_inv (sectionMap N.source.inclusion _) z

private theorem targetPoint_inv (N : Normalizers P Q D E d τ)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) : targetPoint N z⁻¹ = (targetPoint N z)⁻¹ :=
  map_inv (sectionMap (N.hom ≫ N.target.inclusion) _) z

private theorem transport_map {G H : GroupScheme k} (f : G ⟶ H)
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} {x y : A.group ⟶ G}
    (h : TransportsCoordinate n x y) :
    TransportsCoordinate (sectionMap f _ n) (x ≫ f) (y ≫ f) := by
  intro R a
  let F := sectionMap f ((testSpec k).obj (op R))
  let g : GroupPoints G R := toUnit _ ≫ n
  have he : F (g * rootPoint x R a * g⁻¹) = F (rootPoint y R a) := congrArg F (h R a)
  rw [map_mul, map_mul, map_inv] at he
  simpa only [F, sectionMap, MonoidHom.coe_mk, OneHom.coe_mk, ← rootPoint_comp,
    Category.assoc, g] using he

private theorem transport_of_map {G H : GroupScheme k} (f : G ⟶ H) [Mono f.hom.hom]
    {n : 𝟙_ (SchemeOver k) ⟶ G.X} {x y : A.group ⟶ G}
    (h : TransportsCoordinate (sectionMap f _ n) (x ≫ f) (y ≫ f)) :
    TransportsCoordinate n x y := by
  intro R a
  apply (cancel_mono f.hom.hom).mp
  dsimp only
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, ← rootPoint_comp, ← rootPoint_comp]
  simpa only [sectionMap, MonoidHom.coe_mk, OneHom.coe_mk, Category.assoc] using h R a

private theorem parameter_substitution {G H : GroupScheme k} (x : A.group ⟶ G)
    [Mono x.hom.hom] (y : A.group ⟶ H) (p : A.group ⟶ A.group)
    (R : TestAlgebra k) (a b : R) (h : rootPoint (p ≫ x) R a = rootPoint x R b) :
    rootPoint (p ≫ y) R a = rootPoint y R b := by
  simp only [rootPoint_eq, Grp.comp_hom_hom, ← Category.assoc] at h ⊢
  rw [(cancel_mono x.hom.hom).mp h]

private def AgreeOnPins (h : Compatible P Q D E d τ) (N : Normalizers P Q D E d τ)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X) (i j : SimpleRoot P.pair) : Prop :=
  ∃ p : A.group ≅ A.group,
    TransportsCoordinate (sourcePoint N z) (pinMap i) (p.hom ≫ pinMap j) ∧
    TransportsCoordinate (targetPoint N z) (pinMap (correspondingSimple h i))
      (p.hom ≫ pinMap (correspondingSimple h j))

private theorem agreeOnPins_mul (h : Compatible P Q D E d τ) (N : Normalizers P Q D E d τ)
    {z w : 𝟙_ (SchemeOver k) ⟶ N.source.group.X} {i j l : SimpleRoot P.pair}
    (hz : AgreeOnPins h N z i j) (hw : AgreeOnPins h N w j l) :
    AgreeOnPins h N (w * z) i l := by
  obtain ⟨p, hp, hp'⟩ := hz
  obtain ⟨q, hq, hq'⟩ := hw
  refine ⟨p ≪≫ q, ?_, ?_⟩
  · simpa only [sourcePoint_mul, Iso.trans_hom, Category.assoc] using
      transport_compose hp (transport_precompose hq p.hom)
  · simpa only [targetPoint_mul, Iso.trans_hom, Category.assoc] using
      transport_compose hp' (transport_precompose hq' p.hom)

private theorem agreeOnPins_torus (h : Compatible P Q D E d τ) (N : Normalizers P Q D E d τ)
    (i : SimpleRoot P.pair) (t : 𝟙_ (SchemeOver k) ⟶ P.pair.T.group.X)
    (hz : MovesCharacter P.pair.T (sourcePoint N (sectionMap N.sourceTorus _ t)) i.val.val i.val.val) :
    AgreeOnPins h N (sectionMap N.sourceTorus _ t) i i := by
  let j := correspondingSimple h i
  let z := sectionMap N.sourceTorus _ t
  obtain ⟨x, hx⟩ := exists_transportedRootCoordinate P i.val i.val hz (P.pin i)
  let p := x.val ≪≫ (P.pin i).val.symm
  have hp : p.hom ≫ pinMap i = x.val.hom ≫ (P.roots i.val).val.inclusion := by
    simp only [p, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have hs : sourcePoint N z = sectionMap P.pair.T.inclusion _ t := by
    change sectionMap N.source.inclusion _ (sectionMap N.sourceTorus _ t) = _
    rw [← sectionMap_comp, N.sourceTorus_eq]
  have ht : targetPoint N z = sectionMap (τ ≫ Q.pair.T.inclusion) _ t := by
    change sectionMap (N.hom ≫ N.target.inclusion) _ (sectionMap N.sourceTorus _ t) = _
    rw [← sectionMap_comp, ← Category.assoc, N.torus_comm, Category.assoc, N.targetTorus_eq]
  refine ⟨p, hp.symm ▸ hx, ?_⟩
  intro R a
  let B := (testSpec k).obj (op R)
  let tR : GroupPoints P.pair.T.group R := toUnit B ≫ t
  let uR : GroupPoints Q.pair.T.group R := tR ≫ τ.hom.hom
  have hc : characterValue j.val.val R uR = characterValue i.val.val R tR := by
    have hχ : τ ≫ j.val.val = i.val.val := h.root i.val
    have hu : uR ≫ j.val.val.hom.hom = tR ≫ i.val.val.hom.hom := by
      dsimp only [uR]
      rw [Category.assoc, ← Grp.comp_hom_hom, hχ]
    unfold characterValue
    rw [hu]
  letI := (P.roots i.val).val.isClosedImmersion
  letI : Mono (P.roots i.val).val.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono (pinMap i).hom.hom := by
    change Mono ((P.pin i).val.hom.hom.hom ≫ (P.roots i.val).val.inclusion.hom.hom)
    infer_instance
  let gs : GroupPoints P.pair.G.val R := tR ≫ P.pair.T.inclusion.hom.hom
  let gt : GroupPoints Q.pair.G.val R := uR ≫ Q.pair.T.inclusion.hom.hom
  have hgs : toUnit B ≫ sourcePoint N z = gs := by
    rw [hs]
    change toUnit B ≫ t ≫ P.pair.T.inclusion.hom.hom = _
    simp only [gs, tR, Category.assoc]
  have hgt : toUnit B ≫ targetPoint N z = gt := by
    rw [ht]
    change toUnit B ≫ t ≫ (τ ≫ Q.pair.T.inclusion).hom.hom = _
    simp only [gt, uR, tR, Grp.comp_hom_hom, Category.assoc]
  let pz : GroupPoints P.pair.G.val R := toUnit B ≫ sourcePoint N z
  have hs₀ : pz * rootPoint (pinMap i) R a * pz⁻¹ =
      rootPoint (x.val.hom ≫ (P.roots i.val).val.inclusion) R a := hx R a
  have hs₁ : gs * rootPoint (pinMap i) R a * gs⁻¹ =
      rootPoint (x.val.hom ≫ (P.roots i.val).val.inclusion) R a := by
    dsimp only [pz] at hs₀
    rw [hgs] at hs₀
    exact hs₀
  have hpar : rootPoint (p.hom ≫ pinMap i) R a =
      rootPoint (pinMap i) R (characterValue i.val.val R tR * a) := by
    rw [hp, ← hs₁]
    exact (P.pin i).property R tR a
  let qz : GroupPoints Q.pair.G.val R := toUnit B ≫ targetPoint N z
  have hqz : qz = gt := hgt
  change qz * rootPoint (pinMap j) R a * qz⁻¹ = _
  rw [hqz]
  exact ((Q.pin j).property R uR a).trans
    (by rw [hc]; exact (parameter_substitution (pinMap i) (pinMap j) p.hom R a _ hpar).symm)

-- The image of a subgroup generated by specified representatives lies in
-- any simultaneous image containing those generators.
private theorem exists_matching_word {F G J : Type*} [Group F] [Group G] [Group J]
    (f : F →* J) (g : G →* J) {s : Set F} (hs : ∀ x ∈ s, ∃ y, g y = f x)
    (z : F) (hz : z ∈ Subgroup.closure s) : ∃ w, g w = f z := by
  exact (show z ∈ g.range.comap f from
    ((Subgroup.closure_le _).mpr (show s ⊆ g.range.comap f from hs)) hz)

private noncomputable def simpleInLevi {I : Set (Root P.pair.T)} (L : PinnedLevi P D I)
    (i : SimpleRoot P.pair) (hi : i.val ∈ I) : SimpleRoot (PinnedLevi.pinned L).pair :=
  let r := (PinnedLevi.rootIndex L).symm ⟨i.val, Submodule.subset_span ⟨_, hi, rfl⟩⟩
  ⟨r, ((PinnedLevi.simple_iff L) r).mpr ((congrArg Subtype.val
    ((PinnedLevi.rootIndex L).apply_symm_apply ⟨i.val, Submodule.subset_span ⟨_, hi, rfl⟩⟩)).symm ▸ hi)⟩

private theorem simpleInLevi_root {I : Set (Root P.pair.T)} (L : PinnedLevi P D I)
    (i : SimpleRoot P.pair) (hi : i.val ∈ I) :
    ((PinnedLevi.rootIndex L) (simpleInLevi L i hi).val).val = i.val :=
  congrArg Subtype.val ((PinnedLevi.rootIndex L).apply_symm_apply _)

set_option maxHeartbeats 650000 in
private theorem agreeOnPins_pair (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ)
    (n : SimpleRoot P.pair → (𝟙_ (SchemeOver k) ⟶ N.source.group.X))
    (hn : ∀ i, sourcePoint N (n i) = (N.sourceSimple i).reflection.representative ∧
      targetPoint N (n i) = (N.targetSimple (correspondingSimple h i)).reflection.representative)
    (i j l : SimpleRoot P.pair) (hj : j = i ∨ j = l)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X)
    (hz : z ∈ Subgroup.closure ({n i, n l} : Set _))
    (hm : MovesCharacter P.pair.T (sourcePoint N z) i.val.val j.val.val) :
    AgreeOnPins h N z i j := by
  classical
  letI := D.comm
  letI := E.comm
  let I : Finset (Root P.pair.T) := {i.val, l.val}
  have hi : i.val ∈ I := Finset.mem_insert_self _ _
  have hl : l.val ∈ I := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hj' : j.val ∈ I := hj.elim (fun e => e.symm ▸ hi) (fun e => e.symm ▸ hl)
  have hI : (I : Set (Root P.pair.T)) ⊆ D.base.support := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
    exact ha.elim (fun e => e.symm ▸ (D.simple_iff _).mpr i.property)
      (fun e => e.symm ▸ (D.simple_iff _).mpr l.property)
  have hI' : d '' (I : Set (Root P.pair.T)) ⊆ E.base.support := by
    rintro _ ⟨α, hα, rfl⟩
    exact (h.simple α).mp (hI hα)
  obtain ⟨L⟩ := lift_pinning_to_levi P D (I : Set (Root P.pair.T)) hI
  obtain ⟨M⟩ := lift_pinning_to_levi Q E (d '' (I : Set (Root P.pair.T))) hI'
  obtain ⟨W⟩ := exists_weylIdentification Q.pair E
  obtain ⟨δ, hδ, hcompat⟩ := compatible_levis h L M
  let σ := (PinnedLevi.torus L).inv ≫ τ ≫ (PinnedLevi.torus M).hom
  have hrank := (levi_rank L I rfl).trans (Finset.card_le_two (a := i.val) (b := l.val))
  obtain ⟨f, hf, _, _, _, _, _, hgroups⟩ :=
    Classification.RankTwoLifting.liftTorusMap (PinnedLevi.pinned L) (PinnedLevi.pinned M) (PinnedLevi.datum L) (PinnedLevi.datum M) hrank δ σ hcompat
  let F := f ≫ (PinnedLevi.inclusion M)
  let a := simpleInLevi L i hi
  let b := simpleInLevi L j hj'
  have ha := simpleInLevi_root L i hi
  have hb := simpleInLevi_root L j hj'
  let a' := correspondingSimple hcompat a
  let b' := correspondingSimple hcompat b
  have ha' : ((PinnedLevi.rootIndex M) a'.val).val = d i.val := (hδ a.val).trans (congrArg d ha)
  have hb' : ((PinnedLevi.rootIndex M) b'.val).val = d j.val := (hδ b.val).trans (congrArg d hb)
  let fN := (sectionMap N.source.inclusion (𝟙_ (SchemeOver k))).prod
    (sectionMap (N.hom ≫ N.target.inclusion) (𝟙_ (SchemeOver k)))
  let fL := (sectionMap (PinnedLevi.inclusion L) (𝟙_ (SchemeOver k))).prod
    (sectionMap F (𝟙_ (SchemeOver k)))
  have hg (v : SimpleRoot P.pair) (hv : v.val ∈ I) : ∃ w, fL w = fN (n v) := by
    have hs : correspondingSimple h v = compatibleSimpleRoots h v := Subtype.ext rfl
    obtain ⟨u, hu, hu'⟩ := match_levi_representative h L M W δ hδ hcompat f hf hgroups v hv
      (N.sourceSimple v) (N.targetSimple (compatibleSimpleRoots h v))
    refine ⟨u, Prod.ext (hu.trans (hn v).1.symm) ?_⟩
    change sectionMap F _ u = targetPoint N (n v)
    rw [hu', (hn v).2, hs]
  have hgen : ∀ z ∈ ({n i, n l} : Set _), ∃ w, fL w = fN z := by
    intro z hz
    rcases hz with hz | hz
    · subst z
      exact hg i hi
    · obtain rfl := Set.mem_singleton_iff.mp hz
      exact hg l hl
  obtain ⟨w, hw⟩ := exists_matching_word fN fL hgen z hz
  have hwP : sectionMap (PinnedLevi.inclusion L) _ w = sourcePoint N z := congrArg Prod.fst hw
  have hwQ : sectionMap F _ w = targetPoint N z := congrArg Prod.snd hw
  have hpa : pinMap a ≫ (PinnedLevi.inclusion L) = pinMap i := (PinnedLevi.pin_eq L) a i ha
  have hpb : pinMap b ≫ (PinnedLevi.inclusion L) = pinMap j := (PinnedLevi.pin_eq L) b j hb
  have hqa : pinMap a ≫ F = pinMap (correspondingSimple h i) := by
    rw [← Category.assoc, show pinMap a ≫ f = pinMap a' from hf.2 a a' rfl]
    exact (PinnedLevi.pin_eq M) a' (correspondingSimple h i) ha'
  have hqb : pinMap b ≫ F = pinMap (correspondingSimple h j) := by
    rw [← Category.assoc, show pinMap b ≫ f = pinMap b' from hf.2 b b' rfl]
    exact (PinnedLevi.pin_eq M) b' (correspondingSimple h j) hb'
  obtain ⟨x, hx⟩ := exists_transportedRootCoordinate P i.val j.val hm (P.pin i)
  let p := x.val ≪≫ (P.pin j).val.symm
  have hp : p.hom ≫ pinMap j = x.val.hom ≫ (P.roots j.val).val.inclusion := by
    simp only [p, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  letI := (PinnedLevi.mono L)
  have hlocal : TransportsCoordinate w (pinMap a) (p.hom ≫ pinMap b) :=
    transport_of_map (PinnedLevi.inclusion L) (by simpa only [hwP, hpa, Category.assoc, hpb, hp] using hx)
  refine ⟨p, hp.symm ▸ hx, ?_⟩
  simpa only [hwQ, hqa, Category.assoc, hqb] using transport_map F hlocal

set_option maxHeartbeats 900000 in
private theorem simpleTransports (h : Compatible P Q D E d τ) (N : Normalizers P Q D E d τ) :
    ∀ (i j : SimpleRoot P.pair) (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X),
      MovesCharacter P.pair.T (sourcePoint N z) i.val.val j.val.val →
        ∃ x : A.group ≅ (P.roots j.val).val.group,
          TransportsCoordinate (sourcePoint N z) (pinMap i)
            (x.hom ≫ (P.roots j.val).val.inclusion) ∧
          TransportsCoordinate (targetPoint N z) (pinMap (correspondingSimple h i))
            ((x ≪≫ comparedSimplePin h j).hom ≫ (Q.roots (d j.val)).val.inclusion) := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  classical
  have hs (i : SimpleRoot P.pair) :
      ∃ z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X,
        sourcePoint N z = (N.sourceSimple i).reflection.representative ∧
        targetPoint N z = (N.targetSimple (correspondingSimple h i)).reflection.representative :=
    N.simple_comm i (correspondingSimple h i) rfl
  choose n hn using hs
  obtain ⟨π, hπ, hkernel, hgen⟩ := source_normalizer_labels N
  have hπn (i : D.base.support) :
      π (n (simpleRootOfIndex D i)) = weylGroup.ofIdx D.datum.rootDatum i.val := by
    exact hgen (simpleRootOfIndex D i) (n (simpleRootOfIndex D i)) (hn _).1
  have hsurj : Function.Surjective π := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← weylGeneratedByBase D.datum.rootDatum D.base]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨n (simpleRootOfIndex D i), hπn i⟩
  let a := simpleRootOfIndex D
  have hind := representativeInductionOnSimpleTransport D.datum.rootDatum D.base π hsurj
    (fun i => n (a i)) hπn (fun z i j => AgreeOnPins h N z (a i) (a j))
    (fun t ht i => by
      obtain ⟨v, hv⟩ := hkernel t ht
      have hv' : sectionMap N.sourceTorus _ v = t := hv
      rw [← hv']
      apply agreeOnPins_torus h N (a i) v
      apply (hπ (sectionMap N.sourceTorus _ v) i.val i.val).mpr
      rw [hv', ht, map_one]
      rfl)
    (fun i j l z _ hj hz he =>
      agreeOnPins_pair h N n hn (a i) (a j) (a l)
        (hj.imp (congrArg a) (congrArg a)) z hz ((hπ z i.val j.val).mpr he))
    (fun z w i j l hz hw => agreeOnPins_mul h N hz hw)
  intro i j z hz
  let i' : D.base.support := ⟨i.val, (D.simple_iff _).mpr i.property⟩
  let j' : D.base.support := ⟨j.val, (D.simple_iff _).mpr j.property⟩
  obtain ⟨p, hp, hq⟩ := hind z i' j' ((hπ z _ _).mp hz)
  have hi : a i' = i := Subtype.ext rfl
  have hj : a j' = j := Subtype.ext rfl
  rw [hi, hj] at hp hq
  refine ⟨p ≪≫ (P.pin j).val, ?_, ?_⟩
  · simpa only [pinMap, Iso.trans_hom, Category.assoc] using hp
  · change TransportsCoordinate (targetPoint N z) (pinMap (correspondingSimple h i))
      (((p ≪≫ (P.pin j).val) ≪≫ comparedSimplePin h j).hom ≫
        (Q.roots (correspondingSimple h j).val).val.inclusion)
    simpa only [pinMap, comparedSimplePin, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using hq

end ChamberIndependence


section LinkedTransports

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CharacterDescent (Character Cocharacter)
open Pinning (RootCoordinate SimpleRoot)
open CharacterPairing (pairing)
open RootGroups (CorootReflection HasScalarAction rankOneWord rootPoint)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)

open private innerMap comp_innerMap from LinearAlgebraicGroups.Reductive.BorelProper
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private sectionMap sectionMap_comp map_linked_reflection linked_representative_eq
  from LinearAlgebraicGroups.Classification.NormalizerComparison
open private rescale coordinate_change rescale_point from LinearAlgebraicGroups.Classification.Pinning
open private rescaleLinkedPair from LinearAlgebraicGroups.Classification.RankTwoRelations
open private linked_coroot from LinearAlgebraicGroups.Classification.RankTwoLifting
open private scalar_action_of_normalized_tangent rootPoint_comp
  from LinearAlgebraicGroups.RootData.RootGroups
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false

private def rootCoordinate (P : PinnedGroup A) (a : Root P.pair.T)
    (x : A.group ≅ (P.roots a).val.group) : RootCoordinate A P.pair.T (P.roots a).val a.val :=
  ⟨x, scalar_action_of_normalized_tangent _ _ P.pair.split _ (P.roots a).property A x⟩

private abbrev rootMap {P : PinnedGroup A} {a : Root P.pair.T}
    (x : A.group ≅ (P.roots a).val.group) : A.group ⟶ P.pair.G.val :=
  x.hom ≫ (P.roots a).val.inclusion

private theorem matchedTransport_at (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (he : MatchesTransports N e)
    {a b : Root P.pair.T} (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X)
    (hz : MovesCharacter P.pair.T (sourcePoint N z) a.val b.val)
    (x : A.group ≅ (P.roots a).val.group) :
    ∃ y : A.group ≅ (P.roots b).val.group,
      TransportsCoordinate (sourcePoint N z) (rootMap (P := P) (a := a) x)
        (rootMap (P := P) (a := b) y) ∧
      TransportsCoordinate (targetPoint N z) (rootMap (P := Q) (a := d a) (x ≪≫ e a))
        (rootMap (P := Q) (a := d b) (y ≪≫ e b)) := by
  obtain ⟨u, v, hu, hv⟩ := matchesTransports_rational h N e he a b z hz
  let p := x ≪≫ u.symm
  refine ⟨p ≪≫ v, ?_, ?_⟩
  · change TransportsCoordinate (z ≫ N.source.inclusion.hom.hom) _ _
    simpa only [rootMap, p, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using
      transport_precompose hu p.hom
  · change TransportsCoordinate (z ≫ N.hom.hom.hom ≫ N.target.inclusion.hom.hom) _ _
    simpa only [rootMap, p, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using
      transport_precompose hv p.hom

private theorem reflection_moves_opposite {G : GroupScheme k} {T : ClosedSubgroup G}
    {α : Character T.group} {x y : A.group ⟶ G} (r : CorootReflection T α x y) :
    MovesCharacter T r.representative α α⁻¹ := by
  refine ⟨r.conjugation, r.conjugates, ?_⟩
  rw [r.reflection, r.root_pairing]
  group

private theorem oppositeTransport (P : PinnedGroup A) {a : Root P.pair.T}
    {x y : A.group ⟶ P.pair.G.val}
    (r : CorootReflection P.pair.T a.val x y)
    (hx : HasScalarAction P.pair.T a.val x) (hy : HasScalarAction P.pair.T a.val⁻¹ y)
    (R : TestAlgebra k) (t : R) :
    let n : AdjointRepresentation.GroupPoints P.pair.G.val R := toUnit _ ≫ r.representative
    n * rootPoint x R t * n⁻¹ = rootPoint y R (-t) :=
  ((RankOneRelations.oppositeRootRelations P.pair.G P.pair.reductive P.pair.T P.pair.split
    P.pair.maximal a.val a.property x y r hx hy R).2).2 t

private theorem matchedOpposite_of_representatives (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (he : MatchesTransports N e)
    {a b : Root P.pair.T} (hab : b.val = a.val⁻¹)
    (x : RootCoordinate A P.pair.T (P.roots a).val a.val)
    (y : RootCoordinate A P.pair.T (P.roots b).val b.val)
    (r : CorootReflection P.pair.T a.val (rootMap (P := P) (a := a) x.val)
      (rootMap (P := P) (a := b) y.val))
    {v : A.group ⟶ Q.pair.G.val}
    (s : CorootReflection Q.pair.T (d a).val (rootMap (P := Q) (a := d a) (x.val ≪≫ e a)) v)
    (hv : HasScalarAction Q.pair.T (d a).val⁻¹ v)
    (z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X)
    (hz : sourcePoint N z = r.representative) (hz' : targetPoint N z = s.representative) :
    v = rootMap (P := Q) (a := d b) (y.val ≪≫ e b) := by
  have hm : MovesCharacter P.pair.T (sourcePoint N z) a.val b.val := by
    rw [hz]
    exact Eq.mpr (congrArg (MovesCharacter P.pair.T r.representative a.val) hab)
      (reflection_moves_opposite r)
  obtain ⟨y', hP, hQ⟩ := matchedTransport_at h N he z hm x.val
  have hyn : HasScalarAction P.pair.T a.val⁻¹ (rootMap (P := P) (a := b) y.val) := hab ▸ y.property
  apply rootMorphism_ext
  intro R t
  have hsrc := hP R (-t)
  have hsrc' := oppositeTransport P r x.property hyn R (-t)
  dsimp only at hsrc hsrc'
  rw [hz, hsrc', neg_neg] at hsrc
  letI := (P.roots b).val.isClosedImmersion
  letI : Mono (P.roots b).val.inclusion.hom.hom := Over.mono_of_mono_left _
  have hparam : rootPoint y'.hom R (-t) = rootPoint y.val.hom R t := by
    apply (cancel_mono (P.roots b).val.inclusion.hom.hom).mp
    simpa only [rootPoint, Grp.comp_hom_hom, Category.assoc] using hsrc.symm
  have hqparam : rootPoint (rootMap (P := Q) (a := d b) (y' ≪≫ e b)) R (-t) =
      rootPoint (rootMap (P := Q) (a := d b) (y.val ≪≫ e b)) R t := by
    simp only [rootMap, Iso.trans_hom, Category.assoc, rootPoint_comp, hparam]
  have htrg := hQ R (-t)
  have htrg' := oppositeTransport Q s (rootCoordinate Q (d a) (x.val ≪≫ e a)).property hv R (-t)
  dsimp only at htrg htrg'
  rw [hz', htrg', neg_neg, hqparam] at htrg
  exact htrg

private theorem reflection_congr {G : GroupScheme k} {T : ClosedSubgroup G}
    {α : Character T.group} {x y x' y' : A.group ⟶ G} (hx : x = x') (hy : y = y')
    (r : CorootReflection T α x y) :
    ∃ s : CorootReflection T α x' y', s.coroot = r.coroot ∧ s.representative = r.representative := by
  subst x'
  subst y'
  exact ⟨r, rfl, rfl⟩

private theorem conjugate_linked {G : GroupScheme k} {T : ClosedSubgroup G}
    (hT : GeometricRadicals.IsSplitTorus T.group) {α β : Character T.group}
    {g : 𝟙_ (SchemeOver k) ⟶ G.X} (hm : MovesCharacter T g α β)
    {x y x' y' : A.group ⟶ G} (r : CorootReflection T α x y)
    (hx : TransportsCoordinate g x x') (hy : TransportsCoordinate g y y')
    (hx' : HasScalarAction T β x') (hy' : HasScalarAction T β⁻¹ y') :
    ∃ s : CorootReflection T β x' y',
      s.representative = g * r.representative * g⁻¹ := by
  obtain ⟨c, hc, hχ⟩ := hm
  let f := innerMap g
  have ht : T.inclusion ≫ f = c.hom ≫ T.inclusion := by
    apply Grp.hom_ext
    change T.inclusion.hom.hom ≫ (innerMap g).hom.hom = _
    rw [comp_innerMap, ← hc]
  have hβ : c.hom ≫ β = α := by rw [← hχ, Iso.hom_inv_id_assoc]
  have map_coord {x y : A.group ⟶ G} (h : TransportsCoordinate g x y) : x ≫ f = y := by
    apply rootMorphism_ext
    intro R a
    rw [rootPoint_comp, comp_innerMap]
    exact h R a
  have hX := map_coord hx
  have hY := map_coord hy
  have hx'' : HasScalarAction T β (x ≫ f) := hX.symm ▸ hx'
  have hy'' : HasScalarAction T β⁻¹ (y ≫ f) := hY.symm ▸ hy'
  obtain ⟨s, _, hs⟩ := map_linked_reflection f c.hom ht hT hβ r hx'' hy''
  have hs' : s.representative = g * r.representative * g⁻¹ := by
    rw [hs]
    change r.representative ≫ (innerMap g).hom.hom = _
    rw [comp_innerMap, show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _,
      Category.id_comp]
  obtain ⟨r', _, hr'⟩ := reflection_congr hX hY s
  exact ⟨r', hr'.trans hs'⟩

private def torusValue {T : GroupScheme k} (cochar : Cocharacter T) (c : kˣ) :
    𝟙_ (SchemeOver k) ⟶ T.X :=
  (groundIso (k := k)).inv ≫ cocharacterPoint cochar (CommAlgCat.of k k)
    (Units.map (algebraMap k (CommAlgCat.of k k)).toMonoidHom c)

private theorem torusValue_map {T S : GroupScheme k} (τ : T ⟶ S)
    (cochar : Cocharacter T) (c : kˣ) : sectionMap τ _ (torusValue cochar c) = torusValue (cochar ≫ τ) c := by
  let R := CommAlgCat.of k k
  let s := Units.map (algebraMap k R).toMonoidHom c
  let j := (groundIso (k := k)).inv
  change (j ≫ unitPoint R s ≫ cochar.hom.hom) ≫ τ.hom.hom =
    j ≫ unitPoint R s ≫ (cochar ≫ τ).hom.hom
  simp only [Grp.comp_hom_hom, Category.assoc]

private theorem rescaled_representative {G : GroupScheme k} {T U V : ClosedSubgroup G}
    {α : Character T.group} (x : RootCoordinate A T U α) (y : RootCoordinate A T V α⁻¹)
    (r : CorootReflection T α (x.val.hom ≫ U.inclusion) (y.val.hom ≫ V.inclusion))
    (c : kˣ) (s : CorootReflection T α
      ((rescale (A := A) x c).val.hom ≫ U.inclusion)
      ((rescale (A := A) y c⁻¹).val.hom ≫ V.inclusion)) :
    s.representative = sectionMap T.inclusion _ (torusValue r.coroot c) * r.representative := by
  let R := CommAlgCat.of k k
  let cR := Units.map (algebraMap k R).toMonoidHom c
  have he : rankOneWord ((rescale (A := A) x c).val.hom ≫ U.inclusion)
      ((rescale (A := A) y c⁻¹).val.hom ≫ V.inclusion) R 1 =
      rankOneWord (x.val.hom ≫ U.inclusion) (y.val.hom ≫ V.inclusion) R cR := by
    simp only [rankOneWord, rescale_point, Units.val_one, inv_one, mul_one,
      mul_neg, cR, Units.coe_map_inv, Units.coe_map]
    rfl
  let g := groundIso (k := k)
  let B := (testSpec k).obj (op R)
  have hs : toUnit B ≫ s.representative = rankOneWord _ _ R 1 := s.representative_word
  have hr : toUnit B ≫ r.representative = rankOneWord _ _ R 1 := r.representative_word
  have hpoint : toUnit B ≫ sectionMap T.inclusion _ (torusValue r.coroot c) =
      cocharacterPoint r.coroot R cR ≫ T.inclusion.hom.hom := by
    change toUnit B ≫ (g.inv ≫ cocharacterPoint r.coroot R cR) ≫ T.inclusion.hom.hom = _
    rw [show toUnit B = g.hom from Subsingleton.elim _ _]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply (cancel_epi g.hom).mp
  rw [show g.hom = toUnit B from Subsingleton.elim _ _, MonObj.comp_mul,
    hs, hpoint, hr, he, r.coroot_word]
  group

set_option maxHeartbeats 1000000 in
private theorem matchedLinkedPairs (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (he : MatchesTransports N e) :
    MatchesLinkedPairs N e := by
  letI := D.comm
  letI := E.comm
  intro a b hab x y r hr
  have hab' := map_opposite h hab
  obtain ⟨i, w, hw⟩ := he.1 a
  let j := correspondingSimple h i
  let m := N.sourceSimple i
  let n := N.targetSimple j
  obtain ⟨v, hv, hv'⟩ := N.simple_comm i j rfl
  obtain ⟨u, hu, hu'⟩ := he.2 a i j rfl w hw
  have hw' := movesCharacter_map h N w i.val a hw
  have hP : MovesCharacter P.pair.T (sourcePoint N w) m.opposite.val b.val := by
    rw [m.opposite_eq, hab]
    exact movesCharacter_invCharacter hw
  have hQ : MovesCharacter Q.pair.T (targetPoint N w) n.opposite.val (d b).val := by
    rw [n.opposite_eq, hab']
    exact movesCharacter_invCharacter hw'
  obtain ⟨p, hp⟩ := exists_transportedRootCoordinate P m.opposite b hP m.negative
  obtain ⟨q, hq⟩ := exists_transportedRootCoordinate Q n.opposite (d b) hQ n.negative
  let x₀ := rootCoordinate P a u
  let x₁ := rootCoordinate Q (d a) (u ≪≫ e a)
  let y₀ : RootCoordinate A P.pair.T (P.roots b).val a.val⁻¹ := ⟨p.val, hab ▸ p.property⟩
  let y₁ : RootCoordinate A Q.pair.T (Q.roots (d b)).val (d a).val⁻¹ := ⟨q.val, hab' ▸ q.property⟩
  obtain ⟨r₀, hr₀⟩ := conjugate_linked P.pair.split hw m.reflection hu hp x₀.property y₀.property
  obtain ⟨r₁, hr₁⟩ := conjugate_linked Q.pair.split hw' n.reflection hu' hq x₁.property y₁.property
  let z₀ := w * v * w⁻¹
  have hz₀ : sourcePoint N z₀ = r₀.representative := by
    rw [show sourcePoint N z₀ = sourcePoint N w * sourcePoint N v * (sourcePoint N w)⁻¹
      from by simp only [z₀, sourcePoint_mul, sourcePoint_inv], hr₀, show sourcePoint N v = _ from hv]
    rfl
  have hz₁ : targetPoint N z₀ = r₁.representative := by
    rw [show targetPoint N z₀ = targetPoint N w * targetPoint N v * (targetPoint N w)⁻¹
      from by simp only [z₀, targetPoint_mul, targetPoint_inv], hr₁, show targetPoint N v = _ from hv']
    rfl
  obtain ⟨c, hc⟩ := coordinate_change x₀ x
  obtain ⟨s₀⟩ := rescaleLinkedPair (A := A) P.pair.split x₀ y₀ r₀ c
  obtain ⟨s₁⟩ := rescaleLinkedPair (A := A) Q.pair.split x₁ y₁ r₁ c
  have hpos₀ : (rescale (A := A) x₀ c).val.hom ≫ (P.roots a).val.inclusion =
      x.val.hom ≫ (P.roots a).val.inclusion := by rw [← hc]
  have hpos₁ : (rescale (A := A) x₁ c).val.hom ≫ (Q.roots (d a)).val.inclusion =
      (x.val ≪≫ e a).hom ≫ (Q.roots (d a)).val.inclusion := by
    rw [hc]
    simp only [rescale, x₀, x₁, rootCoordinate, Iso.trans_hom, Category.assoc]
  let t := torusValue r₀.coroot c
  have ht : sectionMap τ _ t = torusValue r₁.coroot c := by
    rw [show sectionMap τ _ t = torusValue (r₀.coroot ≫ τ) c from torusValue_map τ _ _,
      linked_coroot D.datum a r₀, h.coroot a, linked_coroot E.datum (d a) r₁]
  let z := sectionMap N.sourceTorus _ t * z₀
  have hz : sourcePoint N z = s₀.representative := by
    change sectionMap N.source.inclusion _ (_ * _) = _
    rw [map_mul, ← sectionMap_comp, N.sourceTorus_eq]
    change sectionMap P.pair.T.inclusion _ t * sourcePoint N z₀ = _
    rw [hz₀, rescaled_representative x₀ y₀ r₀ c s₀]
  have hz' : targetPoint N z = s₁.representative := by
    change sectionMap (N.hom ≫ N.target.inclusion) _ (_ * _) = _
    rw [map_mul, ← sectionMap_comp, ← Category.assoc N.sourceTorus, N.torus_comm,
      Category.assoc, N.targetTorus_eq, sectionMap_comp, ht]
    change sectionMap Q.pair.T.inclusion _ (torusValue r₁.coroot c) * targetPoint N z₀ = _
    rw [hz₁, rescaled_representative x₁ y₁ r₁ c s₁]
  obtain ⟨W⟩ := exists_weylIdentification P.pair D
  have hsc : s₀.coroot = r.coroot := (linked_coroot D.datum a s₀).trans hr.symm
  have hneg : HasScalarAction P.pair.T a.val⁻¹ (y.val.hom ≫ (P.roots b).val.inclusion) :=
    hab ▸ y.property
  have hrep := linked_representative_eq D W s₀ r hpos₀ hsc
    (rescale (A := A) x₀ c).property (rescale (A := A) y₀ c⁻¹).property hneg
  obtain ⟨s, _, hs⟩ := reflection_congr hpos₁ rfl s₁
  have hy' := matchedOpposite_of_representatives h N he hab x y r s
    (rescale (A := A) y₁ c⁻¹).property z (hz.trans hrep) (hz'.trans hs.symm)
  obtain ⟨s', _, hsr⟩ := reflection_congr rfl hy' s
  exact ⟨hab', s', linked_coroot E.datum _ s', z, hz.trans hrep, hz'.trans (hsr.trans hs).symm⟩

end LinkedTransports


section LocalComparison

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CharacterDescent (Character)
open RootGroups (CorootReflection HasScalarAction Proportional rootPoint)
open Pinning (RootCoordinate SimpleRoot)
open CellHomomorphism (Coordinates)
open BorelsAndChambers (subgroupRoots)
open Additive
open Specs.RankTwoLifting (MatchesPinning MatchesRootGroups)

open private sectionMap sectionMap_comp simple_representatives_exist map_linked_reflection
  linked_representative_eq from LinearAlgebraicGroups.Classification.NormalizerComparison
open private linked_coroot positive_transfer base_isPos_iff_subgroupRoots
  from LinearAlgebraicGroups.Classification.RankTwoLifting
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option backward.isDefEq.respectTransparency false

private noncomputable def comparedCoordinates (e : RootIsomorphisms P Q d)
    (X : ∀ a, RootCoordinate A P.pair.T (P.roots a).val a.val) :
    ∀ b, RootCoordinate A Q.pair.T (Q.roots b).val b.val :=
  (Equiv.piCongrLeft (fun b => RootCoordinate A Q.pair.T (Q.roots b).val b.val) d)
    (fun a => rootCoordinate Q (d a) ((X a).val ≪≫ e a))

private theorem comparedCoordinates_apply (e : RootIsomorphisms P Q d)
    (X : ∀ a, RootCoordinate A P.pair.T (P.roots a).val a.val) (a : Root P.pair.T) :
    comparedCoordinates e X (d a) = rootCoordinate Q (d a) ((X a).val ≪≫ e a) :=
  Equiv.piCongrLeft_apply_apply _ _ _ a

private abbrev subsystemInclusion {a b : Root P.pair.T} (S : Subsystem P D a b) :=
  S.groupIso.hom ≫ S.closed.inclusion

private theorem subsystemInclusion_torus {a b : Root P.pair.T} (S : Subsystem P D a b) :
    S.localGroup.pair.T.inclusion ≫ subsystemInclusion S = S.torus.inv ≫ P.pair.T.inclusion := by
  rw [← S.torus_comm, Iso.inv_hom_id_assoc]

private theorem subsystemInclusion_map {a b : Root P.pair.T} (S : Subsystem P D a b)
    {r : Root S.localGroup.pair.T} (x : A.group ≅ (S.localGroup.roots r).val.group) :
    rootMap (P := S.localGroup) (a := r) x ≫ subsystemInclusion S =
      rootMap (P := P) (a := S.roots r) (x ≪≫ S.rootIso r) := by
  simp only [rootMap, Iso.trans_hom, Category.assoc, S.root_comm]

private theorem along_full_torus {a b : Root P.pair.T} (S : Subsystem P D a b)
    {w : 𝟙_ (SchemeOver k) ⟶ S.localGroup.pair.G.val.X}
    {r s : Root S.localGroup.pair.T} (hw : MovesCharacter S.localGroup.pair.T w r.val s.val) :
    MovesCharacter P.pair.T (sectionMap (subsystemInclusion S) _ w)
      (S.roots r).val (S.roots s).val := by
  obtain ⟨v, hv, hχ⟩ := hw
  refine ⟨S.torus ≪≫ v ≪≫ S.torus.symm, ?_, ?_⟩
  · let i := S.torus.hom.hom.hom
    let j := S.localGroup.pair.T.inclusion.hom.hom
    let f := (subsystemInclusion S).hom.hom
    let g := toUnit S.localGroup.pair.T.group.X ≫ w
    have ht : i ≫ j ≫ f = P.pair.T.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map S.torus_comm
    have ht' : j ≫ f = S.torus.inv.hom.hom ≫ P.pair.T.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map (subsystemInclusion_torus S)
    have hv' : v.hom.hom.hom ≫ j = g * j * g⁻¹ := hv
    have hg : i ≫ g = toUnit P.pair.T.group.X ≫ w := by
      dsimp only [g]
      rw [← Category.assoc, comp_toUnit]
    calc
      _ = (i ≫ (v.hom.hom.hom ≫ j)) ≫ f := by
        simp only [i, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc, ht']
      _ = _ := by
        rw [hv', MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
          MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hg, Category.assoc i j, ht]
        rfl
  · simp only [Iso.trans_inv, Iso.symm_inv, ← S.root_eq, Category.assoc,
      Iso.inv_hom_id_assoc, hχ]

set_option maxHeartbeats 950000 in
/-- A rank-two lift matching the prescribed local pins has matching images
of each linked simple representative in the two ambient normalizers. -/
private theorem localSimple_matches (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (hl : MatchesLinkedPairs N e)
    {a b : Root P.pair.T} (S : Subsystem P D a b) (T : Subsystem Q E (d a) (d b))
    (δ : Root S.localGroup.pair.T ≃ Root T.localGroup.pair.T)
    (hδ : ∀ r, T.roots (δ r) = d (S.roots r))
    (f : S.localGroup.pair.G.val ⟶ T.localGroup.pair.G.val)
    (hf : MatchesPinning δ (S.torus.inv ≫ τ ≫ T.torus.hom) f) (hg : MatchesRootGroups δ f)
    (hpins : ∀ i : SimpleRoot S.localGroup.pair,
      pinMap i ≫ f ≫ subsystemInclusion T =
        (S.localGroup.pin i).val.hom ≫ (S.rootIso i.val).hom ≫ (e (S.roots i.val)).hom ≫
          (Q.roots (d (S.roots i.val))).val.inclusion)
    (i : SimpleRoot S.localGroup.pair)
    (n : Specs.NormalizerComparison.SimpleRepresentative S.localGroup S.datum i) :
    ∃ z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X,
      sourcePoint N z = sectionMap (subsystemInclusion S) _ n.reflection.representative ∧
      targetPoint N z = sectionMap (f ≫ subsystemInclusion T) _ n.reflection.representative := by
  letI := D.comm
  letI := E.comm
  let α := S.roots i.val
  let β := S.roots n.opposite
  have hβ : β.val = α.val⁻¹ := by
    rw [show β.val = S.torus.hom ≫ n.opposite.val from (S.root_eq _).symm, n.opposite_eq,
      show α.val = S.torus.hom ≫ i.val.val from (S.root_eq _).symm]
    exact (pullbackCharacters S.torus.hom).map_inv i.val.val
  have hβ' := map_opposite h hβ
  let x := rootCoordinate P α ((S.localGroup.pin i).val ≪≫ S.rootIso i.val)
  let y := rootCoordinate P β (n.negative.val ≪≫ S.rootIso n.opposite)
  have hx : pinMap i ≫ subsystemInclusion S = rootMap (P := P) (a := α) x.val :=
    subsystemInclusion_map S _
  have hy : rootMap (P := S.localGroup) (a := n.opposite) n.negative.val ≫ subsystemInclusion S =
      rootMap (P := P) (a := β) y.val :=
    subsystemInclusion_map S _
  have hα : S.torus.inv ≫ α.val = i.val.val := by
    rw [show α.val = S.torus.hom ≫ i.val.val from (S.root_eq _).symm, Iso.inv_hom_id_assoc]
  obtain ⟨r, _, hr⟩ := map_linked_reflection (subsystemInclusion S) S.torus.inv
    (subsystemInclusion_torus S) P.pair.split hα n.reflection (hx.symm ▸ x.property)
    (hy.symm ▸ (hβ ▸ y.property))
  obtain ⟨r', _, hr'⟩ := reflection_congr hx hy r
  obtain ⟨_, s, hsc, z, hz, hz'⟩ := hl α β hβ x y r' (linked_coroot D.datum α r')
  let F := f ≫ subsystemInclusion T
  let σ := S.torus.inv ≫ τ
  have hT : S.localGroup.pair.T.inclusion ≫ F = σ ≫ Q.pair.T.inclusion := by
    rw [show S.localGroup.pair.T.inclusion ≫ F =
      (S.localGroup.pair.T.inclusion ≫ f) ≫ subsystemInclusion T from (Category.assoc _ _ _).symm,
      hf.1]
    simp only [σ, Category.assoc, subsystemInclusion_torus, Iso.hom_inv_id_assoc]
  have hχ : σ ≫ (d α).val = i.val.val := by
    rw [show σ = S.torus.inv ≫ τ from rfl, Category.assoc, h.root, hα]
  have hp : pinMap i ≫ F = rootMap (P := Q) (a := d α) (x.val ≪≫ e α) := by
    simpa only [x, α, rootCoordinate, rootMap, Iso.trans_hom, Category.assoc] using hpins i
  obtain ⟨yiso, hyiso⟩ := hg n.opposite
  have hyF : HasScalarAction Q.pair.T (d α).val⁻¹
      (rootMap (P := S.localGroup) (a := n.opposite) n.negative.val ≫ F) := by
    have hw : rootMap (P := S.localGroup) (a := n.opposite) n.negative.val ≫ F =
        rootMap (P := Q) (a := T.roots (δ n.opposite))
          (n.negative.val ≪≫ yiso ≪≫ T.rootIso (δ n.opposite)) := by
      change (n.negative.val.hom ≫ (S.localGroup.roots n.opposite).val.inclusion) ≫
        (f ≫ subsystemInclusion T) = _
      simp only [rootMap, Iso.trans_hom, Category.assoc]
      rw [← Category.assoc (S.localGroup.roots n.opposite).val.inclusion, hyiso,
        Category.assoc, T.root_comm]
    rw [hw, ← hβ', ← hδ]
    exact (rootCoordinate Q _ _).property
  have hxF : HasScalarAction Q.pair.T (d α).val (pinMap i ≫ F) :=
    hp.symm ▸ (rootCoordinate Q (d α) (x.val ≪≫ e α)).property
  obtain ⟨s', _, hs'⟩ := map_linked_reflection F σ hT Q.pair.split hχ n.reflection hxF hyF
  obtain ⟨W⟩ := exists_weylIdentification Q.pair E
  have hy' : HasScalarAction Q.pair.T (d α).val⁻¹
      (rootMap (P := Q) (a := d β) (y.val ≪≫ e β)) :=
    hβ' ▸ (rootCoordinate Q (d β) (y.val ≪≫ e β)).property
  have hsrep := linked_representative_eq E W s' s hp
    ((linked_coroot E.datum (d α) s').trans hsc.symm) hxF hyF hy'
  exact ⟨z, hz.trans (hr'.trans hr), hz'.trans (hsrep.symm.trans hs')⟩

private theorem subsystem_transports (N : Normalizers P Q D E d τ)
    {a b : Root P.pair.T} (S : Subsystem P D a b)
    (F : S.localGroup.pair.G.val ⟶ Q.pair.G.val)
    (n : ∀ i : SimpleRoot S.localGroup.pair,
      Specs.NormalizerComparison.SimpleRepresentative S.localGroup S.datum i)
    (z : SimpleRoot S.localGroup.pair → (𝟙_ (SchemeOver k) ⟶ N.source.group.X))
    (hz : ∀ i, sourcePoint N (z i) =
      sectionMap (subsystemInclusion S) _ (n i).reflection.representative)
    (hz' : ∀ i, targetPoint N (z i) = sectionMap F _ (n i).reflection.representative)
    (r : Root S.localGroup.pair.T) :
    ∃ (i : SimpleRoot S.localGroup.pair)
      (v : 𝟙_ (SchemeOver k) ⟶ N.source.group.X)
      (w : 𝟙_ (SchemeOver k) ⟶ S.localGroup.pair.G.val.X),
      sourcePoint N v = sectionMap (subsystemInclusion S) _ w ∧
      targetPoint N v = sectionMap F _ w ∧
      MovesCharacter P.pair.T (sourcePoint N v) (S.roots i.val).val (S.roots r).val := by
  letI := S.datum.comm
  letI := S.datum.datum.finiteRoots
  letI := S.datum.datum.reduced
  let R := S.datum.datum.rootDatum
  have step (i : SimpleRoot S.localGroup.pair) (r : Root S.localGroup.pair.T) :
      MovesCharacter P.pair.T (sourcePoint N (z i)) (S.roots r).val
        (S.roots (R.reflectionPerm i.val r)).val := by
    let s := (n i).reflection
    have hp : CharacterPairing.pairing S.localGroup.pair.T.group r.val s.coroot =
        R.pairing r i.val := by
      rw [show s.coroot = Additive.toMul (R.coroot i.val) from (n i).coroot_eq,
        ← S.datum.datum.pairing_eq, ← S.datum.datum.root_eq]
      rfl
    have he : MovesCharacter S.localGroup.pair.T s.representative r.val (R.reflectionPerm i.val r).val := by
      refine ⟨s.conjugation, s.conjugates, ?_⟩
      have hρ := R.reflection_apply_root (i := i.val) (j := r)
      rw [← R.root_reflectionPerm] at hρ
      apply Additive.ofMul.injective
      rw [s.reflection, ofMul_mul, ofMul_zpow, neg_smul, ← sub_eq_add_neg, hp,
        ← S.datum.datum.root_eq r, ← S.datum.datum.root_eq i.val, ← hρ, S.datum.datum.root_eq]
    rw [hz]
    exact along_full_torus S he
  have hop (r : Root S.localGroup.pair.T) :
      (S.roots (R.reflectionPerm r r)).val = (S.roots r).val⁻¹ := by
    have hr := (R.root_eq_neg_iff (i := R.reflectionPerm r r) (j := r)).mpr rfl
    rw [S.datum.datum.root_eq, S.datum.datum.root_eq] at hr
    rw [← S.root_eq (R.reflectionPerm r r), ← S.root_eq r,
      show (R.reflectionPerm r r).val = r.val⁻¹ from hr]
    exact (pullbackCharacters S.torus.hom).map_inv r.val
  refine S.datum.base.induction_reflect r (p := fun r =>
    ∃ (i : SimpleRoot S.localGroup.pair) (v : 𝟙_ (SchemeOver k) ⟶ N.source.group.X)
      (w : 𝟙_ (SchemeOver k) ⟶ S.localGroup.pair.G.val.X),
      sourcePoint N v = sectionMap (subsystemInclusion S) _ w ∧
      targetPoint N v = sectionMap F _ w ∧
      MovesCharacter P.pair.T (sourcePoint N v) (S.roots i.val).val (S.roots r).val) ?_ ?_ ?_
  · intro r hr
    obtain ⟨i, v, w, hv, hv', hm⟩ := hr
    have hs := step i i.val
    rw [hop] at hs ⊢
    refine ⟨i, v * z i, w * (n i).reflection.representative, ?_, ?_, ?_⟩
    · rw [sourcePoint_mul, map_mul, hz, hv]
    · rw [targetPoint_mul, map_mul, hz', hv']
    · rw [sourcePoint_mul]
      exact movesCharacter_mul hs (movesCharacter_invCharacter hm)
  · intro r hr
    refine ⟨⟨r, (S.datum.simple_iff r).mp hr⟩, 1, 1, by rw [sourcePoint_one, map_one],
      by rw [targetPoint_one, map_one], ?_⟩
    rw [sourcePoint_one]
    exact movesCharacter_one P.pair.T _
  · intro r s hr hs
    obtain ⟨i, v, w, hv, hv', hm⟩ := hr
    let j : SimpleRoot S.localGroup.pair := ⟨s, (S.datum.simple_iff s).mp hs⟩
    refine ⟨i, z j * v, (n j).reflection.representative * w, ?_, ?_, ?_⟩
    · rw [sourcePoint_mul, map_mul, hz, hv]
    · rw [targetPoint_mul, map_mul, hz', hv']
    · rw [sourcePoint_mul]
      exact movesCharacter_mul hm (step j r)

set_option maxHeartbeats 700000 in
private theorem localRootMaps_match (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d}
    (he : MatchesTransports N e) (hl : MatchesLinkedPairs N e)
    {a b : Root P.pair.T} (S : Subsystem P D a b) (T : Subsystem Q E (d a) (d b))
    (δ : Root S.localGroup.pair.T ≃ Root T.localGroup.pair.T)
    (hδ : ∀ r, T.roots (δ r) = d (S.roots r))
    (f : S.localGroup.pair.G.val ⟶ T.localGroup.pair.G.val)
    (hf : MatchesPinning δ (S.torus.inv ≫ τ ≫ T.torus.hom) f) (hg : MatchesRootGroups δ f)
    (hpins : ∀ i : SimpleRoot S.localGroup.pair,
      pinMap i ≫ f ≫ subsystemInclusion T =
        (S.localGroup.pin i).val.hom ≫ (S.rootIso i.val).hom ≫ (e (S.roots i.val)).hom ≫
          (Q.roots (d (S.roots i.val))).val.inclusion) :
    ∀ r, (S.localGroup.roots r).val.inclusion ≫ f ≫ subsystemInclusion T =
      (S.rootIso r).hom ≫ (e (S.roots r)).hom ≫ (Q.roots (d (S.roots r))).val.inclusion := by
  classical
  let F := f ≫ subsystemInclusion T
  obtain ⟨n⟩ := simple_representatives_exist S.localGroup S.datum
  choose z hz hz' using fun i => localSimple_matches h N hl S T δ hδ f hf hg hpins i (n i)
  intro r
  obtain ⟨i, v, w, hv, hv', hm⟩ := subsystem_transports N S F n z hz hz' r
  let x := (S.localGroup.pin i).val ≪≫ S.rootIso i.val
  obtain ⟨y, hy, hy'⟩ := matchedTransport_at h N he v hm x
  let y₀ := y ≪≫ (S.rootIso r).symm
  have hx : pinMap i ≫ subsystemInclusion S = rootMap (P := P) (a := S.roots i.val) x :=
    subsystemInclusion_map S _
  have hy₀ : rootMap (P := S.localGroup) (a := r) y₀ ≫ subsystemInclusion S =
      rootMap (P := P) (a := S.roots r) y := by
    rw [subsystemInclusion_map]
    simp only [rootMap, y₀, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  letI := S.closed.isClosedImmersion
  letI : Mono S.closed.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono (subsystemInclusion S).hom.hom := by
    change Mono (S.groupIso.hom.hom.hom ≫ S.closed.inclusion.hom.hom)
    infer_instance
  have ht : TransportsCoordinate w (pinMap i) (rootMap (P := S.localGroup) (a := r) y₀) :=
    transport_of_map (subsystemInclusion S) (by simpa only [← hv, hx, hy₀] using hy)
  have ht' := transport_map F ht
  have hp : pinMap i ≫ F = rootMap (P := Q) (a := d (S.roots i.val)) (x ≪≫ e (S.roots i.val)) := by
    simpa only [rootMap, x, Iso.trans_hom, Category.assoc] using hpins i
  rw [← hv', hp] at ht'
  have heq : rootMap (P := S.localGroup) (a := r) y₀ ≫ F =
      rootMap (P := Q) (a := d (S.roots r)) (y ≪≫ e (S.roots r)) :=
    rootMorphism_ext fun R t => (ht' R t).symm.trans (hy' R t)
  apply (cancel_epi y₀.hom).mp
  simpa only [rootMap, y₀, F, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using heq

set_option maxHeartbeats 750000 in
private theorem matchesRankTwo (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d}
    (he : MatchesTransports N e) (hl : MatchesLinkedPairs N e)
    (X : ∀ a, RootCoordinate A P.pair.T (P.roots a).val a.val) :
    MatchesRankTwo (D := D) (E := E) (τ := τ) e := by
  letI := D.comm
  letI := E.comm
  intro a b hab
  have hab' : ¬ Proportional (d a).val (d b).val := by
    rintro ⟨m, n, hm, hn, hp⟩
    apply hab
    refine ⟨m, n, hm, hn, ?_⟩
    simpa only [map_zpow, show ∀ r, pullbackCharacters τ (d r).val = r.val from h.root]
      using congrArg (pullbackCharacters τ) hp
  obtain ⟨KS⟩ := commonKernelSubtorus P.pair.split a.val b.val
  obtain ⟨KT⟩ := commonKernelSubtorus Q.pair.split (d a).val (d b).val
  obtain ⟨S, hSpos, hSpin⟩ := exists_subsystem P D a b hab X KS
  obtain ⟨T, hTpos, hTpin⟩ := exists_subsystem Q E (d a) (d b) hab' (comparedCoordinates e X) KT
  obtain ⟨δ, hδ⟩ := exists_subsystem_root_equiv h S T
  have hδ' (r : Root S.localGroup.pair.T) : d (S.roots r) = T.roots (δ r) := (hδ r).symm
  have hpos (r : Root S.localGroup.pair.T) :
      r ∈ subgroupRoots S.localGroup.pair.T S.localGroup.pair.B ↔
        δ r ∈ subgroupRoots T.localGroup.pair.T T.localGroup.pair.B := by
    rw [hSpos, hTpos, hδ, ← base_isPos_iff_subgroupRoots D, ← base_isPos_iff_subgroupRoots E]
    exact positive_transfer h (S.roots r)
  let σ := S.torus.inv ≫ τ ≫ T.torus.hom
  let H := subsystemCompatible h S T δ hδ hpos
  obtain ⟨f, hf, hfin, hflat, hsurj, hker, hiso, hg⟩ :=
    Classification.RankTwoLifting.liftTorusMap S.localGroup T.localGroup S.datum T.datum
      S.rank.le δ σ H
  have hp (i : SimpleRoot S.localGroup.pair) :
      pinMap i ≫ f ≫ subsystemInclusion T =
        (S.localGroup.pin i).val.hom ≫ (S.rootIso i.val).hom ≫ (e (S.roots i.val)).hom ≫
          (Q.roots (d (S.roots i.val))).val.inclusion := by
    let j := correspondingSimple H i
    have h := hTpin j
    have hS : ((S.localGroup.pin i).val ≪≫ S.rootIso i.val) = (X (S.roots i.val)).val := by
      letI := inclusion_mono (P.roots (S.roots i.val)).val
      apply Iso.ext
      apply (cancel_mono (P.roots (S.roots i.val)).val.inclusion).mp
      exact (subsystemInclusion_map S (S.localGroup.pin i).val).symm.trans (hSpin i)
    rw [← Category.assoc, show pinMap i ≫ f = pinMap j from hf.2 i j rfl]
    change pinMap j ≫ subsystemInclusion T = _
    change pinMap j ≫ subsystemInclusion T =
      ((comparedCoordinates e X (T.roots (δ i.val))).val.hom ≫
        (Q.roots (T.roots (δ i.val))).val.inclusion) at h
    rw [h, hδ, comparedCoordinates_apply, ← hS]
    simp only [rootCoordinate, Iso.trans_hom, Category.assoc]
  refine ⟨S, T, δ, H, hδ', f, hf, hfin, hflat, hsurj, hker, ?_,
    localRootMaps_match h N he hl S T δ hδ f hf hg hp⟩
  exact fun hs => hiso ((pullbackToriCompatibility S.torus T.torus τ h.injective h.finiteIndex).2.2 hs)

end LocalComparison


section SignedCommutators

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AbstractPairing (Datum)
open AdjointRepresentation (GroupPoints)
open CellHomomorphism (CommutatorTerm Coordinates SameSignedCommutators)
open Pinning (RootCoordinate SimpleRoot IsSimple)
open BorelsAndChambers (subgroupRoots)
open RootGroups (CorootReflection rootPoint)

open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private coordinatesAt_exists from LinearAlgebraicGroups.Classification.RankTwoRelations
open private cellCoordinates oppositeRoot oppositeRoot_val oppositeRoot_oppositeRoot
  positive_opposite_iff base_isPos_iff_subgroupRoots signed_rank_two paired_nonproportional
  from LinearAlgebraicGroups.Classification.RankTwoLifting

set_option backward.isDefEq.respectTransparency false

private theorem exists_linkedCoordinates (P : PinnedGroup A) (D : AttachedDatum P.pair) :
    Nonempty (Specs.RankTwoRelations.Coordinates (P := P)) := by
  classical
  letI := D.comm
  have hpos := base_isPos_iff_subgroupRoots D
  let x (r : Root P.pair.T) : RootCoordinate A P.pair.T (P.roots r).val r.val :=
    if h : IsSimple P.pair r then P.pin ⟨r, h⟩
    else Classical.choice (coordinatesAt_exists P r)
  choose y hy using fun r => RankTwoRelations.linkedOppositeCoordinate P r (oppositeRoot D.datum r)
    (oppositeRoot_val D.datum r) (x r)
  let c (r : Root P.pair.T) : RootCoordinate A P.pair.T (P.roots r).val r.val :=
    if D.base.IsPos r then x r
    else oppositeRoot_oppositeRoot D.datum r ▸ y (oppositeRoot D.datum r)
  refine ⟨⟨c, ?_, ?_⟩⟩
  · intro i
    simp only [c, x, ite_eq_left ((hpos i.val).mpr i.property.1), dite_eq_left i.property]
  · intro a b ha hb
    have h : b = oppositeRoot D.datum a :=
      Subtype.ext (hb.trans (oppositeRoot_val D.datum a).symm)
    subst b
    have ha' := (hpos a).mpr ha
    have hb' : ¬ D.base.IsPos (oppositeRoot D.datum a) :=
      fun h => ((positive_opposite_iff D a).mp h) ha'
    have hc : c (oppositeRoot D.datum a) = y a := by
      simp only [c, ite_eq_right hb']
      have move (b : Root P.pair.T) (e : b = a) :
          (congrArg (oppositeRoot D.datum) e ▸ y b) = y a := by
        subst b
        rfl
      exact move _ (oppositeRoot_oppositeRoot D.datum a)
    rw [show c a = x a from ite_eq_left ha', hc]
    exact hy a

private theorem comparison_matchesPin (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (he : MatchesTransports N e)
    (i : SimpleRoot P.pair) (j : SimpleRoot Q.pair) (hij : d i.val = j.val) :
    rootMap (P := Q) (a := d i.val) ((P.pin i).val ≪≫ e i.val) = pinMap j := by
  have hm : MovesCharacter P.pair.T (sourcePoint N 1) i.val.val i.val.val := by
    rw [sourcePoint_one]
    exact movesCharacter_one _ _
  obtain ⟨x, hx, hy⟩ := he.2 i.val i j hij 1 hm
  have hxx : x = (P.pin i).val := by
    letI := inclusion_mono (P.roots i.val).val
    apply Iso.ext
    apply (cancel_mono (P.roots i.val).val.inclusion).mp
    exact rootMorphism_ext fun R t => by
      have h := hx R t
      dsimp only at h
      rw [MonObj.one_comp, MonObj.comp_one, one_mul, inv_one, mul_one] at h
      exact h.symm
  subst x
  exact rootMorphism_ext fun R t => by
    let g : GroupPoints Q.pair.G.val R := toUnit _ ≫ targetPoint N 1
    have hg : g = 1 := by
      change (toUnit _ ≫ targetPoint N 1) = 1
      rw [targetPoint_one, MonObj.comp_one]
    have h : g * rootPoint (pinMap j) R t * g⁻¹ = _ := hy R t
    rw [hg, one_mul, inv_one, mul_one] at h
    exact h.symm

private theorem identityCompatible (P : PinnedGroup A) (D : AttachedDatum P.pair) :
    Compatible P P D D (Equiv.refl _) (𝟙 _) := by
  have hm : pullbackCharacters (𝟙 P.pair.T.group) = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro a
    exact Category.id_comp a
  refine ⟨?_, ?_, fun a => Category.id_comp a.val, fun a => Category.comp_id _, fun _ => Iff.rfl⟩
  · rw [hm]
    exact Function.injective_id
  · have htop : (pullbackCharacters (𝟙 P.pair.T.group)).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (by rw [hm]; exact Function.surjective_id)
    rw [htop]
    letI := QuotientGroup.subsingleton_quotient_top (G := CharacterDescent.Character P.pair.T.group)
    infer_instance

/-- A signed word with scalar coefficients exists in normalized coordinates
in every rank-two centralizer. -/
private theorem rankTwoSigned (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (hrank : letI := D.comm; D.base.support.card = 2) :
    ∃ X : Specs.RankTwoRelations.Coordinates (P := P),
      letI := D.comm
      let C := cellCoordinates P D (base_isPos_iff_subgroupRoots D) X
      SameSignedCommutators C C (Equiv.refl _) := by
  classical
  letI := D.comm
  let h := identityCompatible P D
  obtain ⟨κ, ⟨F⟩⟩ := Classification.RankTwoLifting.rankTwoFrame P D hrank
  obtain ⟨X, _, hX⟩ := RankTwoRelations.rankTwoRelations P κ F
  obtain ⟨Y, _, hactY, hposY, _⟩ :=
    RankTwoRelations.rankTwoRelations P κ (Classification.RankTwoLifting.transportFrame h F)
  have hs := signed_rank_two h (base_isPos_iff_subgroupRoots D) (base_isPos_iff_subgroupRoots D)
    F X Y hX ⟨hactY, hposY⟩
  refine ⟨X, fun a b hne hopp => ?_⟩
  obtain ⟨L, hL⟩ := hs a b hne hopp
  exact ⟨L, fun R x y => ⟨(hL R x y).1, (hL R x y).1⟩⟩

private theorem rescaleCommutator {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {a b : Root T} (X X' : Root T → (A.group ⟶ G.val)) (c : Root T → kˣ)
    (hx : ∀ r (R : TestAlgebra k) (t : R),
      rootPoint (X' r) R t = rootPoint (X r) R (algebraMap k R (c r : k) * t))
    (L : List (CommutatorTerm a b))
    (hL : ∀ (R : TestAlgebra k) (x y : R),
      let p := rootPoint (X a) R x
      let q := rootPoint (X b) R y
      p * q * p⁻¹ * q⁻¹ =
        (L.map fun t => rootPoint (X t.root) R (algebraMap k R t.coefficient * x ^ t.i * y ^ t.j)).prod) :
    ∃ L' : List (CommutatorTerm a b), ∀ (R : TestAlgebra k) (x y : R),
      let p := rootPoint (X' a) R x
      let q := rootPoint (X' b) R y
      p * q * p⁻¹ * q⁻¹ =
        (L'.map fun t => rootPoint (X' t.root) R (algebraMap k R t.coefficient * x ^ t.i * y ^ t.j)).prod := by
  let scale (t : CommutatorTerm a b) : CommutatorTerm a b :=
    { t with coefficient := (↑(c t.root)⁻¹ : k) * t.coefficient * (c a : k) ^ t.i * (c b : k) ^ t.j }
  refine ⟨L.map scale, fun R u v => ?_⟩
  have parameter (t : CommutatorTerm a b) :
      algebraMap k R (c t.root : k) * (algebraMap k R (scale t).coefficient * u ^ t.i * v ^ t.j) =
        algebraMap k R t.coefficient * (algebraMap k R (c a : k) * u) ^ t.i *
          (algebraMap k R (c b : k) * v) ^ t.j := by
    have hunit : algebraMap k R (c t.root : k) * algebraMap k R (↑(c t.root)⁻¹ : k) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    simp only [scale, map_mul, map_pow, mul_pow]
    calc
      _ = (algebraMap k R (c t.root : k) * algebraMap k R (↑(c t.root)⁻¹ : k)) *
          (algebraMap k R t.coefficient * (algebraMap k R (c a : k) * u) ^ t.i *
            (algebraMap k R (c b : k) * v) ^ t.j) := by simp only [mul_pow]; ring
      _ = _ := by rw [hunit, one_mul, mul_pow, mul_pow]
  have H := hL R (algebraMap k R (c a : k) * u) (algebraMap k R (c b : k) * v)
  dsimp only at H ⊢
  rw [hx, hx, H, List.map_map]
  apply congrArg List.prod
  exact List.map_congr_left (fun t _ => by
    change rootPoint (X t.root) R _ = rootPoint (X' t.root) R _
    rw [hx, parameter])

set_option maxHeartbeats 950000 in
private theorem signedAlongSubsystems {e : RootIsomorphisms P Q d}
    (hr : MatchesRankTwo (D := D) (E := E) (τ := τ) e)
    (x : ∀ a, A.group ≅ (P.roots a).val.group)
    (a b : Root P.pair.T) (hne : a ≠ b) (hopp : b.val ≠ a.val⁻¹) :
    ∃ L : List (CommutatorTerm a b),
      ∀ (R : TestAlgebra k) (u v : R),
        let g := rootPoint (rootMap (P := P) (a := a) (x a)) R u
        let h := rootPoint (rootMap (P := P) (a := b) (x b)) R v
        let g' := rootPoint (rootMap (P := Q) (a := d a) (x a ≪≫ e a)) R u
        let h' := rootPoint (rootMap (P := Q) (a := d b) (x b ≪≫ e b)) R v
        (g * h * g⁻¹ * h⁻¹ = (L.map fun t => rootPoint (rootMap (P := P) (a := t.root) (x t.root)) R
          (algebraMap k R t.coefficient * u ^ t.i * v ^ t.j)).prod) ∧
        (g' * h' * g'⁻¹ * h'⁻¹ = (L.map fun t =>
          rootPoint (rootMap (P := Q) (a := d t.root) (x t.root ≪≫ e t.root)) R
            (algebraMap k R t.coefficient * u ^ t.i * v ^ t.j)).prod) := by
  classical
  obtain ⟨S, T, δ, _, _, f, _, _, _, _, _, _, hroot⟩ := hr a b (paired_nonproportional hne hopp)
  have ha : a ∈ Set.range S.roots := by
    rw [S.root_range]
    exact ⟨1, 1, 0, one_ne_zero, by simp⟩
  have hb : b ∈ Set.range S.roots := by
    rw [S.root_range]
    exact ⟨1, 0, 1, one_ne_zero, by simp⟩
  obtain ⟨α, hα⟩ := ha
  obtain ⟨β, hβ⟩ := hb
  have hne' : α ≠ β := fun h => hne (hα.symm.trans ((congrArg S.roots h).trans hβ))
  have hopp' : β.val ≠ α.val⁻¹ := by
    intro h
    apply hopp
    calc
      _ = (S.roots β).val := congrArg Subtype.val hβ.symm
      _ = (S.roots α).val⁻¹ := by
        rw [← S.root_eq β, ← S.root_eq α, h]
        exact (pullbackCharacters S.torus.hom).map_inv α.val
      _ = _ := congrArg (fun r : Root P.pair.T => r.val⁻¹) hα
  obtain ⟨C, hC⟩ := rankTwoSigned S.localGroup S.datum S.rank
  let X (r : Root S.localGroup.pair.T) := rootMap (P := S.localGroup) (a := r) (C.coordinate r).val
  let y (r : Root S.localGroup.pair.T) := x (S.roots r) ≪≫ (S.rootIso r).symm
  let Y (r : Root S.localGroup.pair.T) := rootMap (P := S.localGroup) (a := r) (y r)
  have hscale (r : Root S.localGroup.pair.T) :=
    Classification.Pinning.coordinateChanges A S.localGroup.pair.T
      (S.localGroup.roots r).val r.val (C.coordinate r) (rootCoordinate S.localGroup r (y r))
  choose c hc _ using hscale
  obtain ⟨L₀, hL₀⟩ := hC α β hne' hopp'
  obtain ⟨L, hL⟩ := rescaleCommutator X Y c (fun r => by simpa only [X, Y, rootMap, rootCoordinate] using hc r)
    L₀ (fun R u v => (hL₀ R u v).1)
  let term (t : CommutatorTerm α β) : CommutatorTerm a b :=
    { root := S.roots t.root
      i := t.i
      j := t.j
      i_pos := t.i_pos
      j_pos := t.j_pos
      root_eq := by
        calc
          _ = (S.roots α).val ^ t.i * (S.roots β).val ^ t.j := by
            simp only [← S.root_eq]
            change pullbackCharacters S.torus.hom t.root.val =
              (pullbackCharacters S.torus.hom α.val) ^ t.i * (pullbackCharacters S.torus.hom β.val) ^ t.j
            have h := congrArg (pullbackCharacters S.torus.hom) t.root_eq
            simpa only [map_mul, map_pow] using h
          _ = _ := congrArg₂ (fun (a b : Root P.pair.T) => a.val ^ t.i * b.val ^ t.j) hα hβ
      coefficient := t.coefficient }
  refine ⟨L.map term, fun R u v => ?_⟩
  let p (r : Root P.pair.T) := rootMap (P := P) (a := r) (x r)
  let q (r : Root P.pair.T) := rootMap (P := Q) (a := d r) (x r ≪≫ e r)
  have hs (r : Root S.localGroup.pair.T) : Y r ≫ subsystemInclusion S = p (S.roots r) := by
    change rootMap (P := S.localGroup) (a := r) (y r) ≫ subsystemInclusion S = _
    rw [subsystemInclusion_map]
    simp only [p, rootMap, y, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have ht (r : Root S.localGroup.pair.T) : Y r ≫ (f ≫ subsystemInclusion T) = q (S.roots r) := by
    change ((y r).hom ≫ (S.localGroup.roots r).val.inclusion) ≫ (f ≫ subsystemInclusion T) = _
    rw [Category.assoc, hroot]
    simp only [q, rootMap, y, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  let liftWord {H : GroupScheme k} (g : S.localGroup.pair.G.val ⟶ H) :=
    (((groupPointsFunctor k).map g).app R).hom
  have map_eval {H : GroupScheme k} (g : S.localGroup.pair.G.val ⟶ H) (r : Root S.localGroup.pair.T) (u : R) :
      liftWord g (rootPoint (Y r) R u) = rootPoint (Y r ≫ g) R u :=
    (rootPoint_comp (Y r) g R u).symm
  have map_word {H : GroupScheme k} (g : S.localGroup.pair.G.val ⟶ H) :=
    congrArg (liftWord g) (hL R u v)
  have hp := map_word (subsystemInclusion S)
  have hq := map_word (f ≫ subsystemInclusion T)
  dsimp only at hp hq ⊢
  constructor
  · simpa only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, term, map_eval,
      hs, hα, hβ, p] using hp
  · simpa only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def, term, map_eval,
      ht, hα, hβ, q] using hq

set_option maxHeartbeats 650000 in
private theorem exists_matchedCellCoordinates (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d}
    (he : MatchesTransports N e) (hl : MatchesLinkedPairs N e)
    (hr : MatchesRankTwo (D := D) (E := E) (τ := τ) e) :
    MatchesCellCoordinates (D := D) (E := E) e := by
  classical
  letI := D.comm
  letI := E.comm
  obtain ⟨C⟩ := exists_linkedCoordinates P D
  let X := cellCoordinates P D (base_isPos_iff_subgroupRoots D) C
  let Y := comparedCoordinates e C.coordinate
  have hop (a : Root P.pair.T) : oppositeRoot E.datum (d a) = d (X.opposite a) :=
    Subtype.ext ((oppositeRoot_val E.datum (d a)).trans (map_opposite h (X.opposite_eq a)).symm)
  have hy (b : Root Q.pair.T) :
      ∃ r : CorootReflection Q.pair.T b.val (rootMap (P := Q) (a := b) (Y b).val)
          (rootMap (P := Q) (a := oppositeRoot E.datum b) (Y (oppositeRoot E.datum b)).val),
        r.coroot = Additive.toMul (E.datum.rootDatum.coroot b) := by
    obtain ⟨a, rfl⟩ := d.surjective b
    rw [hop, show Y (d a) = _ from comparedCoordinates_apply e C.coordinate a,
      show Y (d (X.opposite a)) = _ from comparedCoordinates_apply e C.coordinate (X.opposite a)]
    obtain ⟨_, s, hcs, _⟩ :=
      hl a (X.opposite a) (X.opposite_eq a) (C.coordinate a) (C.coordinate (X.opposite a))
        (X.reflection a) (X.coroot_eq a)
    exact ⟨s, hcs⟩
  let Y' : Coordinates E.datum A :=
    { groups := Q.roots
      parametrization := fun b => (Y b).val
      scalarAction := fun b => (Y b).property
      opposite := oppositeRoot E.datum
      opposite_eq := oppositeRoot_val E.datum
      reflection := fun b => (hy b).choose
      coroot_eq := fun b => (hy b).choose_spec }
  have hY (a : Root P.pair.T) :
      Y'.root (d a) = rootMap (P := Q) (a := d a) ((C.coordinate a).val ≪≫ e a) := by
    change rootMap (P := Q) (a := d a) (Y (d a)).val = _
    rw [show Y (d a) = _ from comparedCoordinates_apply e C.coordinate a]
    rfl
  refine ⟨X, Y', fun a => ⟨(C.coordinate a).val, rfl, hY a⟩, ?_, ?_, ?_⟩
  · intro i
    change rootMap (P := P) (a := i.val) (C.coordinate i.val).val = pinMap i
    rw [C.pin]
  · intro j
    obtain ⟨a, ha⟩ := d.surjective j.val
    have hs := (h.simple a).mpr (ha.symm ▸ (E.simple_iff j.val).mpr j.property)
    let i : SimpleRoot P.pair := ⟨a, (D.simple_iff a).mp hs⟩
    have hi : d i.val = j.val := ha
    change Y'.root j.val = pinMap j
    calc
      _ = Y'.root (d i.val) := congrArg Y'.root hi.symm
      _ = rootMap (P := Q) (a := d i.val) ((P.pin i).val ≪≫ e i.val) := by rw [hY, C.pin i]
      _ = _ := comparison_matchesPin N he i j hi
  · intro a b hne hopp
    obtain ⟨L, hL⟩ := signedAlongSubsystems hr (fun a => (C.coordinate a).val) a b hne hopp
    have hX (r : Root P.pair.T) :
        X.root r = rootMap (P := P) (a := r) (C.coordinate r).val := rfl
    exact ⟨L, fun R u v => by simpa only [hX, hY] using hL R u v⟩

end SignedCommutators


section SchemeEquivariance

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open Pinning (SimpleRoot)
open RootGroups (CorootReflection rankOneWord)
open DatumAndWeyl (Identification)
open RootPairing
open _root_.LinearAlgebraicGroups.Specs.CellHomomorphism (Matches)

open private sectionMap sectionMap_comp simpleRootOfIndex representative_label
  from LinearAlgebraicGroups.Classification.NormalizerComparison
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private rankOneWord_comp from LinearAlgebraicGroups.RootData.RootGroups
open private subgroupIso_of_same subgroup_inclusion_of_represents
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers
open private positive_transfer base_isPos_iff_subgroupRoots
  from LinearAlgebraicGroups.Classification.RankTwoLifting

set_option backward.isDefEq.respectTransparency false

private theorem representative_map {G H : GroupScheme k} {S : ClosedSubgroup G} {T : ClosedSubgroup H}
    {α : CharacterDescent.Character S.group} {β : CharacterDescent.Character T.group}
    {x y : A.group ⟶ G} {x' y' : A.group ⟶ H}
    (f : G ⟶ H) (r : CorootReflection S α x y) (s : CorootReflection T β x' y')
    (hx : x ≫ f = x') (hy : y ≫ f = y') :
    sectionMap f _ r.representative = s.representative := by
  let g := groundIso (k := k)
  let R := CommAlgCat.of k k
  let B := (testSpec k).obj (op R)
  have hr : toUnit B ≫ r.representative = rankOneWord x y R 1 := r.representative_word
  have hs : toUnit B ≫ s.representative = rankOneWord x' y' R 1 := s.representative_word
  apply (cancel_epi g.hom).mp
  rw [show g.hom = toUnit B from Subsingleton.elim _ _]
  change (toUnit B ≫ r.representative ≫ f.hom.hom) = toUnit B ≫ s.representative
  rw [← Category.assoc, hr, hs, ← rankOneWord_comp, hx, hy]

private theorem hom_agrees_on_generated_quotient {F G W I : Type*}
    [Group F] [Group G] [Group W] (f g : F →* G) (π : F →* W) (n : I → F)
    (hw : Subgroup.closure (Set.range (π ∘ n)) = ⊤)
    (hgen : ∀ i, f (n i) = g (n i))
    (hker : ∀ z, π z = 1 → f z = g z) : ∀ z, f z = g z := by
  let M := f.eqLocus g
  let N := Subgroup.closure (Set.range n)
  have hNM : N ≤ M := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨i, rfl⟩
    exact hgen i)
  have hN : N.map π = ⊤ := by
    simp only [N, MonoidHom.map_closure, ← Set.range_comp, hw]
  intro z
  have hz : π z ∈ N.map π := hN ▸ Subgroup.mem_top _
  obtain ⟨w, hw, hπw⟩ := hz
  have hπ : π (z * w⁻¹) = 1 := by rw [map_mul, map_inv, hπw, mul_inv_cancel]
  have ha : z * w⁻¹ ∈ M := hker _ hπ
  have hb : (z * w⁻¹) * w ∈ M := M.mul_mem ha (hNM hw)
  rw [inv_mul_cancel_right] at hb
  exact hb

private theorem agrees_on_normalizerTorus (N : Normalizers P Q D E d τ)
    (f : P.pair.G.val ⟶ Q.pair.G.val)
    (hT : P.pair.T.inclusion ≫ f = τ ≫ Q.pair.T.inclusion) :
    N.sourceTorus ≫ (N.source.inclusion ≫ f) =
      N.sourceTorus ≫ (N.hom ≫ N.target.inclusion) := by
  rw [← Category.assoc N.sourceTorus N.source.inclusion, N.sourceTorus_eq, hT,
    ← Category.assoc N.sourceTorus N.hom, N.torus_comm, Category.assoc, N.targetTorus_eq]

set_option maxHeartbeats 700000 in
private theorem maps_normalizer_simple (N : Normalizers P Q D E d τ)
    {e : RootIsomorphisms P Q d} (hl : MatchesLinkedPairs N e)
    (f : P.pair.G.val ⟶ Q.pair.G.val)
    (hr : ∀ a, (P.roots a).val.inclusion ≫ f = (e a).hom ≫ (Q.roots (d a)).val.inclusion)
    (i : SimpleRoot P.pair) :
    ∃ z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X,
      sourcePoint N z = (N.sourceSimple i).reflection.representative ∧
      sectionMap (N.source.inclusion ≫ f) _ z = targetPoint N z := by
  letI := D.comm
  letI := E.comm
  let n := N.sourceSimple i
  obtain ⟨_, s, _, z, hz, hz'⟩ :=
    hl i.val n.opposite n.opposite_eq (P.pin i) n.negative n.reflection n.coroot_eq
  have hx : pinMap i ≫ f = rootMap (P := Q) (a := d i.val) ((P.pin i).val ≪≫ e i.val) := by
    simp only [pinMap, rootMap, Category.assoc, Iso.trans_hom, hr]
  have hy : rootMap (P := P) (a := n.opposite) n.negative.val ≫ f =
      rootMap (P := Q) (a := d n.opposite) (n.negative.val ≪≫ e n.opposite) := by
    simp only [rootMap, Category.assoc, Iso.trans_hom, hr]
  refine ⟨z, hz, ?_⟩
  rw [sectionMap_comp]
  change sectionMap f _ (sourcePoint N z) = targetPoint N z
  rw [show sourcePoint N z = n.reflection.representative from hz,
    representative_map f n.reflection s hx hy]
  exact hz'.symm

set_option maxHeartbeats 1600000 in
private theorem rational_normalizer_agrees
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (hl : MatchesLinkedPairs N e)
    (f : P.pair.G.val ⟶ Q.pair.G.val)
    (hT : P.pair.T.inclusion ≫ f = τ ≫ Q.pair.T.inclusion)
    (hr : ∀ a, (P.roots a).val.inclusion ≫ f = (e a).hom ≫ (Q.roots (d a)).val.inclusion) :
    ∀ z : 𝟙_ (SchemeOver k) ⟶ N.source.group.X,
      sectionMap (N.source.inclusion ≫ f) _ z = targetPoint N z := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  classical
  let g := sectionMap (N.source.inclusion ≫ f) (𝟙_ (SchemeOver k))
  let g' := sectionMap (N.hom ≫ N.target.inclusion) (𝟙_ (SchemeOver k))
  choose n hn hn' using fun i : D.base.support => maps_normalizer_simple N hl f hr (simpleRootOfIndex D i)
  obtain ⟨π, _, hkernel, hlab⟩ := source_normalizer_labels N
  have hnπ : (π ∘ n) = fun i : D.base.support => weylGroup.ofIdx D.datum.rootDatum i.val :=
    funext (fun i => hlab (simpleRootOfIndex D i) (n i) (hn i))
  have hgen : Subgroup.closure (Set.range (π ∘ n)) = ⊤ := by
    rw [hnπ]
    exact weylGeneratedByBase D.datum.rootDatum D.base
  refine hom_agrees_on_generated_quotient g g' π n hgen hn' ?_
  intro z hz
  obtain ⟨t, ht⟩ := hkernel z hz
  have htz : sectionMap N.sourceTorus _ t = z := ht
  rw [← htz]
  change sectionMap (N.source.inclusion ≫ f) _ (sectionMap N.sourceTorus _ t) =
    sectionMap (N.hom ≫ N.target.inclusion) _ (sectionMap N.sourceTorus _ t)
  rw [← sectionMap_comp, ← sectionMap_comp, agrees_on_normalizerTorus N f hT]

-- On the open components of the constant quotient, a rational section and
-- the full torus determine the morphism.
private theorem normalizer_ext_on_fibres {G H : GroupScheme k} {T : ClosedSubgroup G}
    {N L : GroupScheme k} {W : Type u} [Group W]
    (j : T.group ⟶ N) (q : N ⟶ L)
    (hc : IsClosedImmersion j.hom.hom.left)
    (hker : IsSchemeKernel q (⟨T.group, j, hc⟩ : ClosedSubgroup N))
    (C : NormalizerLatticeAction.ConstantGroup L W)
    (rep : ∀ w : W, ∃ n : 𝟙_ (SchemeOver k) ⟶ N.X, n ≫ q.hom.hom = C.sectionPoint w)
    (f g : N ⟶ H) (ht : j ≫ f = j ≫ g)
    (hr : ∀ n : 𝟙_ (SchemeOver k) ⟶ N.X, sectionMap f _ n = sectionMap g _ n) :
    f = g := by
  classical
  choose s hs using rep
  let c := C.families N.X q.hom.hom
  let U (w : W) : N.X.left.Opens := ⟨{x | c x = w}, c.isLocallyConstant.isOpen_fiber w⟩
  let P : N.X.left.OpenCover :=
    { I₀ := W
      X w := U w
      f w := (U w).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨c x, ⟨⟨x, rfl⟩, rfl⟩⟩, fun w ↦ inferInstance⟩ }
  let Z (w : W) : SchemeOver k := Over.mk ((U w).ι ≫ N.X.hom)
  let u (w : W) : Z w ⟶ N.X := Over.homMk (U w).ι
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply P.hom_ext
  intro w
  have he : u w ≫ q.hom.hom = (toUnit _ ≫ s w) ≫ q.hom.hom := by
    apply (C.families (Z w)).injective
    rw [Category.assoc, hs, C.constant, C.naturality]
    exact LocallyConstant.ext fun x => x.property
  obtain ⟨t, ht'⟩ := eq_mul_of_same_quotient hker (u w) (toUnit _ ≫ s w) he
  have hw : u w ≫ f.hom.hom = u w ≫ g.hom.hom := by
    rw [ht', MonObj.mul_comp, MonObj.mul_comp]
    have ht'' : j.hom.hom ≫ f.hom.hom = j.hom.hom ≫ g.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map ht
    rw [Category.assoc t, Category.assoc t, ht'']
    simp only [Category.assoc]
    exact congrArg (fun n => (t ≫ j.hom.hom ≫ g.hom.hom) * (toUnit (Z w) ≫ n)) (hr (s w))
  exact congrArg (fun x : Z w ⟶ H.X => x.left) hw

set_option maxHeartbeats 650000 in
private theorem normalizer_agrees (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d} (hl : MatchesLinkedPairs N e)
    (f : P.pair.G.val ⟶ Q.pair.G.val)
    (hT : P.pair.T.inclusion ≫ f = τ ≫ Q.pair.T.inclusion)
    (hr : ∀ a, (P.roots a).val.inclusion ≫ f = (e a).hom ≫ (Q.roots (d a)).val.inclusion) :
    N.source.inclusion ≫ f = N.hom ≫ N.target.inclusion := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  obtain ⟨I⟩ := exists_weylIdentification P.pair D
  obtain ⟨u, hu⟩ := subgroupIso_of_same
    ⟨subgroup_inclusion_of_represents N.representsSource I.representsNormalizer (fun _ _ h => h),
      subgroup_inclusion_of_represents I.representsNormalizer N.representsSource (fun _ _ h => h)⟩
  have hu' : u.inv ≫ N.source.inclusion = I.normalizer.inclusion := by
    rw [← hu, Iso.inv_hom_id_assoc]
  have ht' : I.torusInclusion ≫ u.inv = N.sourceTorus := by
    letI := inclusion_mono N.source
    apply (cancel_mono N.source.inclusion).mp
    rw [Category.assoc, hu', I.inclusion_eq, N.sourceTorus_eq]
  obtain ⟨L, hL⟩ := rationalWeylLabel I
  have hLsurj : Function.Surjective L := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← weylGeneratedByBase D.datum.rootDatum D.base]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    let j := simpleRootOfIndex D i
    let r := N.sourceSimple j
    obtain ⟨n, hn⟩ := (I.representsNormalizer _ _).mp r.reflection.normalizes
    refine ⟨n, I.labelEquiv.injective ?_⟩
    exact representative_label D I j r n hn (I.labelEquiv (L n)) (hL n).1
  have hs (w : I.image.labels) :=
    (hLsurj (I.labelEquiv.symm w)).imp fun n hn => (hL n).1.trans (by rw [hn, MulEquiv.apply_symm_apply])
  apply (cancel_epi u.inv).mp
  apply normalizer_ext_on_fibres I.torusInclusion I.quotient I.torusClosed
    I.isQuotient.1 I.image.constantGroup hs
  · simp only [← Category.assoc I.torusInclusion, ht']
    rw [← Category.assoc N.sourceTorus N.source.inclusion, N.sourceTorus_eq, hT,
      ← Category.assoc N.sourceTorus N.hom, N.torus_comm, Category.assoc, N.targetTorus_eq]
  · intro n
    rw [sectionMap_comp, sectionMap_comp]
    exact rational_normalizer_agrees N hl f hT hr _

private theorem intertwines_of_hom (N : Normalizers P Q D E d τ) (e : RootIsomorphisms P Q d)
    (f : P.pair.G.val ⟶ Q.pair.G.val)
    (hN : N.source.inclusion ≫ f = N.hom ≫ N.target.inclusion)
    (hr : ∀ a, (P.roots a).val.inclusion ≫ f = (e a).hom ≫ (Q.roots (d a)).val.inclusion) :
    Intertwines N e := by
  intro Z z a b c hc
  let p := (e a).hom.hom.hom ▷ Z
  let q := (e a).inv.hom.hom ▷ Z
  have hpq : p ≫ q = 𝟙 _ := by
    change (_ ▷ Z) ≫ (_ ▷ Z) = _
    rw [← MonoidalCategory.comp_whiskerRight, ← Grp.comp_hom_hom, Iso.hom_inv_id]
    exact MonoidalCategory.id_whiskerRight _ _
  have hqp : q ≫ p = 𝟙 _ := by
    change (_ ▷ Z) ≫ (_ ▷ Z) = _
    rw [← MonoidalCategory.comp_whiskerRight, ← Grp.comp_hom_hom, Iso.inv_hom_id]
    exact MonoidalCategory.id_whiskerRight _ _
  let c' := q ≫ c ≫ (e b).hom.hom.hom
  have hcc : p ≫ c' = c ≫ (e b).hom.hom.hom := by
    rw [show c' = q ≫ c ≫ (e b).hom.hom.hom from rfl, ← Category.assoc, hpq, Category.id_comp]
  refine ⟨c', ?_, hcc⟩
  have hp_cancel {v w : (Q.roots (d a)).val.group.X ⊗ Z ⟶ Q.pair.G.val.X}
      (h : p ≫ v = p ≫ w) : v = w := by
    simpa only [← Category.assoc, hqp, Category.id_comp] using congrArg (q ≫ ·) h
  apply hp_cancel
  have h0 := congrArg (fun t => t ≫ f.hom.hom) hc
  have ha : (P.roots a).val.inclusion.hom.hom ≫ f.hom.hom =
      (e a).hom.hom.hom ≫ (Q.roots (d a)).val.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).congr_map (hr a)
  have hb : (P.roots b).val.inclusion.hom.hom ≫ f.hom.hom =
      (e b).hom.hom.hom ≫ (Q.roots (d b)).val.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).congr_map (hr b)
  have hN' : N.source.inclusion.hom.hom ≫ f.hom.hom = N.hom.hom.hom ≫ N.target.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).congr_map hN
  rw [← Category.assoc p c', hcc, Category.assoc c, ← hb, ← Category.assoc c, h0]
  rw [comp_conjugateFamily]
  have hs : p ≫ snd (Q.roots (d a)).val.group.X Z = snd (P.roots a).val.group.X Z :=
    whiskerRight_snd _ _
  have hf : p ≫ fst (Q.roots (d a)).val.group.X Z =
      fst (P.roots a).val.group.X Z ≫ (e a).hom.hom.hom := whiskerRight_fst _ _
  simp only [conjugateFamily, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hN', ha,
    reassoc_of% hs, reassoc_of% hf]

/-- The open-cell multiplication criterion supplies a homomorphism after the
signed relations have been matched. Its equality on the scheme normalizer
then proves equivariance for any scheme family. -/
private theorem schemeEquivariance (h : Compatible P Q D E d τ)
    (N : Normalizers P Q D E d τ) {e : RootIsomorphisms P Q d}
    (hl : MatchesLinkedPairs N e) (hc : MatchesCellCoordinates (D := D) (E := E) e) :
    Intertwines N e := by
  letI := D.comm
  letI := E.comm
  obtain ⟨X, Y, hXY, _, _, hs⟩ := hc
  obtain ⟨f, ⟨hf, _⟩, _⟩ := Classification.CellHomomorphism.cellHomomorphism
    P.pair.G Q.pair.G P.pair.reductive Q.pair.reductive P.pair.T Q.pair.T
    P.pair.split Q.pair.split P.pair.maximal Q.pair.maximal
    P.pair.B Q.pair.B P.pair.borel Q.pair.borel P.pair.containsTorus Q.pair.containsTorus
    D.comm E.comm D.datum E.datum D.base E.base
      (base_isPos_iff_subgroupRoots D) (base_isPos_iff_subgroupRoots E) A X Y d τ
      h.injective h.finiteIndex h.root h.coroot (positive_transfer h) h.simple hs
  have hr (a : Root P.pair.T) : (P.roots a).val.inclusion ≫ f = (e a).hom ≫ (Q.roots (d a)).val.inclusion := by
    obtain ⟨x, hx, hy⟩ := hXY a
    have hm : x.hom ≫ (P.roots a).val.inclusion ≫ f =
        x.hom ≫ (e a).hom ≫ (Q.roots (d a)).val.inclusion := by
      simpa only [hx, hy, Iso.trans_hom, Category.assoc] using hf.2 a
    exact (cancel_epi x.hom).mp hm
  exact intertwines_of_hom N e f (normalizer_agrees N hl f hf.1 hr) hr

end SchemeEquivariance

/-- The matched root subgroup isomorphisms are determined by the simple pins
and the normalizer comparison, and preserve the signed rank-two relations. -/
theorem transportedRootCoordinates : Statement.{u} := by
  intro k _ A P Q D E d τ h
  obtain ⟨N⟩ := normalizersOfComparison Classification.NormalizerComparison.normalizerComparison h
  obtain ⟨e, he⟩ := exists_comparisonFromSimpleTransports h N (simpleTransports h N)
  have hl := matchedLinkedPairs h N he
  obtain ⟨X⟩ := exists_linkedCoordinates P D
  have hr := matchesRankTwo h N he hl X.coordinate
  have hc := exists_matchedCellCoordinates h N he hl hr
  exact ⟨N, e, he, fun e' he' => matchesTransports_unique h N he he',
    schemeEquivariance h N hl hc, hl, hr, hc⟩

end

end LinearAlgebraicGroups.Classification.TransportedRootCoordinates
