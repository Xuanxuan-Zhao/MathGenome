import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open AlgebraicGeometry Bialgebra Coalgebra CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u v

namespace LinearAlgebraicGroups.NontrivialRationalTorus

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme IsSchemeKernel Lie)
open Specs.Unipotent (closedSubgroupAlgebraicGroup IsUnipotent)
open private groupPresentation schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private groupAlgebraOfCharacters groupLikeSpanOfSplit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsSplitTorus IsTorus IsTrivialSubgroup)
open Specs.CentralFrobeniusDescent (CentralFrobeniusReduction ComparesWeights IsAdjointWeight
  IsCentral IsCharacterPower LiftsTori)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.SemisimpleLieCentralizer (HasGeometricNoncentralSemisimple)
open private exists_maximal_torus_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private factor_closed isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private geometricallyConnected_of_connected geometricallyIrreducible_of_connected
  geometry_of_smooth_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private tangentComparison tangentComparison_matrix faithfulLieHom faithfulLieHom_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private affine_tensor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private matrixDifferential_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket

noncomputable section

variable {k : Type u} [Field k]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

private def pullbackCharacter {S T : GroupScheme k} (f : S ⟶ T) :
    Character T →* Character S where
  toFun χ := f ≫ χ
  map_one' := by
    apply Grp.hom_ext
    exact MonObj.comp_one _
  map_mul' χ ψ := by
    apply Grp.hom_ext
    exact MonObj.comp_mul _ _ _

private def characterIso {S T : GroupScheme k} (f : S ≅ T) :
    Character T ≃* Character S where
  toFun := pullbackCharacter f.hom
  invFun := pullbackCharacter f.inv
  left_inv χ := by change f.inv ≫ f.hom ≫ χ = χ; simp
  right_inv χ := by change f.hom ≫ f.inv ≫ χ = χ; simp
  map_mul' := (pullbackCharacter f.hom).map_mul

private theorem torus_of_iso {S T : GroupScheme k} (e : S ≅ T) (hS : IsTorus S) :
    IsTorus T := by
  obtain ⟨E, _, _, _, r, ⟨t⟩⟩ := hS
  exact ⟨E, inferInstance, inferInstance, inferInstance, r,
    ⟨(groupBaseChange k E).mapIso e.symm ≪≫ t⟩⟩

private theorem isSplitTorus_of_isAlgClosed [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val)
    (hT : IsTorus T.group) : IsSplitTorus T.group := by
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup (G := G) T)
  have ht := (GeometricRadicals.torusCoordinateComparison A).mp (torus_of_iso e.symm hT)
  have hm := CharacterDescent.torusIsMultiplicativeType A ht
  have hc := CharacterDescent.torusAndSplitCriteria (k := k) (K := k) A hm
  obtain ⟨r, ⟨i⟩⟩ := hc.1.mp ht
  have hd := hc.2.mpr (fun σ x ↦ by
    rw [show σ = 1 from Subsingleton.elim _ _]
    apply Descent.SemilinearAction.one_act)
  let j := (MulEquiv.ofBijective (CharacterDescent.baseChangeCharacterMap k A)
    (CharacterDescent.baseChangeCharacterMap_bijective k A hd)).trans i
  let f : groupAlgebra k (StandardLattice.{u} r) ≅ A :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k j.symm) ≪≫
      groupAlgebraOfCharacters A (groupLikeSpanOfSplit A hd)
  obtain ⟨t⟩ := CharacterDescent.standardSplitTorus (k := k) r
  exact ⟨r, ⟨e.symm ≪≫ (hopfSpec (CommRingCat.of k)).mapIso f.op ≪≫ t⟩⟩

private theorem character_not_all_prime_powers {T : GroupScheme k} (hT : IsSplitTorus T)
    (p : ℕ) (hp : p.Prime) (χ : Character T) (hχ : χ ≠ 1) :
    ∃ n, ¬ IsCharacterPower (p ^ n) χ := by
  obtain ⟨r, ⟨i⟩⟩ := hT
  obtain ⟨j⟩ := CharacterDescent.standardSplitTorus (k := k) r
  obtain ⟨e, -⟩ := CharacterDescent.splitCompositionPairing (k := k) r
  let a : Character T ≃* StandardLattice.{u} r := (characterIso (j ≪≫ i.symm)).trans e.symm
  have ha : a χ ≠ 1 := by
    intro h
    apply hχ
    apply a.injective
    simpa using h
  have hcoord : ∃ x, a χ x ≠ 1 := by
    by_contra! h
    exact ha (funext h)
  obtain ⟨x, hx⟩ := hcoord
  let z : ℤ := (a χ x).down.toAdd
  have hz : z ≠ 0 := by
    intro h
    apply hx
    exact ULift.ext h
  refine ⟨z.natAbs.factorization p + 1, ?_⟩
  rintro ⟨ψ, hψ⟩
  have h := congrArg (fun c : Character T ↦ (a c x).down.toAdd) hψ
  change (a (ψ ^ _) x).down.toAdd = z at h
  rw [map_pow, Pi.pow_apply] at h
  change ((a ψ x).down ^ (p ^ (z.natAbs.factorization p + 1))).toAdd = z at h
  have hz' : (p ^ (z.natAbs.factorization p + 1) : ℕ) ∣ z.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    refine ⟨(a ψ x).down.toAdd, ?_⟩
    simpa only [toAdd_pow, nsmul_eq_mul, Int.natCast_pow] using h.symm
  exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.mpr hz) hp hz'

private def baseChangeSelfIso (k : Type u) [Field k] :
    groupBaseChange k k ≅ 𝟭 (GroupScheme k) := by
  have eq : fieldSpecMap k k = 𝟙 (Spec (CommRingCat.of k)) := by
    change Spec.map (𝟙 (CommRingCat.of k)) = _
    simp
  let e : Over.pullback (fieldSpecMap k k) ≅ 𝟭 (SchemeOver k) := by
    rw [eq]
    exact Over.pullbackId
  exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpIdIso

private theorem trivial_of_epi {G H : GroupScheme k}
    (S : ClosedSubgroup G) (T : ClosedSubgroup H) (f : S.group ⟶ T.group)
    [Epi f] (hS : IsTrivialSubgroup S) : IsTrivialSubgroup T := by
  obtain ⟨e⟩ := hS
  let a : T.group ⟶ Grp.trivial (SchemeOver k) := default
  let b : Grp.trivial (SchemeOver k) ⟶ T.group := default
  refine ⟨⟨a, b, ?_, Subsingleton.elim _ _⟩⟩
  apply (cancel_epi f).mp
  apply (cancel_epi e.inv).mp
  exact Subsingleton.elim _ _

private theorem trivial_of_flat_surjective {G H : GroupScheme k}
    (S : ClosedSubgroup G) (T : ClosedSubgroup H) (f : S.group ⟶ T.group)
    (hf : Flat f.hom.hom.left) (hs : Surjective f.hom.hom.left)
    (hS : IsTrivialSubgroup S) : IsTrivialSubgroup T := by
  let : Flat f.hom.hom.left := hf
  let : Surjective f.hom.hom.left := hs
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : Epi (F.map f) := Flat.epi_of_flat_of_surjective f.hom.hom.left
  have : Epi f := F.epi_of_epi_map inferInstance
  exact trivial_of_epi S T f hS

private theorem nontrivial_maximal_torus (G : AffineAlgebraicGroup k)
    (S : ClosedSubgroup G.val) (hS : IsTorus S.group) (hn : ¬ IsTrivialSubgroup S) :
    ∃ T : ClosedSubgroup G.val, IsMaximalTorus T ∧ ¬ IsTrivialSubgroup T := by
  obtain ⟨T, hT, f, hf⟩ := exists_maximal_torus_over G S hS
  refine ⟨T, hT, fun ht ↦ hn ?_⟩
  have : IsClosedImmersion f.hom.hom.left := factor_closed hf
  have : Mono f.hom.hom := Over.mono_of_mono_left f.hom.hom
  have : Mono f := (Grp.forget (SchemeOver k)).mono_of_mono_map (show Mono f.hom.hom from inferInstance)
  obtain ⟨e⟩ := ht
  let a : S.group ⟶ Grp.trivial (SchemeOver k) := f ≫ e.hom
  let b : Grp.trivial (SchemeOver k) ⟶ S.group := default
  have : Mono a := by dsimp [a]; infer_instance
  exact ⟨⟨a, b, (cancel_mono a).mp (Subsingleton.elim _ _), Subsingleton.elim _ _⟩⟩

private theorem lift_rational_torus {G H : AffineAlgebraicGroup k} {q : G.val ⟶ H.val}
    (hq : LiftsTori q) (h : ∃ T : ClosedSubgroup H.val, IsTorus T.group ∧ ¬ IsTrivialSubgroup T) :
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧ ¬ IsTrivialSubgroup T := by
  obtain ⟨T, ht, hn⟩ := h
  let e := baseChangeSelfIso k
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  let T' : ClosedSubgroup ((groupBaseChange k k).obj H.val) :=
    ⟨T.group, T.inclusion ≫ e.inv.app H.val, by
      have := T.isClosedImmersion
      have : IsIso (e.inv.app H.val).hom.hom.left := F.map_isIso (e.inv.app H.val)
      change IsClosedImmersion (T.inclusion.hom.hom.left ≫ (e.inv.app H.val).hom.hom.left)
      exact IsClosedImmersion.comp _ _⟩
  obtain ⟨S', f, hs, _, hf, hsurj⟩ := hq k T' ht
  let S : ClosedSubgroup G.val := ⟨S'.group, S'.inclusion ≫ e.hom.app G.val, by
    have := S'.isClosedImmersion
    have : IsIso (e.hom.app G.val).hom.hom.left := F.map_isIso (e.hom.app G.val)
    change IsClosedImmersion (S'.inclusion.hom.hom.left ≫ (e.hom.app G.val).hom.hom.left)
    exact IsClosedImmersion.comp _ _⟩
  exact ⟨S, hs, fun ht ↦ hn (trivial_of_flat_surjective S' T' f hf hsurj ht)⟩

private abbrev groupDimension (G : AffineAlgebraicGroup k) : ℕ :=
  (ringKrullDim Γ(G.val.X.left, ⊤)).unbotD 0 |>.toNat

private theorem groupDimension_cast (G : AffineAlgebraicGroup k) :
    (groupDimension G : WithBot ℕ∞) = ringKrullDim Γ(G.val.X.left, ⊤) := by
  obtain ⟨A, hA, ⟨e⟩⟩ := groupPresentation G
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  let i := (Scheme.Γ.mapIso (F.mapIso e).op) ≪≫
    Scheme.ΓSpecIso (CommRingCat.of A)
  change ((ringKrullDim Γ(G.val.X.left, ⊤)).unbotD 0 |>.toNat : WithBot ℕ∞) = _
  rw [show ringKrullDim Γ(G.val.X.left, ⊤) = ringKrullDim A from
    ringKrullDim_eq_of_ringEquiv i.commRingCatIsoToRingEquiv]
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have hle : ringKrullDim A ≤ (n : WithBot ℕ∞) := by
    simpa using ringKrullDim_le_of_surjective f.toRingHom hf
  have hA₀ : Nontrivial A := (Bialgebra.counitAlgHom k A).toRingHom.domain_nontrivial
  have hn : ringKrullDim A ≠ ⊥ := ne_bot_of_le_ne_bot (by simp : (0 : WithBot ℕ∞) ≠ ⊥)
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hn
  rw [← hd] at hle ⊢
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top (by simp : (n : ℕ∞) ≠ ⊤)
    (WithBot.coe_le_coe.mp hle)
  simpa using congrArg (fun t : ℕ∞ ↦ (t : WithBot ℕ∞)) (ENat.natCast_toNat hdtop)

private theorem groupDimension_le_of_finite_surjective {G H : AffineAlgebraicGroup k}
    (q : G.val ⟶ H.val) (hf : IsFinite q.hom.hom.left)
    (hs : Surjective q.hom.hom.left) : groupDimension H ≤ groupDimension G := by
  let A := Γ(H.val.X.left, ⊤)
  let B := Γ(G.val.X.left, ⊤)
  let f : A →+* B := q.hom.hom.left.appTop.hom
  have : IsAffine H.val.X.left := H.property.1
  have : IsAffine G.val.X.left := G.property.1
  let : Algebra A B := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨q.hom.hom.left.finite_appTop.to_isIntegral⟩
  have hfSpec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
    have h : Surjective (G.val.X.left.isoSpec.hom ≫ Spec.map q.hom.hom.left.appTop) := by
      rw [Scheme.isoSpec_hom_naturality]
      infer_instance
    exact (Surjective.of_comp G.val.X.left.isoSpec.hom
      (Spec.map q.hom.hom.left.appTop)).surj
  have hle : ringKrullDim A ≤ ringKrullDim B := by
    apply iSup_le
    intro l
    obtain ⟨P, hP⟩ := hfSpec l.head
    have : P.asIdeal.LiesOver l.head.asIdeal :=
      ⟨(congrArg PrimeSpectrum.asIdeal hP).symm⟩
    obtain ⟨L, hL, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    exact hL ▸ le_iSup (fun l : LTSeries (PrimeSpectrum B) ↦ (l.length : WithBot ℕ∞)) L
  change ringKrullDim Γ(H.val.X.left, ⊤) ≤ ringKrullDim Γ(G.val.X.left, ⊤) at hle
  rw [← groupDimension_cast, ← groupDimension_cast] at hle
  exact_mod_cast hle

private theorem groupDimension_lt_of_proper {G : AffineAlgebraicGroup k}
    (hG : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (H : ClosedSubgroup G.val) (hH : ¬ IsIso H.inclusion) :
    groupDimension (closedSubgroupAlgebraicGroup H) < groupDimension G := by
  have : GeometricallyIrreducible G.val.X.hom := geometricallyIrreducible_of_connected G
  have : IsIntegral G.val.X.left := (geometry_of_smooth_geometricallyIrreducible G.val.X).2.2
  have : IsAffine G.val.X.left := G.property.1
  have : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  let f := H.inclusion.hom.hom.left.appTop.hom
  have hsur : Function.Surjective f :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine H.inclusion.hom.hom.left).2
  have hker : RingHom.ker f ≠ ⊥ := by
    intro h
    have : IsIso H.inclusion.hom.hom.left := IsClosedImmersion.isIso_of_injective_of_isAffine
      ((RingHom.injective_iff_ker_eq_bot f).mpr h)
    exact hH (isIso_of_schemeIso _)
  obtain ⟨a, ha, hane⟩ : ∃ a ∈ RingHom.ker f, a ≠ 0 := by
    by_contra! h
    exact hker ((RingHom.ker f).eq_bot_iff.mpr h)
  have hdim := ringKrullDim_succ_le_of_surjective f hsur
    (mem_nonZeroDivisors_of_ne_zero hane) (RingHom.mem_ker.mp ha)
  change ringKrullDim Γ((closedSubgroupAlgebraicGroup H).val.X.left, ⊤) + 1 ≤
    ringKrullDim Γ(G.val.X.left, ⊤) at hdim
  rw [← groupDimension_cast, ← groupDimension_cast, ← Nat.cast_one, ← Nat.cast_add] at hdim
  exact Nat.lt_of_succ_le (by exact_mod_cast hdim)

private theorem strictUpper_pow_card {R : Type*} [Ring R] {n : ℕ}
    (M : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) R)
    (hM : ∀ i j, j ≤ i → M i j = 0) : M ^ n = 0 := by
  classical
  have hz (d : ℕ) (i j : ULift.{u} (Fin n)) (h : j.down.val < i.down.val + d) :
      (M ^ d) i j = 0 := by
    induction d generalizing i j with
    | zero =>
      rw [pow_zero, Matrix.one_apply_ne]
      rintro rfl
      simp at h
    | succ d ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hji : j ≤ l
      · rw [hM _ _ hji, mul_zero]
      · have hl : l.down.val < j.down.val := lt_of_not_ge hji
        rw [ih i l (by omega), zero_mul]
  exact Matrix.ext fun i j ↦ hz n i j (by have := j.down.isLt; omega)

private theorem unipotent_matrixDifferential_nilpotent (G : AffineAlgebraicGroup k)
    (hG : Specs.Unipotent.IsUnipotent G) {idx : Type u} [Fintype idx] [DecidableEq idx]
    {L : GroupScheme k} (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k idx)
    (f : G.val ⟶ L) (x : Lie k G.val) :
    IsNilpotent (InfinitesimalCommutator.matrixDifferential f l x) := by
  let V := idx → k
  cases subsingleton_or_nontrivial V with
  | inl h =>
    have : Subsingleton (Matrix idx idx k) := inferInstanceAs (Subsingleton (idx → V))
    exact isNilpotent_of_subsingleton
  | inr h =>
    obtain ⟨A, ⟨i⟩, hA⟩ := hG
    let e := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso i
    let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
    let b := Pi.basisFun k idx
    obtain ⟨E, hE⟩ := RationalRepresentations.representationCoactionComparison A b G' L e l
    let ρ := E f
    obtain ⟨D, rfl⟩ := (tangentComparison A G.val e).surjective x
    rw [tangentComparison_matrix A G' e L l f D, ← hE f]
    let d := (Coalgebra.counit (R := k)).comp D.val.toLinearMap
    let F : Module.End k V := (TensorProduct.rid k V).toLinearMap.comp
      ((d.lTensor V).comp ρ.coaction)
    have hF {J : Type u} [Fintype J] [DecidableEq J] (c : Module.Basis J k V) :
        LinearMap.toMatrix c c F =
          Specs.SemisimpleLieCentralizer.matrixAction A (RationalRepresentations.coefficients A c ρ) D := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      change c.repr (TensorProduct.rid k V ((d.lTensor V) (ρ.coaction (c j)))) i = _
      rw [RationalRepresentations.coaction_apply_basis A c ρ j]
      simp [Specs.SemisimpleLieCentralizer.matrixAction, d]
      rw [Finset.sum_eq_single i]
      · simp
      · intro a _ ha
        simp [ha]
      · simp
    obtain ⟨c, hc⟩ := Unipotent.hasFullFlags_of_invariants A hA V ρ
    have hn : IsNilpotent (LinearMap.toMatrix c c F) := by
      rw [hF]
      refine ⟨_, strictUpper_pow_card _ ?_⟩
      intro i j hij
      rcases lt_or_eq_of_le hij with hlt | rfl
      · change d _ = 0
        rw [hc.1 hlt, map_zero]
      · change d _ = 0
        rw [hc.2, show d 1 = 0 by simp [d]]
    rw [← hF b]
    exact (LinearMap.isNilpotent_toMatrix_iff b F).mpr ((LinearMap.isNilpotent_toMatrix_iff c F).mp hn)

private theorem dualNumber_spectrum_subsingleton :
    Subsingleton (Spec (CommRingCat.of (DualNumber k))) := by
  refine ⟨fun I J ↦ ?_⟩
  apply PrimeSpectrum.ext
  ext a
  have h (P : PrimeSpectrum (DualNumber k)) : a ∈ P.asIdeal ↔ a.fst = 0 := by
    constructor
    · intro ha
      by_contra hn
      exact P.isPrime.ne_top (P.asIdeal.eq_top_of_isUnit_mem ha
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hn)))
    · intro ha
      have ha₂ : a ^ 2 = 0 := by
        rw [pow_two]
        apply TrivSqZeroExt.ext <;> simp [ha]
      exact P.isPrime.mem_of_pow_mem 2 (ha₂.symm ▸ P.asIdeal.zero_mem)
  exact (h I).trans (h J).symm

/-- An open subgroup through the identity has the same dual-number tangent
space. A tangent point has one topological image point, its reduction. -/
private theorem tangent_surjective_of_open {G H : GroupScheme k} (i : H ⟶ G)
    (hi : IsOpenImmersion i.hom.hom.left) :
    Function.Surjective (mapPointKernel i) := by
  let R := CommAlgCat.of k (DualNumber k)
  let X := (testSpec k).obj (op R)
  have : Subsingleton X.left := dualNumber_spectrum_subsingleton
  intro x
  let a : X ⟶ G.X := x.toMul.val
  have hrange : Set.range a.left ⊆ Set.range i.hom.hom.left := by
    rintro _ ⟨s, rfl⟩
    let t := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
    let r := (testSpec k).map (dualReduction k).op
    have h₁ : (r ≫ a) = 1 := x.toMul.property
    refine ⟨((1 : (testSpec k).obj (op (CommAlgCat.of k k)) ⟶ H.X).left) t, ?_⟩
    calc
      i.hom.hom.left ((1 : (testSpec k).obj (op (CommAlgCat.of k k)) ⟶ H.X).left t) =
          (1 : (testSpec k).obj (op (CommAlgCat.of k k)) ⟶ G.X).left t :=
        congrArg (fun h : (testSpec k).obj (op (CommAlgCat.of k k)) ⟶ G.X ↦ h.left t)
          (map_one (((groupPointsFunctor k).map i).app (CommAlgCat.of k k)).hom)
      _ = a.left (r.left t) := congrArg (fun h : _ ⟶ G.X ↦ h.left t) h₁.symm
      _ = a.left s := congrArg a.left (Subsingleton.elim _ _)
  let b₀ := IsOpenImmersion.lift i.hom.hom.left a.left hrange
  have hb₀ : b₀ ≫ i.hom.hom.left = a.left := IsOpenImmersion.lift_fac _ _ _
  let b : X ⟶ H.X := Over.homMk b₀ (by rw [← Over.w i.hom.hom, ← Category.assoc, hb₀, Over.w a])
  have hb : b ≫ i.hom.hom = a := Over.OverMorphism.ext hb₀
  have : Mono i.hom.hom := Over.mono_of_mono_left i.hom.hom
  have hbr : (testSpec k).map (dualReduction k).op ≫ b = 1 := by
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, hb]
    exact x.toMul.property.trans (map_one (((groupPointsFunctor k).map i).app
      (CommAlgCat.of k k)).hom).symm
  exact ⟨⟨b, hbr⟩, Subtype.ext hb⟩

private theorem matrixDifferential_comp {G H L : GroupScheme k} {idx : Type u}
    [Fintype idx] [DecidableEq idx] (i : H ⟶ G) (f : G ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k idx)
    (x : Lie k H) :
    InfinitesimalCommutator.matrixDifferential (i ≫ f) l x =
      InfinitesimalCommutator.matrixDifferential f l (mapPointKernel i x) := by
  unfold InfinitesimalCommutator.matrixDifferential
  rw [(lieFunctoriality k).2.2 H G L i f x]

private theorem smooth_connected_centralizer [Infinite k]
    (torusFree : Specs.TorusFreeUnipotent.Unipotence.{u})
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom) (hconn : ConnectedSpace G.val.X.left)
    (hss : HasGeometricNoncentralSemisimple G) :
    ∃ H : ClosedSubgroup G.val, Smooth H.group.X.hom ∧ ConnectedSpace H.group.X.left ∧
      groupDimension (closedSubgroupAlgebraicGroup H) < groupDimension G ∧
      ∃ T : ClosedSubgroup (GeometricGroup (closedSubgroupAlgebraicGroup H)).val,
        IsTorus T.group ∧ ¬ IsTrivialSubgroup T := by
  classical
  let s := identityLieStructure G
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, b, -⟩ := adjointRepresentation k G s
  obtain ⟨x, hx⟩ := ((SemisimpleLieCentralizer.adjointNonnilpotentOpen k G s
    (ULift.{u} (Fin n)) b).2.2 hss).2 inferInstance
  have hnx := ((SemisimpleLieCentralizer.adjointNonnilpotentOpen k G s
    (ULift.{u} (Fin n)) b).2.1 x).mp hx
  obtain ⟨r, L, ⟨l⟩, f, hf⟩ := faithfulLinearization k G
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  let E := hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hA : Algebra.Smooth k A := by
    have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      change Smooth ((specGroup A).X.hom)
      rw [← e.hom.hom.hom.w]
      have : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
      infer_instance
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs)
  obtain ⟨y, hy, _, hny, _, _⟩ :=
    SemisimpleLieCentralizer.rationalSemisimpleWitness k G ⟨L.val, L.property.1⟩ s
      A E (ULift.{u} (Fin r)) l f hf x hnx
  obtain ⟨C, hsC, _, hLie, _⟩ :=
    SemisimpleLieCentralizer.schemeCentralizerOfSemisimple k G ⟨L.val, L.property.1⟩ s hG
      (ULift.{u} (Fin r)) l f hf y hy
  let C' := closedSubgroupAlgebraicGroup C
  obtain ⟨Q, H, q, i, hi, -⟩ := identityComponentAndQuotient k C'
  have : IsClosedImmersion i.hom.hom.left := hi.closedImmersion
  have : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  let j := i ≫ C.inclusion
  let S : ClosedSubgroup G.val := ⟨H, j, IsClosedImmersion.comp _ _⟩
  have hs : Smooth H.X.hom := by
    have : IsOpenImmersion i.hom.hom.left := hi.openImmersion
    rw [← Over.w i.hom.hom]
    change Smooth (i.hom.hom.left ≫ C.group.X.hom)
    infer_instance
  have : GeometricallyConnected H.X.hom := hi.geometricallyConnected
  have hc : ConnectedSpace H.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom
  have hj : ¬ IsIso j := by
    intro h
    apply hny
    apply LinearMap.ext
    intro z
    have hz : mapPointKernel j (mapPointKernel (inv j) z) = z := by
      rw [← ((lieFunctoriality k).2.2 _ _ _ (inv j) j _), IsIso.inv_hom_id]
      exact (lieFunctoriality k).2.1 _ _
    have hzc : mapPointKernel C.inclusion (mapPointKernel i (mapPointKernel (inv j) z)) = z :=
      ((lieFunctoriality k).2.2 _ _ _ i C.inclusion _).symm.trans hz
    exact (hLie z).mp ⟨_, hzc⟩
  obtain ⟨z, hz⟩ := (hLie y).mpr (lie_self y)
  obtain ⟨w, hw⟩ := tangent_surjective_of_open i hi.openImmersion z
  have hwy : mapPointKernel j w = y := by
    rw [(lieFunctoriality k).2.2 _ _ _ i C.inclusion, hw]
    exact hz
  have hNotUnipotent : ¬ Specs.Unipotent.IsUnipotent (closedSubgroupAlgebraicGroup S) := by
    intro hU
    have hn := unipotent_matrixDifferential_nilpotent (closedSubgroupAlgebraicGroup S) hU
      l (j ≫ f) w
    have hn := (congrArg (InfinitesimalCommutator.matrixDifferential f l) hwy) ▸
      (matrixDifferential_comp j f l w ▸ hn)
    let Y := InfinitesimalCommutator.matrixDifferential f l y
    change IsNilpotent Y at hn
    have hn' : IsNilpotent (Matrix.toLinAlgEquiv'
        (Y.map (algebraMap k (AlgebraicClosure k)))) :=
      (hn.map ((algebraMap k (AlgebraicClosure k)).mapMatrix)).map Matrix.toLinAlgEquiv'
    have hzY : Y = 0 := by
      have he := Module.End.eq_zero_of_isNilpotent_isSemisimple hn' hy
      have hm : Y.map (algebraMap k (AlgebraicClosure k)) = 0 :=
        Matrix.toLinAlgEquiv'.injective (he.trans (map_zero _).symm)
      ext i j
      apply (algebraMap k (AlgebraicClosure k)).injective
      simpa using congrArg (fun M : Matrix (ULift.{u} (Fin r)) (ULift.{u} (Fin r))
        (AlgebraicClosure k) ↦ M i j) hm
    let D := faithfulLieHom ⟨G.val, G.property.1⟩ ⟨L.val, L.property.1⟩ s l f hf
    have hDy : D y = 0 := by
      change Matrix.toLinAlgEquiv' Y = 0
      rw [hzY, map_zero]
    have hy0 : y = 0 := faithfulLieHom_injective ⟨G.val, G.property.1⟩
      ⟨L.val, L.property.1⟩ s l f hf (hDy.trans D.map_zero.symm)
    exact hny (by rw [hy0, map_zero])
  refine ⟨S, hs, hc, groupDimension_lt_of_proper hG hconn S hj, ?_⟩
  by_contra! h
  exact hNotUnipotent (torusFree _ hs hc h)

/-- A bound on the divisibility of a tracked nontrivial weight suffices to
reduce to a case with a noncentral semisimple Lie vector or a central torus. -/
private theorem solve_using_weight [Infinite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (reduce : CentralFrobeniusReduction.{u}) (P : AffineAlgebraicGroup k → Prop)
    (hTerminal : ∀ (G : AffineAlgebraicGroup k), P G → Smooth G.val.X.hom →
      ConnectedSpace G.val.X.left → ∀ T : ClosedSubgroup (GeometricGroup G).val,
      IsMaximalTorus T → (HasGeometricNoncentralSemisimple G ∨ IsCentral T.inclusion) →
      (∃ χ : Character T.group, χ ≠ 1) →
      ∃ S : ClosedSubgroup G.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S)
    (hQuotient : ∀ {G H : AffineAlgebraicGroup k} (q : G.val ⟶ H.val),
      IsFinite q.hom.hom.left → Surjective q.hom.hom.left → P G → P H)
    (n : ℕ) (G : AffineAlgebraicGroup k) (hP : P G)
    (hG : Smooth G.val.X.hom) (hconn : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup (GeometricGroup G).val) (hT : IsMaximalTorus T)
    (χ : Character T.group) (hχ : χ ≠ 1) (hw : IsAdjointWeight T.inclusion χ)
    (hn : ¬ IsCharacterPower (p ^ n) χ) :
    ∃ S : ClosedSubgroup G.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S := by
  induction n generalizing G with
  | zero => exact False.elim (hn ⟨χ, by simp⟩)
  | succ n ih =>
    by_cases h₁ : HasGeometricNoncentralSemisimple G
    · exact hTerminal G hP hG hconn T hT (.inl h₁) ⟨χ, hχ⟩
    by_cases h₂ : IsCentral T.inclusion
    · exact hTerminal G hP hG hconn T hT (.inr h₂) ⟨χ, hχ⟩
    obtain ⟨_, hdiv, E, G₁, q, _, _, _, hquot, hfinite, hsmooth, hconnected,
      hlifts, _, T₁, f, hmax, _, _, _, hinj, himage, hweights, hpower⟩ :=
      reduce k p G hG hconn T hT h₂ h₁
    obtain ⟨ψ, hψ⟩ := (himage χ).mpr (hdiv χ hχ hw)
    have hψ₀ : ψ ≠ 1 := by
      rintro rfl
      exact hχ (hψ.symm.trans (pullbackCharacter f).map_one)
    have hw₁ := (hweights ψ hψ₀).mpr (hψ ▸ hw)
    have hn₁ : ¬ IsCharacterPower (p ^ n) ψ := by
      intro h
      exact hn (hψ ▸ (hpower ψ hψ₀ hw₁ n).mpr h)
    exact lift_rational_torus hlifts
      (ih G₁ (hQuotient q hfinite hquot.2.2.1 hP) hsmooth hconnected T₁ hmax ψ hψ₀ hw₁ hn₁)

private theorem nontrivial_of_character {G : GroupScheme k} (T : ClosedSubgroup G)
    {χ : Character T.group} (hχ : χ ≠ 1) : ¬ IsTrivialSubgroup T := by
  rintro ⟨e⟩
  exact hχ ((cancel_epi e.inv).mp (Subsingleton.elim _ _))

private theorem central_torus_unipotent_quotient [IsAlgClosed k]
    (centralizer : Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u})
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup G.val) (ht : IsMaximalTorus T) (hz : IsCentral T.inclusion) :
    ∃ (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsUnipotent Q ∧ IsSchemeKernel q T := by
  obtain ⟨C, hC, _, _, _, _, j, hj, Q, q, hji, hq, hU⟩ := centralizer G hG hc T ht
  have : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
  have hm : Mono C.inclusion.hom.hom := Over.mono_of_mono_left C.inclusion.hom.hom
  obtain ⟨s, hs⟩ := (hC G.val.X (𝟙 _)).mp (hz G.val.X (𝟙 _))
  have hsi : C.inclusion.hom.hom ≫ s = 𝟙 _ :=
    (cancel_mono C.inclusion.hom.hom).mp (by simp [Category.assoc, hs])
  let e : C.group.X ≅ G.val.X := ⟨C.inclusion.hom.hom, s, hsi, hs⟩
  have : IsIso e.hom := e.isIso_hom
  have hIso : IsIso C.inclusion.hom.hom.left :=
    (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  have : IsIso C.inclusion := isIso_of_schemeIso _
  let q' := inv C.inclusion ≫ q
  refine ⟨Q, q', hU, ?_⟩
  have hp := hq.1
  change IsPullback j.hom.hom (toUnit _) q.hom.hom η[Q.val.X] at hp
  change IsPullback T.inclusion.hom.hom (toUnit _)
    ((inv C.inclusion).hom.hom ≫ q.hom.hom) η[Q.val.X]
  have : IsIso C.inclusion.hom.hom :=
    (Grp.forget (SchemeOver k)).map_isIso C.inclusion
  have hp' : IsPullback C.inclusion.hom.hom q.hom.hom
      ((inv C.inclusion).hom.hom ≫ q.hom.hom) (𝟙 _) := by
    apply IsPullback.of_horiz_isIso
    apply CommSq.mk
    change (C.inclusion ≫ inv C.inclusion ≫ q).hom.hom = q.hom.hom ≫ 𝟙 _
    simp
  simpa only [Category.comp_id, show j.hom.hom ≫ C.inclusion.hom.hom =
      T.inclusion.hom.hom from congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) hji] using
    hp.paste_horiz hp'

open private unipotent_iff_exists_embedding from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.ExactOperations

private theorem nilpotent_add_one_pow_eq_one_of_charP {R : Type*} [Ring R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (x : R) (t e : ℕ) (ht : x ^ t = 0) (he : t ≤ p ^ e) :
    (1 + x) ^ p ^ e = 1 := by
  rw [add_pow_char_pow_of_commute p e (Commute.one_left x), one_pow,
    pow_eq_zero_of_le he ht, add_zero]

private theorem unipotent_points_bounded_exponent (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : AffineAlgebraicGroup k) (hU : IsUnipotent U) :
    ∃ e : ℕ, ∀ (R : TestAlgebra k) (x : Specs.AdjointRepresentation.GroupPoints U.val R),
      x ^ p ^ e = 1 := by
  classical
  obtain ⟨n, N, ⟨E⟩, f, hf⟩ := (unipotent_iff_exists_embedding U).mp hU
  let e := n
  have he : n < p ^ e := Nat.lt_pow_self (Fact.out (p := p.Prime)).one_lt
  refine ⟨e, fun R x ↦ ?_⟩
  let F := groupPointsFunctor k
  let q := (F.map f).app R
  let g : Specs.Unipotent.upperUnitriangular (ULift.{u} (Fin n)) R := E.hom.app R (q x)
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left f.hom.hom
  have hq : Function.Injective q := by
    intro x y h
    apply (cancel_mono f.hom.hom).mp
    exact h
  apply hq
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app R)).injective
  change (E.hom.app R).hom (q.hom (x ^ p ^ e)) = (E.hom.app R).hom (q.hom 1)
  rw [map_pow, map_pow, map_one, map_one]
  apply Subtype.ext
  apply Units.ext
  change g.val.val ^ p ^ e = 1
  by_cases hR : Subsingleton R
  · exact Subsingleton.elim _ _
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  let : CharP R p := charP_of_injective_algebraMap (algebraMap k R).injective p
  by_cases hIndex : Nonempty (ULift.{u} (Fin n))
  swap
  · have : IsEmpty (ULift.{u} (Fin n)) := not_nonempty_iff.mp hIndex
    exact Subsingleton.elim _ _
  let M := g.val.val - 1
  have hM (i j : ULift.{u} (Fin n)) (h : j ≤ i) : M i j = 0 := by
    rcases lt_or_eq_of_le h with hlt | hEq
    · change g.val.val i j - (1 : Matrix _ _ R) i j = 0
      rw [g.property.1 hlt, Matrix.one_apply_ne (ne_of_gt hlt), sub_zero]
    · subst j
      change g.val.val i i - (1 : Matrix _ _ R) i i = 0
      rw [g.property.2 i, Matrix.one_apply_eq, sub_self]
  have hn : M ^ n = 0 := strictUpper_pow_card M hM
  rw [← show 1 + M = g.val.val by dsimp [M]; abel]
  exact nilpotent_add_one_pow_eq_one_of_charP p M n e hn he.le

/-- In characteristic p a uniform power map on the ambient group factors
through a central geometric maximal torus. The factor restricts to the
same power map on the torus. -/
private theorem central_torus_power_factor [IsAlgClosed k] (p : ℕ)
    [Fact p.Prime] [CharP k p]
    (centralizer : Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u})
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup G.val) (ht : IsMaximalTorus T) (hz : IsCentral T.inclusion) :
    ∃ (e : ℕ) (f : G.val.X ⟶ T.group.X),
      f ≫ T.inclusion.hom.hom = (𝟙 G.val.X) ^ (p ^ e) ∧
      T.inclusion.hom.hom ≫ f = (𝟙 T.group.X) ^ (p ^ e) := by
  obtain ⟨Q, q, hU, hk⟩ := central_torus_unipotent_quotient centralizer G hG hc T ht hz
  obtain ⟨e, he⟩ := unipotent_points_bounded_exponent p Q hU
  obtain ⟨A, _, ⟨i⟩⟩ := groupPresentation G
  let R := CommAlgCat.of k A
  let x : (testSpec k).obj (op R) ⟶ G.val.X := i.hom.hom.hom
  have hx : (x ≫ q.hom.hom) ^ p ^ e = 1 := he R (x ≫ q.hom.hom)
  have hPow : ((𝟙 G.val.X) ^ (p ^ e)) ≫ q.hom.hom = 1 := by
    have : IsIso x := by
      change IsIso ((Grp.forget (SchemeOver k)).map i.hom)
      infer_instance
    apply (cancel_epi x).mp
    rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, MonObj.comp_one]
    exact hx
  obtain ⟨f, hf⟩ := (schemeKernel_sections hk _).mpr hPow
  change f ≫ T.inclusion.hom.hom = _ at hf
  have : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  have : Mono T.inclusion.hom.hom := Over.mono_of_mono_left T.inclusion.hom.hom
  refine ⟨e, f, hf, (cancel_mono T.inclusion.hom.hom).mp ?_⟩
  rw [Category.assoc, hf, MonObj.comp_pow, MonObj.pow_comp, Category.id_comp, Category.comp_id]

/-- The pullback of the scheme power map, computed at the universal point. -/
private def coordinatePower (A : HopfAlgebraCategory k) (n : ℕ) : A →ₐ[k] A :=
  ((toConv (AlgHom.id k A)) ^ n).ofConv

private theorem coordinatePower_of {M : Type u} [CommGroup M] (n : ℕ) (m : M) :
    coordinatePower (groupAlgebra k M) n (MonoidAlgebra.of k M m) =
      MonoidAlgebra.of k M (m ^ n) := by
  induction n with
  | zero =>
    change (1 : WithConv (MonoidAlgebra k M →ₐ[k] MonoidAlgebra k M)) _ = _
    simp
  | succ n ih =>
    change ((toConv (AlgHom.id k (MonoidAlgebra k M))) ^ (n + 1))
      (MonoidAlgebra.of k M m) = _
    rw [pow_succ, AlgHom.convMul_apply,
      (MonoidAlgebra.isGroupLikeElem_of (R := k) (A := k) m).comul_eq_tmul_self,
      Algebra.TensorProduct.lift_tmul]
    change coordinatePower (groupAlgebra k M) n (MonoidAlgebra.of k M m) *
      MonoidAlgebra.of k M m = _
    rw [ih, ← map_mul, pow_succ]

private theorem coordinatePower_split_injective (r : ℕ) {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (coordinatePower (groupAlgebra k (StandardLattice.{u} r)) n) := by
  let M := StandardLattice.{u} r
  let f : M →* M := {toFun := (· ^ n), map_one' := one_pow _, map_mul' := fun _ _ ↦ mul_pow _ _ _}
  have he : coordinatePower (groupAlgebra k M) n =
      (MonoidAlgebra.mapDomainBialgHom k f).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      change coordinatePower (groupAlgebra k M) n (MonoidAlgebra.of k M m) = _
      rw [coordinatePower_of]
      change MonoidAlgebra.single (m ^ n) 1 = _
      exact (MonoidAlgebra.mapDomainBialgHom_single f m (1 : k)).symm
    · ext
  rw [he]
  change Function.Injective (MonoidAlgebra.mapDomain (R := k) (· ^ n : M → M))
  apply MonoidAlgebra.mapDomain_injective
  intro x y h
  funext i
  have hi := congrArg (fun z : M ↦ (z i).down.toAdd) h
  change ((x i).down ^ n).toAdd = ((y i).down ^ n).toAdd at hi
  simp only [toAdd_pow, nsmul_eq_mul] at hi
  have hval : (x i).down.toAdd = (y i).down.toAdd :=
    mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) hi
  exact ULift.ext hval

private theorem coordinatePower_baseChange (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (n : ℕ) :
    coordinatePower (extendedHopf K A) n =
      Algebra.TensorProduct.map (AlgHom.id K K) (coordinatePower A n) := by
  suffices h : ∀ a : A, coordinatePower (extendedHopf K A) n (1 ⊗ₜ[k] a) =
      (1 : K) ⊗ₜ[k] coordinatePower A n a by
    apply Algebra.TensorProduct.ext_ring
    ext a
    exact h a
  intro a
  let Id := toConv (AlgHom.id K (K ⊗[k] A))
  let id := toConv (AlgHom.id k A)
  change (Id ^ n) ((1 : K) ⊗ₜ[k] a) = (1 : K) ⊗ₜ[k] ((id ^ n) a)
  induction n generalizing a with
  | zero =>
    simp only [pow_zero, AlgHom.convOne_apply, TensorProduct.counit_tmul,
      Algebra.TensorProduct.algebraMap_apply]
    simpa [Algebra.smul_def] using Algebra.TensorProduct.tmul_one_eq_one_tmul
      (R := k) (A := K) (B := A) (Coalgebra.counit (R := k) a)
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.convMul_apply, AlgHom.convMul_apply,
      TensorProduct.comul_tmul, Bialgebra.comul_one]
    generalize Coalgebra.comul (R := k) a = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      change (Id ^ n) ((1 : K) ⊗ₜ[k] x) * ((1 : K) ⊗ₜ[k] y) =
        (1 : K) ⊗ₜ[k] ((id ^ n) x * y)
      rw [ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]

open private tensorAlong tensorAlong_injective tensorAlong_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

set_option maxHeartbeats 1500000 in
/-- A Hopf quotient whose coordinate kernel is a scalar extension descends
as a Hopf quotient, with the same inclusion after base change. -/
private theorem isHopfIdeal_of_baseChange (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (B : HopfAlgebraCategory K)
    (b : extendedHopf K A ⟶ B) (I : Ideal A)
    (e : (K ⊗[k] (A ⧸ I)) ≃ₐ[K] B)
    (he : ∀ a : A, e (1 ⊗ₜ[k] Ideal.Quotient.mk I a) = b.hom (1 ⊗ₜ[k] a)) :
    I.IsHopfIdeal k := by
  let : Algebra k B := ((algebraMap K B).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  let q := Ideal.Quotient.mkₐ k I
  let inc : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let c : A ⧸ I →ₐ[k] B := (e.toAlgHom.restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hc (a : A) : c (q a) = b.hom (inc a) := he a
  have hLift : c.toLinearMap.liftBaseChange K = e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r a
    rw [LinearMap.liftBaseChange_tmul]
    change r • e (1 ⊗ₜ[k] a) = e (r ⊗ₜ[k] a)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hTensor : Function.Injective (tensorAlong (K := K) c c) :=
    tensorAlong_injective c c (hLift.symm ▸ e.injective) (hLift.symm ▸ e.injective)
  have hComul (a : A) :
      tensorAlong (K := K) c c (TensorProduct.map q.toLinearMap q.toLinearMap
        (Coalgebra.comul (R := k) a)) = Coalgebra.comul (R := K) (b.hom (inc a)) := by
    rw [← CoalgHomClass.map_comp_comul_apply b.hom]
    have hbase : Coalgebra.comul (R := K) (inc a) =
        tensorAlong (K := K) inc inc (Coalgebra.comul (R := k) a) := by
      exact DFunLike.congr_fun (Bialgebra.comul_includeRight (R := k) (A := K) (B := A)) a
    rw [hbase]
    generalize Coalgebra.comul (R := k) a = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [TensorProduct.map_tmul, tensorAlong_tmul, tensorAlong_tmul, TensorProduct.map_tmul]
      change c (q x) ⊗ₜ[K] c (q y) = _
      rw [hc, hc]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hPhi : ∀ a : A, q a = 0 ↔ b.hom (inc a) = 0 := fun a ↦ by
    rw [← hc, map_eq_zero_iff c (e.injective.comp
      (Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective))]
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro a ha
    have h := (hPhi a).mp (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    apply (algebraMap k K).injective
    rw [map_zero, ← show Coalgebra.counit (R := K) (inc a) = algebraMap k K (Coalgebra.counit (R := k) a)
        from DFunLike.congr_fun (Bialgebra.counitAlgHom_comp_includeRight (R := k) (A := K) (B := A)) a]
    rw [← CoalgHomClass.counit_comp_apply b.hom, h, map_zero]
  · intro a ha
    have h := (hPhi a).mp (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    apply hTensor
    change tensorAlong (K := K) c c
      (TensorProduct.map q.toLinearMap q.toLinearMap (Coalgebra.comul (R := k) a)) =
        tensorAlong (K := K) c c 0
    rw [hComul, h, map_zero, map_zero]
  · intro a ha
    have h := (hPhi a).mp (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (hPhi _).mpr
    change b.hom ((1 : K) ⊗ₜ[k] HopfAlgebra.antipode k a) = 0
    rw [← show HopfAlgebra.antipode K ((1 : K) ⊗ₜ[k] a) =
      (1 : K) ⊗ₜ[k] HopfAlgebra.antipode k a by
      simp [TensorProduct.antipode_def]]
    have hb := DFunLike.congr_fun (hopfSpecMorphism K b).2 (inc a)
    change b.hom (HopfAlgebra.antipode K (inc a)) =
      HopfAlgebra.antipode K (b.hom (inc a)) at hb
    change b.hom (HopfAlgebra.antipode K (inc a)) = 0
    rw [hb, h, map_zero]

open private liftHopfQuotient extendedQuotientMap_ker extendedQuotientMap_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem hopfQuotient_of_baseChange (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (B : HopfAlgebraCategory K)
    (b : extendedHopf K A ⟶ B) (I : Ideal A)
    (e : (K ⊗[k] (A ⧸ I)) ≃ₐ[K] B)
    (he : ∀ a : A, e (1 ⊗ₜ[k] Ideal.Quotient.mk I a) = b.hom (1 ⊗ₜ[k] a))
    (hb : Function.Surjective b.hom) :
    ∃ (_ : I.IsHopfIdeal k), Nonempty (extendedHopf K (hopfQuotient A I) ≅ B) := by
  let hI : I.IsHopfIdeal k := isHopfIdeal_of_baseChange K A B b I e he
  let qK := extendedHopfMap K (hopfQuotientMap A I)
  have hComp (z : K ⊗[k] A) : e (qK.hom z) = b.hom z := by
    induction z using TensorProduct.inductionOn with
    | tmul r a =>
      change e (r ⊗ₜ[k] Ideal.Quotient.mk I a) = b.hom (r ⊗ₜ[k] a)
      rw [← show r • ((1 : K) ⊗ₜ[k] Ideal.Quotient.mk I a) = r ⊗ₜ[k] Ideal.Quotient.mk I a by
        simp [TensorProduct.smul_tmul'],
        ← show r • ((1 : K) ⊗ₜ[k] a) = r ⊗ₜ[k] a by simp [TensorProduct.smul_tmul'],
        map_smul, map_smul, he]
    | add x y hx hy => simp only [map_add, hx, hy]
  let J := extendedIdeal K I
  have hJ : J.IsHopfIdeal K := extendedHopfIdeal k K A I
  have hker : RingHom.ker b.hom.toAlgHom = J := by
    change RingHom.ker b.hom.toAlgHom = extendedIdeal K I
    rw [← extendedQuotientMap_ker K A I]
    ext x
    change b.hom x = 0 ↔ qK.hom x = 0
    rw [← hComp, map_eq_zero_iff e e.injective]
  let c := liftHopfQuotient J b (fun x hx ↦ show x ∈ RingHom.ker b.hom.toAlgHom from hker.symm ▸ hx)
  have hc : Function.Bijective c.hom := by
    constructor
    · intro x y h
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply Ideal.Quotient.eq.mpr
      rw [← hker]
      change b.hom (x - y) = 0
      rw [map_sub, sub_eq_zero]
      exact h
    · intro y
      obtain ⟨x, rfl⟩ := hb y
      exact ⟨Ideal.Quotient.mk J x, rfl⟩
  obtain ⟨i, -⟩ := extendedHopfQuotient k K A I
  exact ⟨hI, ⟨i.symm ≪≫ CommHopfAlgCat.isoMk (BialgEquiv.ofBijective c.hom hc)⟩⟩

private theorem spec_coordinatePower (A : HopfAlgebraCategory k) (n : ℕ) :
    (algSpec (R := CommRingCat.of k)).map (CommAlgCat.ofHom (coordinatePower A n)).op =
      (𝟙 (specGroup A).X) ^ n := by
  let R := CommAlgCat.of k A
  let F := (hopfSpecPointIso A).hom.app R
  let a := toConv (AlgHom.id k A)
  have he := map_pow F.hom a n
  change F.hom (a ^ n) = F.hom a ^ n at he
  have ha : F.hom a = 𝟙 (specGroup A).X := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 (CommRingCat.of A)) = 𝟙 (Spec (CommRingCat.of A))
    simp
  exact he.trans (congrArg (· ^ n) ha)

private theorem ker_coordinatePower_of_factor (A B : HopfAlgebraCategory k)
    (b : A ⟶ B) (f : (specGroup A).X ⟶ (specGroup B).X) (n : ℕ)
    (hf : f ≫ (specGroupMap b).hom.hom = (𝟙 (specGroup A).X) ^ n)
    (hfb : (specGroupMap b).hom.hom ≫ f = (𝟙 (specGroup B).X) ^ n)
    (hB : Function.Injective (coordinatePower B n)) :
    RingHom.ker (coordinatePower A n).toRingHom = RingHom.ker b.hom.toAlgHom.toRingHom := by
  let F := algSpec (R := CommRingCat.of k)
  let E := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a : B →ₐ[k] A := (E.preimage f).unop.hom
  have ha : F.map (CommAlgCat.ofHom a).op = f := E.map_preimage f
  let b' := b.hom.toAlgHom
  have hb : F.map (CommAlgCat.ofHom b').op = (specGroupMap b).hom.hom := rfl
  have h₁ : a.comp b' = coordinatePower A n := by
    have t : (CommAlgCat.ofHom a).op ≫ (CommAlgCat.ofHom b').op =
        (CommAlgCat.ofHom (coordinatePower A n)).op := E.map_injective (by
        change F.map _ = _
        rw [F.map_comp, ha, hb, hf, spec_coordinatePower])
    exact congrArg (fun g : op (CommAlgCat.of k A) ⟶ op (CommAlgCat.of k A) ↦
      (Quiver.Hom.unop g).hom) t
  have h₂ : b'.comp a = coordinatePower B n := by
    have t : (CommAlgCat.ofHom b').op ≫ (CommAlgCat.ofHom a).op =
        (CommAlgCat.ofHom (coordinatePower B n)).op := E.map_injective (by
        change F.map _ = _
        rw [F.map_comp, hb, ha, hfb, spec_coordinatePower])
    exact congrArg (fun g : op (CommAlgCat.of k B) ⟶ op (CommAlgCat.of k B) ↦
      (Quiver.Hom.unop g).hom) t
  have hi : Function.Injective a := by
    intro x y h
    apply hB
    rw [← h₂]
    exact congrArg b' h
  ext x
  change coordinatePower A n x = 0 ↔ b' x = 0
  rw [← h₁, AlgHom.comp_apply, map_eq_zero_iff a hi]

private theorem quotient_of_extended_kernel (K : Type u) [Field K] [Algebra k K]
    (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra K B]
    (a : A →ₐ[k] A) (b : K ⊗[k] A →ₐ[K] B) (hb : Function.Surjective b)
    (hker : RingHom.ker b.toRingHom =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id K K) a).toRingHom) :
    ∃ e : (K ⊗[k] (A ⧸ RingHom.ker a.toRingHom)) ≃ₐ[K] B,
      ∀ x : A, e (1 ⊗ₜ[k] Ideal.Quotient.mk _ x) = b (1 ⊗ₜ[k] x) := by
  let I := RingHom.ker a.toRingHom
  let q := Ideal.Quotient.mkₐ k I
  let i := Ideal.Quotient.liftₐ I a (fun x hx ↦ hx)
  have hi : Function.Injective i := by
    intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    change a (x - y) = 0
    rw [map_sub, sub_eq_zero]
    exact h
  let qK := Algebra.TensorProduct.map (AlgHom.id K K) q
  let iK := Algebra.TensorProduct.map (AlgHom.id K K) i
  have hiK : Function.Injective iK := by
    change Function.Injective (TensorProduct.map (LinearMap.id : K →ₗ[k] K) i.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id hi
  have hqK : Function.Surjective qK :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id Ideal.Quotient.mk_surjective
  have ha : iK.comp qK = Algebra.TensorProduct.map (AlgHom.id K K) a := by
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  have hI : RingHom.ker qK.toRingHom = RingHom.ker b.toRingHom := by
    rw [hker, ← ha]
    ext z
    change qK z = 0 ↔ iK (qK z) = 0
    exact (map_eq_zero_iff iK hiK).symm
  let e := ((Ideal.quotientKerAlgEquivOfSurjective hqK).symm.trans
    (Ideal.quotientEquivAlgOfEq K hI)).trans (Ideal.quotientKerAlgEquivOfSurjective hb)
  have he (z : K ⊗[k] A) : e (qK z) = b z := by
    change Ideal.quotientKerAlgEquivOfSurjective hb (Ideal.quotientEquivAlgOfEq K hI
      ((Ideal.quotientKerAlgEquivOfSurjective hqK).symm (qK z))) = _
    have hh : Ideal.quotientKerAlgEquivOfSurjective hqK
        (Ideal.Quotient.mk (RingHom.ker qK.toRingHom) z) = qK z := rfl
    rw [← hh, AlgEquiv.symm_apply_apply]
    have hk := Ideal.quotientEquivAlgOfEq_mk K hI z
    exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective hb) hk).trans rfl
  exact ⟨e, fun x ↦ he (1 ⊗ₜ[k] x)⟩

/-- The central torus is the geometric scalar extension of the closed
subgroup cut out by the kernel of the power pullback over the ground field. -/
private theorem central_torus_as_geometric_baseChange (p : ℕ) [Fact p.Prime] [CharP k p]
    (centralizer : Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u})
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (T : ClosedSubgroup (GeometricGroup G).val) (ht : IsMaximalTorus T)
    (hz : IsCentral T.inclusion) :
    ∃ S : ClosedSubgroup G.val, Nonempty (((groupBaseChange k (AlgebraicClosure k)).obj S.group) ≅ T.group) := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hs : Smooth (GeometricGroup G).val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  have hgc : GeometricallyConnected G.val.X.hom := geometricallyConnected_of_connected G
  have hc' : ConnectedSpace (GeometricGroup G).val.X.left :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace K (fieldSpecMap k K)
  obtain ⟨e, f, hf, hft⟩ := central_torus_power_factor p centralizer (GeometricGroup G) hs hc' T ht hz
  obtain ⟨r, ⟨t⟩⟩ := isSplitTorus_of_isAlgClosed T ht.1
  let M := StandardLattice.{u} r
  let B := groupAlgebra K M
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := K) r
  let TB : specGroup B ≅ T.group := i ≪≫ t.symm
  obtain ⟨A, _, ⟨g⟩⟩ := groupPresentation G
  obtain ⟨a, -⟩ := hopfSpectrumBaseChange k K A
  let AK := extendedHopf K A
  let GA : specGroup AK ≅ (GeometricGroup G).val := a ≪≫ F.mapIso g
  let j := TB.hom ≫ T.inclusion ≫ GA.inv
  let b : AK ⟶ B := (hopfSpec.fullyFaithful.preimage j).unop
  have hbj : specGroupMap b = j := hopfSpec.fullyFaithful.map_preimage j
  let underlying := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have hb : Function.Surjective b.hom := by
    apply (hopfMapClosedImmersion K b).mp
    rw [hbj]
    have := T.isClosedImmersion
    have : IsIso (underlying.map TB.hom) := inferInstance
    have : IsIso (underlying.map GA.inv) := inferInstance
    change IsClosedImmersion (underlying.map TB.hom ≫ T.inclusion.hom.hom.left ≫ underlying.map GA.inv)
    infer_instance
  let U := Grp.forget (SchemeOver K)
  have hT : U.map (specGroupMap b) = U.map TB.hom ≫ T.inclusion.hom.hom ≫ U.map GA.inv :=
    congrArg U.map hbj
  have hG_id : U.map GA.inv ≫ U.map GA.hom = 𝟙 _ := (U.mapIso GA).inv_hom_id
  have hG_id' : U.map GA.hom ≫ U.map GA.inv = 𝟙 _ := (U.mapIso GA).hom_inv_id
  have hT_id : U.map TB.inv ≫ U.map TB.hom = 𝟙 _ := (U.mapIso TB).inv_hom_id
  have hT_id' : U.map TB.hom ≫ U.map TB.inv = 𝟙 _ := (U.mapIso TB).hom_inv_id
  have hG_cancel {X : SchemeOver K} (a : _ ⟶ X) : U.map GA.inv ≫ U.map GA.hom ≫ a = a := by
    rw [← Category.assoc, hG_id, Category.id_comp]
  have hT_cancel {X : SchemeOver K} (a : _ ⟶ X) : U.map TB.inv ≫ U.map TB.hom ≫ a = a := by
    rw [← Category.assoc, hT_id, Category.id_comp]
  let f' := U.map GA.hom ≫ f ≫ U.map TB.inv
  have hf' : f' ≫ U.map (specGroupMap b) = (𝟙 (specGroup AK).X) ^ (p ^ e) := by
    dsimp only [f']
    rw [hT]
    simp only [Category.assoc, hT_cancel]
    rw [← Category.assoc f T.inclusion.hom.hom, hf]
    change U.map GA.hom ≫ ((𝟙 (GeometricGroup G).val.X) ^ (p ^ e)) ≫ GA.inv.hom.hom = _
    rw [MonObj.pow_comp]
    rw [show (𝟙 (GeometricGroup G).val.X) ≫ GA.inv.hom.hom = GA.inv.hom.hom from
      Category.id_comp GA.inv.hom.hom]
    let a : (specGroup AK).X ⟶ (GeometricGroup G).val.X := GA.hom.hom.hom
    let b : (GeometricGroup G).val.X ⟶ (specGroup AK).X := GA.inv.hom.hom
    change a ≫ b ^ (p ^ e) = _
    rw [MonObj.comp_pow]
    exact congrArg (fun z : (specGroup AK).X ⟶ (specGroup AK).X ↦ z ^ (p ^ e)) hG_id'
  have hft' : U.map (specGroupMap b) ≫ f' = (𝟙 (specGroup B).X) ^ (p ^ e) := by
    dsimp only [f']
    rw [hT]
    simp only [Category.assoc, hG_cancel]
    rw [← Category.assoc T.inclusion.hom.hom f, hft]
    change U.map TB.hom ≫ ((𝟙 T.group.X) ^ (p ^ e)) ≫ TB.inv.hom.hom = _
    rw [MonObj.pow_comp]
    rw [show (𝟙 T.group.X) ≫ TB.inv.hom.hom = TB.inv.hom.hom from
      Category.id_comp TB.inv.hom.hom]
    let a : (specGroup B).X ⟶ T.group.X := TB.hom.hom.hom
    let b : T.group.X ⟶ (specGroup B).X := TB.inv.hom.hom
    change a ≫ b ^ (p ^ e) = _
    rw [MonObj.comp_pow]
    exact congrArg (fun z : (specGroup B).X ⟶ (specGroup B).X ↦ z ^ (p ^ e)) hT_id'
  have hK := ker_coordinatePower_of_factor AK B b f' (p ^ e) hf' hft'
    (coordinatePower_split_injective r (pow_ne_zero _ (Fact.out (p := p.Prime)).ne_zero))
  rw [coordinatePower_baseChange] at hK
  obtain ⟨iso, hiso⟩ := quotient_of_extended_kernel K A B (coordinatePower A (p ^ e))
    b.hom.toAlgHom hb hK.symm
  let I := RingHom.ker (coordinatePower A (p ^ e)).toRingHom
  obtain ⟨hI, ⟨E⟩⟩ := hopfQuotient_of_baseChange K A B b I iso hiso hb
  let W := hopfQuotient A I
  let q := specGroupMap (hopfQuotientMap A I)
  have : IsClosedImmersion q.hom.hom.left :=
    (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective
  let Fk := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsIso (Fk.map g.hom) := inferInstance
  let S : ClosedSubgroup G.val := ⟨specGroup W, q ≫ g.hom, by
    change IsClosedImmersion (q.hom.hom.left ≫ Fk.map g.hom)
    infer_instance⟩
  obtain ⟨w, -⟩ := hopfSpectrumBaseChange k K W
  exact ⟨S, ⟨w.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso E.symm.op ≪≫ TB⟩⟩

private theorem groupLike_scalarMap {k K R A : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [CommRing A] [Bialgebra k A]
    (f : K →ₐ[k] R) (x : K ⊗[k] A) (hx : IsGroupLikeElem K x) :
    IsGroupLikeElem R (Algebra.TensorProduct.map f (AlgHom.id k A) x) := by
  let δ := Algebra.TensorProduct.map f (AlgHom.id k A)
  have hcompat : δ.toRingHom.comp (algebraMap K (K ⊗[k] A)) =
      (algebraMap R (R ⊗[k] A)).comp f.toRingHom := by
    ext t
    simp [δ, Algebra.TensorProduct.algebraMap_apply]
  let Λ := Algebra.TensorProduct.mapRingHom f.toRingHom δ.toRingHom δ.toRingHom hcompat hcompat
  have hε (z : K ⊗[k] A) : Coalgebra.counit (R := R) (δ z) = f (Coalgebra.counit (R := K) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp [δ, TensorProduct.counit_tmul, Algebra.smul_def]
    | add s t hs ht => simp only [map_add, hs, ht]
  have hΔ (z : K ⊗[k] A) : Coalgebra.comul (R := R) (δ z) = Λ (Coalgebra.comul (R := K) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [δ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.comul_tmul]
      generalize Coalgebra.comul (R := k) b = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        simp [Λ, δ, Algebra.TensorProduct.mapRingHom_tmul]
      | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
    | add s t hs ht => simp only [map_add, hs, ht]
  exact ⟨by rw [hε, hx.counit_eq_one, map_one], by
    rw [hΔ, hx.comul_eq_tmul_self]
    exact Algebra.TensorProduct.mapRingHom_tmul _ _ _ hcompat hcompat _ _⟩
private noncomputable def bialg_cancelBaseChange (k K R A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
    [CommRing A] [Bialgebra k A] :
    (R ⊗[K] (K ⊗[k] A)) ≃ₐc[R] (R ⊗[k] A) := by
  let e := Algebra.TensorProduct.cancelBaseChange k K R R A
  refine BialgEquiv.ofAlgEquiv e ?_ ?_
  · apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r t =>
      induction t using TensorProduct.inductionOn with
      | tmul a x =>
        simp [e, TensorProduct.counit_tmul, Algebra.smul_def, map_mul, mul_assoc, mul_comm]
        rw [IsScalarTower.algebraMap_apply k K R]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  · apply AlgHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r t =>
      induction t using TensorProduct.inductionOn with
      | tmul a x =>
        simp only [e, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
          Bialgebra.comulAlgHom_apply, TensorProduct.comul_tmul]
        generalize Coalgebra.comul (R := k) x = d
        induction d using TensorProduct.inductionOn with
        | tmul v w =>
          simp [Algebra.smul_def, Algebra.TensorProduct.map_tmul]
        | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable def bialg_groupAlgebraBaseChange (K R M : Type u) [Field K] [CommRing R] [Algebra K R]
    [CommGroup M] : (R ⊗[K] MonoidAlgebra K M) ≃ₐc[R] MonoidAlgebra R M := by
  let f := MonoidAlgebra.scalarTensorEquiv K R (M := M)
  have hf (a : R) (m : M) :
      f (a ⊗ₜ[K] MonoidAlgebra.single m (1 : K)) = MonoidAlgebra.single m a :=
    f.toEquiv.eq_symm_apply.mp (MonoidAlgebra.scalarTensorEquiv_symm_single (R := K) (A := R) m a).symm
  refine BialgEquiv.ofAlgEquiv f ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    apply MonoidAlgebra.algHom_ext
    · intro m
      change Coalgebra.counit (R := R) (f ((1 : R) ⊗ₜ[K] MonoidAlgebra.single m (1 : K))) = _
      rw [hf]
      simp
    · ext
  · apply Algebra.TensorProduct.ext_ring
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Bialgebra.comulAlgHom_apply,
        TensorProduct.comul_tmul, CommSemiring.comul_apply, MonoidAlgebra.comul_single,
        TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_apply, hf]
    · ext

private theorem coeff_idempotent_of_groupLike {R M : Type u} [CommRing R] [CommGroup M]
    (x : MonoidAlgebra R M) (hx : IsGroupLikeElem R x) (m : M) :
    IsIdempotentElem (x.coeff m) := by
  classical
  let b := MonoidAlgebra.basis M R
  let d := b.coord m
  let L := (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map d d)
  have hd : L.comp (Coalgebra.comul (R := R)) = d := by
    apply b.ext
    intro j
    change L (Coalgebra.comul (R := R) (MonoidAlgebra.single j 1)) = d (MonoidAlgebra.single j 1)
    rw [(MonoidAlgebra.isGroupLikeElem_single_one (R := R) (A := R) j).comul_eq_tmul_self]
    change d (MonoidAlgebra.single j 1) * d (MonoidAlgebra.single j 1) = d (MonoidAlgebra.single j 1)
    change (b.repr (b j) m) * (b.repr (b j) m) = b.repr (b j) m
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    split <;> simp_all
  have he := LinearMap.congr_fun hd x
  change L (Coalgebra.comul (R := R) x) = d x at he
  rw [hx.comul_eq_tmul_self] at he
  exact he

private theorem tensor_square_idempotent {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] (x : K ⊗[k] K) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨n, hn, y, hy⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (R := K) x
  have hyx : algebraMap K (K ⊗[k] K) y = x := hy.trans (hx.pow_eq hn.ne')
  have hi : Function.Injective (algebraMap K (K ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap k K).injective
  have hy' : IsIdempotentElem y := by
    apply hi
    rw [map_mul, hyx]
    exact hx
  rcases mul_eq_zero.mp hy'.mul_one_sub_self with h | h
  · exact .inl (by rw [← hyx, h, map_zero])
  · exact .inr (by rw [← hyx, ← sub_eq_zero.mp h, map_one])

/-- The two scalar embeddings have equal effect on a group-like in a split
Hopf algebra over a purely inseparable extension. -/
private theorem groupLike_purelyInseparable_equalizer {k K A M : Type u}
    [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing A] [Bialgebra k A]
    [CommGroup M] (b : (K ⊗[k] A) ≃ₐc[K] MonoidAlgebra K M)
    (x : K ⊗[k] A) (hx : IsGroupLikeElem K x) :
    Algebra.TensorProduct.map ((Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[k] K).restrictScalars k)
      (AlgHom.id k A) x =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (A := K) (B := K))
        (AlgHom.id k A) x := by
  let R := K ⊗[k] K
  let left : K →ₐ[k] R := (Algebra.TensorProduct.includeLeft : K →ₐ[K] R).restrictScalars k
  let right : K →ₐ[k] R := Algebra.TensorProduct.includeRight
  let mult : R →ₐ[k] K := Algebra.TensorProduct.lmul' k
  let pull₁ := Algebra.TensorProduct.map left (AlgHom.id k A)
  let pull₂ := Algebra.TensorProduct.map right (AlgHom.id k A)
  let π := Algebra.TensorProduct.map mult (AlgHom.id k A)
  let e := bialg_cancelBaseChange k K R A
  let j := Bialgebra.TensorProduct.map (BialgHom.id R R) b.toBialgHom
  let d := bialg_groupAlgebraBaseChange K R M
  let χ := d.toBialgHom.comp (j.comp e.symm.toBialgHom)
  have hj : Function.Injective j := by
    change Function.Injective (TensorProduct.map (LinearMap.id : R →ₗ[K] R) b.toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id b.injective
  have hχ : Function.Injective χ := d.injective.comp (hj.comp e.symm.injective)
  have hEval (z : R ⊗[k] A) : MonoidAlgebra.mapRingHom M mult.toRingHom (χ z) = b (π z) := by
    induction z using TensorProduct.inductionOn with
    | tmul r a =>
      change MonoidAlgebra.mapRingHom M mult.toRingHom (d (j (e.symm (r ⊗ₜ[k] a)))) = _
      rw [show e.symm (r ⊗ₜ[k] a) = r ⊗ₜ[K] ((1 : K) ⊗ₜ[k] a) from rfl,
        Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
      change MonoidAlgebra.mapRingHom M mult.toRingHom
        (MonoidAlgebra.scalarTensorEquiv K R (r ⊗ₜ[K] b ((1 : K) ⊗ₜ[k] a))) = _
      rw [MonoidAlgebra.scalarTensorEquiv_tmul]
      ext m
      rw [MonoidAlgebra.coeff_mapRingHom]
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, MonoidAlgebra.coeff_mapAlgHom]
      change mult (r * algebraMap K R ((b ((1 : K) ⊗ₜ[k] a)).coeff m)) = (b (mult r ⊗ₜ[k] a)).coeff m
      have hmult (c : K) : mult (algebraMap K R c) = c := by
        change c * 1 = c
        exact mul_one c
      rw [map_mul, hmult, ← show mult r • ((1 : K) ⊗ₜ[k] a) = mult r ⊗ₜ[k] a by
        simp [TensorProduct.smul_tmul'], map_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
    | add p q hp hq => simp only [map_add, hp, hq]
  have hπ₁ (z : K ⊗[k] A) : π (pull₁ z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change (a * 1) ⊗ₜ[k] b = a ⊗ₜ[k] b
      rw [mul_one]
    | add p q hp hq => simp only [map_add, hp, hq]
  have hπ₂ (z : K ⊗[k] A) : π (pull₂ z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change (1 * a) ⊗ₜ[k] b = a ⊗ₜ[k] b
      rw [one_mul]
    | add p q hp hq => simp only [map_add, hp, hq]
  have h₁ : IsGroupLikeElem R (χ (pull₁ x)) := (groupLike_scalarMap left x hx).map χ
  have h₂ : IsGroupLikeElem R (χ (pull₂ x)) := (groupLike_scalarMap right x hx).map χ
  apply hχ
  ext m
  change (χ (pull₁ x)).coeff m = (χ (pull₂ x)).coeff m
  have h := congrArg (fun s : MonoidAlgebra K M ↦ s.coeff m) ((hEval _).trans
    ((congrArg b ((hπ₁ x).trans (hπ₂ x).symm)).trans (hEval _).symm))
  simp only [MonoidAlgebra.coeff_mapRingHom] at h
  rcases tensor_square_idempotent _ (coeff_idempotent_of_groupLike _ h₁ m) with h₁' | h₁' <;>
    rcases tensor_square_idempotent _ (coeff_idempotent_of_groupLike _ h₂ m) with h₂' | h₂' <;>
    simp_all

private theorem tensor_candidate_in_base_of_equalizer {k K A : Type u} [Field k] [Field K]
    [Algebra k K] [CommRing A] [Algebra k A] (x : K ⊗[k] A)
    (h : Algebra.TensorProduct.map
      ((Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[k] K).restrictScalars k)
      (AlgHom.id k A) x = Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := K)) (AlgHom.id k A) x) :
    ∃ a : A, (1 : K) ⊗ₜ[k] a = x := by
  classical
  let b := Module.Free.chooseBasis k A
  let p := (b.baseChange K).repr
  let R := K ⊗[k] K
  let left : K →ₐ[k] R := (Algebra.TensorProduct.includeLeft : K →ₐ[K] R).restrictScalars k
  let right : K →ₐ[k] R := Algebra.TensorProduct.includeRight
  have hEq (f : K →ₐ[k] R) (z : K ⊗[k] A) (i : Module.Free.ChooseBasisIndex k A) :
      (b.baseChange R).repr (Algebra.TensorProduct.map f (AlgHom.id k A) z) i = f (p z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul z a =>
      change (b.baseChange R).repr (f z ⊗ₜ[k] a) i = f ((b.baseChange K).repr (z ⊗ₜ[k] a) i)
      simp [Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  have hcoeff (i : Module.Free.ChooseBasisIndex k A) : ∃ c : k, algebraMap k K c = p x i := by
    have hc := congrArg (fun z ↦ (b.baseChange R).repr z i) h
    change (b.baseChange R).repr (Algebra.TensorProduct.map left (AlgHom.id k A) x) i =
      (b.baseChange R).repr (Algebra.TensorProduct.map right (AlgHom.id k A) x) i at hc
    rw [hEq, hEq] at hc
    have he := (Algebra.IsEffective.of_faithfullyFlat (R := k) (S := K)).eqLocus_includeLeft_includeRight
    have hm : p x i ∈ (Algebra.TensorProduct.includeLeftRingHom.eqLocus
        Algebra.TensorProduct.includeRight.toRingHom (S := K ⊗[k] K)) := hc
    change p x i ∈ Set.range (algebraMap k K)
    rw [← he]
    exact hm
  choose c hc using hcoeff
  let t := p x
  let f : Module.Free.ChooseBasisIndex k A →₀ k :=
    Finsupp.onFinset t.support (fun i ↦ if i ∈ t.support then c i else 0)
      (by intro i h; by_contra hn; simp [hn] at h)
  refine ⟨b.repr.symm f, p.injective ?_⟩
  ext i
  change (b.baseChange K).repr ((1 : K) ⊗ₜ[k] b.repr.symm f) i = t i
  rw [Module.Basis.baseChange_repr_tmul, LinearEquiv.apply_symm_apply, Algebra.smul_def, mul_one]
  by_cases hi : i ∈ t.support
  · simpa only [f, Finsupp.onFinset_apply, ite_eq_left hi] using hc i
  · simp [f, Finsupp.notMem_support_iff.mp hi]

private theorem groupLike_of_includeRight {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing A] [Bialgebra k A] {a : A} (h : IsGroupLikeElem K ((1 : K) ⊗ₜ[k] a)) :
    IsGroupLikeElem k a := by
  constructor
  · apply (algebraMap k K).injective
    have he := h.counit_eq_one
    simpa [TensorProduct.counit_tmul, Algebra.smul_def] using he
  · let e := TensorProduct.AlgebraTensorModule.distribBaseChange k K A A
    let i : (A ⊗[k] A) →ₐ[k] K ⊗[k] (A ⊗[k] A) := Algebra.TensorProduct.includeRight
    let D := (e.restrictScalars k).toLinearMap.comp i.toLinearMap
    have hDi : Function.Injective D :=
      e.injective.comp (Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective)
    have hΔ : Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[k] a) = D (Coalgebra.comul (R := k) a) := by
      rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
      generalize Coalgebra.comul (R := k) a = t
      induction t using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
    apply hDi
    rw [← hΔ, h.comul_eq_tmul_self]
    rfl

/-- A group algebra presentation after purely inseparable scalar extension
already has a group algebra presentation over the ground field. -/
private theorem split_of_purelyInseparable {k K A M : Type u} [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing A] [Bialgebra k A] [CommGroup M]
    (b : (K ⊗[k] A) ≃ₐc[K] MonoidAlgebra K M) :
    Nonempty (MonoidAlgebra k M ≃ₐc[k] A) := by
  classical
  let j : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let g (m : M) := b.symm (MonoidAlgebra.single m 1)
  have hg (m : M) : IsGroupLikeElem K (g m) :=
    (MonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) m).map b.symm
  have hExists (m : M) : ∃ a : A, j a = g m :=
    tensor_candidate_in_base_of_equalizer _ (groupLike_purelyInseparable_equalizer b _ (hg m))
  choose a ha using hExists
  have hap (m : M) : IsGroupLikeElem k (a m) :=
    groupLike_of_includeRight ((ha m).symm ▸ hg m)
  have hba (m : M) : b (j (a m)) = MonoidAlgebra.of K M m := by
    rw [ha]
    exact b.apply_symm_apply _
  have hi : Function.Injective (fun z : A ↦ b (j z)) :=
    b.injective.comp (Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective)
  let p : M →* GroupLike k A := {
    toFun := fun m ↦ ⟨a m, hap m⟩
    map_one' := by
      apply GroupLike.val_injective
      apply hi
      change b (j (a 1)) = b (j 1)
      rw [hba, map_one, map_one, map_one]
    map_mul' := by
      intro m n
      apply GroupLike.val_injective
      apply hi
      change b (j (a (m * n))) = b (j (a m * a n))
      rw [map_mul, map_mul, hba, hba, hba, map_mul] }
  let f := MonoidAlgebra.liftGroupLikeBialgHom.comp (MonoidAlgebra.mapDomainBialgHom k p)
  have hf (m : M) : f (MonoidAlgebra.single m 1) = a m := by
    dsimp [f]
    rw [MonoidAlgebra.mapDomainBialgHom_single]
    simp
    rfl
  let fK := Algebra.TensorProduct.map (AlgHom.id K K) f.toAlgHom
  let C := MonoidAlgebra.scalarTensorEquiv k K (M := M)
  have hw : b.toAlgEquiv.toAlgHom.comp fK = C.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply MonoidAlgebra.algHom_ext
    · intro m
      change b (fK (1 ⊗ₜ[k] MonoidAlgebra.single m 1)) = C (1 ⊗ₜ[k] MonoidAlgebra.single m 1)
      change b ((1 : K) ⊗ₜ[k] f (MonoidAlgebra.single m 1)) = _
      rw [hf]
      change b (j (a m)) = C (1 ⊗ₜ[k] MonoidAlgebra.single m 1)
      rw [hba]
      exact (C.toEquiv.eq_symm_apply.mp
        (MonoidAlgebra.scalarTensorEquiv_symm_single (R := k) (A := K) m 1).symm).symm
    · ext
  have hBij : Function.Bijective fK := by
    have hFun : (fun x ↦ b (fK x)) = C := congrArg (fun t : _ →ₐ[K] _ ↦ (t : _ → _)) hw
    constructor
    · intro x y h
      apply C.injective
      rw [← congrFun hFun x, ← congrFun hFun y, h]
    · intro z
      obtain ⟨x, hx⟩ := C.surjective (b z)
      exact ⟨x, b.injective ((congrFun hFun x).trans hx)⟩
  exact ⟨BialgEquiv.ofBijective f <|
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k K f.toAlgHom.toLinearMap).mp hBij⟩

/-- Geometric splitness produces a separable splitting field for the group. -/
private theorem isTorus_of_split_baseChange (S : GroupScheme k) [IsAffine S.X.left]
    (hS : IsSplitTorus ((groupBaseChange k (AlgebraicClosure k)).obj S)) :
    IsTorus S := by
  let K := AlgebraicClosure k
  let E : IntermediateField k K := separableClosure k K
  obtain ⟨r, ⟨s⟩⟩ := hS
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := K) r
  let A : AffineGroupCategory k := ⟨S, inferInstance⟩
  let W := coordinateHopf A
  let w : specGroup W ≅ S := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso A)
  obtain ⟨a, -⟩ := hopfSpectrumBaseChange k K W
  let j := a ≪≫ (groupBaseChange k K).mapIso w ≪≫ s ≪≫ i.symm
  let b : extendedHopf K W ≅ groupAlgebra K (StandardLattice.{u} r) :=
    ((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimageIso j).unop.symm
  let c := (bialg_cancelBaseChange k E K W).trans (CommHopfAlgCat.ofIso b)
  obtain ⟨d⟩ := split_of_purelyInseparable c
  apply torus_of_iso w
  apply (GeometricRadicals.torusCoordinateComparison W).mpr
  exact ⟨E, inferInstance, inferInstance, inferInstance, r, ⟨CommHopfAlgCat.isoMk d⟩⟩

private def baseChange_trivial_iso (K : Type u) [Field K] [Algebra k K] :
    (groupBaseChange k K).obj (Grp.trivial (SchemeOver k)) ≅
      Grp.trivial (SchemeOver K) := by
  let e := Functor.Monoidal.εIso (baseChange k K)
  let f : (groupBaseChange k K).obj (Grp.trivial (SchemeOver k)) ⟶
      Grp.trivial (SchemeOver K) := default
  have h : f.hom.hom = e.inv := toUnit_unique _ _
  haveI : IsIso f.hom.hom := by rw [h]; infer_instance
  exact Grp.mkIso (asIso f.hom.hom) (IsMonHom.one_hom (f := f.hom.hom))
    (IsMonHom.mul_hom (f := f.hom.hom))

private theorem torus_of_subgroup_baseChange
    {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup (GeometricGroup G).val) (ht : IsTorus T.group)
    (hn : ¬ IsTrivialSubgroup T) (S : ClosedSubgroup G.val)
    (e : (groupBaseChange k (AlgebraicClosure k)).obj S.group ≅ T.group) :
    ∃ S : ClosedSubgroup G.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S := by
  have : IsAffine S.group.X.left := (closedSubgroupAlgebraicGroup S).property.1
  obtain ⟨r, ⟨s⟩⟩ := isSplitTorus_of_isAlgClosed T ht
  refine ⟨S, isTorus_of_split_baseChange S.group ⟨r, ⟨e ≪≫ s⟩⟩, ?_⟩
  rintro ⟨j⟩
  exact hn ⟨e.symm ≪≫ (groupBaseChange k (AlgebraicClosure k)).mapIso j ≪≫
    baseChange_trivial_iso (AlgebraicClosure k)⟩

private def latticeCoordinate {r : ℕ} (i : Fin r) (m : StandardLattice.{u} r) : ℤ :=
  (m i).down.toAdd

/-- A nilpotent perturbation of the identity has no nonidentity
finite-order elements over a field of characteristic zero. -/
private theorem nilpotent_add_one_torsion_eq_one [CharZero k] {A : Type u}
    [Ring A] [Algebra k A] (N : A) (hN : IsNilpotent N) (n : ℕ) (hn : n ≠ 0)
    (h : (1 + N) ^ n = 1) : N = 0 := by
  have hl (x y : A) (j : ℕ) : x * (j • y) = j • (x * y) :=
    map_nsmul (AddMonoidHom.mulLeft x) j y
  have hr (x y : A) (j : ℕ) : (j • x) * y = j • (x * y) :=
    map_nsmul (AddMonoidHom.mulRight y) j x
  have expansion (j : ℕ) : ∃ C : A, (1 + N) ^ j = 1 + j • N + N ^ 2 * C := by
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨j • (1 : A) + C + C * N, ?_⟩
      rw [pow_succ, hC, succ_nsmul]
      simp only [mul_add, add_mul, one_mul, mul_one, pow_two, hl, hr, mul_assoc]
      abel
  obtain ⟨C, hC⟩ := expansion n
  have hLine : n • N + N ^ 2 * C = 0 := by
    apply add_left_cancel (a := (1 : A))
    rw [add_zero]
    simpa only [h, add_assoc] using hC.symm
  obtain ⟨m, hm⟩ := hN
  have hd : ∀ j : ℕ, N ^ (j + 1) = 0 → N = 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      apply ih
      have he := congrArg (fun z : A ↦ N ^ j * z) hLine
      rw [mul_add, hl, ← pow_succ, ← mul_assoc, ← pow_add,
        show j + 2 = j.succ + 1 by omega, hj, zero_mul, add_zero, mul_zero] at he
      have hc : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
      rw [← Nat.cast_smul_eq_nsmul k] at he
      exact (smul_eq_zero.mp he).resolve_left hc
  apply hd m
  rw [pow_succ, hm, zero_mul]

private theorem unipotent_points_torsion_eq_one [CharZero k]
    (U : AffineAlgebraicGroup k) (hU : IsUnipotent U)
    (R : TestAlgebra k) (x : Specs.AdjointRepresentation.GroupPoints U.val R)
    (n : ℕ) (hn : n ≠ 0) (hx : x ^ n = 1) : x = 1 := by
  classical
  obtain ⟨d, J, ⟨e⟩, f, hf⟩ := (unipotent_iff_exists_embedding U).mp hU
  let F := groupPointsFunctor k
  let a := (F.map f).app R
  let g : Specs.Unipotent.upperUnitriangular (ULift.{u} (Fin d)) R := e.hom.app R (a x)
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left f.hom.hom
  have ha : Function.Injective a := fun _ _ h ↦ (cancel_mono f.hom.hom).mp h
  let j := (e.hom.app R).hom.comp a.hom
  apply ha
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app R)).injective
  change j x = j 1
  rw [map_one]
  apply Subtype.ext
  apply Units.ext
  change g.val.val = 1
  let N := g.val.val - 1
  have hN (i j : ULift.{u} (Fin d)) (h : j ≤ i) : N i j = 0 := by
    rcases lt_or_eq_of_le h with hlt | heq
    · change g.val.val i j - (1 : Matrix _ _ R) i j = 0
      rw [g.property.1 hlt, Matrix.one_apply_ne (ne_of_gt hlt), sub_zero]
    · subst j
      change g.val.val i i - (1 : Matrix _ _ R) i i = 0
      rw [g.property.2 i, Matrix.one_apply_eq, sub_self]
  have hPow := congrArg (fun y ↦ (j y).val.val) hx
  have hEq : g.val.val = 1 + N := by dsimp [N]; abel
  have hEqPow : (1 + N) ^ n = 1 := by
    change ((j (x ^ n)).val : Matrix.GeneralLinearGroup (ULift.{u} (Fin d)) R).val = _ at hPow
    rw [map_pow, map_one] at hPow
    change g.val.val ^ n = 1 at hPow
    rwa [hEq] at hPow
  rw [hEq, nilpotent_add_one_torsion_eq_one (k := k) N ⟨d, strictUpper_pow_card _ hN⟩ n hn hEqPow,
    add_zero]

private def torsionFunctions (A : HopfAlgebraCategory k) (n : ℕ) : A →ₗ[k] A :=
  (coordinatePower A n).toLinearMap - (Algebra.linearMap k A).comp (Coalgebra.counit (R := k))

private def torsionIdeal (A : HopfAlgebraCategory k) (n : ℕ) : Ideal A :=
  Ideal.span (Set.range (torsionFunctions A n))

private theorem torsionIdeal_le_ker_iff (A : HopfAlgebraCategory k) (n : ℕ)
    (R : TestAlgebra k) (a : A →ₐ[k] R) :
    torsionIdeal A n ≤ RingHom.ker a.toRingHom ↔
      (toConv a : (convolutionPoints A).obj R) ^ n = 1 := by
  let α := (convolutionPoints A).map (CommAlgCat.ofHom a)
  have hα := map_pow α.hom (toConv (AlgHom.id k A)) n
  change toConv (a.comp (coordinatePower A n)) = (toConv a : (convolutionPoints A).obj R) ^ n at hα
  rw [← hα, torsionIdeal, Ideal.span_le]
  constructor
  · intro h
    apply WithConv.ofConv_injective
    ext x
    have hx := h (Set.mem_range_self x)
    change a (coordinatePower A n x - algebraMap k A (Coalgebra.counit (R := k) x)) = 0 at hx
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at hx
    exact hx
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    change a (coordinatePower A n y - algebraMap k A (Coalgebra.counit (R := k) y)) = 0
    rw [map_sub, AlgHom.commutes, sub_eq_zero]
    exact congrArg (fun z : (convolutionPoints A).obj R ↦ z.ofConv y) h

private theorem coordinatePower_natural (A B : HopfAlgebraCategory k) (b : A ⟶ B) (n : ℕ) :
    b.hom.toAlgHom.comp (coordinatePower A n) =
      (coordinatePower B n).comp b.hom.toAlgHom := by
  let f := b.hom.toAlgHom
  change f.comp (coordinatePower A n) = _
  induction n with
  | zero =>
    ext x
    change f (algebraMap k A (Coalgebra.counit (R := k) x)) =
      algebraMap k B (Coalgebra.counit (R := k) (b.hom x))
    rw [AlgHom.commutes, CoalgHomClass.counit_comp_apply]
  | succ n ih =>
    change f.comp ((((toConv (AlgHom.id k A)) ^ (n + 1))).ofConv) =
      (((toConv (AlgHom.id k B)) ^ (n + 1)).ofConv.comp b.hom.toAlgHom)
    rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib,
      AlgHom.convMul_comp_bialgHom_distrib _ _ b.hom]
    change (toConv (f.comp (coordinatePower A n)) * toConv f).ofConv =
      (toConv ((coordinatePower B n).comp f) * toConv f).ofConv
    rw [ih]

private theorem torsionIdeal_baseChange (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (n : ℕ) :
    torsionIdeal (extendedHopf K A) n = extendedIdeal K (torsionIdeal A n) := by
  let f := torsionFunctions (extendedHopf K A) n
  let g := torsionFunctions A n
  have h (r : K) (a : A) : f (r ⊗ₜ[k] a) = r ⊗ₜ[k] g a := by
    change coordinatePower (extendedHopf K A) n (r ⊗ₜ[k] a) -
      algebraMap K (K ⊗[k] A) (Coalgebra.counit (R := K) (r ⊗ₜ[k] a)) =
        r ⊗ₜ[k] (coordinatePower A n a - algebraMap k A (Coalgebra.counit (R := k) a))
    rw [coordinatePower_baseChange, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      TensorProduct.counit_tmul, Algebra.TensorProduct.algebraMap_apply, TensorProduct.tmul_sub]
    congr 1
    change (Coalgebra.counit (R := k) a • r) ⊗ₜ[k] (1 : A) =
      r ⊗ₜ[k] (algebraMap k A (Coalgebra.counit (R := k) a))
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change f z ∈ extendedIdeal K (torsionIdeal A n)
    induction z using TensorProduct.inductionOn with
    | tmul r a =>
      rw [h]
      have hm : (1 : K) ⊗ₜ[k] g a ∈ extendedIdeal K (torsionIdeal A n) :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self a))
      have hh : r ⊗ₜ[k] g a = (r ⊗ₜ[k] (1 : A)) * (1 ⊗ₜ[k] g a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hh]
      exact Ideal.mul_mem_left _ _ hm
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change (1 : K) ⊗ₜ[k] g a ∈ torsionIdeal (extendedHopf K A) n
    rw [← h 1 a]
    exact Ideal.subset_span (Set.mem_range_self _)

private theorem torsionIdeal_eq_comap (A B : HopfAlgebraCategory k) (b : A ⟶ B)
    (hSurj : Function.Surjective b.hom) (n : ℕ)
    (hlift : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R),
      (toConv a : (convolutionPoints A).obj R) ^ n = 1 →
        ∃ c : B →ₐ[k] R, c.comp b.hom.toAlgHom = a) :
    torsionIdeal A n = (torsionIdeal B n).comap b.hom.toAlgHom := by
  have hnat (a : A) :
      b.hom (torsionFunctions A n a) = torsionFunctions B n (b.hom a) := by
    change b.hom (coordinatePower A n a - algebraMap k A (Coalgebra.counit (R := k) a)) =
      coordinatePower B n (b.hom a) - algebraMap k B (Coalgebra.counit (R := k) (b.hom a))
    rw [map_sub, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]
    exact congrArg (· - algebraMap k B (Coalgebra.counit (R := k) a))
      (DFunLike.congr_fun (coordinatePower_natural A B b n) a)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change b.hom (torsionFunctions A n a) ∈ torsionIdeal B n
    rw [hnat]
    exact Ideal.subset_span (Set.mem_range_self _)
  · let I := torsionIdeal A n
    let R := CommAlgCat.of k (A ⧸ I)
    let a := Ideal.Quotient.mkₐ k I
    have ha : I ≤ RingHom.ker a.toRingHom := fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr hx
    obtain ⟨c, hc⟩ := hlift R a ((torsionIdeal_le_ker_iff A n R a).mp ha)
    have hcI : torsionIdeal B n ≤ RingHom.ker c.toRingHom := by
      apply Ideal.span_le.mpr
      rintro x ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hSurj y
      rw [← hnat]
      change (c.comp b.hom.toAlgHom) (torsionFunctions A n z) = 0
      rw [hc]
      exact ha (Ideal.subset_span (Set.mem_range_self z))
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change a x = 0
    rw [← hc]
    exact hcI hx

private def latticeReduction (r n : ℕ) :
    StandardLattice.{u} r →* (Fin r → ULift.{u} (Multiplicative (ZMod n))) where
  toFun m i := ⟨Multiplicative.ofAdd (latticeCoordinate i m : ZMod n)⟩
  map_one' := by
    funext i
    apply ULift.ext
    change ((0 : ℤ) : ZMod n) = 0
    simp
  map_mul' a b := by
    funext i
    apply ULift.ext
    change ((latticeCoordinate i a + latticeCoordinate i b : ℤ) : ZMod n) =
      (latticeCoordinate i a : ZMod n) + latticeCoordinate i b
    rw [Int.cast_add]

private theorem latticeReduction_pow (r n : ℕ) (m : StandardLattice.{u} r) :
    latticeReduction r n (m ^ n) = 1 := by
  funext i
  apply ULift.ext
  change ((n • latticeCoordinate i m : ℤ) : ZMod n) = 0
  rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

private theorem torsionIdeals_split_inf (r : ℕ)
    (x : MonoidAlgebra k (StandardLattice.{u} r))
    (hx : ∀ n : ℕ, n ≠ 0 → x ∈ torsionIdeal (groupAlgebra k (StandardLattice r)) n) :
    x = 0 := by
  classical
  let s := x.coeff.support
  let f (a b : StandardLattice.{u} r) (i : Fin r) : ℕ :=
    (latticeCoordinate i a - latticeCoordinate i b).natAbs
  let g a b := Finset.univ.sup (f a b)
  let h a := s.sup (g a)
  let N := s.sup h
  let n := N + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero N
  let M := StandardLattice.{u} r
  let L := Fin r → ULift.{u} (Multiplicative (ZMod n))
  let F := latticeReduction r n
  let a := MonoidAlgebra.mapDomainAlgHom k k F
  have hi : Set.InjOn F (s : Set M) := by
    intro y hy z hz he
    funext i
    apply ULift.ext
    change latticeCoordinate i y = latticeCoordinate i z
    have ht : (latticeCoordinate i z - latticeCoordinate i y).natAbs ≤ N :=
      (Finset.le_sup (s := Finset.univ) (f := f z y) (Finset.mem_univ i)).trans
        ((Finset.le_sup (s := s) (f := g z) hy).trans (Finset.le_sup (s := s) (f := h) hz))
    have hEq := congrArg (fun h : L ↦ (h i).down.toAdd) he
    have hD := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp hEq
    symm
    apply sub_eq_zero.mp
    by_contra hne
    have hh := Int.natAbs_le_of_dvd_ne_zero hD hne
    simp only [Int.natAbs_natCast] at hh
    omega
  have hMem : torsionIdeal (groupAlgebra k M) n ≤ RingHom.ker a.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change a (coordinatePower (groupAlgebra k M) n y -
      algebraMap k (MonoidAlgebra k M) (Coalgebra.counit (R := k) y)) = 0
    rw [map_sub, AlgHom.commutes, sub_eq_zero]
    have hMap : a.comp (coordinatePower (groupAlgebra k M) n) =
        (Algebra.ofId k (MonoidAlgebra k L)).comp (Bialgebra.counitAlgHom k (MonoidAlgebra k M)) := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        change a (coordinatePower (groupAlgebra k M) n (MonoidAlgebra.of k M m)) =
          algebraMap k (MonoidAlgebra k L) (Coalgebra.counit (R := k) (MonoidAlgebra.of k M m))
        rw [coordinatePower_of, (MonoidAlgebra.isGroupLikeElem_of (R := k) (A := k) m).counit_eq_one,
          map_one]
        change MonoidAlgebra.mapDomain F (MonoidAlgebra.single (m ^ n) (1 : k)) = 1
        rw [MonoidAlgebra.mapDomain_single, latticeReduction_pow]
        rfl
      · ext
    exact DFunLike.congr_fun hMap y
  have ha : a x = 0 := hMem (hx n hn)
  ext m
  by_cases hm : m ∈ s
  · have hcoeff := Finsupp.mapDomain_apply' (s : Set M) x.coeff (fun _ hx ↦ hx) hi hm
    change (a x).coeff (F m) = x.coeff m at hcoeff
    rw [ha] at hcoeff
    exact hcoeff.symm
  · exact Finsupp.notMem_support_iff.mp hm


open private tensorQuotient_ker from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem extendedIdeal_mem_iff_coefficients (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I : Ideal A) {J : Type u} [DecidableEq J] (b : Module.Basis J k K)
    (x : K ⊗[k] A) : x ∈ extendedIdeal K I ↔
      ∀ j, TensorProduct.equivFinsuppOfBasisLeft b x j ∈ I := by
  let a := Ideal.Quotient.mkₐ k I
  let aK := Algebra.TensorProduct.map (AlgHom.id k K) a
  have he : RingHom.ker aK.toRingHom = extendedIdeal K I :=
    tensorQuotient_ker (k := k) (K := K) I
  rw [← he]
  change aK x = 0 ↔ _
  let E := TensorProduct.equivFinsuppOfBasisLeft b (N := A ⧸ I)
  have h (j : J) : E (aK x) j = a (TensorProduct.equivFinsuppOfBasisLeft b x j) := by
    induction x using TensorProduct.inductionOn with
    | tmul r z =>
      rw [show aK (r ⊗ₜ[k] z) = r ⊗ₜ[k] a z from rfl]
      change TensorProduct.equivFinsuppOfBasisLeft b (r ⊗ₜ[k] a z) j = _
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (map_smul a.toLinearMap (b.repr r j) z).symm
    | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw]
  constructor
  · intro hz j
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change a _ = 0
    rw [← h, hz, map_zero]
    rfl
  · intro hz
    apply E.injective
    ext j
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hz j)

private theorem extendedIdeal_iInf (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) {J : Type v} (I : J → Ideal A) :
    extendedIdeal K (⨅ j, I j) = ⨅ j, extendedIdeal K (I j) := by
  classical
  let b := Module.Free.chooseBasis k K
  ext x
  rw [extendedIdeal_mem_iff_coefficients K A _ b x]
  rw [Ideal.mem_iInf (I := fun j ↦ extendedIdeal K (I j))]
  constructor
  · intro h j
    rw [extendedIdeal_mem_iff_coefficients K A (I j) b]
    intro i
    exact (Ideal.mem_iInf.mp (h i)) j
  · intro h i
    apply Ideal.mem_iInf.mpr
    intro j
    exact (extendedIdeal_mem_iff_coefficients K A (I j) b x).mp (h j) i

private theorem subgroup_from_extendedIdeal (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (A : HopfAlgebraCategory k) (g : specGroup A ≅ G.val)
    (B : HopfAlgebraCategory K) (b : extendedHopf K A ⟶ B) (hb : Function.Surjective b.hom)
    (I : Ideal A) (hker : RingHom.ker b.hom.toAlgHom = extendedIdeal K I) :
    ∃ S : ClosedSubgroup G.val,
      Nonempty ((groupBaseChange k K).obj S.group ≅ specGroup B) := by
  let e := ((Algebra.TensorProduct.tensorQuotientEquiv K A K I).trans
    (Ideal.quotientEquivAlgOfEq K hker.symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := b.hom.toAlgHom) hb)
  have he (x : A) : e (1 ⊗ₜ[k] Ideal.Quotient.mk I x) = b.hom (1 ⊗ₜ[k] x) := by
    change Ideal.quotientKerAlgEquivOfSurjective hb (Ideal.quotientEquivAlgOfEq K hker.symm
      (Ideal.Quotient.mk (extendedIdeal K I) (1 ⊗ₜ[k] x))) = _
    rw [Ideal.quotientEquivAlgOfEq_mk]
    rfl
  obtain ⟨hI, ⟨E⟩⟩ := hopfQuotient_of_baseChange K A B b I e he hb
  let W := hopfQuotient A I
  let q := specGroupMap (hopfQuotientMap A I)
  have : IsClosedImmersion q.hom.hom.left :=
    (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsIso (F.map g.hom) := inferInstance
  let S : ClosedSubgroup G.val := ⟨specGroup W, q ≫ g.hom, by
    change IsClosedImmersion (q.hom.hom.left ≫ F.map g.hom)
    infer_instance⟩
  obtain ⟨w, -⟩ := hopfSpectrumBaseChange k K W
  exact ⟨S, ⟨w.symm ≪≫ (hopfSpec (CommRingCat.of K)).mapIso E.symm.op⟩⟩

private theorem factors_algebra_of_torsion_point [CharZero k]
    (H : GroupScheme k) (T : ClosedSubgroup H) (Q : AffineAlgebraicGroup k)
    (q : H ⟶ Q.val) (hQ : IsUnipotent Q) (hk : IsSchemeKernel q T)
    (A B : HopfAlgebraCategory k) (aH : specGroup A ≅ H) (bT : specGroup B ≅ T.group)
    (b : A ⟶ B) (hb : specGroupMap b = bT.hom ≫ T.inclusion ≫ aH.inv)
    (n : ℕ) (hn : n ≠ 0)
    (R : TestAlgebra k) (a : A →ₐ[k] R)
    (ha : (toConv a : (convolutionPoints A).obj R) ^ n = 1) :
    ∃ c : B →ₐ[k] R, c.comp b.hom.toAlgHom = a := by
  let P := groupPointsFunctor k
  let aP := (P.map aH.hom).app R
  let qP := (P.map q).app R
  let x := (hopfSpecPointIso A).hom.app R (toConv a)
  have hx : x ^ n = 1 := by
    have e := congrArg ((hopfSpecPointIso A).hom.app R).hom ha
    rw [map_pow, map_one] at e
    exact e
  have hxQ : (qP (aP x)) ^ n = 1 := by
    change (qP.hom (aP.hom x)) ^ n = 1
    rw [← map_pow, ← map_pow, hx, map_one, map_one]
  have hxQ1 := unipotent_points_torsion_eq_one Q hQ R (qP (aP x)) n hn hxQ
  obtain ⟨t, ht⟩ := (schemeKernel_sections hk _).mpr hxQ1
  let t' := t ≫ bT.inv.hom.hom
  let z := ((hopfSpecPointIso B).inv.app R).hom t'
  refine ⟨z.ofConv, ?_⟩
  apply WithConv.toConv_injective
  apply (ConcreteCategory.bijective_of_isIso ((hopfSpecPointIso A).hom.app R)).injective
  apply (cancel_mono aH.hom.hom.hom).mp
  change (hopfSpecPointIso A).hom.app R (toConv (z.ofConv.comp b.hom.toAlgHom)) ≫
    aH.hom.hom.hom = x ≫ aH.hom.hom.hom
  have hp : (hopfSpecPointIso A).hom.app R (toConv (z.ofConv.comp b.hom.toAlgHom)) =
      (hopfSpecPointIso B).hom.app R z ≫ (specGroupMap b).hom.hom := by
    apply Over.OverMorphism.ext
    exact Spec.map_comp (CommRingCat.ofHom b.hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom z.ofConv.toRingHom)
  have hp' : (hopfSpecPointIso B).hom.app R z = t' := by
    change (((hopfSpecPointIso B).hom.app R).hom
      (((hopfSpecPointIso B).inv.app R).hom t')) = t'
    rw [← GrpCat.comp_apply]
    change ((Iso.app (hopfSpecPointIso B) R).inv ≫ (Iso.app (hopfSpecPointIso B) R).hom) t' = t'
    simp
  rw [hp, hp', hb]
  change (t ≫ bT.inv.hom.hom) ≫ (bT.hom.hom.hom ≫
      T.inclusion.hom.hom ≫ aH.inv.hom.hom) ≫ aH.hom.hom.hom = _
  have haH : aH.inv.hom.hom ≫ aH.hom.hom.hom = 𝟙 H.X :=
    ((Grp.forget (SchemeOver k)).mapIso aH).inv_hom_id
  have hbT : bT.inv.hom.hom ≫ bT.hom.hom.hom = 𝟙 T.group.X :=
    ((Grp.forget (SchemeOver k)).mapIso bT).inv_hom_id
  have hc {X : SchemeOver k} (i : T.group.X ⟶ X) :
      bT.inv.hom.hom ≫ bT.hom.hom.hom ≫ i = i := by
    rw [← Category.assoc, hbT, Category.id_comp]
  simp only [Category.assoc, haH, Category.comp_id, hc]
  exact ht

set_option maxHeartbeats 2500000 in
/-- In characteristic zero the closed subschemes cut out by the
finite-order equations have schematic union equal to the central torus. -/
private theorem central_torus_charZero_baseChange [CharZero k]
    (centralizer : Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u})
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left) (T : ClosedSubgroup (GeometricGroup G).val)
    (ht : IsMaximalTorus T) (hz : IsCentral T.inclusion) :
    ∃ S : ClosedSubgroup G.val, Nonempty ((groupBaseChange k (AlgebraicClosure k)).obj S.group ≅
      T.group) := by
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  let F := groupBaseChange k K
  have hHs : Smooth H.val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  have hgc : GeometricallyConnected G.val.X.hom := geometricallyConnected_of_connected G
  have hHc : ConnectedSpace H.val.X.left :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace K (fieldSpecMap k K)
  obtain ⟨Q, q, hQ, hk⟩ := central_torus_unipotent_quotient centralizer H hHs hHc T ht hz
  obtain ⟨r, ⟨t⟩⟩ := isSplitTorus_of_isAlgClosed T ht.1
  let M := StandardLattice.{u} r
  let B := groupAlgebra K M
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := K) r
  let TB : specGroup B ≅ T.group := i ≪≫ t.symm
  obtain ⟨A, _, ⟨g⟩⟩ := groupPresentation G
  obtain ⟨a, -⟩ := hopfSpectrumBaseChange k K A
  let AK := extendedHopf K A
  let GA : specGroup AK ≅ H.val := a ≪≫ F.mapIso g
  let j : specGroup B ⟶ specGroup AK := TB.hom ≫ T.inclusion ≫ GA.inv
  let b : AK ⟶ B := (hopfSpec.fullyFaithful.preimage j).unop
  have hbj : specGroupMap b = j := hopfSpec.fullyFaithful.map_preimage j
  let underlying := Grp.forget (SchemeOver K) ⋙ Over.forget (Spec (CommRingCat.of K))
  have hb : Function.Surjective b.hom := by
    apply (hopfMapClosedImmersion K b).mp
    change IsClosedImmersion (underlying.map (specGroupMap b))
    rw [hbj, show j = TB.hom ≫ T.inclusion ≫ GA.inv from rfl, underlying.map_comp, underlying.map_comp]
    have : IsClosedImmersion (underlying.map T.inclusion) := T.isClosedImmersion
    infer_instance
  let J := {n : ℕ // n ≠ 0}
  let I : Ideal A := ⨅ n : J, torsionIdeal A n.val
  have hker : RingHom.ker b.hom.toAlgHom = extendedIdeal K I := by
    change _ = extendedIdeal K (⨅ n : J, torsionIdeal A n.val)
    rw [extendedIdeal_iInf K A (fun n : J ↦ torsionIdeal A n.val)]
    ext x
    rw [Ideal.mem_iInf]
    have hE (n : J) : extendedIdeal K (torsionIdeal A n.val) =
        (torsionIdeal B n.val).comap b.hom.toAlgHom := by
      rw [← torsionIdeal_baseChange]
      exact torsionIdeal_eq_comap AK B b hb n.val
        (factors_algebra_of_torsion_point H.val T Q q hQ hk AK B GA TB b hbj n.val n.property)
    simp only [hE]
    change b.hom x = 0 ↔ (∀ n : J, b.hom x ∈ torsionIdeal B n.val)
    exact ⟨fun h n ↦ h ▸ Ideal.zero_mem _, fun he ↦
      torsionIdeals_split_inf r (b.hom x) (fun n hn ↦ he ⟨n, hn⟩)⟩
  obtain ⟨S, ⟨e⟩⟩ := subgroup_from_extendedIdeal K G A g B b hb I hker
  exact ⟨S, ⟨e ≪≫ TB⟩⟩

private theorem algebraAction_semisimple_of_basis
    {V W J : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [Fintype J] (d : Module.Basis J k V) (X : Module.End k V) (v : J → k)
    (h : ∀ j, X (d j) = v j • d j) (e : Module.End k V ≃ₐ[k] Module.End k W) :
    (e X).IsSemisimple := by
  classical
  let s := Finset.univ.image v
  let f : Polynomial k := ∏ a ∈ s, (Polynomial.X - Polynomial.C a)
  have hp : Squarefree f := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a _ b _ hab
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit).isRelPrime
    · intro a _
      exact (Polynomial.irreducible_X_sub_C a).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  rw [Polynomial.aeval_algHom_apply e]
  suffices ha : Polynomial.aeval X f = 0 by rw [ha, map_zero]
  apply d.ext
  intro j
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (h j), LinearMap.zero_apply]
  have hv : v j ∈ s := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  change (Polynomial.eval (v j) f) • d j = 0
  rw [show Polynomial.eval (v j) f = 0 by
    rw [show Polynomial.eval (v j) f = ∏ a ∈ s, (v j - a) by
      change Polynomial.evalRingHom (v j) (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) = _
      rw [map_prod]
      simp,
      Finset.prod_eq_zero hv (sub_self (v j))], zero_smul]

open RationalRepresentations

private def coactionOperator (A : HopfAlgebraCategory k) {V : Type u}
    [AddCommGroup V] [Module k V] (ρ : RightComodule k A V)
    (R : Type u) [CommRing R] [Algebra k R] (q : A →ₗ[k] R) :
    Module.End R (R ⊗[k] V) :=
  ((TensorProduct.comm k V R).toLinearMap.comp
    ((q.lTensor V).comp ρ.coaction)).liftBaseChange R

private theorem coactionOperator_apply_tmul (A : HopfAlgebraCategory k) {V : Type u}
    [AddCommGroup V] [Module k V] (ρ : RightComodule k A V)
    {R : Type u} [CommRing R] [Algebra k R] (q : A →ₗ[k] R)
    {x : V} {a : A} (hx : ρ.coaction x = x ⊗ₜ[k] a) :
    coactionOperator A ρ R q (1 ⊗ₜ[k] x) = q a ⊗ₜ[k] x := by
  simp [coactionOperator, LinearMap.liftBaseChange_tmul, hx]

private theorem coactionOperator_toMatrix (A : HopfAlgebraCategory k) {V I : Type u}
    [AddCommGroup V] [Module k V] [Fintype I] [DecidableEq I]
    (d : Module.Basis I k V) (ρ : RightComodule k A V)
    {R : Type u} [CommRing R] [Algebra k R] (q : A →ₗ[k] R) :
    LinearMap.toMatrix (d.baseChange R) (d.baseChange R) (coactionOperator A ρ R q) =
      (coefficients A d ρ).map q := by
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  change (d.baseChange R).repr (((TensorProduct.comm k V R).toLinearMap.comp
    ((q.lTensor V).comp ρ.coaction)).liftBaseChange R (1 ⊗ₜ[k] d j)) i = q (coefficients A d ρ i j)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  simp only [LinearMap.comp_apply, coaction_apply_basis A d ρ, map_sum,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    Finsupp.finsetSum_apply, Module.Basis.baseChange_repr_tmul, d.repr_self,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

private theorem coactionOperator_diagonal (r : ℕ) {V I : Type u} [AddCommGroup V] [Module k V]
    [Fintype I] [DecidableEq I] (d : Module.Basis I k V)
    (ρ : RightComodule k (groupAlgebra k (StandardLattice r)) V)
    (w : I → StandardLattice.{u} r) (hw : ∀ j, d j ∈ WeightDecomposition.weightSpace ρ (w j))
    {R : Type u} [CommRing R] [Algebra k R]
    (q : MonoidAlgebra k (StandardLattice.{u} r) →ₗ[k] R) :
    LinearMap.toMatrix (d.baseChange R) (d.baseChange R) (coactionOperator _ ρ R q) =
      Matrix.diagonal (fun j ↦ q (MonoidAlgebra.of k (StandardLattice r) (w j))) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    coactionOperator_apply_tmul _ _ _ (WeightDecomposition.mem_weightSpace.mp (hw j)),
    Module.Basis.baseChange_repr_tmul, d.repr_self]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij]

private def torusDualCoordinates (r : ℕ) (i : Fin r) :
    MonoidAlgebra k (StandardLattice.{u} r) →ₐ[k] DualNumber k :=
  MonoidAlgebra.lift k _ _ {
    toFun m := (1, (latticeCoordinate i m : k))
    map_one' := by
      apply TrivSqZeroExt.ext
      · rfl
      · change ((0 : ℤ) : k) = 0
        simp
    map_mul' := fun m n => by
      apply TrivSqZeroExt.ext
      · change (1 : k) = 1 * 1
        simp
      · change ((latticeCoordinate i m + latticeCoordinate i n : ℤ) : k) =
          1 * (latticeCoordinate i n : k) + (latticeCoordinate i m : k) * 1
        simp [add_comm] }

private theorem torusDualCoordinates_monomial (r : ℕ) (i : Fin r) (m : StandardLattice.{u} r) :
    torusDualCoordinates (k := k) r i (MonoidAlgebra.of k _ m) =
      (1, (latticeCoordinate i m : k)) := by
  change MonoidAlgebra.lift k _ _ _ (MonoidAlgebra.single m 1) = _
  rw [MonoidAlgebra.lift_single, one_smul]
  rfl

private def torusDualPoint (r : ℕ) (i : Fin r) :
    Lie k (specGroup (groupAlgebra k (StandardLattice.{u} r))) := by
  let B := groupAlgebra k (StandardLattice.{u} r)
  let g := torusDualCoordinates (k := k) r i
  refine mapDualKernel (hopfSpecPointIso B).hom ((hopfKernelLifts B).symm ⟨g, ?_⟩)
  change (TrivSqZeroExt.fstHom k k k).comp g = counitAlgHom k B
  apply MonoidAlgebra.algHom_ext
  · intro m
    change (g (MonoidAlgebra.of k _ m)).fst = _
    rw [torusDualCoordinates_monomial]
    exact (MonoidAlgebra.isGroupLikeElem_of (R := k) (A := k) m).counit_eq_one.symm
  · ext

open private representationPointsEquiv pointMatrix pointMatrix_evaluation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private semisimple_is_geometric from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SemisimpleLieCentralizer

private theorem representation_point_matrix (A : HopfAlgebraCategory k)
    {I V : Type u} [Fintype I] [DecidableEq I] [AddCommGroup V] [Module k V]
    (b : Module.Basis I k V) (G : AffineGroupCategory k) (L : GroupScheme k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k I)
    (f : G.val ⟶ L) (ρ : RightComodule k A V) (h : coefficients A b ρ = universalMatrix A G L e l f)
    (R : TestAlgebra k) (g : A →ₐ[k] R) :
    (l.hom.app R (((groupPointsFunctor k).map f).app R (e.hom.app R (toConv g)))).val =
      (coefficients A b ρ).map g := by
  rw [h]
  exact pointMatrix_evaluation A (representationPointsEquiv A G L e l f) R (toConv g)

private theorem commutes_with_weight_diagonal [CharZero k] {I : Type u}
    [Fintype I] [DecidableEq I] {r : ℕ}
    (w : I → StandardLattice.{u} r) (R : Type u) [CommRing R] [Algebra k R]
    (P : Matrix I I R)
    (hP : ∀ i : Fin r, Commute P (Matrix.diagonal fun j ↦
      algebraMap k R (latticeCoordinate i (w j) : k)))
    (a : StandardLattice.{u} r → R) :
    Commute P (Matrix.diagonal (a ∘ w)) := by
  apply Matrix.ext
  intro s t
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : w s = w t
  · rw [Function.comp_apply, Function.comp_apply, h, mul_comm]
  have hcoord : ∃ i, latticeCoordinate i (w s) ≠ latticeCoordinate i (w t) := by
    by_contra! he
    apply h
    funext i
    exact ULift.ext (he i)
  obtain ⟨i, hi⟩ := hcoord
  have hne : (latticeCoordinate i (w t) : k) - (latticeCoordinate i (w s) : k) ≠ 0 :=
    sub_ne_zero.mpr (fun he ↦ hi (Int.cast_injective he.symm))
  have he := congrArg (fun M : Matrix I I R ↦ M s t) (hP i).eq
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm _ (P s t), ← sub_eq_zero,
    ← mul_sub, ← map_sub] at he
  have hz : P s t = 0 :=
    ((IsUnit.map (algebraMap k R) hne.isUnit).mul_left_eq_zero).mp he
  rw [hz, mul_zero, zero_mul]

private theorem central_of_points {S H : GroupScheme k} [IsAffine S.X.left] [IsAffine H.X.left]
    (i : S ⟶ H)
    (h : ∀ (R : TestAlgebra k) (s : Specs.AdjointRepresentation.GroupPoints S R)
      (g : Specs.AdjointRepresentation.GroupPoints H R),
      Commute g (((groupPointsFunctor k).map i).app R s)) :
    IsCentral i := by
  let P := S.X ⊗ H.X
  have : IsAffine P.left := affine_tensor
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (show IsAffine P.left from inferInstance)
  have hs : Commute (snd S.X H.X) (fst S.X H.X ≫ i.hom.hom) := by
    apply (cancel_epi e.hom).mp
    simp only [MonObj.comp_mul]
    exact (h A.unop (e.hom ≫ fst S.X H.X) (e.hom ≫ snd S.X H.X)).eq
  intro Y g
  apply (centralizes_iff i g).mpr
  intro Z z t
  exact show Commute (z ≫ g) (t ≫ i.hom.hom) by
    have he := congrArg (lift t (z ≫ g) ≫ ·) hs.eq
    change (z ≫ g) * (t ≫ i.hom.hom) = (t ≫ i.hom.hom) * (z ≫ g)
    simpa only [MonObj.comp_mul, lift_fst_assoc, lift_snd] using he

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem commutes_of_no_noncentral_semisimple (G : AffineAlgebraicGroup k)
    (hG : Smooth (GeometricGroup G).val.X.hom)
    (hc : ConnectedSpace (GeometricGroup G).val.X.left)
    (hn : ¬ HasGeometricNoncentralSemisimple G)
    (L : AffineGroupCategory (AlgebraicClosure k))
    (s : Specs.IdentityLieStructure (GeometricGroup G).val)
    {I : Type u} [Fintype I] [DecidableEq I]
    (l : (groupPointsFunctor (AlgebraicClosure k)).obj L.val ≅
      Specs.StandardGroups.generalLinearPoints (AlgebraicClosure k) I)
    (f : (GeometricGroup G).val ⟶ L.val) (hf : IsClosedImmersion f.hom.hom.left)
    (y : Lie (AlgebraicClosure k) (GeometricGroup G).val)
    (hy : Module.End.IsSemisimple (Matrix.toLinAlgEquiv'
      (InfinitesimalCommutator.matrixDifferential f l y)))
    (R : TestAlgebra (AlgebraicClosure k))
    (g : Specs.AdjointRepresentation.GroupPoints (GeometricGroup G).val R) :
    Commute (l.hom.app R (((groupPointsFunctor (AlgebraicClosure k)).map f).app R g)).val
      ((InfinitesimalCommutator.matrixDifferential f l y).map (algebraMap (AlgebraicClosure k) R)) := by
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  let : LieRing (Lie K H.val) := s.lieRing
  let : LieAlgebra K (Lie K H.val) := s.lieAlgebra
  let : LieRing (Module.End K (Lie K H.val)) := LieRing.ofAssociativeRing
  have ha : (LieAlgebra.ad K (Lie K H.val)).toLinearMap y = 0 := by
    by_contra he
    exact hn ⟨s, I, inferInstance, inferInstance, L, l, f, hf, y, hy, he⟩
  obtain ⟨C, _, hC, _, hi⟩ := SemisimpleLieCentralizer.schemeCentralizerOfSemisimple
    K H L s hG I l f hf y (semisimple_is_geometric _ hy)
  have := hi hc.toPreconnectedSpace ha
  let a := ((groupPointsFunctor K).map C.inclusion).app R
  have : IsIso a := inferInstance
  exact (hC R g).mp ⟨(inv a).hom g, by
    change a.hom ((inv a).hom g) = g
    rw [← GrpCat.comp_apply, IsIso.inv_hom_id, GrpCat.id_apply]⟩

set_option maxHeartbeats 3500000 in
private theorem central_in_charZero [CharZero k]
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left) (T : ClosedSubgroup (GeometricGroup G).val)
    (ht : IsMaximalTorus T) (hn : ¬ HasGeometricNoncentralSemisimple G) :
    IsCentral T.inclusion := by
  classical
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  have hH : Smooth (GeometricGroup G).val.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  have hgc : GeometricallyConnected G.val.X.hom := geometricallyConnected_of_connected G
  have hcH : ConnectedSpace (GeometricGroup G).val.X.left :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace K (fieldSpecMap k K)
  let s := identityLieStructure H
  let := s.lieRing
  let := s.lieAlgebra
  obtain ⟨n, L, ⟨l⟩, f, hf⟩ := faithfulLinearization K H
  let I := ULift.{u} (Fin n)
  let V := I → K
  let b : Module.Basis I K V := Pi.basisFun K I
  obtain ⟨r, ⟨t⟩⟩ := isSplitTorus_of_isAlgClosed T ht.1
  let M := StandardLattice.{u} r
  let B := groupAlgebra K M
  obtain ⟨j⟩ := CharacterDescent.standardSplitTorus (k := K) r
  let e : specGroup B ≅ T.group := j ≪≫ t.symm
  let S : AffineGroupCategory K := ⟨specGroup B, inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))⟩
  let i := e.hom ≫ T.inclusion
  let f₀ : S.val ⟶ L.val := i ≫ f
  let p := hopfSpecPointIso B
  obtain ⟨F, hF⟩ := representationCoactionComparison B b S L.val p l
  let ρ := F f₀
  obtain ⟨J, hJ, d, w, hw⟩ := DiagonalizableFixedLocus.existsWeightBasis ρ
  let : Fintype J := Fintype.ofFinite J
  have hMatrix (R : TestAlgebra K) (g : B →ₐ[K] R) :
      (l.hom.app R (((groupPointsFunctor K).map f₀).app R (p.hom.app R (toConv g)))).val =
        (coefficients B b ρ).map g := representation_point_matrix B b S L.val p l f₀ ρ (hF f₀) R g
  let y (a : Fin r) : Lie K H.val := mapPointKernel i (torusDualPoint r a)
  let q (a : Fin r) : B →ₗ[K] K :=
    (TrivSqZeroExt.sndHom K K).comp (torusDualCoordinates (k := K) r a).toLinearMap
  let Y (a : Fin r) := InfinitesimalCommutator.matrixDifferential f l (y a)
  have hY (a : Fin r) : Y a = (coefficients B b ρ).map (q a) := by
    rw [show Y a = InfinitesimalCommutator.matrixDifferential f l (mapPointKernel i (torusDualPoint r a)) from rfl,
      ← matrixDifferential_comp]
    ext x z
    change ((l.hom.app (CommAlgCat.of K (DualNumber K))
      (((groupPointsFunctor K).map f₀).app _ (p.hom.app _ (toConv (torusDualCoordinates r a))))).val x z).snd =
        q a (coefficients B b ρ x z)
    rw [hMatrix]
    rfl
  have h0 (a : Fin r) : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (Y a)) := by
    let X := coactionOperator B ρ K (q a)
    let b' := b.baseChange K
    let d' := d.baseChange K
    have hX (j : J) : X (d' j) = (latticeCoordinate a (w j) : K) • d' j := by
      rw [show d' j = (1 : K) ⊗ₜ[K] d j from Module.Basis.baseChange_apply K d j]
      rw [coactionOperator_apply_tmul B ρ _ (WeightDecomposition.mem_weightSpace.mp (hw j))]
      change (torusDualCoordinates r a (MonoidAlgebra.of K M (w j))).snd ⊗ₜ[K] d j = _
      rw [torusDualCoordinates_monomial, TensorProduct.smul_tmul']
      simp
    have hss := algebraAction_semisimple_of_basis d' X
      (fun j ↦ (latticeCoordinate a (w j) : K)) hX
      ((LinearMap.toMatrixAlgEquiv b').trans Matrix.toLinAlgEquiv')
    change Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (LinearMap.toMatrix b' b' X)) at hss
    rwa [coactionOperator_toMatrix B b ρ, ← hY] at hss
  have hCentral (a : Fin r) (R : TestAlgebra K)
      (g : Specs.AdjointRepresentation.GroupPoints H.val R) :
      Commute (l.hom.app R (((groupPointsFunctor K).map f).app R g)).val
        ((Y a).map (algebraMap K R)) :=
    commutes_of_no_noncentral_semisimple G hH hcH hn
      ⟨L.val, L.property.1⟩ s l f hf (y a) (h0 a) R g
  have hA : IsAffine T.group.X.left := (closedSubgroupAlgebraicGroup T).property.1
  have hAff : IsAffine (GeometricGroup G).val.X.left := (GeometricGroup G).property.1
  apply central_of_points T.inclusion
  intro R t g
  let U := (LinearMap.toMatrixAlgEquiv (b.baseChange R))
  let D := (LinearMap.toMatrixAlgEquiv (d.baseChange R))
  let N := (l.hom.app R (((groupPointsFunctor K).map f).app R g)).val
  let P := D (U.symm N)
  let v : B →ₐ[K] R := ((p.inv.app R).hom
    (((groupPointsFunctor K).map e.inv).app R t)).ofConv
  have hv : ((groupPointsFunctor K).map e.hom).app R (p.hom.app R (toConv v)) = t := by
    change (((groupPointsFunctor K).mapIso e).hom.app R).hom
      ((p.hom.app R).hom ((p.inv.app R).hom
        ((((groupPointsFunctor K).mapIso e).inv.app R).hom t))) = t
    simp
    let eR := Iso.app ((groupPointsFunctor K).mapIso e) R
    change eR.hom.hom (eR.inv.hom t) = t
    rw [← GrpCat.comp_apply, eR.inv_hom_id, GrpCat.id_apply]
  have hP (a : Fin r) : Commute P (Matrix.diagonal fun j ↦
      algebraMap K R (latticeCoordinate a (w j) : K)) := by
    let qR := (Algebra.linearMap K R).comp (q a)
    let X := coactionOperator B ρ R qR
    have hX1 : U X = (Y a).map (algebraMap K R) := by
      change LinearMap.toMatrix (b.baseChange R) (b.baseChange R) X = _
      rw [coactionOperator_toMatrix B b ρ, hY]
      rfl
    have hX2 : D X = Matrix.diagonal (fun j ↦ algebraMap K R (latticeCoordinate a (w j) : K)) := by
      change LinearMap.toMatrix (d.baseChange R) (d.baseChange R) X = _
      rw [coactionOperator_diagonal r d ρ w hw]
      congr 1
      funext j
      change algebraMap K R (torusDualCoordinates r a (MonoidAlgebra.of K M (w j))).snd = _
      rw [torusDualCoordinates_monomial]
      rfl
    rw [← hX2]
    have hNX : Commute (U.symm N) X := by
      apply U.injective
      rw [map_mul, map_mul, U.apply_symm_apply, hX1]
      exact (hCentral a R g).eq
    exact hNX.map D
  have hcomm := commutes_with_weight_diagonal w R P hP
    (fun m ↦ v (MonoidAlgebra.of K M m))
  let X := coactionOperator B ρ R v.toLinearMap
  have hDU : D X = Matrix.diagonal ((fun m ↦ v (MonoidAlgebra.of K M m)) ∘ w) := by
    exact coactionOperator_diagonal r d ρ w hw _
  have hU : U X = (l.hom.app R (((groupPointsFunctor K).map f).app R
      (((groupPointsFunctor K).map T.inclusion).app R t))).val := by
    change LinearMap.toMatrix (b.baseChange R) (b.baseChange R) X = _
    rw [coactionOperator_toMatrix B b ρ]
    have hm := (hMatrix R v).symm
    calc
      _ = _ := hm
      _ = _ := by
        unfold f₀ i
        simp only [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
        rw [hv]
  rw [← hDU] at hcomm
  have hC : Commute (U.symm N) X := by
    apply D.injective
    rw [map_mul, map_mul]
    exact hcomm.eq
  have hCL := hC.map U
  rw [U.apply_symm_apply, hU] at hCL
  have hfi : Function.Injective (((groupPointsFunctor K).map f).app R).hom := by
    have : Mono f.hom.hom := Over.mono_of_mono_left f.hom.hom
    intro x y he
    apply (cancel_mono f.hom.hom).mp
    exact he
  apply hfi
  simp only [map_mul]
  apply (ConcreteCategory.bijective_of_isIso (l.hom.app R)).injective
  simp only [map_mul]
  exact Units.ext hCL.eq

private theorem rational_torus_of_terminal_cases
    (reduce : CentralFrobeniusReduction.{u})
    (torusFree : Specs.TorusFreeUnipotent.Unipotence.{u})
    {k : Type u} [Field k] [Infinite k]
    (hCentral : ∀ (G : AffineAlgebraicGroup k),
      Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
      ∀ T : ClosedSubgroup (GeometricGroup G).val,
        IsMaximalTorus T → IsCentral T.inclusion → ¬ IsTrivialSubgroup T →
        ∃ S : ClosedSubgroup G.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S)
    (hCharZero : CharZero k → ∀ (G : AffineAlgebraicGroup k),
      Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
      ∀ T : ClosedSubgroup (GeometricGroup G).val,
        IsMaximalTorus T → ¬ HasGeometricNoncentralSemisimple G → IsCentral T.inclusion)
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom)
    (hconn : ConnectedSpace G.val.X.left)
    (hT : ∃ T : ClosedSubgroup (GeometricGroup G).val, IsTorus T.group ∧ ¬ IsTrivialSubgroup T) :
    ∃ S : ClosedSubgroup G.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S := by
  classical
  generalize hd : groupDimension G = d
  induction d using Nat.strong_induction_on generalizing G with
  | h d ih =>
    have hProper (A : AffineAlgebraicGroup k) (ha : groupDimension A ≤ d)
        (hs : Smooth A.val.X.hom) (hc : ConnectedSpace A.val.X.left)
        (hn : HasGeometricNoncentralSemisimple A) :
        ∃ S : ClosedSubgroup A.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S := by
      obtain ⟨H, hH, hHc, hdim, hgeom⟩ := smooth_connected_centralizer torusFree A hs hc hn
      obtain ⟨S, hS, hSn⟩ := ih (groupDimension (closedSubgroupAlgebraicGroup H))
        (hdim.trans_le ha) (closedSubgroupAlgebraicGroup H) hH hHc hgeom rfl
      have := H.isClosedImmersion
      have := S.isClosedImmersion
      exact ⟨⟨S.group, S.inclusion ≫ H.inclusion, IsClosedImmersion.comp _ _⟩, hS, hSn⟩
    by_cases hn : HasGeometricNoncentralSemisimple G
    · exact hProper G hd.le hG hconn hn
    obtain ⟨S, hs, hsn⟩ := hT
    obtain ⟨T, ht, htn⟩ := nontrivial_maximal_torus (GeometricGroup G) S hs hsn
    by_cases hc : IsCentral T.inclusion
    · exact hCentral G hG hconn T ht hc htn
    rcases CharP.exists' k with h0 | ⟨p, hp, hk⟩
    · exact (hc (hCharZero h0 G hG hconn T ht hn)).elim
    let := Fact.mk hp
    let := hk
    obtain ⟨χ, hχ, hw⟩ := (reduce k p G hG hconn T ht hc hn).1
    obtain ⟨n, hpow⟩ := character_not_all_prime_powers
      (isSplitTorus_of_isAlgClosed T ht.1) p hp.out χ hχ
    refine solve_using_weight p reduce (fun A ↦ groupDimension A ≤ d) ?_ ?_
      n G hd.le hG hconn T ht χ hχ hw hpow
    · intro A ha hs hc T' ht' hterminal hχ'
      rcases hterminal with hn' | hc'
      · exact hProper A ha hs hc hn'
      · obtain ⟨χ', hχ'⟩ := hχ'
        exact hCentral A hs hc T' ht' hc' (nontrivial_of_character T' hχ')
    · intro A B q hf hs ha
      exact (groupDimension_le_of_finite_surjective q hf hs).trans ha

private theorem central_torus_rational
    (centralizer : Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u})
    (G : AffineAlgebraicGroup k) (hG : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left) (T : ClosedSubgroup (GeometricGroup G).val)
    (ht : IsMaximalTorus T) (hz : IsCentral T.inclusion) (hn : ¬ IsTrivialSubgroup T) :
    ∃ S : ClosedSubgroup G.val, IsTorus S.group ∧ ¬ IsTrivialSubgroup S := by
  rcases CharP.exists' k with h₀ | ⟨p, hp, hP⟩
  · let := h₀
    obtain ⟨S, ⟨e⟩⟩ := central_torus_charZero_baseChange centralizer G hG hc T ht hz
    exact torus_of_subgroup_baseChange T ht.1 hn S e
  · let := hp
    let := hP
    obtain ⟨S, ⟨e⟩⟩ := central_torus_as_geometric_baseChange p centralizer G hG hc T ht hz
    exact torus_of_subgroup_baseChange T ht.1 hn S e

/-- The rational torus follows from central Frobenius reduction, the
maximal-torus centralizer theorem and the unipotence criterion. -/
theorem existsNontrivialTorus_conditional :
    Specs.CentralFrobeniusDescent.CentralFrobeniusReduction.{u} →
    Specs.TorusFreeUnipotent.MaximalTorusCentralizer.{u} →
    Specs.TorusFreeUnipotent.Unipotence.{u} →
    Specs.NontrivialRationalTorus.ExistsNontrivialTorus.{u} := by
  intro reduce centralizer torusFree k _ _ G hG hconn hT
  refine rational_torus_of_terminal_cases reduce torusFree
    (central_torus_rational centralizer) ?_ G hG hconn hT
  intro h₀ H hs hc T ht hn
  let := h₀
  exact central_in_charZero H hs hc T ht hn


end

end LinearAlgebraicGroups.NontrivialRationalTorus

universe v8_closure_3b2431911ff0ffaf_u0
theorem _root_.«LinearAlgebraicGroups».«NontrivialRationalTorus».«existsNontrivialTorus» : _root_.«LinearAlgebraicGroups».«Specs».«NontrivialRationalTorus».«ExistsNontrivialTorus».{v8_closure_3b2431911ff0ffaf_u0} :=
  @_root_.«LinearAlgebraicGroups».«NontrivialRationalTorus».«existsNontrivialTorus_conditional».{v8_closure_3b2431911ff0ffaf_u0} (@_root_.«LinearAlgebraicGroups».«CentralFrobeniusDescent».«centralFrobeniusReduction».{v8_closure_3b2431911ff0ffaf_u0}) (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«maximalTorusCentralizer».{v8_closure_3b2431911ff0ffaf_u0}) (@_root_.«LinearAlgebraicGroups».«TorusFreeUnipotent».«torusFreeUnipotent».{v8_closure_3b2431911ff0ffaf_u0})
