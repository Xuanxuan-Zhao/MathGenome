import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.PinnedDatumFromMarkedRootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped BigOperators CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Classification.PinnedDatumFromMarkedRootGroups

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.PinnedDatumFromMarkedRootGroups
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Datum Root)
open Specs.BorelNormalizer (InducesTorusConjugation)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter StandardLattice)
open Specs.CharacterPairing (characterValue pairing)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.Pinning (AttachedDatum BasedIso BasedRootDatum IsSimple SplitBorelPair)
open Specs.RootGroups (AdditiveLine rankOneWord)
open CocharacterDynamics (cocharacterPoint existsLimitDecomposition unitPoint)
open Specs.DiagonalizableGroups (IntegerCharacters)

open private splitPresentation charactersOfIso algebraPoint characterValue_monomial
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_point_from_coordinates rankOneRepresentative rankOneRepresentative_point
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private unitEquiv unitEquiv_unitPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private inducedConjugation_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private coroot_functional_of_reflection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning

noncomputable section

set_option backward.isDefEq.respectTransparency false

section DatumComparison

private def positiveCorootSum (D : BasedRootDatum.{u}) : D.Y := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  exact ∑ i ∈ Finset.univ.filter D.base.flip.IsPos, D.datum.coroot i

private theorem positiveCorootSum_pairing_simple (D : BasedRootDatum.{u}) (j : D.I)
    (hj : j ∈ D.base.support) : D.datum.root' j (positiveCorootSum D) = 2 := by
  classical
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let := D.freeY
  let := D.freeX
  let := D.reduced
  let P := D.datum.flip
  let b := D.base.flip
  let s := Finset.univ.filter b.IsPos
  let σ := P.reflectionPerm j
  have hj' : j ∈ b.support := hj
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isPos_of_mem_support hj'⟩
  have hmap : ∀ i ∈ s.erase j, σ i ∈ s.erase j := by
    intro i hi
    obtain ⟨hne, his⟩ := Finset.mem_erase.mp hi
    have hpos := (Finset.mem_filter.mp his).2
    have hne' : σ i ≠ j := by
      intro h
      have hi' : i = σ j := (P.reflectionPerm_self j i).symm.trans (congrArg σ h)
      let := P.indexNeg
      have hpos' : b.IsPos (-j) := by
        change b.IsPos (σ j)
        exact hi' ▸ hpos
      exact (RootPairing.Base.IsPos.neg_iff_not b j).mp hpos' (b.isPos_of_mem_support hj')
    exact Finset.mem_erase.mpr ⟨hne', Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hpos.reflectionPerm hj' hne⟩⟩
  have hsum : (∑ i ∈ s.erase j, P.root (σ i)) = ∑ i ∈ s.erase j, P.root i := by
    refine Finset.sum_bij (fun i _ => σ i) hmap (fun _ _ _ _ h => σ.injective h) ?_ (by simp)
    intro i hi
    exact ⟨σ i, hmap i hi, P.reflectionPerm_self j i⟩
  let v := ∑ i ∈ s.erase j, P.root i
  have hfix : P.reflection j v = v := by
    dsimp only [v]
    rw [map_sum]
    simpa only [σ, P.root_reflectionPerm] using hsum
  rw [P.reflection_apply] at hfix
  have hz : P.coroot' j v = 0 := (smul_eq_zero.mp (sub_eq_self.mp hfix)).resolve_right (P.ne_zero j)
  change P.coroot' j (∑ i ∈ s, P.root i) = _
  rw [← Finset.sum_erase_add s P.root hjs, map_add]
  change P.coroot' j v + P.coroot' j (P.root j) = _
  simp [hz]

private theorem positiveCorootSum_pairing_pos (D : BasedRootDatum.{u}) (i : D.I)
    (hi : D.base.IsPos i) : D.datum.root' i (positiveCorootSum D) = 2 * D.base.height i := by
  let := D.finiteRoots
  let p (l : D.I) := D.datum.root' l (positiveCorootSum D) = 2 * D.base.height l
  have hbase (j : D.I) (hj : j ∈ D.base.support) : p j := by
    dsimp only [p]
    rw [positiveCorootSum_pairing_simple D j hj, D.base.height_one_of_mem_support hj, mul_one]
  have hstep (j k l : D.I) (h : D.datum.root l = D.datum.root j + D.datum.root k)
      (ih : p j) (hk : k ∈ D.base.support) : p l := by
    change D.datum.toLinearMap (D.datum.root l) (positiveCorootSum D) = 2 * D.base.height l
    rw [D.base.height_add h, h, map_add, LinearMap.add_apply]
    change D.datum.root' j (positiveCorootSum D) + D.datum.root' k (positiveCorootSum D) = _
    rw [ih, positiveCorootSum_pairing_simple D k hk, D.base.height_one_of_mem_support hk]
    omega
  exact hi.induction_on_add hbase hstep

private theorem positiveCorootSum_pairing (D : BasedRootDatum.{u}) (i : D.I) :
    D.datum.root' i (positiveCorootSum D) = 2 * D.base.height i := by
  let := D.datum.indexNeg
  obtain h | h := RootPairing.Base.IsPos.or_neg D.base i
  · exact positiveCorootSum_pairing_pos D i h
  · have h' := positiveCorootSum_pairing_pos D (-i) h
    rw [D.base.height_reflectionPerm_self] at h'
    change D.datum.toLinearMap (D.datum.root (D.datum.reflectionPerm i i))
      (positiveCorootSum D) = _ at h'
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self, map_neg, LinearMap.neg_apply] at h'
    change -(D.datum.root' i (positiveCorootSum D)) = _ at h'
    omega

/-- The sum of the positive coroots, transported by perfect duality, gives
a regular cocharacter with the prescribed positive system. -/
private theorem regularCocharacter_with_positives {k : Type u} [Field k] (D : BasedRootDatum.{u})
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val) [IsCommMonObj T.group.X] (E : Datum T)
    (idx : D.I ≃ Root T) (L : D.X ≃ₗ[ℤ] Additive (Character T.group))
    (hroot : ∀ a, Additive.ofMul (idx a).val = L (D.datum.root a)) :
    ∃ c : Cocharacter T.group, IsRegular T c ∧
      ∀ a, idx a ∈ positiveRoots T c ↔ D.base.IsPos a := by
  let p := L.symm.dualMap (D.datum.flip.toPerfPair (positiveCorootSum D))
  let y := E.rootDatum.flip.toPerfPair.symm p
  let c := Additive.toMul y
  have hy (x : D.X) : E.rootDatum.toLinearMap (L x) y =
      D.datum.toLinearMap x (positiveCorootSum D) := by
    have h := DFunLike.congr_fun (E.rootDatum.flip.toPerfPair.apply_symm_apply p) (L x)
    change E.rootDatum.toLinearMap (L x) y =
      D.datum.toLinearMap (L.symm (L x)) (positiveCorootSum D) at h
    rw [L.symm_apply_apply] at h
    exact h
  have hp (a : D.I) : pairing T.group (idx a).val c = 2 * D.base.height a := by
    rw [← E.pairing_eq, hroot]
    change E.rootDatum.toLinearMap (L (D.datum.root a)) y = _
    rw [hy]
    exact positiveCorootSum_pairing D a
  refine ⟨c, ?_, ?_⟩
  · intro i
    obtain ⟨a, rfl⟩ := idx.surjective i
    rw [hp]
    exact mul_ne_zero (by decide) (D.base.height_ne_zero a)
  · intro a
    change 0 < pairing T.group (idx a).val c ↔ 0 < D.base.height a
    rw [hp]
    omega

private theorem simple_iff_positive_indecomposable (D : BasedRootDatum.{u}) (a : D.I) :
    a ∈ D.base.support ↔
      D.base.IsPos a ∧
        ∀ b, D.base.IsPos b → ∀ c, D.base.IsPos c →
          D.datum.root a ≠ D.datum.root b + D.datum.root c := by
  let := D.finiteRoots
  constructor
  · intro ha
    refine ⟨D.base.isPos_of_mem_support ha, ?_⟩
    intro b hb c hc h
    have hh := D.base.height_add h
    rw [D.base.height_one_of_mem_support ha] at hh
    change 0 < D.base.height b at hb
    change 0 < D.base.height c at hc
    omega
  · rintro ⟨ha, hw⟩
    have h (i : D.I) (hi : D.base.IsPos i) :
        D.base.IsPos i ∧
          ((∀ b, D.base.IsPos b → ∀ c, D.base.IsPos c →
            D.datum.root i ≠ D.datum.root b + D.datum.root c) →
          i ∈ D.base.support) := by
      let p (l : D.I) : Prop := D.base.IsPos l ∧
        ((∀ b, D.base.IsPos b → ∀ c, D.base.IsPos c →
          D.datum.root l ≠ D.datum.root b + D.datum.root c) → l ∈ D.base.support)
      have hb (j : D.I) (hs : j ∈ D.base.support) : p j :=
        ⟨D.base.isPos_of_mem_support hs, fun _ => hs⟩
      have hStep (j k l : D.I) (hsum : D.datum.root l = D.datum.root j + D.datum.root k)
          (ih : p j) (hk : k ∈ D.base.support) : p l := by
        have hkp := D.base.isPos_of_mem_support hk
        exact ⟨ih.1.add hkp hsum, fun hc => (hc j ih.1 k hkp hsum).elim⟩
      exact hi.induction_on_add hb hStep
    exact (h a ha).2 hw

private theorem corresponding_simple {k : Type u} [Field k] (D : BasedRootDatum.{u})
    (P : SplitBorelPair k)
    (idx : D.I ≃ Root P.T)
    (χ : D.X ≃ₗ[ℤ] Additive (Character P.T.group))
    (hr : ∀ a, (idx a).val = Additive.toMul (χ (D.datum.root a)))
    (hp : ∀ a, idx a ∈ subgroupRoots P.T P.B ↔ D.base.IsPos a)
    (a : D.I) : IsSimple P (idx a) ↔ a ∈ D.base.support := by
  rw [simple_iff_positive_indecomposable]
  have h (b c : D.I) :
      (idx a).val = (idx b).val * (idx c).val ↔
        D.datum.root a = D.datum.root b + D.datum.root c := by
    rw [hr, hr, hr]
    change Additive.toMul (χ (D.datum.root a)) =
      Additive.toMul (χ (D.datum.root b) + χ (D.datum.root c)) ↔ _
    rw [← map_add]
    exact Additive.toMul.injective.eq_iff.trans χ.injective.eq_iff
  constructor
  · rintro ⟨ha, ha'⟩
    refine ⟨(hp a).mp ha, fun b hb c hc hsum => ?_⟩
    exact ha' _ ((hp b).mpr hb) _ ((hp c).mpr hc) ((h b c).mpr hsum)
  · rintro ⟨ha, ha'⟩
    refine ⟨(hp a).mpr ha, ?_⟩
    intro bRoot hb cRoot hc hsum
    obtain ⟨b, rfl⟩ := idx.surjective bRoot
    obtain ⟨c, rfl⟩ := idx.surjective cRoot
    exact ha' b ((hp b).mp hb) c ((hp c).mp hc) ((h b c).mp hsum)

/-- Once the marked roots and full coroot functionals are identified, perfect
duality gives the required cocharacter marking on the full lattice. -/
private def compareBasedDatum {k : Type u} [Field k] {D : BasedRootDatum.{u}}
    {P : SplitBorelPair k} (A : AttachedDatum P)
    (idx : D.I ≃ Root P.T)
    (χ : D.X ≃ₗ[ℤ] Additive (Character P.T.group))
    (hr : ∀ a, (idx a).val = Additive.toMul (χ (D.datum.root a)))
    (hc : ∀ a x, A.toBased.datum.coroot' (idx a) (χ x) = D.datum.coroot' a x)
    (hp : ∀ a, idx a ∈ subgroupRoots P.T P.B ↔ D.base.IsPos a) :
    BasedIso D A.toBased := by
  letI := A.comm
  let E := A.toBased
  let ξ := E.datum.flip.toPerfPair.trans
      (χ.dualMap.trans D.datum.flip.toPerfPair.symm)
  have hpair (x : D.X) (y : E.Y) :
      D.datum.toLinearMap x (ξ y) = E.datum.toLinearMap (χ x) y := by
    let p := χ.dualMap (E.datum.flip.toPerfPair y)
    exact DFunLike.congr_fun (D.datum.flip.toPerfPair.apply_symm_apply p) x
  have hcoroot (a : D.I) : ξ (E.datum.coroot (idx a)) = D.datum.coroot a := by
    apply D.datum.flip.toPerfPair.injective
    ext x
    exact (hpair x (E.datum.coroot (idx a))).trans (hc a x)
  let e : D.datum.Equiv E.datum :=
    { weightMap := χ.toLinearMap
      coweightMap := ξ.toLinearMap
      indexEquiv := idx
      weight_coweight_transpose := by
        ext y x
        exact (hpair x y).symm
      root_weightMap := by
        funext a
        change χ (D.datum.root a) = A.datum.rootDatum.root (idx a)
        rw [A.datum.root_eq]
        exact (congrArg Additive.ofMul (hr a)).symm
      coroot_coweightMap := by
        funext i
        obtain ⟨a, rfl⟩ := idx.surjective i
        change ξ (E.datum.coroot (idx a)) = D.datum.coroot (idx.symm (idx a))
        rw [hcoroot, Equiv.symm_apply_apply]
      bijective_weightMap := χ.bijective
      bijective_coweightMap := ξ.bijective }
  refine ⟨e, ?_⟩
  have hs (a : D.I) : idx a ∈ A.base.support ↔ a ∈ D.base.support :=
    (A.simple_iff (idx a)).trans (corresponding_simple D P idx χ hr hp a)
  ext i
  obtain ⟨a, rfl⟩ := idx.surjective i
  change idx a ∈ idx '' (D.base.support : Set D.I) ↔ idx a ∈ A.base.support
  constructor
  · rintro ⟨b, hb, he⟩
    exact (hs a).mpr (idx.injective he ▸ hb)
  · intro h
    exact ⟨a, (hs a).mp h, rfl⟩


end DatumComparison

section RankOne

variable {k : Type u} [Field k]
variable {D : BasedRootDatum.{u}} {H : AffineAlgebraicGroup k}
variable {T : ClosedSubgroup H.val} {A : AdditiveLine k}

private def elementaryWord {R : Type u} [CommRing R] (s : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  upper (s : R) * lower (-(↑s⁻¹ : R)) * upper (s : R)

private theorem diagonal_mul_word_one {R : Type u} [CommRing R] (s : Rˣ) :
    diagonal s * elementaryWord 1 = elementaryWord s := by
  have matrix (t : Rˣ) : (elementaryWord t).val = !![0, (t : R); -(↑t⁻¹ : R), 0] := by
    change (!![1, (t : R); 0, 1] * !![1, 0; -(↑t⁻¹ : R), 1] * !![1, (t : R); 0, 1]) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Subtype.val_injective
  change !![(s : R), 0; 0, (↑s⁻¹ : R)] * (elementaryWord 1).val = (elementaryWord s).val
  rw [matrix, matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem rankOneWord_eq (M : Marking D H T A) (ρ : RankOneRelations M)
    (a : D.I) (R : TestAlgebra k) (s : Rˣ) :
    (ρ.hom a).app R (elementaryWord s) =
      rankOneWord (M.rootMap a) (M.rootMap (D.datum.reflectionPerm a a)) R s := by
  let f := ((ρ.hom a).app R).hom
  change f (_ * _ * _) = _
  rw [map_mul, map_mul]
  unfold rankOneWord
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (ρ.upper_eq a R _) (ρ.lower_eq a R _)) (ρ.upper_eq a R _)

private theorem splitTorus_points_ext {S : GroupScheme k} (hS : IsSplitTorus S)
    (R : TestAlgebra k) (a b : GroupPoints S R)
    (h : ∀ χ : Character S, characterValue χ R a = characterValue χ R b) : a = b := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hS
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  obtain ⟨f, hf⟩ := torus_point_from_coordinates r i R a
  obtain ⟨g, hg⟩ := torus_point_from_coordinates r i R b
  have heval (q : MonoidAlgebra k (StandardLattice.{u} r) →ₐ[k] R) (m : StandardLattice.{u} r) :
      characterValue ((charactersOfIso i) (χ m)) R (algebraPoint R q ≫ i.hom.hom.hom) =
        q (MonoidAlgebra.single m 1) := by
    have he : (algebraPoint R q ≫ i.hom.hom.hom) ≫ ((charactersOfIso i) (χ m)).hom.hom =
        algebraPoint R q ≫ (χ m).hom.hom := by
      change (algebraPoint R q ≫ i.hom.hom.hom) ≫ i.inv.hom.hom ≫ (χ m).hom.hom = _
      have hi : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 _ := (Grp.forget _).congr_map i.hom_inv_id
      simp only [Category.assoc, ← Category.assoc (f := i.hom.hom.hom), hi, Category.id_comp]
    unfold characterValue
    dsimp only
    rw [he]
    change characterValue (χ m) R (algebraPoint R q) = _
    rw [hχ, characterValue_monomial]
  have hfg : f = g := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      rw [← heval, ← heval, hf, hg, h]
    · ext
  rw [← hf, ← hg, hfg]

variable [IsCommMonObj T.group.X]

/-- Transport a marked coroot functional to the actual cocharacter lattice
using perfect duality. -/
private def markedCoroot (E : Datum T) (M : Marking D H T A) (a : D.I) :
    Cocharacter T.group :=
  Additive.toMul (E.rootDatum.flip.toPerfPair.symm
    (M.character.symm.dualMap (D.datum.flip.toPerfPair (D.datum.coroot a))))

private theorem markedCoroot_pairing (E : Datum T) (M : Marking D H T A) (a : D.I) (x : D.X) :
    pairing T.group (Additive.toMul (M.character x)) (markedCoroot E M a) =
      D.datum.coroot' a x := by
  let p := M.character.symm.dualMap (D.datum.flip.toPerfPair (D.datum.coroot a))
  rw [← E.pairing_eq]
  change E.rootDatum.toLinearMap (M.character x) (E.rootDatum.flip.toPerfPair.symm p) = _
  have h := DFunLike.congr_fun (E.rootDatum.flip.toPerfPair.apply_symm_apply p) (M.character x)
  change _ = D.datum.coroot' a (M.character.symm (M.character x)) at h
  rwa [M.character.symm_apply_apply] at h

private theorem markedCoroot_word (E : Datum T) (hT : IsSplitTorus T.group)
    (M : Marking D H T A) (ρ : RankOneRelations M) (a : D.I) (R : TestAlgebra k) (s : Rˣ) :
    cocharacterPoint (markedCoroot E M a) R s ≫ T.inclusion.hom.hom =
      rankOneWord (M.rootMap a) (M.rootMap (D.datum.reflectionPerm a a)) R s *
      (rankOneWord (M.rootMap a) (M.rootMap (D.datum.reflectionPerm a a)) R 1)⁻¹ := by
  obtain ⟨t, ht, hχ⟩ := ρ.diagonal_eq a R s
  have he : t = cocharacterPoint (markedCoroot E M a) R s := by
    apply splitTorus_points_ext hT
    intro χ
    obtain ⟨x, hx⟩ := M.character.surjective (Additive.ofMul χ)
    change Additive.toMul (M.character x) = χ at hx
    rw [← hx, hχ, (RootData.CharacterPairing.characterPairingComposition T.group _ _).2 R s,
      markedCoroot_pairing]
  rw [← he, ← ht, ← rankOneWord_eq M ρ a R s, ← rankOneWord_eq M ρ a R 1]
  let f := ((ρ.hom a).app R).hom
  change f (diagonal s) = f (elementaryWord s) * (f (elementaryWord 1))⁻¹
  rw [← diagonal_mul_word_one, map_mul, mul_inv_cancel_right]

private theorem identified_coroot (E : Datum T) (hT : IsSplitTorus T.group)
    (M : Marking D H T A) (ρ : RankOneRelations M) (a : D.I) (x : D.X) :
    E.rootDatum.coroot' (M.index a) (M.character x) = D.datum.coroot' a x := by
  let j := M.index a
  let b := D.datum.reflectionPerm a a
  let c := markedCoroot E M a
  let p := (D.datum.coroot' a).comp M.character.symm.toLinearMap
  have hj : E.rootDatum.root j = M.character (D.datum.root a) := by
    rw [E.root_eq]
    exact congrArg Additive.ofMul (M.rootCharacter a)
  have hb : (M.index b).val = j.val⁻¹ := by
    change (M.index b).val = (M.index a).val⁻¹
    rw [M.rootCharacter b, M.rootCharacter a]
    change Additive.toMul (M.character (D.datum.root (D.datum.reflectionPerm a a))) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg]
    rfl
  have hneg := (M.coordinate (M.index b)).property
  change Specs.RootGroups.HasScalarAction T (M.index b).val (M.rootMap b) at hneg
  rw [hb] at hneg
  have hp : p (E.rootDatum.root j) = 2 := by
    rw [hj]
    change D.datum.coroot' a (M.character.symm (M.character (D.datum.root a))) = _
    rw [M.character.symm_apply_apply]
    exact D.datum.pairing_same a
  have hpair : pairing T.group j.val c = 2 := by
    change pairing T.group (M.index a).val (markedCoroot E M a) = _
    rw [M.rootCharacter a, markedCoroot_pairing]
    exact D.datum.pairing_same a
  let n := rankOneRepresentative (M.rootMap a) (M.rootMap b)
  obtain ⟨r⟩ := RootData.RootGroups.corootReflection_of_word T hT j.val
    (M.rootMap a) (M.rootMap b) (M.coordinate j).property hneg c n
    (rankOneRepresentative_point _ _) (markedCoroot_word E hT M ρ a) hpair
  have hcoroot : r.coroot = c := by
    apply Grp.hom_ext
    -- The identity morphism of Gₘ is its universal point over the coordinate algebra.
    let R := CommAlgCat.of k (MonoidAlgebra k IntegerCharacters.{u})
    let s := unitEquiv R (𝟙 _)
    have hs : unitPoint R s = 𝟙 _ :=
      (unitEquiv R).injective (unitEquiv_unitPoint R s)
    have h := (r.coroot_word R s).trans (markedCoroot_word E hT M ρ a R s).symm
    change (unitPoint R s ≫ r.coroot.hom.hom) ≫ T.inclusion.hom.hom =
      (unitPoint R s ≫ c.hom.hom) ≫ T.inclusion.hom.hom at h
    rw [hs, Category.id_comp, Category.id_comp] at h
    let := T.isClosedImmersion
    let : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono T.inclusion.hom.hom).mp h
  obtain ⟨N, hN, act, hact⟩ := E.normalizerAction
  obtain ⟨v, hv⟩ := (hN _ r.representative).mp r.normalizes
  obtain ⟨e, he, heWeight, _⟩ := hact v
  have he' : InducesTorusConjugation T r.representative e := by
    unfold InducesTorusConjugation
    simpa only [← Category.assoc, hv, Category.assoc] using he
  have heq := inducedConjugation_unique he' r.conjugates
  have hW (y : Additive (Character T.group)) :
      (act v).weightEquiv y = y - p y • E.rootDatum.root j := by
    obtain ⟨z, rfl⟩ := M.character.surjective y
    let χ := Additive.toMul (M.character z)
    change (act v).weightEquiv (Additive.ofMul χ) = _
    rw [heWeight, heq, r.reflection, E.root_eq]
    rw [hcoroot]
    change Additive.ofMul (χ * j.val ^ (-pairing T.group χ c)) =
      M.character z - D.datum.coroot' a (M.character.symm (M.character z)) • Additive.ofMul j.val
    rw [M.character.symm_apply_apply, sub_eq_add_neg, ← neg_smul]
    change Additive.ofMul (χ * j.val ^ (-pairing T.group χ c)) =
      Additive.ofMul (χ * j.val ^ (-(D.datum.coroot' a z)))
    rw [markedCoroot_pairing E M a z]
  have h := coroot_functional_of_reflection E.rootDatum j (act v) p hp hW
  have hx := DFunLike.congr_fun h (M.character x)
  change E.rootDatum.coroot' j (M.character x) =
    D.datum.coroot' a (M.character.symm (M.character x)) at hx
  rwa [M.character.symm_apply_apply] at hx

end RankOne

/-- Recover the Borel, attached datum, and pinning from the marked
root groups and rank-one homomorphisms. -/
theorem pinnedDatumFromMarkedRootGroups : Statement.{u} := by
  intro D k _ H hH T hT hMax A M ρ
  obtain ⟨hcomm, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing H hH T hT hMax
  let := hcomm
  obtain ⟨c, hc, hpos⟩ := regularCocharacter_with_positives D H T E M.index M.character
    (fun a => congrArg Additive.ofMul (M.rootCharacter a))
  obtain ⟨L⟩ := existsLimitDecomposition H (c ≫ T.inclusion)
  obtain ⟨_, hB, hTB, hroots, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel H hH T hT hMax c hc L
  let P := markedBorelPair hH hT hMax L.parabolic hB hTB
  have hp (a : D.I) : M.index a ∈ subgroupRoots T L.parabolic ↔ D.base.IsPos a := by
    rw [hroots]
    exact hpos a
  let F := Classification.Pinning.attachedDatum P
  let e := compareBasedDatum F M.index M.character M.rootCharacter
    (identified_coroot F.datum hT M ρ) hp
  exact ⟨L.parabolic, hB, hTB, F, e, fun α => M.coordinate α.val, M.coordinate,
    hp, LinearEquiv.ext (fun _ => rfl), rfl, fun _ => rfl, fun _ => rfl⟩

end

end LinearAlgebraicGroups.Classification.PinnedDatumFromMarkedRootGroups
