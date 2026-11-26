import Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import LinearAlgebraicGroups.Reductive.CentralDerived
import LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.Classification.CentralIsogenies
import Mathlib.Tactic.Abel
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open AlgebraicGeometry CategoryTheory Opposite
open scoped BigOperators CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.RootData.SpecialLinearDatum

open _root_.LinearAlgebraicGroups.Specs
open Specs.SpecialLinearDatum
open Specs.SimplyConnectedLattice (AdjointForm LatticeCriterion SplitCover)
open Specs.Unipotent (Index)
open StandardGroups
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.GeometricRadicals (baseChangedSubgroup)
open private diagonalMatrixHom
  diagonalMatrixHom_val
  diagonal_units_surjective
  upper_inclusion
  diagonal_in_upper
  centralizes_iff_testAlgebras
  maxTorus_of_self_centralizer
  baseChangePowerTorusIso
  from LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private Unipotent.onPoints Unipotent.onPoints_comp Unipotent.scheme_hom_spec
  Unipotent.group_hom_ext Unipotent.factor_through_closed
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open LinearAlgebraicGroups.GeneralLinearStructure
open LinearAlgebraicGroups.Reductive.CentralDerived (derivedSemisimple)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false

theorem semisimple_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    Semisimple.{u} := by
  intro k _ r S s
  let G := generalLinearGroup k (Index.{u} (r + 1))
  let e := generalLinearGroupPointsIso k (Index.{u} (r + 1))
  obtain ⟨f, hf, _, _, hD⟩ := generalLinearDerived k (r + 1) (Nat.succ_pos r) G S e s
  exact derivedSemisimple G (generalLinearReductive k _ (Nat.succ_pos r) G e)
    ⟨S.val, f, hf⟩ hD

theorem rankOneTrivial_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    RankOneTrivial.{u} := by
  intro k _ S s
  exact (generalLinearRankOne k (generalLinearGroup k (Index.{u} 1))
    S (multiplicativeGroup k)
    (generalLinearGroupPointsIso k _) s
    (multiplicativeGroupPointsIso k)).2.1

private theorem coroot_chain (r : ℕ) (i : Fin (r + 1)) :
    coroot (r + 1) i 0 ∈ Submodule.span ℤ (Set.range (simpleCoroot r)) := by
  induction i using Fin.induction with
  | zero =>
    have hz : coroot (r + 1) 0 0 = 0 := by
      apply Subtype.ext
      exact sub_self _
    rw [hz]
    exact Submodule.zero_mem _
  | succ i hi =>
    have he : coroot (r + 1) i.succ 0 =
        coroot (r + 1) i.castSucc 0 - simpleCoroot r i := by
      apply Subtype.ext
      change coordinate (r + 1) i.succ - coordinate (r + 1) 0 =
        coordinate (r + 1) i.castSucc - coordinate (r + 1) 0 -
          (coordinate (r + 1) i.castSucc - coordinate (r + 1) i.succ)
      abel
    rw [he]
    exact Submodule.sub_mem _ hi (Submodule.subset_span ⟨i, rfl⟩)

private theorem simpleCoroot_spans (r : ℕ) :
    Submodule.span ℤ (Set.range (simpleCoroot r)) = ⊤ := by
  apply top_unique
  intro y _
  have hy : ∑ i : Fin (r + 1), y.val i = 0 := by
    have h : sumExponents (r + 1) y.val = 0 := y.property
    simpa only [sumExponents, LinearMap.sum_apply, LinearMap.proj_apply] using h
  have he : y = ∑ i : Fin (r + 1), y.val i • coroot (r + 1) i 0 := by
    apply (LinearMap.ker (sumExponents (r + 1))).subtype_injective
    rw [map_sum]
    change y.val = ∑ i : Fin (r + 1), y.val i • (coordinate (r + 1) i - coordinate (r + 1) 0)
    ext j
    rw [Finset.sum_apply]
    change y.val j = ∑ i : Fin (r + 1), y.val i *
      (coordinate (r + 1) i j - coordinate (r + 1) 0 j)
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy, zero_mul, sub_zero]
    have h (i : Fin (r + 1)) : y.val i * coordinate (r + 1) i j = (Pi.single i (y.val i) : Fin (r + 1) → ℤ) j := by
      by_cases hij : i = j
      · subst j
        simp [coordinate]
      · simp [coordinate, Pi.single_eq_of_ne (show j ≠ i from fun h => hij h.symm)]
    simp only [h, Fintype.sum_pi_single]
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (coroot_chain r i)

private def prefixSum (r : ℕ) (j : Fin r) : CocharacterLattice (r + 1) →ₗ[ℤ] ℤ :=
  ∑ i ∈ Finset.Iic j.castSucc, (LinearMap.proj i).comp
    (LinearMap.ker (sumExponents (r + 1))).subtype

private theorem prefixSum_simpleCoroot (r : ℕ) (i j : Fin r) :
    prefixSum r j (simpleCoroot r i) = if i = j then 1 else 0 := by
  simp only [prefixSum, LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    simpleCoroot, coroot, coordinate]
  change (∑ k ∈ Finset.Iic j.castSucc,
    ((Pi.single i.castSucc 1 : Fin (r + 1) → ℤ) k -
      (Pi.single i.succ 1 : Fin (r + 1) → ℤ) k)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
  simp only [Finset.mem_Iic, Fin.castSucc_le_castSucc_iff, Fin.succ_le_castSucc_iff]
  by_cases he : i = j
  · subst j
    simp
  · rcases lt_or_gt_of_ne he with h | h
    · simp [he, h, h.le]
    · simp [he, h.not_ge, h.asymm]

theorem simpleCorootBasis_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    SimpleCorootBasis := by
  intro r
  have hli : LinearIndependent ℤ (simpleCoroot r) := by
    apply linearIndependent_iff'.mpr
    intro s g h j hj
    have hh := congrArg (prefixSum r j) h
    simpa [map_sum, prefixSum_simpleCoroot, smul_ite, Finset.sum_ite_eq', hj] using hh
  let b := Module.Basis.mk hli (simpleCoroot_spans r).ge
  exact ⟨b, Module.Basis.mk_apply _ _⟩

private theorem dotPairing_mk (n : ℕ) (x : Fin n → ℤ) (y : CocharacterLattice n) :
    dotPairing n ((Submodule.span ℤ ({(1 : Fin n → ℤ)} : Set (Fin n → ℤ))).mkQ x) y =
      ∑ i : Fin n, x i * y.val i := by
  rfl

private theorem dotPairing_root (n : ℕ) (i j : Fin n) (y : CocharacterLattice n) :
    dotPairing n (root n i j) y = y.val i - y.val j := by
  rw [root, dotPairing_mk]
  simp_rw [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1 <;> simp [coordinate, Pi.single_apply, ite_mul, Finset.sum_ite_eq']

theorem simpleCartanPairings_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    SimpleCartanPairings := by
  intro r i j
  rw [dotPairing_root]
  change (coordinate (r + 1) j.castSucc i.castSucc - coordinate (r + 1) j.succ i.castSucc) -
    (coordinate (r + 1) j.castSucc i.succ - coordinate (r + 1) j.succ i.succ) = _
  simp only [coordinate, Pi.single_apply, Fin.castSucc_inj, Fin.succ_inj]
  have h₁ : i.castSucc = j.succ ↔ j.val + 1 = i.val := by
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, eq_comm]
  have h₂ : i.succ = j.castSucc ↔ i.val + 1 = j.val := by
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  simp only [h₁, h₂]
  split_ifs <;> simp_all [Fin.ext_iff]
  omega

private lemma decreasingVector_sum (r : ℕ) : ∑ i, decreasingVector r i = 0 := by
  let s := ∑ i, decreasingVector r i
  have hterm (i : Fin (r + 1)) : decreasingVector r i.rev = -decreasingVector r i := by
    have h := i.isLt
    simp only [decreasingVector, Fin.val_rev]
    omega
  have h : s = -s := by
    change (∑ i : Fin (r + 1), decreasingVector r i) = -(∑ i, decreasingVector r i)
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun i => by simp [hterm])
  omega

def decreasingCocharacter (r : ℕ) : CocharacterLattice (r + 1) :=
  ⟨decreasingVector r, by
    change sumExponents (r + 1) (decreasingVector r) = 0
    simpa only [sumExponents, LinearMap.sum_apply, LinearMap.proj_apply] using decreasingVector_sum r⟩

theorem pair_decreasing (r : ℕ) (i j : Fin (r + 1)) :
    dotPairing (r + 1) (root (r + 1) i j) (decreasingCocharacter r) =
      2 * ((j.val : ℤ) - i.val) := by
  rw [dotPairing_root]
  change decreasingVector r i - decreasingVector r j = _
  simp only [decreasingVector]
  omega

private lemma root_add_chain (n : ℕ) (i j l : Fin n) :
    root n i j + root n j l = root n i l := by
  simp only [root, ← map_add]
  congr 1
  abel

private lemma simple_of_adjacent (r : ℕ) (i : Fin r)
    (a b c d : Fin (r + 1)) (hab : a < b) (hcd : c < d) :
    root (r + 1) i.castSucc i.succ ≠ root (r + 1) a b + root (r + 1) c d := by
  intro h
  have hh := congrArg (fun x => dotPairing (r + 1) x (decreasingCocharacter r)) h
  simp only [map_add, LinearMap.add_apply, pair_decreasing, Fin.val_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one] at hh
  have hab' := Fin.val_fin_lt.mp hab
  have hcd' := Fin.val_fin_lt.mp hcd
  omega

private lemma adjacent_of_simple (r : ℕ) (i j : Fin (r + 1)) (hij : i < j)
    (hs : ∀ a b c d : Fin (r + 1), a < b → c < d →
      root (r + 1) i j ≠ root (r + 1) a b + root (r + 1) c d) :
    ∃ p : Fin r, i = p.castSucc ∧ j = p.succ := by
  have hij' := Fin.val_fin_lt.mp hij
  have hi : i.val < r := by omega
  let p : Fin r := ⟨i.val, hi⟩
  refine ⟨p, Fin.ext rfl, ?_⟩
  apply Fin.ext
  change j.val = i.val + 1
  by_contra h
  have hm : p.succ < j := Fin.val_fin_lt.mpr (by change i.val + 1 < j.val; omega)
  have hp : i < p.succ := Fin.val_fin_lt.mpr (Nat.lt_succ_self i.val)
  exact hs i p.succ p.succ j hp hm (root_add_chain (r + 1) i p.succ j).symm

private abbrev determinantRelation (n : ℕ) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ ({(1 : Fin n → ℤ)} : Set (Fin n → ℤ))

private def characterDifference (r : ℕ) : (Fin (r + 1) → ℤ) →ₗ[ℤ] (Fin r → ℤ) where
  toFun x i := x i.succ - x 0
  map_add' x y := by ext i; simp [Pi.add_apply]; abel
  map_smul' c x := by ext i; simp [mul_sub]

private def characterTail (r : ℕ) : CharacterLattice (r + 1) →ₗ[ℤ] (Fin r → ℤ) :=
  (determinantRelation (r + 1)).liftQ (characterDifference r) (Submodule.span_le.mpr (by
    intro x hx
    obtain rfl : x = 1 := hx
    change characterDifference r 1 = 0
    ext i
    exact sub_self 1))

private def characterSection (r : ℕ) (a : Fin r → ℤ) : CharacterLattice (r + 1) :=
  (determinantRelation (r + 1)).mkQ (Fin.cons (α := fun _ => ℤ) 0 a)

private lemma characterTail_mk (r : ℕ) (x : Fin (r + 1) → ℤ) (i : Fin r) :
    characterTail r ((determinantRelation (r + 1)).mkQ x) i = x i.succ - x 0 := rfl

private lemma characterSection_characterTail (r : ℕ) (x : CharacterLattice (r + 1)) :
    characterSection r (characterTail r x) = x := by
  refine Submodule.Quotient.induction_on (p := determinantRelation (r + 1)) x ?_
  intro v
  have hv : Fin.cons (α := fun _ => ℤ) 0
      (characterTail r ((determinantRelation (r + 1)).mkQ v)) =
      v - v 0 • (1 : Fin (r + 1) → ℤ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 = v 0 - v 0 * 1
      simp
    · change characterTail r ((determinantRelation (r + 1)).mkQ v) j = v j.succ - v 0 * 1
      rw [characterTail_mk, mul_one]
  have hrel : (determinantRelation (r + 1)).mkQ (v 0 • (1 : Fin (r + 1) → ℤ)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (p := determinantRelation (r + 1))).2
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  change (determinantRelation (r + 1)).mkQ (Fin.cons (α := fun _ => ℤ) 0
    (characterTail r ((determinantRelation (r + 1)).mkQ v))) = (determinantRelation (r + 1)).mkQ v
  rw [hv, map_sub, hrel, sub_zero]

def characterCoordinates (r : ℕ) : CharacterLattice (r + 1) ≃ₗ[ℤ] (Fin r → ℤ) :=
  LinearEquiv.ofBijective (characterTail r) ⟨fun _ _ h => by
    simpa only [characterSection_characterTail] using congrArg (characterSection r) h,
    fun a => ⟨characterSection r a, by
      ext i
      rw [characterSection, characterTail_mk]
      simp⟩⟩

def cocharacterCoordinates (r : ℕ) : CocharacterLattice (r + 1) ≃ₗ[ℤ] (Fin r → ℤ) := by
  let f : CocharacterLattice (r + 1) →ₗ[ℤ] (Fin r → ℤ) :=
    LinearMap.pi fun i => (LinearMap.proj i.succ).comp (sumExponents (r + 1)).ker.subtype
  have hker (v : CocharacterLattice (r + 1)) : v.val 0 + ∑ i : Fin r, v.val i.succ = 0 := by
    rw [← Fin.sum_univ_succ]
    have hv : sumExponents (r + 1) v.val = 0 := v.property
    simpa only [sumExponents, LinearMap.sum_apply, LinearMap.proj_apply] using hv
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => congrFun h j) i
    have hv := hker v
    have hw := hker w
    have hs : (∑ j : Fin r, v.val j.succ) = ∑ j : Fin r, w.val j.succ :=
      Finset.sum_congr rfl fun j _ => congrFun h j
    omega
  · intro a
    let v : Fin (r + 1) → ℤ := Fin.cons (α := fun _ => ℤ) (-(∑ j, a j)) a
    have hv : v ∈ (sumExponents (r + 1)).ker := by
      change sumExponents (r + 1) v = 0
      simp [sumExponents, LinearMap.sum_apply, Fin.sum_univ_succ, v]
    exact ⟨⟨v, hv⟩, rfl⟩

theorem dotPairing_in_coordinates (r : ℕ) (x : CharacterLattice (r + 1))
    (y : CocharacterLattice (r + 1)) :
    dotPairing (r + 1) x y = ∑ i, characterCoordinates r x i * cocharacterCoordinates r y i := by
  refine Submodule.Quotient.induction_on (p := determinantRelation (r + 1)) x ?_
  intro v
  change dotPairing (r + 1) ((determinantRelation (r + 1)).mkQ v) y = _
  rw [dotPairing_mk, Fin.sum_univ_succ]
  change _ = ∑ i : Fin r, (v i.succ - v 0) * y.val i.succ
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hy : y.val 0 + ∑ i : Fin r, y.val i.succ = 0 := by
    rw [← Fin.sum_univ_succ]
    have hy' : sumExponents (r + 1) y.val = 0 := y.property
    simpa only [sumExponents, LinearMap.sum_apply, LinearMap.proj_apply] using hy'
  have hh : ∑ i : Fin r, y.val i.succ = -y.val 0 := by omega
  rw [hh, mul_neg, sub_neg_eq_add, add_comm]

private lemma sizeOne_lattices :
    Subsingleton (CharacterLattice 1) ∧ Subsingleton (CocharacterLattice 1) := by
  exact ⟨(characterCoordinates 0).injective.subsingleton, (cocharacterCoordinates 0).injective.subsingleton⟩

theorem sizeOneLattices_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    SizeOneLattices :=
  sizeOne_lattices

theorem adjacentPositiveRoots_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    AdjacentPositiveRoots := by
  intro r i j hij
  refine ⟨adjacent_of_simple r i j hij, ?_⟩
  rintro ⟨p, rfl, rfl⟩ a b c d hab hcd
  exact simple_of_adjacent r p a b c d hab hcd

open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)

theorem simplyConnectedOfMatrixDatum (criterion : LatticeCriterion.{u})
    {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
    {s : SpecialMatrixPoints S (r + 1)} (hS : IsSemisimple S)
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) (D : Specs.Pinning.AttachedDatum B.pair)
    (hD : IsMatrixBasedDatum B D) : GeometricallySimplyConnected S := by
  letI : IsCommMonObj B.pair.T.group.X := D.comm
  letI : IsCommMonObj T.subgroup.group.X := D.comm
  let K := @corootLatticeOf k _ B.pair.G B.pair.T D.comm D.datum
  apply (criterion S hS T.subgroup T.split B.maximal D.datum).2
  change K = ⊤
  have hspan : ⊤ ≤ K.comap L.cocharacters.symm.toLinearMap := by
    rw [← simpleCoroot_spans r]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let p : RootIndices (r + 1) := ⟨(i.castSucc, i.succ), by
      intro he
      have hv := congrArg Fin.val he
      simp at hv⟩
    change L.cocharacters.symm (simpleCoroot r i) ∈ K
    have he := hD.1 p
    change L.cocharacters (D.datum.rootDatum.coroot (M.indices p)) = simpleCoroot r i at he
    rw [← he, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span (Set.mem_range_self (M.indices p))
  apply top_unique
  intro y _
  have h := hspan (show L.cocharacters y ∈ (⊤ : Submodule ℤ (CocharacterLattice (r + 1))) by simp)
  change L.cocharacters.symm (L.cocharacters y) ∈ K at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

theorem sizeTwoLattices_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    SizeTwoLattices := by
  let e := (LinearEquiv.funUnique (Fin 1) ℤ ℤ).trans (LinearEquiv.neg ℤ (M := ℤ))
  refine ⟨(characterCoordinates 1).trans e, (cocharacterCoordinates 1).trans e, ?_, ?_, ?_, ?_⟩
  · change -(coordinate 2 0 (1 : Fin 2) - coordinate 2 0 0) = 1
    simp [coordinate]
  · change -(coordinate 2 0 (1 : Fin 2) - coordinate 2 1 1) = 1
    simp [coordinate]
  · change -((coordinate 2 0 (1 : Fin 2) - coordinate 2 1 1) -
      (coordinate 2 0 0 - coordinate 2 1 0)) = 2
    simp [coordinate]
  · intro a b
    rw [dotPairing_in_coordinates, Fin.sum_univ_one]
    change _ = -(characterCoordinates 1 a 0) * -(cocharacterCoordinates 1 b 0)
    rw [neg_mul_neg]

theorem cocharacters_eq_of_root_pairings (r : ℕ)
    {y z : CocharacterLattice (r + 1)}
    (h : ∀ p : RootIndices (r + 1),
      dotPairing (r + 1) (root (r + 1) p.val.1 p.val.2) y =
        dotPairing (r + 1) (root (r + 1) p.val.1 p.val.2) z) :
    y = z := by
  have hdiff (i : Fin (r + 1)) : y.val i - z.val i = y.val 0 - z.val 0 := by
    by_cases hi : i = 0
    · rw [hi]
    · have hh := h ⟨(i, 0), hi⟩
      rw [dotPairing_root, dotPairing_root] at hh
      change y.val i - y.val 0 = z.val i - z.val 0 at hh
      omega
  have hsum (v : CocharacterLattice (r + 1)) : ∑ i : Fin (r + 1), v.val i = 0 := by
    have hv : sumExponents (r + 1) v.val = 0 := v.property
    simpa only [sumExponents, LinearMap.sum_apply, LinearMap.proj_apply] using hv
  have hconst : ((r : ℤ) + 1) * (y.val 0 - z.val 0) = 0 := by
    calc
      _ = ∑ _ : Fin (r + 1), (y.val 0 - z.val 0) := by
        simp [Finset.sum_const, mul_sub]
      _ = ∑ i : Fin (r + 1), (y.val i - z.val i) :=
        Finset.sum_congr rfl fun i _ => (hdiff i).symm
      _ = 0 := by rw [Finset.sum_sub_distrib, hsum, hsum, sub_zero]
  have h₀ := (mul_eq_zero.mp hconst).resolve_left (by omega)
  apply Subtype.ext
  funext i
  exact sub_eq_zero.mp ((hdiff i).trans h₀)


private theorem coordinate_swap_eq (n : ℕ) (i j a : Fin n) (hij : i ≠ j) :
    coordinate n ((Equiv.swap i j) a) =
      coordinate n a - (coroot n i j).val a • (coordinate n i - coordinate n j) := by
  by_cases hai : a = i
  · subst a
    rw [Equiv.swap_apply_left]
    have h : (coroot n i j).val i = 1 := by
      simp [coroot, coordinate, Pi.single_eq_of_ne hij]
    rw [h, one_smul]
    abel
  · by_cases haj : a = j
    · subst a
      rw [Equiv.swap_apply_right]
      have h : (coroot n i j).val j = -1 := by
        simp [coroot, coordinate, Pi.single_eq_of_ne hai]
      rw [h, neg_one_smul]
      abel
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
      have h : (coroot n i j).val a = 0 := by
        simp [coroot, coordinate, Pi.single_eq_of_ne hai, Pi.single_eq_of_ne haj]
      simp [h]

private theorem reflection_root_eq (n : ℕ) (i j a b : Fin n) (hij : i ≠ j) :
    root n a b - dotPairing n (root n a b) (coroot n i j) • root n i j =
      root n ((Equiv.swap i j) a) ((Equiv.swap i j) b) := by
  rw [dotPairing_root]
  simp only [root, ← map_smul, ← map_sub]
  rw [coordinate_swap_eq n i j a hij, coordinate_swap_eq n i j b hij]
  congr 1
  rw [sub_smul]
  abel

private theorem root_coroot_pairing (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    dotPairing n (root n i j) (coroot n i j) = 2 := by
  rw [dotPairing_root]
  simp [coroot, coordinate, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]

open Specs.AbstractPairing (Datum)
open Specs.CharacterDescent (Character Cocharacter)

theorem corootsOfMatrixDatum {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
    {s : SpecialMatrixPoints S (r + 1)} {T : DiagonalTorus s}
    {L : LatticeIdentification T} (M : RootIdentification T L)
    [IsCommMonObj T.subgroup.group.X] (D : Datum T.subgroup)
    (p : RootIndices (r + 1)) :
    L.cocharacters (D.rootDatum.coroot (M.indices p)) = coroot (r + 1) p.val.1 p.val.2 := by
  let X := CharacterLattice (r + 1)
  let y := L.cocharacters (D.rootDatum.coroot (M.indices p))
  let z := coroot (r + 1) p.val.1 p.val.2
  let a (q : RootIndices (r + 1)) := root (r + 1) q.val.1 q.val.2
  let Φ := Set.range a
  let f : Module.Dual ℤ X := (dotPairing (r + 1)).flip y
  let g : Module.Dual ℤ X := (dotPairing (r + 1)).flip z
  have hroot (q : RootIndices (r + 1)) : L.characters (D.rootDatum.root (M.indices q)) = a q := by
    rw [D.root_eq, M.character_eq]
  have hpair (q : RootIndices (r + 1)) :
      D.rootDatum.toLinearMap (D.rootDatum.root (M.indices q)) (D.rootDatum.coroot (M.indices p)) =
        f (a q) := by
    rw [D.root_eq]
    have h := D.pairing_eq (M.indices q).val
      (Additive.toMul (D.rootDatum.coroot (M.indices p)))
    change D.rootDatum.toLinearMap (Additive.ofMul (M.indices q).val)
      (D.rootDatum.coroot (M.indices p)) = _ at h
    rw [h, L.pairing_eq, M.character_eq]
    rfl
  have hf : f (a p) = 2 := (hpair p).symm.trans (D.rootDatum.root_coroot_two _)
  have hg : g (a p) = 2 := root_coroot_pairing _ _ _ p.property
  have hf' : Set.MapsTo (Module.preReflection (a p) f) Φ Φ := by
    rintro _ ⟨q, rfl⟩
    let q' := M.indices.symm (D.rootDatum.reflectionPerm (M.indices p) (M.indices q))
    refine ⟨q', ?_⟩
    rw [Module.preReflection_apply, ← hpair q, ← hroot p, ← hroot q, ← map_smul, ← map_sub,
      D.rootDatum.reflectionPerm_root, ← hroot q', Equiv.apply_symm_apply]
  have hg' : Set.MapsTo (Module.preReflection (a p) g) Φ Φ := by
    rintro _ ⟨q, rfl⟩
    let swap := Equiv.swap p.val.1 p.val.2
    refine ⟨⟨(swap q.val.1, swap q.val.2), fun he => q.property (swap.injective he)⟩, ?_⟩
    exact (reflection_root_eq _ _ _ _ _ p.property).symm
  letI : Module.IsTorsionFree ℤ X :=
    (characterCoordinates r).injective.moduleIsTorsionFree _ (by simp)
  have he :=
    Module.Dual.eq_of_preReflection_mapsTo' (Set.finite_range a)
      (Submodule.subset_span (Set.mem_range_self p)) hf hf' hg hg'
  apply cocharacters_eq_of_root_pairings r
  intro q
  exact congrArg (fun l : Module.Dual ℤ (Submodule.span ℤ Φ) =>
    l ⟨a q, Submodule.subset_span (Set.mem_range_self q)⟩) he

theorem matrixBasedDatum_of_attachedDatum {k : Type u} [Field k] {r : ℕ}
    {S : AffineAlgebraicGroup k} {s : SpecialMatrixPoints S (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M) (D : Specs.Pinning.AttachedDatum B.pair) :
    IsMatrixBasedDatum B D := by
  letI : IsCommMonObj T.subgroup.group.X := D.comm
  refine ⟨corootsOfMatrixDatum M D.datum, fun p => ?_⟩
  rw [D.simple_iff]
  let a (q : RootIndices (r + 1)) := root (r + 1) q.val.1 q.val.2
  have hproduct {p q l : RootIndices (r + 1)} :
      (M.indices p).val = (M.indices q).val * (M.indices l).val ↔
        a p = a q + a l := by
    have h :
        L.characters (Additive.ofMul ((M.indices q).val * (M.indices l).val)) = a q + a l := by
      change L.characters (Additive.ofMul (M.indices q).val + Additive.ofMul (M.indices l).val) = _
      rw [map_add, M.character_eq, M.character_eq]
    have hp : L.characters (Additive.ofMul (M.indices p).val) = a p := M.character_eq p
    rw [← hp, ← h, L.characters.injective.eq_iff]
    rfl
  constructor
  · intro ⟨hp, hsimple⟩
    apply adjacent_of_simple r p.val.1 p.val.2 ((B.positive_iff p).mp hp)
    intro i j l m hij hlm h
    let q : RootIndices (r + 1) := ⟨(i, j), ne_of_lt hij⟩
    let t : RootIndices (r + 1) := ⟨(l, m), ne_of_lt hlm⟩
    exact hsimple (M.indices q) ((B.positive_iff q).mpr hij)
      (M.indices t) ((B.positive_iff t).mpr hlm) (hproduct.mpr h)
  · rintro ⟨i, hi, hj⟩
    have hp : p.val.1 < p.val.2 := by rw [hi, hj]; exact Fin.castSucc_lt_succ
    refine ⟨(B.positive_iff p).mpr hp, ?_⟩
    intro alpha hAlpha beta hBeta he
    obtain ⟨q, rfl⟩ := M.indices.surjective alpha
    obtain ⟨l, rfl⟩ := M.indices.surjective beta
    have h := hproduct.mp he
    change root (r + 1) p.val.1 p.val.2 = _ at h
    rw [hi, hj] at h
    exact simple_of_adjacent r i q.val.1 q.val.2 l.val.1 l.val.2
      ((B.positive_iff q).mp hAlpha) ((B.positive_iff l).mp hBeta) h

section Matrices

variable {R : Type u} [CommRing R]

private theorem prod_index {M : Type*} [CommMonoid M] (r : ℕ) (f : Index.{u} r → M) :
    (∏ i, f i) = ∏ i : Fin r, f ⟨i⟩ :=
  Fintype.prod_equiv Equiv.ulift f _ (fun _ => rfl)

private theorem determinantOneUnits_prod {r : ℕ} (a : Index.{u} r → Rˣ) :
    ∏ i, determinantOneUnits a i = 1 := by
  rw [prod_index, Fin.prod_univ_succ]
  change (∏ j, a j)⁻¹ * (∏ j : Fin r, a ⟨j⟩) = 1
  rw [← prod_index r a, inv_mul_cancel]

private theorem determinantOneUnits_succ {r : ℕ} (a : Index.{u} r → Rˣ) (j : Index.{u} r) :
    determinantOneUnits a ⟨j.down.succ⟩ = a j := rfl

private theorem determinantOneUnits_mul {r : ℕ} (a b : Index.{u} r → Rˣ) :
    determinantOneUnits (a * b) = determinantOneUnits a * determinantOneUnits b := by
  funext i
  obtain ⟨j⟩ := i
  refine Fin.cases ?_ (fun _ => rfl) j
  change (∏ i, a i * b i)⁻¹ = (∏ i, a i)⁻¹ * (∏ i, b i)⁻¹
  rw [Finset.prod_mul_distrib, mul_inv_rev, mul_comm]

private theorem determinantOneUnits_map {S : Type u} [CommRing S] (f : R →+* S)
    {r : ℕ} (a : Index.{u} r → Rˣ) (i : Index.{u} (r + 1)) :
    determinantOneUnits (fun j => Units.map f.toMonoidHom (a j)) i =
      Units.map f.toMonoidHom (determinantOneUnits a i) := by
  obtain ⟨j⟩ := i
  refine Fin.cases ?_ (fun _ => rfl) j
  change (∏ i, Units.map f.toMonoidHom (a i))⁻¹ =
    Units.map f.toMonoidHom ((∏ i, a i)⁻¹)
  rw [map_inv, map_prod]

private theorem determinantOneUnits_of_prod_eq_one {r : ℕ} (a : Index.{u} (r + 1) → Rˣ)
    (ha : ∏ i, a i = 1) : determinantOneUnits (fun i => a ⟨i.down.succ⟩) = a := by
  funext i
  obtain ⟨j⟩ := i
  refine Fin.cases ?_ (fun _ => rfl) j
  rw [prod_index, Fin.prod_univ_succ, ← prod_index r (fun j => a ⟨j.down.succ⟩)] at ha
  exact (eq_inv_of_mul_eq_one_left ha).symm

variable {idx : Type*} [Fintype idx] [DecidableEq idx]

private def diagonalSL (d : idx → Rˣ) (h : ∏ i, d i = 1) : Matrix.SpecialLinearGroup idx R :=
  ⟨Matrix.diagonal fun i => (d i : R), by
    rw [Matrix.det_diagonal]
    exact (map_prod (Units.coeHom R) _ _).symm.trans (congrArg Units.val h)⟩

private def diagonalEmbedding (r : ℕ) : (Index.{u} r → Rˣ) →* Matrix.SpecialLinearGroup (Index.{u} (r + 1)) R :=
  MonoidHom.mk' (fun a => diagonalSL (determinantOneUnits a) (determinantOneUnits_prod a))
    (fun a b => by
      apply Subtype.ext
      change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
      rw [Matrix.diagonal_mul_diagonal]
      exact congrArg (fun t : Index.{u} (r + 1) → Rˣ =>
        Matrix.diagonal fun i => (t i : R)) (determinantOneUnits_mul a b))

private theorem diagonalEmbedding_map {S : Type u} [CommRing S] (f : R →+* S)
    (r : ℕ) (a : Index.{u} r → Rˣ) :
    diagonalEmbedding r (fun i => Units.map f.toMonoidHom (a i)) =
      Matrix.SpecialLinearGroup.map f (diagonalEmbedding r a) := by
  apply Subtype.ext
  change Matrix.diagonal _ = (Matrix.diagonal _).map f
  rw [Matrix.diagonal_map (map_zero f)]
  exact congrArg Matrix.diagonal (funext fun i =>
    congrArg Units.val (determinantOneUnits_map f a i))


private theorem coordinatePairUnits_prod {i j : idx} (hij : i ≠ j) (a : Rˣ) :
    ∏ l, coordinatePairUnits i j a l = 1 := by
  have h (l : idx) : coordinatePairUnits i j a l =
      (if l = i then a else 1) * (if l = j then a⁻¹ else 1) := by
    by_cases h : l = i
    · subst l
      simp [coordinatePairUnits, hij]
    · simp [coordinatePairUnits, h]
  simp_rw [h, Finset.prod_mul_distrib]
  simp


private theorem transvectionWord_entries {i j : idx} (hij : i ≠ j) (a : Rˣ) :
    (transvectionWord hij a).val =
      Matrix.diagonal (fun l => if l = i ∨ l = j then 0 else 1) +
        Matrix.single i j (a : R) + Matrix.single j i (-(↑a⁻¹ : R)) := by
  change ((1 + Matrix.single i j (a : R)) * (1 + Matrix.single j i (-(↑a⁻¹ : R)))) *
    (1 + Matrix.single i j (a : R)) = _
  have h₁ : (a : R) * (-(↑a⁻¹ : R)) = -1 := by simp
  have h₂ : (-(↑a⁻¹ : R)) * (a : R) = -1 := by simp
  have hzero : Matrix.single i j (a : R) * Matrix.single i j (a : R) = 0 :=
    Matrix.single_mul_single_of_ne _ i j i hij.symm _
  simp only [Matrix.mul_add, Matrix.add_mul, one_mul, mul_one, Matrix.single_mul_single_same,
    hzero, h₁, h₂, neg_one_mul, add_zero]
  have hdiag : (1 : Matrix idx idx R) + Matrix.single i i (-1) + Matrix.single j j (-1) =
      Matrix.diagonal (fun l => if l = i ∨ l = j then 0 else 1) := by
    ext l m
    by_cases hlm : l = m
    · subst m
      by_cases hl : l = i <;> by_cases hl' : l = j
      <;> simp_all [Matrix.single, eq_comm]
    · have hi : ¬(i = l ∧ i = m) := fun ⟨h, h'⟩ => hlm (h.symm.trans h')
      have hj : ¬(j = l ∧ j = m) := fun ⟨h, h'⟩ => hlm (h.symm.trans h')
      simp [Matrix.single, hlm, hi, hj]
  rw [← hdiag, ← Matrix.single_neg i j (a : R)]
  abel

private theorem normalizedTransvectionWord {i j : idx} (hij : i ≠ j) (a : Rˣ) :
    transvectionWord hij a * (transvectionWord hij 1)⁻¹ =
      diagonalSL (coordinatePairUnits i j a) (coordinatePairUnits_prod hij a) := by
  apply (mul_inv_eq_iff_eq_mul).2
  apply Subtype.ext
  change (transvectionWord hij a).val =
    Matrix.diagonal (fun l => (coordinatePairUnits i j a l : R)) * (transvectionWord hij 1).val
  rw [transvectionWord_entries, transvectionWord_entries]
  ext l m
  rw [Matrix.diagonal_mul]
  by_cases hl : l = i
  · subst l
    by_cases hm : m = j <;>
      simp [coordinatePairUnits, hij, hij.symm, hm, Ne.symm, Matrix.single, Matrix.diagonal_apply]
  · by_cases hl' : l = j
    · subst l
      by_cases hm : m = i <;>
        simp [coordinatePairUnits, hij, hij.symm, hm, Ne.symm, Matrix.single, Matrix.diagonal_apply]
    · simp [coordinatePairUnits, hl, hl', Ne.symm, Matrix.single, Matrix.diagonal_apply]

private theorem diagonalEntries_of_commutes {g : Matrix.SpecialLinearGroup idx R}
    (h : ∀ {i j : idx} (hij : i ≠ j),
      let t : (LaurentPolynomial R)ˣ := (LaurentPolynomial.isUnit_T 1).unit
      let d := diagonalSL (coordinatePairUnits i j t) (coordinatePairUnits_prod hij t)
      Matrix.SpecialLinearGroup.map LaurentPolynomial.C g * d =
        d * Matrix.SpecialLinearGroup.map LaurentPolynomial.C g) :
    ∀ i j, i ≠ j → g.val i j = 0 := by
  intro i j hij
  let B := LaurentPolynomial R
  let t : Bˣ := (LaurentPolynomial.isUnit_T 1).unit
  let d := Matrix.diagonal (fun l => (coordinatePairUnits i j t l : B))
  have ht : (t : B) = LaurentPolynomial.T 1 := IsUnit.unit_spec _
  have ht' : (↑t⁻¹ : B) = LaurentPolynomial.T (-1) := by
    let v : Bˣ := (LaurentPolynomial.isUnit_T (-1)).unit
    have hv : (v : B) = LaurentPolynomial.T (-1) := IsUnit.unit_spec _
    have hv' : t * v = 1 := by
      apply Units.ext
      change (t : B) * (v : B) = 1
      rw [ht, hv, ← LaurentPolynomial.T_add]
      simp
    exact congrArg Units.val (eq_inv_of_mul_eq_one_right hv').symm
  have hh := congrArg (fun m : Matrix.SpecialLinearGroup idx B => m.val i j) (h hij)
  change ((g.val.map LaurentPolynomial.C) * d) i j =
    (d * (g.val.map LaurentPolynomial.C)) i j at hh
  change ((g.val.map LaurentPolynomial.C) *
      Matrix.diagonal (fun l => (coordinatePairUnits i j t l : B))) i j =
    (Matrix.diagonal (fun l => (coordinatePairUnits i j t l : B)) *
      (g.val.map LaurentPolynomial.C)) i j at hh
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at hh
  simp only [coordinatePairUnits, hij.symm, ite_false, ite_true, ht, ht'] at hh
  rw [mul_comm (LaurentPolynomial.T 1 : B), ← LaurentPolynomial.single_eq_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T] at hh
  have hc := congrArg (fun x : B => x.coeff 1) hh
  simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (show (1 : ℤ) ≠ -1 by decide)] using hc.symm


theorem normalizedWord_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    NormalizedWord.{u} := by
  intro R idx _ _ _ i j hij a
  exact congrArg Subtype.val (normalizedTransvectionWord hij a)

end Matrices

section DiagonalTorus

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}

private def diagonalPoints (r : ℕ) :
    multiplicativePowerPoints k (Index.{u} r) ⟶ specialLinearPoints k (Index.{u} (r + 1)) where
  app R := GrpCat.ofHom (diagonalEmbedding r)
  naturality R A f := by
    apply GrpCat.ext
    intro a
    exact diagonalEmbedding_map f.hom.toRingHom r a

private theorem diagonalEmbedding_surjective_on_diagonals
    {R : Type u} [CommRing R] (m : Matrix.SpecialLinearGroup (Index.{u} (r + 1)) R)
    (hm : ∀ i j, i ≠ j → m.val i j = 0) :
    ∃ a : Index.{u} r → Rˣ, diagonalEmbedding r a = m := by
  obtain ⟨d, hd⟩ := diagonal_units_surjective m.toGL hm
  have hval : Matrix.diagonal (fun i => (d i : R)) = m.val := by
    rw [← diagonalMatrixHom_val, hd]
    rfl
  have hprod : ∏ i, d i = 1 := by
    apply Units.ext
    rw [show (↑(∏ i, d i) : R) = ∏ i, (d i : R) from map_prod (Units.coeHom R) _ _,
      ← Matrix.det_diagonal, hval]
    exact m.property
  refine ⟨fun i => d ⟨i.down.succ⟩, Subtype.ext ?_⟩
  change Matrix.diagonal (fun i => (determinantOneUnits (fun j => d ⟨j.down.succ⟩) i : R)) = _
  rw [determinantOneUnits_of_prod_eq_one d hprod, hval]


private def determinantOnePoints (r : ℕ) : multiplicativePowerPoints k (Index.{u} r) ⟶
    multiplicativePowerPoints k (Index.{u} (r + 1)) where
  app R := GrpCat.ofHom (MonoidHom.mk' determinantOneUnits determinantOneUnits_mul)
  naturality R A f := by
    apply GrpCat.ext
    intro a
    exact funext (determinantOneUnits_map f.hom.toRingHom a)

private def diagonalTailPoints (r : ℕ) : multiplicativePowerPoints k (Index.{u} (r + 1)) ⟶
    multiplicativePowerPoints k (Index.{u} r) where
  app R := GrpCat.ofHom (MonoidHom.mk' (fun a i => a ⟨i.down.succ⟩) (fun _ _ => rfl))
  naturality R A f := by apply GrpCat.ext; intro a; rfl

private theorem determinantOneInclusion_closedImmersion (r : ℕ) :
    ∃ j : (Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)).val ⟶
        (Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} (r + 1))).val,
      IsClosedImmersion j.hom.hom.left ∧
        ∀ (R : TestAlgebra k) (x : Points (Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)).val.X R),
          (multiplicativePowerGroupPointsIso k (Index.{u} (r + 1))).hom.app R
              (Unipotent.onPoints j R x) =
            determinantOneUnits ((multiplicativePowerGroupPointsIso k (Index.{u} r)).hom.app R x) := by
  let P := Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)
  let Q := Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} (r + 1))
  let p := multiplicativePowerGroupPointsIso k (Index.{u} r)
  let q := multiplicativePowerGroupPointsIso k (Index.{u} (r + 1))
  let a := p.hom ≫ determinantOnePoints r ≫ q.inv
  let b := q.hom ≫ diagonalTailPoints r ≫ p.inv
  let j := (AffineAlgebraicGroup.groupHomEquiv P Q).symm a
  let l := (AffineAlgebraicGroup.groupHomEquiv Q P).symm b
  have ha (R : TestAlgebra k) (x : Points P.val.X R) :
      q.hom.app R (Unipotent.onPoints j R x) = determinantOneUnits (p.hom.app R x) := by
    have hj : Unipotent.onPoints j R x = a.app R x :=
      Unipotent.scheme_hom_spec a R x
    exact (congrArg (fun z : Points Q.val.X R => q.hom.app R z) hj).trans
      ((q.app R).groupIsoToMulEquiv.apply_symm_apply _)
  have hb (R : TestAlgebra k) (x : Points Q.val.X R) :
      p.hom.app R (Unipotent.onPoints l R x) = fun i => q.hom.app R x ⟨i.down.succ⟩ := by
    have hl : Unipotent.onPoints l R x = b.app R x :=
      Unipotent.scheme_hom_spec b R x
    exact (congrArg (fun z : Points P.val.X R => p.hom.app R z) hl).trans
      ((p.app R).groupIsoToMulEquiv.apply_symm_apply _)
  have hsec : j ≫ l = 𝟙 P.val := by
    apply Unipotent.group_hom_ext P.property.1
    intro R x
    apply (p.app R).groupIsoToMulEquiv.injective
    change p.hom.app R (Unipotent.onPoints l R (Unipotent.onPoints j R x)) = p.hom.app R x
    rw [hb, ha]
    funext i
    exact determinantOneUnits_succ _ i
  refine ⟨j, ?_, ha⟩
  haveI : IsAffine Q.val.X.left := Q.property.1
  haveI : IsSeparated Q.val.X.hom := IsSeparated.of_isAffineHom _
  haveI : IsSeparated (l.hom.hom.left ≫ P.val.X.hom) := Over.w l.hom.hom ▸ inferInstance
  haveI : IsSeparated l.hom.hom.left := IsSeparated.of_comp (g := P.val.X.hom) _
  haveI : IsClosedImmersion (j.hom.hom.left ≫ l.hom.hom.left) := by
    change IsClosedImmersion (j ≫ l).hom.hom.left
    rw [hsec]
    exact inferInstanceAs (IsClosedImmersion (𝟙 P.val.X.left))
  exact IsClosedImmersion.of_comp j.hom.hom.left l.hom.hom.left

private theorem inclusion_closedImmersion (s : SpecialMatrixPoints S (r + 1))
    (f : (Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)).val ⟶ S.val)
    (hf : ∀ (R : TestAlgebra k)
      (x : Points (Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)).val.X R),
      s.hom.app R (Unipotent.onPoints f R x) =
        diagonalEmbedding r ((multiplicativePowerGroupPointsIso k (Index.{u} r)).hom.app R x)) :
    IsClosedImmersion f.hom.hom.left := by
  let G := generalLinearGroup k (Index.{u} (r + 1))
  let e := generalLinearGroupPointsIso k (Index.{u} (r + 1))
  let P := Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)
  obtain ⟨i, hi, hS, _, _⟩ := generalLinearDerived k (r + 1) (Nat.succ_pos r) G S e s
  obtain ⟨j, hj, hD⟩ := determinantOneInclusion_closedImmersion (k := k) r
  obtain ⟨b, hb, hB⟩ := upper_inclusion e
  obtain ⟨d, hd, hd'⟩ := diagonal_in_upper k (r + 1)
  have he : f ≫ i = j ≫ d ≫ b := by
    apply Unipotent.group_hom_ext P.property.1
    intro R x
    simp only [Unipotent.onPoints_comp]
    apply (e.app R).groupIsoToMulEquiv.injective
    change e.hom.app R (Unipotent.onPoints i R (Unipotent.onPoints f R x)) =
      e.hom.app R (Unipotent.onPoints b R (Unipotent.onPoints d R (Unipotent.onPoints j R x)))
    rw [show ∀ w, e.hom.app R (Unipotent.onPoints i R w) =
      Matrix.SpecialLinearGroup.toGL (s.hom.app R w) from hS R, hf, hB, hd', hD]
    apply Units.ext
    rw [diagonalMatrixHom_val]
    rfl
  haveI : IsClosedImmersion (f.hom.hom.left ≫ i.hom.hom.left) := by
    change IsClosedImmersion (f ≫ i).hom.hom.left
    rw [he]
    letI := hj
    letI := hd
    letI := hb
    change IsClosedImmersion (j.hom.hom.left ≫ (d.hom.hom.left ≫ b.hom.hom.left))
    exact IsClosedImmersion.comp _ _
  exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left i.hom.hom.left

private theorem constructDiagonalTorus (s : SpecialMatrixPoints S (r + 1)) :
    ∃ T : DiagonalTorus s,
      T.subgroup.group = (Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)).val := by
  let P := Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} r)
  let p := multiplicativePowerGroupPointsIso k (Index.{u} r)
  let α := p.hom ≫ diagonalPoints r ≫ s.inv
  let f := (AffineAlgebraicGroup.groupHomEquiv P S).symm α
  have hf (R : TestAlgebra k) (x : Points P.val.X R) :
      s.hom.app R (Unipotent.onPoints f R x) = diagonalEmbedding r (p.hom.app R x) := by
    have ha : Unipotent.onPoints f R x = α.app R x :=
      Unipotent.scheme_hom_spec α R x
    exact (congrArg (fun z : Points S.val.X R => s.hom.app R z) ha).trans
      ((s.app R).groupIsoToMulEquiv.apply_symm_apply _)
  have hi : IsClosedImmersion f.hom.hom.left := inclusion_closedImmersion s f hf
  let T : ClosedSubgroup S.val := ⟨P.val, f, hi⟩
  refine ⟨⟨T, p, ⟨r, ⟨Iso.refl _⟩⟩, ?_, ?_⟩, rfl⟩
  · intro R x
    exact congrArg Subtype.val (hf R x)
  · intro R x
    change (∃ y : Points P.val.X R, Unipotent.onPoints f R y = x) ↔ _
    constructor
    · rintro ⟨y, rfl⟩
      rw [hf]
      intro i j hij
      exact Matrix.diagonal_apply_ne _ hij
    · intro hx
      obtain ⟨a, ha⟩ := diagonalEmbedding_surjective_on_diagonals (s.hom.app R x) hx
      let y := (p.app R).groupIsoToMulEquiv.symm a
      refine ⟨y, (s.app R).groupIsoToMulEquiv.injective ?_⟩
      change s.hom.app R (Unipotent.onPoints f R y) = s.hom.app R x
      rw [hf, show p.hom.app R y = a from (p.app R).groupIsoToMulEquiv.apply_symm_apply _, ha]

private theorem diagonalTorus_isCentralizer (s : SpecialMatrixPoints S (r + 1))
    (T : DiagonalTorus s) :
    RepresentsSubgroup T.subgroup (fun _ g => Centralizes T.subgroup.inclusion g) := by
  let A := Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup
  obtain ⟨C, hC⟩ := centralizerScheme k S T.subgroup
  let B := Specs.Unipotent.closedSubgroupAlgebraicGroup C
  have htest (R : TestAlgebra k) (g : Points S.val.X R) :
      g ∈ SubgroupSections C ((testSpec k).obj (op R)) ↔
        g ∈ SubgroupSections T.subgroup ((testSpec k).obj (op R)) := by
    rw [T.range]
    change (∃ c : Points C.group.X R, c ≫ C.inclusion.hom.hom = g) ↔ _
    rw [← hC]
    change Centralizes T.subgroup.inclusion g ↔ _
    rw [centralizes_iff_testAlgebras T.subgroup.inclusion A.property.1]
    have heval (P : TestAlgebra k) (f : R ⟶ P) :
        s.hom.app P (mapPoints f g) =
          Matrix.SpecialLinearGroup.map f.hom.toRingHom (s.hom.app R g) :=
      congrArg (fun τ => τ g) (s.hom.naturality f)
    constructor
    · intro hg
      apply diagonalEntries_of_commutes
      intro i j hij
      let L := LaurentPolynomial R
      letI : Algebra k L := ((algebraMap R L).comp (algebraMap k R)).toAlgebra
      let P : TestAlgebra k := CommAlgCat.of k L
      let f : R ⟶ P := CommAlgCat.ofHom
        { toRingHom := LaurentPolynomial.C
          commutes' := fun _ => rfl }
      let t : Lˣ := (LaurentPolynomial.isUnit_T 1).unit
      let m := diagonalSL (coordinatePairUnits i j t) (coordinatePairUnits_prod hij t)
      let x := (s.app P).groupIsoToMulEquiv.symm m
      have hx : s.hom.app P x = m := (s.app P).groupIsoToMulEquiv.apply_symm_apply _
      have hdiag : x ∈ SubgroupSections T.subgroup ((testSpec k).obj (op P)) := by
        rw [T.range, hx]
        intro i j hij
        exact Matrix.diagonal_apply_ne _ hij
      obtain ⟨y, hy⟩ := hdiag
      change Unipotent.onPoints T.subgroup.inclusion P y = x at hy
      have h := ((hg P f y).map (s.app P).groupIsoToMulEquiv).eq
      change s.hom.app P (mapPoints f g) *
          s.hom.app P (Unipotent.onPoints T.subgroup.inclusion P y) =
        s.hom.app P (Unipotent.onPoints T.subgroup.inclusion P y) *
          s.hom.app P (mapPoints f g) at h
      rw [heval, hy, hx] at h
      exact h
    · intro hg P f y
      let x := Unipotent.onPoints T.subgroup.inclusion P y
      have hd := (T.range P x).mp ⟨y, rfl⟩
      apply (s.app P).groupIsoToMulEquiv.injective
      simp only [map_mul]
      change s.hom.app P (mapPoints f g) * s.hom.app P x =
        s.hom.app P x * s.hom.app P (mapPoints f g)
      rw [heval]
      apply Subtype.ext
      change (s.hom.app R g).val.map f.hom * (s.hom.app P x).val =
        (s.hom.app P x).val * (s.hom.app R g).val.map f.hom
      have eqDiag (m : Matrix (Index.{u} (r + 1)) (Index.{u} (r + 1)) P)
          (h : ∀ i j, i ≠ j → m i j = 0) :
          m = Matrix.diagonal (fun i => m i i) := by
        ext i j
        by_cases hij : i = j
        · subst j
          rw [Matrix.diagonal_apply_eq]
        · rw [h i j hij, Matrix.diagonal_apply_ne _ hij]
      rw [eqDiag ((s.hom.app R g).val.map f.hom)
          (fun i j hij => by rw [Matrix.map_apply, hg i j hij, map_zero]),
        eqDiag _ hd]
      exact (Matrix.commute_diagonal _ _).eq
  obtain ⟨p, hp⟩ := Unipotent.factor_through_closed (A := B) (B := A) (C := S)
    C.inclusion T.subgroup.inclusion T.subgroup.isClosedImmersion
    (fun R x => (htest R _).mp ⟨x, rfl⟩)
  obtain ⟨q, hq⟩ := Unipotent.factor_through_closed (A := A) (B := B) (C := S)
    T.subgroup.inclusion C.inclusion C.isClosedImmersion
    (fun R x => (htest R _).mpr ⟨x, rfl⟩)
  intro X g
  rw [hC]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x ≫ p.hom.hom, (Category.assoc _ _ _).trans
      (congrArg (fun f : C.group ⟶ S.val => x ≫ f.hom.hom) hp)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x ≫ q.hom.hom, (Category.assoc _ _ _).trans
      (congrArg (fun f : T.subgroup.group ⟶ S.val => x ≫ f.hom.hom) hq)⟩

theorem splitDiagonalTorus_conditional
    (_ : AdjointForm.{u}) (_ : LatticeCriterion.{u}) (_ : SplitCover.{u}) :
    SplitDiagonalTorus.{u} := by
  intro k _ r S s
  obtain ⟨T, he⟩ := constructDiagonalTorus s
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  obtain ⟨hK, hC⟩ := centralizerSchemeBaseChange k K T.subgroup.inclusion T.subgroup
    (diagonalTorus_isCentralizer s T)
  refine ⟨T, hK, maxTorus_of_self_centralizer (baseChangedSubgroup K T.subgroup hK) ?_ hC⟩
  let e : (baseChangedSubgroup K T.subgroup hK).group ≅
      (Specs.StandardGroups.multiplicativePowerGroup K (Index.{u} r)).val :=
    F.mapIso (eqToIso he) ≪≫ baseChangePowerTorusIso K r
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    ⟨r, ⟨(groupBaseChange K K).mapIso e ≪≫ baseChangePowerTorusIso K r⟩⟩⟩

end DiagonalTorus

section Lattices

open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra)
open DiagonalizableGroups (groupAlgebraPointsIso)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue pairing)
open CocharacterDynamics (cocharacterPoint unitCoordinates unitPoint)
open private integerHomEquiv pointsIso_spec pointsIso_precompose
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private exponentsEquiv basis_expansion
  from LinearAlgebraicGroups.Affine.StandardGroups
open private splitGroupHomEquiv
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private integerExponent integerExponent_zpow charactersOfIso cocharactersOfIso homToDual
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isCommMonObj_of_groupIso from LinearAlgebraicGroups.Affine.HopfAlgebras

variable {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
  {s : SpecialMatrixPoints S (r + 1)}

private abbrev TailLattice (r : ℕ) := Multiplicative (Index.{u} r → ℤ)

private def tailModelPoints (r : ℕ) :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k (TailLattice.{u} r))) ≅
      multiplicativePowerPoints k (Index.{u} r) :=
  groupAlgebraPointsIso k (TailLattice.{u} r) ≪≫
    NatIso.ofComponents (fun R => (exponentsEquiv («ι» := Index.{u} r) R).toGrpIso) (by
      intro R A f
      apply GrpCat.ext
      intro a
      rfl)

private def tailModel (T : DiagonalTorus s) :
    T.subgroup.group ≅ specGroup (groupAlgebra k (TailLattice.{u} r)) := by
  letI : IsAffine T.subgroup.group.X.left :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup).property.1
  letI : IsAffine (specGroup (groupAlgebra k (TailLattice.{u} r))).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k (TailLattice.{u} r)))))
  exact groupIsoOfPointIso (T.pointsIso ≪≫ (tailModelPoints r).symm)

private theorem tailModel_apply (T : DiagonalTorus s) (R : TestAlgebra k)
    (t : GroupPoints T.subgroup.group R) :
    (tailModelPoints r).hom.app R (t ≫ (tailModel T).hom.hom.hom) =
      T.pointsIso.hom.app R t := by
  letI : IsAffine T.subgroup.group.X.left :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup).property.1
  have he := (groupHomEquiv T.subgroup.group (specGroup (groupAlgebra k (TailLattice.{u} r)))
    inferInstance).apply_symm_apply (T.pointsIso ≪≫ (tailModelPoints r).symm).hom
  change (groupPointsFunctor k).map (tailModel T).hom = _ at he
  have h := congrArg (fun f => (tailModelPoints r).hom.app R (f.app R t)) he
  exact h.trans (((tailModelPoints r).app R).groupIsoToMulEquiv.apply_symm_apply _)

private def liftTailIndex (r : ℕ) : (Fin r → ℤ) ≃ₗ[ℤ] Additive (TailLattice.{u} r) where
  toFun a := Additive.ofMul (Multiplicative.ofAdd (fun i => a i.down))
  invFun a i := a.toMul.toAdd ⟨i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def tailDualCoordinates (r : ℕ) :
    Additive (TailLattice.{u} r →* IntegerCharacters.{u}) ≃ₗ[ℤ] (Fin r → ℤ) :=
  (homToDual (TailLattice.{u} r)).trans
    (((Pi.basisFun ℤ (Index.{u} r)).dualBasis.equivFun).trans (liftTailIndex r).symm)

private theorem tailDualCoordinates_apply (f : TailLattice.{u} r →* IntegerCharacters.{u})
    (i : Fin r) :
    tailDualCoordinates r (Additive.ofMul f) i =
      integerExponent (f (Multiplicative.ofAdd (Pi.single ⟨i⟩ (1 : ℤ)))) := by
  simp only [tailDualCoordinates, LinearEquiv.trans_apply]
  change (Pi.basisFun ℤ (Index.{u} r)).dualBasis.equivFun (homToDual _ (Additive.ofMul f)) ⟨i⟩ = _
  rw [Module.Basis.dualBasis_equivFun, Pi.basisFun_apply]
  rfl

private def tailCharacter (T : DiagonalTorus s) : TailLattice.{u} r ≃* Character T.subgroup.group :=
  ((integerHomEquiv _).trans (splitGroupHomEquiv _ _)).trans (charactersOfIso (tailModel T).symm)

private def tailCocharacter (T : DiagonalTorus s) [IsCommMonObj T.subgroup.group.X] :
    (TailLattice.{u} r →* IntegerCharacters.{u}) ≃* Cocharacter T.subgroup.group :=
  (splitGroupHomEquiv _ _).trans (cocharactersOfIso (tailModel T).symm)

private theorem groupAlgebra_characterValue {H : GroupScheme k} (χ : Character H)
    (R : TestAlgebra k) (t : GroupPoints H R) :
    characterValue χ R t = (↑((show IntegerCharacters.{u} →* Rˣ from
      (groupAlgebraPointsIso k IntegerCharacters).hom.app R (t ≫ χ.hom.hom)) integerGenerator) : R) := by
  let e := hopfSpecPointIso (groupAlgebra k IntegerCharacters)
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app R)).2 (t ≫ χ.hom.hom)
  have hv := pointsIso_spec IntegerCharacters R a.ofConv integerGenerator
  unfold characterValue
  rw [← ha]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom a.ofConv).op)).unop.hom _ = _
  rw [Functor.FullyFaithful.preimage_map]
  exact hv.symm

private theorem tailCharacter_value (T : DiagonalTorus s) (R : TestAlgebra k)
    (t : GroupPoints T.subgroup.group R) (m : TailLattice.{u} r) :
    characterValue (tailCharacter T m) R t =
      ↑(∏ i : Index.{u} r, T.pointsIso.hom.app R t i ^ m.toAdd i) := by
  let x : GroupPoints (specGroup (groupAlgebra k (TailLattice.{u} r))) R :=
    t ≫ (tailModel T).hom.hom.hom
  let f : TailLattice.{u} r →* Rˣ := (groupAlgebraPointsIso k _).hom.app R x
  have hx (i : Index.{u} r) :
      f (Multiplicative.ofAdd (Pi.single i 1)) = T.pointsIso.hom.app R t i :=
    congrFun (tailModel_apply T R t) i
  rw [groupAlgebra_characterValue]
  congr 1
  change (show IntegerCharacters.{u} →* Rˣ from (groupAlgebraPointsIso k IntegerCharacters).hom.app R
    (x ≫ (specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap k
      (integerHomEquiv _ m))).hom.hom)) integerGenerator = _
  refine (pointsIso_precompose (integerHomEquiv _ m) R x integerGenerator).trans ?_
  change f (m ^ (1 : ℤ)) = _
  rw [zpow_one]
  conv_lhs => rw [← basis_expansion m, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow, hx]

private theorem tailCocharacter_value (T : DiagonalTorus s) [IsCommMonObj T.subgroup.group.X]
    (R : TestAlgebra k) (t : Rˣ) (f : TailLattice.{u} r →* IntegerCharacters.{u})
    (i : Index.{u} r) :
    T.pointsIso.hom.app R (cocharacterPoint (tailCocharacter T f) R t) i =
      t ^ tailDualCoordinates r (Additive.ofMul f) i.down := by
  let c := specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap k f)
  let x : GroupPoints (specGroup (groupAlgebra k (TailLattice.{u} r))) R := cocharacterPoint c R t
  have h : cocharacterPoint (tailCocharacter T f) R t ≫ (tailModel T).hom.hom.hom = x := by
    change (unitPoint R t ≫ c.hom.hom ≫ (tailModel T).inv.hom.hom) ≫ _ = _
    simp only [Category.assoc]
    rw [show (tailModel T).inv.hom.hom ≫ (tailModel T).hom.hom.hom = 𝟙 _ from
      (Grp.forget _).congr_map (tailModel T).inv_hom_id, Category.comp_id]
    rfl
  rw [← tailModel_apply T, h, tailDualCoordinates_apply]
  change (show TailLattice.{u} r →* Rˣ from (groupAlgebraPointsIso k (TailLattice.{u} r)).hom.app R
    (unitPoint R t ≫ c.hom.hom)) (Multiplicative.ofAdd (Pi.single i (1 : ℤ))) = _
  refine (pointsIso_precompose f R (unitPoint R t) (Multiplicative.ofAdd (Pi.single i 1))).trans ?_
  apply Units.ext
  refine (pointsIso_spec IntegerCharacters R (unitCoordinates R t)
    (f (Multiplicative.ofAdd (Pi.single i 1)))).trans ?_
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  rfl

private theorem determinantOne_monomial (R : Type u) [CommRing R]
    (t : Index.{u} r → Rˣ) (a : Fin (r + 1) → ℤ) :
    (∏ i : Index.{u} r, t i ^ (a i.down.succ - a 0)) =
      ∏ i : Fin (r + 1), determinantOneUnits t ⟨i⟩ ^ a i := by
  conv_rhs => rw [Fin.prod_univ_succ]
  change _ = ((∏ i, t i)⁻¹) ^ a 0 * ∏ j : Fin r, t ⟨j⟩ ^ a j.succ
  rw [← prod_index r (fun i => t i ^ a i.down.succ)]
  simp only [zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_zpow, inv_zpow, mul_comm]

private theorem determinantOne_powers (R : Type u) [CommRing R]
    (t : Rˣ) (y : CocharacterLattice (r + 1)) :
    determinantOneUnits (fun i : Index.{u} r => t ^ y.val i.down.succ) =
      fun i => t ^ y.val i.down := by
  apply determinantOneUnits_of_prod_eq_one (r := r) (fun i => t ^ y.val i.down)
  rw [prod_index]
  have hy : ∑ i : Fin (r + 1), y.val i = 0 := by
    have h : sumExponents (r + 1) y.val = 0 := y.property
    simpa only [sumExponents, LinearMap.sum_apply, LinearMap.proj_apply] using h
  calc
    (∏ i : Fin (r + 1), t ^ y.val i) =
        (zpowersHom Rˣ t) (∏ i : Fin (r + 1), Multiplicative.ofAdd (y.val i)) := by
      rw [map_prod]
      rfl
    _ = 1 := by rw [← ofAdd_sum, hy]; exact map_one (zpowersHom Rˣ t)

private theorem tailPairing (T : DiagonalTorus s) [IsCommMonObj T.subgroup.group.X]
    (m : TailLattice.{u} r) (f : TailLattice.{u} r →* IntegerCharacters.{u}) :
    pairing T.subgroup.group (tailCharacter T m) (tailCocharacter T f) =
      ∑ i : Fin r, m.toAdd ⟨i⟩ * tailDualCoordinates r (Additive.ofMul f) i := by
  have he : pairing T.subgroup.group (tailCharacter T m) (tailCocharacter T f) =
      integerExponent (f m) := by
    apply ((RootData.CharacterPairing.characterPairingComposition T.subgroup.group _ _).1 _).mp
    change (specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap k f) ≫ (tailModel T).inv) ≫
      ((tailModel T).hom ≫ specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap k
        (integerHomEquiv _ m))) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← specGroupMap_comp, Specs.CharacterPairing.powerMorphism]
    congr 1
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom k f).comp
      (MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv _ m)) =
        MonoidAlgebra.mapDomainBialgHom k
          ((zpowersHom IntegerCharacters (integerGenerator ^ integerExponent (f m))).comp
            MulEquiv.ulift.toMonoidHom)
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    congr 1
    apply MonoidHom.ext
    intro z
    change f (m ^ z.down.toAdd) = (integerGenerator ^ integerExponent (f m)) ^ z.down.toAdd
    have hb : (integerGenerator ^ integerExponent (f m)) = f m :=
      (integerExponent.apply_eq_iff_eq).mp (integerExponent_zpow _)
    rw [map_zpow, hb]
  rw [he]
  let b : Module.Basis (Index.{u} r) ℤ (Additive (TailLattice.{u} r)) := Pi.basisFun ℤ _
  let l := homToDual (TailLattice.{u} r) (Additive.ofMul f)
  calc
    integerExponent (f m) = l (Additive.ofMul m) := rfl
    _ = l (∑ i, m.toAdd i • b i) := by rw [← Module.Basis.sum_equivFun b (Additive.ofMul m)]; rfl
    _ = ∑ i : Index.{u} r, m.toAdd i * tailDualCoordinates r (Additive.ofMul f) i.down := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, tailDualCoordinates_apply, zsmul_eq_mul]
      have hi : (b i : Index.{u} r → ℤ) = Pi.single i 1 := Pi.basisFun_apply ℤ _ i
      rw [show b i = Additive.ofMul (Multiplicative.ofAdd (Pi.single i 1)) from hi]
      rfl
    _ = ∑ i : Fin r, m.toAdd ⟨i⟩ * tailDualCoordinates r (Additive.ofMul f) i :=
      ((Equiv.ulift.symm : Fin r ≃ Index.{u} r).sum_comp
        (fun i => m.toAdd i * tailDualCoordinates r (Additive.ofMul f) i.down)).symm

private def latticeIdentification (T : DiagonalTorus s) : LatticeIdentification T := by
  let hcomm : IsCommMonObj T.subgroup.group.X :=
    isCommMonObj_of_groupIso (tailModel T).symm inferInstance
  letI := hcomm
  let X : (Fin r → ℤ) ≃ₗ[ℤ] Additive (Character T.subgroup.group) :=
    (liftTailIndex r).trans (tailCharacter T).toAdditive.toIntLinearEquiv
  let Y₀ : Additive (TailLattice.{u} r →* IntegerCharacters.{u}) ≃ₗ[ℤ]
      Additive (Cocharacter T.subgroup.group) := (tailCocharacter T).toAdditive.toIntLinearEquiv
  let Y : Additive (Cocharacter T.subgroup.group) ≃ₗ[ℤ] (Fin r → ℤ) :=
    Y₀.symm.trans (tailDualCoordinates r)
  refine ⟨hcomm, X.symm.trans (characterCoordinates r).symm,
    Y.trans (cocharacterCoordinates r).symm, ?_, ?_, ?_⟩
  · intro a R t
    change characterValue (tailCharacter T (Multiplicative.ofAdd
      (fun i : Index.{u} r => a i.down.succ - a 0))) R t = _
    rw [tailCharacter_value]
    exact congrArg Units.val (determinantOne_monomial R _ a)
  · intro y R t
    let f : TailLattice.{u} r →* IntegerCharacters.{u} :=
      Additive.toMul ((tailDualCoordinates r).symm (cocharacterCoordinates r y))
    change (s.hom.app R
      (cocharacterPoint (tailCocharacter T f) R t ≫ T.subgroup.inclusion.hom.hom)).val = _
    rw [T.matrix]
    have hf : tailDualCoordinates r (Additive.ofMul f) = cocharacterCoordinates r y := by
      exact (tailDualCoordinates r).apply_symm_apply _
    have htail : T.pointsIso.hom.app R (cocharacterPoint (tailCocharacter T f) R t) =
        fun i : Index.{u} r => t ^ y.val i.down.succ := by
      funext i
      rw [tailCocharacter_value, hf]
      rfl
    rw [htail, determinantOne_powers]
  · intro χ c
    obtain ⟨m, rfl⟩ := (tailCharacter T).surjective χ
    obtain ⟨f, rfl⟩ := (tailCocharacter T).surjective c
    rw [dotPairing_in_coordinates]
    change _ = ∑ i : Fin r,
      (characterCoordinates r ((characterCoordinates r).symm
        (X.symm (Additive.ofMul (tailCharacter T m)))) i) *
      (cocharacterCoordinates r ((cocharacterCoordinates r).symm
        (Y (Additive.ofMul (tailCocharacter T f)))) i)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hx : X.symm (Additive.ofMul (tailCharacter T m)) =
        (liftTailIndex r).symm (Additive.ofMul m) := by
      apply X.injective
      simp only [X, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply]
      rfl
    have hy : Y (Additive.ofMul (tailCocharacter T f)) =
        tailDualCoordinates r (Additive.ofMul f) := by
      change tailDualCoordinates r (Y₀.symm (Y₀ (Additive.ofMul f))) = _
      rw [LinearEquiv.symm_apply_apply]
    rw [hx, hy]
    exact tailPairing T m f

end Lattices

section RootWeights

open Specs.AdjointRepresentation (GroupPoints constants dualMap scale)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue)

variable {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
  {s : SpecialMatrixPoints S (r + 1)}

private theorem matrixPoints_map {R A : TestAlgebra k}
    (f : R ⟶ A) (g : GroupPoints S.val R) :
    s.hom.app A (mapPoints f g) =
      Matrix.SpecialLinearGroup.map f.hom.toRingHom (s.hom.app R g) :=
  congrArg (fun τ => τ g) (s.hom.naturality f)

private theorem diagonalConjugate_apply {R : Type u} [CommRing R] {idx : Type*}
    [Fintype idx] [DecidableEq idx] {g m : Matrix.SpecialLinearGroup idx R} {d : idx → Rˣ}
    (hd : g.val = Matrix.diagonal fun i => (d i : R)) (i j : idx) :
    (g * m * g⁻¹).val i j = (d i : R) * m.val i j * (↑(d j)⁻¹ : R) := by
  have hprod : ∏ i, d i = 1 := by
    apply Units.ext
    change ((Units.coeHom R) (∏ i, d i)) = (1 : R)
    rw [map_prod, ← Matrix.det_diagonal]
    change (Matrix.diagonal (fun i => (d i : R))).det = 1
    rw [← hd]
    exact g.property
  let h := diagonalSL (fun i => (d i)⁻¹) (by rw [Finset.prod_inv_distrib, hprod, inv_one])
  have hi : g * h = 1 := by
    apply Subtype.ext
    change g.val * Matrix.diagonal _ = 1
    rw [hd, Matrix.diagonal_mul_diagonal]
    simp
  have hh : g⁻¹ = h := (eq_inv_of_mul_eq_one_right hi).symm
  change (g.val * m.val * (g⁻¹).val) i j = _
  rw [hh, hd]
  change (Matrix.diagonal (fun l => (d l : R)) * m.val *
    Matrix.diagonal (fun l => (↑(d l)⁻¹ : R))) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem slTangent_fst (v : Lie k S.val) (i j : Index.{u} (r + 1)) :
    ((s.hom.app (CommAlgCat.of k (DualNumber k)) v.toMul.val).val i j).fst =
      (1 : Matrix (Index.{u} (r + 1)) _ k) i j := by
  have hv : mapPoints (dualReduction k) v.toMul.val = 1 := v.toMul.property
  have hp := matrixPoints_map (s := s) (dualReduction k) v.toMul.val
  rw [hv, map_one] at hp
  exact congrArg (fun m : Matrix.SpecialLinearGroup (Index.{u} (r + 1)) k => m.val i j) hp.symm

private theorem slTangent_zero :
    slTangentCoefficient s (0 : Lie k S.val) = 0 := by
  ext i j
  let R := CommAlgCat.of k (DualNumber k)
  change (((s.hom.app R) (1 : GroupPoints S.val R)).val i j).snd = 0
  rw [map_one]
  change (((1 : Matrix (Index.{u} (r + 1)) _ (DualNumber k)) i j).snd) = 0
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem matrixWeight_iff (T : DiagonalTorus s) (χ : Character T.subgroup.group)
    (v : Lie k S.val) :
    v ∈ adjointWeightVectors T.subgroup χ ↔
      ∀ (R : TestAlgebra k) (t : GroupPoints T.subgroup.group R) (i j : Index.{u} (r + 1)),
        let d := determinantOneUnits (T.pointsIso.hom.app R t)
        (↑(d i * (d j)⁻¹) : R) * algebraMap k R (slTangentCoefficient s v i j) =
          characterValue χ R t * algebraMap k R (slTangentCoefficient s v i j) := by
  change (∀ (R : TestAlgebra k) (t : GroupPoints T.subgroup.group R), _) ↔ _
  refine forall_congr' (fun R => forall_congr' (fun t => ?_))
  let Q := CommAlgCat.of k (DualNumber R)
  let d := determinantOneUnits (T.pointsIso.hom.app R t)
  let a : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  let p := mapPoints (dualMap a) v.toMul.val
  let g := mapPoints (constants R) (t ≫ T.subgroup.inclusion.hom.hom)
  let A := slTangentCoefficient s v
  let b := characterValue χ R t
  change g * p * g⁻¹ = mapPoints (scale R b) p ↔
    ∀ i j, (↑(d i * (d j)⁻¹) : R) * algebraMap k R (A i j) = b * algebraMap k R (A i j)
  let D (i : Index.{u} (r + 1)) := Units.map (constants R).hom.toMonoidHom (d i)
  have hg : (s.hom.app Q g).val = Matrix.diagonal (fun i => (D i : DualNumber R)) := by
    change (s.hom.app Q (mapPoints (constants R) _)).val = _
    rw [matrixPoints_map, show (Matrix.SpecialLinearGroup.map _ _).val =
      (s.hom.app R (t ≫ T.subgroup.inclusion.hom.hom)).val.map (constants R).hom from rfl]
    rw [T.matrix, Matrix.diagonal_map (map_zero (constants R).hom)]
    rfl
  have hp (i j : Index.{u} (r + 1)) : (s.hom.app Q p).val i j =
      (if i = j then 1 else 0, algebraMap k R (A i j)) := by
    change (s.hom.app Q (mapPoints (dualMap a) _)).val i j = _
    rw [matrixPoints_map]
    apply TrivSqZeroExt.ext
    · change algebraMap k R ((s.hom.app (CommAlgCat.of k (DualNumber k)) v.toMul.val).val i j).fst = _
      rw [slTangent_fst]
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rfl
  have hleft (i j : Index.{u} (r + 1)) : (s.hom.app Q (g * p * g⁻¹)).val i j =
      (if i = j then 1 else 0, (↑(d i * (d j)⁻¹) : R) * algebraMap k R (A i j)) := by
    rw [map_mul, map_mul, map_inv, diagonalConjugate_apply hg, hp]
    rw [show (D j)⁻¹ = Units.map (constants R).hom.toMonoidHom ((d j)⁻¹) from
      (map_inv (Units.map (constants R).hom.toMonoidHom) (d j)).symm]
    apply TrivSqZeroExt.ext
    · change (d i : R) * (if i = j then 1 else 0) * (↑(d j)⁻¹ : R) =
        if i = j then 1 else 0
      by_cases h : i = j
      · subst j
        simp
      · simp [h]
    · change (((d i : R) * (if i = j then 1 else 0)) * (0 : R) +
          ((d i : R) * algebraMap k R (A i j) +
            (0 : R) * (if i = j then 1 else 0)) * (↑(d j)⁻¹ : R)) =
        ((d i : R) * (↑(d j)⁻¹ : R)) * algebraMap k R (A i j)
      ring
  have hright (i j : Index.{u} (r + 1)) :
      (s.hom.app Q (mapPoints (scale R b) p)).val i j =
        (if i = j then 1 else 0, b * algebraMap k R (A i j)) := by
    rw [matrixPoints_map]
    change (scale R b).hom ((s.hom.app Q p).val i j) = _
    rw [hp]
    rfl
  constructor
  · intro h i j
    have e := congrArg (fun z : GroupPoints S.val Q => ((s.hom.app Q z).val i j).snd) h
    rw [hleft, hright] at e
    exact e
  · intro h
    apply (s.app Q).groupIsoToMulEquiv.injective
    change s.hom.app Q (g * p * g⁻¹) = s.hom.app Q (mapPoints (scale R b) p)
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rw [hleft, hright, h]

private def matrixRootCharacter {T : DiagonalTorus s} (L : LatticeIdentification T)
    (i j : Fin (r + 1)) : Character T.subgroup.group :=
  Additive.toMul (L.characters.symm (root (r + 1) i j))

private theorem matrixRootCharacter_value {T : DiagonalTorus s} (L : LatticeIdentification T)
    (i j : Fin (r + 1)) (R : TestAlgebra k) (t : GroupPoints T.subgroup.group R) :
    let d := determinantOneUnits (T.pointsIso.hom.app R t)
    characterValue (matrixRootCharacter L i j) R t = (↑(d ⟨i⟩ * (d ⟨j⟩)⁻¹) : R) := by
  change characterValue (Additive.toMul (L.characters.symm ((determinantRelation (r + 1)).mkQ
    (coordinate (r + 1) i - coordinate (r + 1) j)))) R t = _
  rw [L.characterValue_eq]
  let d := fun l : Fin (r + 1) => determinantOneUnits (T.pointsIso.hom.app R t) ⟨l⟩
  have hp (l : Fin (r + 1)) : ∏ m : Fin (r + 1), d m ^ coordinate (r + 1) l m = d l := by
    rw [Finset.prod_eq_single l]
    · simp [coordinate]
    · intro a _ ha
      simp [coordinate, Pi.single_eq_of_ne ha]
    · simp
  congr 1
  change (∏ m : Fin (r + 1), d m ^ (coordinate (r + 1) i m - coordinate (r + 1) j m)) =
    d i * (d j)⁻¹
  simp_rw [zpow_sub]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hp, hp]

private theorem quotient_injective_on_sumZero (r : ℕ) :
    Function.Injective (fun y : CocharacterLattice (r + 1) =>
      (determinantRelation (r + 1)).mkQ y.val) := by
  intro y z h
  have hdiff (i : Fin (r + 1)) : y.val i - y.val 0 = z.val i - z.val 0 := by
    refine Fin.cases (by simp) (fun a => ?_) i
    simpa only [characterTail_mk] using
      congrArg (fun x => characterTail r x a) h
  apply cocharacters_eq_of_root_pairings r
  intro p
  rw [dotPairing_root, dotPairing_root]
  have hi := hdiff p.val.1
  have hj := hdiff p.val.2
  omega

private theorem matrixRoot_eq_iff (r : ℕ) (i j a b : Fin (r + 1)) (hij : i ≠ j) (hab : a ≠ b) :
    root (r + 1) i j = root (r + 1) a b ↔ i = a ∧ j = b := by
  constructor
  · intro h
    have he : coroot (r + 1) i j = coroot (r + 1) a b :=
      quotient_injective_on_sumZero r h
    have h₁ := congrArg (fun y : CocharacterLattice (r + 1) => y.val i) he
    have h₂ := congrArg (fun y : CocharacterLattice (r + 1) => y.val j) he
    change coordinate (r + 1) i i - coordinate (r + 1) j i =
      coordinate (r + 1) a i - coordinate (r + 1) b i at h₁
    change coordinate (r + 1) i j - coordinate (r + 1) j j =
      coordinate (r + 1) a j - coordinate (r + 1) b j at h₂
    simp only [coordinate, Pi.single_apply] at h₁ h₂
    constructor
    · by_contra hia
      simp only [hij, hia, ite_false, ite_true] at h₁
      split_ifs at h₁ <;> omega
    · by_contra hjb
      simp only [hjb, Ne.symm hij, ite_false, ite_true] at h₂
      split_ifs at h₂ <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem matrixRoot_ne_zero (r : ℕ) (i j : Fin (r + 1)) (hij : i ≠ j) :
    root (r + 1) i j ≠ 0 := by
  intro h
  have hz : coroot (r + 1) i j = 0 := quotient_injective_on_sumZero r
    (h.trans ((determinantRelation _).mkQ.map_zero).symm)
  have hval := congrArg (fun y : CocharacterLattice (r + 1) => y.val i) hz
  change coordinate (r + 1) i i - coordinate (r + 1) j i = 0 at hval
  simp [coordinate, Pi.single_eq_of_ne hij] at hval

private theorem characterOf_nonzero_entry {T : DiagonalTorus s} (L : LatticeIdentification T)
    {v : Lie k S.val} {χ : Character T.subgroup.group}
    (hv : v ∈ adjointWeightVectors T.subgroup χ)
    (i j : Index.{u} (r + 1)) (h : slTangentCoefficient s v i j ≠ 0) :
    χ = matrixRootCharacter L i.down j.down := by
  apply RootData.CharacterPairing.characterValuesDetectCharacters T.split
  intro R t
  have hval := (matrixWeight_iff T χ v).mp hv R t i j
  rw [matrixRootCharacter_value]
  exact ((isUnit_iff_ne_zero.mpr h).map (algebraMap k R)).mul_right_cancel hval.symm

private theorem matrixRootCharacter_self {T : DiagonalTorus s} (L : LatticeIdentification T)
    (i : Fin (r + 1)) : matrixRootCharacter L i i = 1 := by
  change Additive.toMul (L.characters.symm (root (r + 1) i i)) = _
  simp [root]

private theorem matrixRootCharacter_ne_one {T : DiagonalTorus s} (L : LatticeIdentification T)
    (i j : Fin (r + 1)) (hij : i ≠ j) : matrixRootCharacter L i j ≠ 1 := by
  intro h
  apply matrixRoot_ne_zero r i j hij
  have he := congrArg (fun x : Character T.subgroup.group => L.characters (Additive.ofMul x)) h
  change L.characters (L.characters.symm (root (r + 1) i j)) = L.characters 0 at he
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using he

private theorem matrixWeight_single {T : DiagonalTorus s} (L : LatticeIdentification T)
    (i j : Fin (r + 1)) (hij : i ≠ j) (v : Lie k S.val) :
    v ∈ adjointWeightVectors T.subgroup (matrixRootCharacter L i j) ↔
      ∃ a : k, slTangentCoefficient s v = Matrix.single ⟨i⟩ ⟨j⟩ a := by
  constructor
  · intro hv
    have hs (a b : Index.{u} (r + 1)) (hn : slTangentCoefficient s v a b ≠ 0) :
        a = ⟨i⟩ ∧ b = ⟨j⟩ := by
      have hχ := characterOf_nonzero_entry L hv a b hn
      have hab : a.down ≠ b.down := by
        intro he
        rw [he, matrixRootCharacter_self] at hχ
        exact matrixRootCharacter_ne_one L i j hij hχ
      have hroot : root (r + 1) i j = root (r + 1) a.down b.down :=
        L.characters.symm.injective (congrArg Additive.ofMul hχ)
      obtain ⟨ha, hb⟩ := (matrixRoot_eq_iff r i j a.down b.down hij hab).mp hroot
      exact ⟨ULift.ext ha.symm, ULift.ext hb.symm⟩
    refine ⟨slTangentCoefficient s v ⟨i⟩ ⟨j⟩, ?_⟩
    apply Matrix.ext
    intro a b
    by_cases h : a = ⟨i⟩ ∧ b = ⟨j⟩
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.single_apply_same]
    · have hz : slTangentCoefficient s v a b = 0 := by
        by_contra hn
        exact h (hs a b hn)
      rw [hz, Matrix.single_apply_of_ne _ _ _ _ _ (fun ⟨ha, hb⟩ => h ⟨ha.symm, hb.symm⟩)]
  · rintro ⟨c, hc⟩
    apply (matrixWeight_iff _ _ _).mpr
    intro R t a b
    rw [matrixRootCharacter_value, hc]
    by_cases ha : a = ⟨i⟩ <;> by_cases hb : b = ⟨j⟩
    · subst a
      subst b
      rfl
    all_goals simp [ha, hb, Ne.symm]

private theorem matrixRoot_identification {T : DiagonalTorus s} (L : LatticeIdentification T) :
    Nonempty (RootIdentification T L) := by
  let b := identityLieStructure S
  letI := b.lieRing
  letI := b.lieAlgebra
  obtain ⟨e, he, _⟩ :=
    LinearAlgebraicGroups.lieSpecialLinear k (Index.{u} (r + 1)) S s b
  have hinj : Function.Injective (slTangentCoefficient s) :=
    fun a b h => e.injective (Subtype.ext ((he a).trans (h.trans (he b).symm)))
  let f (p : RootIndices (r + 1)) := matrixRootCharacter L p.val.1 p.val.2
  have hf (p : RootIndices (r + 1)) : f p ∈ absoluteRoots T.subgroup := by
    let A : LinearMap.ker (Matrix.traceLinearMap (Index.{u} (r + 1)) k k) :=
      ⟨Matrix.single ⟨p.val.1⟩ ⟨p.val.2⟩ 1, by
        change (Matrix.single (⟨p.val.1⟩ : Index.{u} (r + 1)) ⟨p.val.2⟩ (1 : k)).trace = 0
        exact Matrix.trace_single_eq_of_ne _ _ _ (fun h => p.property (congrArg ULift.down h))⟩
    let v := e.symm A
    have hA : slTangentCoefficient s v = A.val := (he v).symm.trans (congrArg Subtype.val (e.apply_symm_apply A))
    refine ⟨matrixRootCharacter_ne_one L _ _ p.property, v,
      (matrixWeight_single L _ _ p.property v).mpr ⟨1, hA⟩, ?_⟩
    intro hz
    rw [hz, slTangent_zero (s := s)] at hA
    have hh := congrFun (congrFun hA (⟨p.val.1⟩ : Index.{u} (r + 1))) (⟨p.val.2⟩ : Index.{u} (r + 1))
    simp [A] at hh
  let f' (p : RootIndices (r + 1)) : Specs.AbstractPairing.Root T.subgroup := ⟨f p, hf p⟩
  refine ⟨⟨Equiv.ofBijective f' ⟨?_, ?_⟩, ?_, ?_⟩⟩
  · intro p q h
    have hroot : root (r + 1) p.val.1 p.val.2 = root (r + 1) q.val.1 q.val.2 :=
      L.characters.symm.injective (congrArg (fun z => Additive.ofMul z.val) h)
    obtain ⟨hi, hj⟩ := (matrixRoot_eq_iff r _ _ _ _ p.property q.property).mp hroot
    exact Subtype.ext (Prod.ext hi hj)
  · intro χ
    obtain ⟨hχ, v, hv, hn⟩ := χ.property
    have hA : slTangentCoefficient s v ≠ 0 := fun h => hn (hinj (h.trans (slTangent_zero (s := s)).symm))
    have hex : ∃ i j, slTangentCoefficient s v i j ≠ 0 := by
      by_contra! h
      exact hA (Matrix.ext h)
    obtain ⟨i, j, h⟩ := hex
    have hχ' := characterOf_nonzero_entry L hv i j h
    have hij : i.down ≠ j.down := by
      intro he
      rw [he, matrixRootCharacter_self] at hχ'
      exact hχ hχ'
    exact ⟨⟨(i.down, j.down), hij⟩, Subtype.ext hχ'.symm⟩
  · intro p
    exact L.characters.apply_symm_apply _
  · intro p v
    exact matrixWeight_single L _ _ p.property v

end RootWeights

section MatrixBorel

open CocharacterDynamics
  (LimitDecomposition cocharacterPoint polynomialAlgebra polynomialToLaurent polynomialEvaluate
    laurentAlgebra laurentConstants laurentParameter orbit HasExtension HasLimit)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsReductive)
open Specs.RankOneFlag (IsGeometricallyMaximal)

variable {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
  {s : SpecialMatrixPoints S (r + 1)}

private def laurentUnitPowers (R : TestAlgebra k) :
    Multiplicative ℤ →* (laurentAlgebra R)ˣ where
  toFun n :=
    ⟨LaurentPolynomial.T n.toAdd, LaurentPolynomial.T (-n.toAdd),
      by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
      by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩
  map_one' := Units.ext LaurentPolynomial.T_zero
  map_mul' m n := Units.ext (LaurentPolynomial.T_add m.toAdd n.toAdd)

private theorem laurentParameter_pow (R : TestAlgebra k) (n : ℤ) :
    (↑(laurentParameter R ^ n) : laurentAlgebra R) = LaurentPolynomial.T n := by
  have h : laurentUnitPowers R (Multiplicative.ofAdd 1) = laurentParameter R := Units.ext rfl
  have hp : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    change Multiplicative.ofAdd (n • (1 : ℤ)) = _
    simp
  have he := (map_zpow (laurentUnitPowers R) (Multiplicative.ofAdd 1) n)
  rw [h, hp] at he
  exact (congrArg Units.val he).symm

private def matrixCocharacter {T : DiagonalTorus s} (L : LatticeIdentification T)
    (y : CocharacterLattice (r + 1)) : Cocharacter T.subgroup.group :=
  letI := L.comm
  Additive.toMul (L.cocharacters.symm y)

private theorem matrixCocharacter_pairing {T : DiagonalTorus s} (L : LatticeIdentification T)
    (M : RootIdentification T L) (y : CocharacterLattice (r + 1)) (p : RootIndices (r + 1)) :
    pairing T.subgroup.group (M.indices p).val (matrixCocharacter L y) =
      y.val p.val.1 - y.val p.val.2 := by
  letI := L.comm
  rw [L.pairing_eq, M.character_eq, dotPairing_root]
  change (L.cocharacters (L.cocharacters.symm y)).val _ -
    (L.cocharacters (L.cocharacters.symm y)).val _ = _
  rw [LinearEquiv.apply_symm_apply]

private theorem matrixOrbit_entry {T : DiagonalTorus s} (L : LatticeIdentification T)
    (y : CocharacterLattice (r + 1)) (R : TestAlgebra k) (g : GroupPoints S.val R)
    (i j : Index.{u} (r + 1)) :
    (s.hom.app (laurentAlgebra R) (orbit (matrixCocharacter L y ≫ T.subgroup.inclusion) g)).val i j =
      LaurentPolynomial.C ((s.hom.app R g).val i j) *
        LaurentPolynomial.T (y.val i.down - y.val j.down) := by
  let P := laurentAlgebra R
  let a := laurentParameter R
  let c := matrixCocharacter L y
  let t := cocharacterPoint (c ≫ T.subgroup.inclusion) P a
  have ht : t = cocharacterPoint c P a ≫ T.subgroup.inclusion.hom.hom := by
    change ((groupPointsFunctor k).map (c ≫ T.subgroup.inclusion)).app P
        (CocharacterDynamics.unitPoint P a) =
      cocharacterPoint c P a ≫ T.subgroup.inclusion.hom.hom
    rw [Functor.map_comp]
    rfl
  have hdiag : (s.hom.app P t).val = Matrix.diagonal
      (fun l => (↑(a ^ y.val l.down) : P)) := ht ▸ L.cocharacterPoint_eq y P a
  let b₀ : GroupPoints S.val P := mapPoints (laurentConstants R) g
  change (s.hom.app P (t * b₀ * t⁻¹)).val i j = _
  rw [map_mul, map_mul, map_inv, diagonalConjugate_apply hdiag]
  change _ * (s.hom.app P (mapPoints (laurentConstants R) g)).val i j * _ = _
  rw [matrixPoints_map]
  let b : P := LaurentPolynomial.C ((s.hom.app R g).val i j)
  change (↑(a ^ y.val i.down) : P) * b * (↑((a ^ y.val j.down)⁻¹) : P) =
    b * LaurentPolynomial.T (y.val i.down - y.val j.down)
  rw [mul_comm (↑(a ^ y.val i.down) : P) b, mul_assoc, ← Units.val_mul, ← zpow_sub, laurentParameter_pow]

private theorem matrixExtension_iff {T : DiagonalTorus s} (L : LatticeIdentification T)
    (R : TestAlgebra k) (g : GroupPoints S.val R) :
    HasExtension (matrixCocharacter L (decreasingCocharacter r) ≫ T.subgroup.inclusion) g ↔
      (s.hom.app R g).val.IsUpperTriangular := by
  let c := matrixCocharacter L (decreasingCocharacter r) ≫ T.subgroup.inclusion
  let m := (s.hom.app R g).val
  let w (i j : Index.{u} (r + 1)) := decreasingVector r i.down - decreasingVector r j.down
  have hw (i j : Index.{u} (r + 1)) : w i j < 0 ↔ j < i := by
    change (r : ℤ) - 2 * (i.down.val : ℤ) - ((r : ℤ) - 2 * (j.down.val : ℤ)) < 0 ↔
      j.down.val < i.down.val
    omega
  have horbit (i j : Index.{u} (r + 1)) :
      (s.hom.app (laurentAlgebra R) (orbit c g)).val i j =
        LaurentPolynomial.C (m i j) * LaurentPolynomial.T (w i j) :=
    matrixOrbit_entry L (decreasingCocharacter r) R g i j
  constructor
  · rintro ⟨_, f, hf, _⟩
    intro i j hij
    have hh := congrArg (fun x : GroupPoints S.val (laurentAlgebra R) =>
      (s.hom.app (laurentAlgebra R) x).val i j) hf
    rw [matrixPoints_map, horbit] at hh
    change ((s.hom.app (polynomialAlgebra R) f).val i j).toLaurent =
      LaurentPolynomial.C (m i j) * LaurentPolynomial.T (w i j) at hh
    have hcoeff := congrArg (fun a : LaurentPolynomial R => a.coeff (w i j)) hh
    rw [CocharacterDynamics.coeff_toLaurent_neg _ ((hw i j).mpr hij),
      ← LaurentPolynomial.single_eq_C_mul_T] at hcoeff
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hcoeff.symm
  · intro hu
    let a : Matrix (Index.{u} (r + 1)) _ (Polynomial R) :=
      fun i j => if 0 ≤ w i j then Polynomial.C (m i j) * Polynomial.X ^ (w i j).toNat else 0
    have he : a.map Polynomial.toLaurent = (s.hom.app (laurentAlgebra R) (orbit c g)).val := by
      apply Matrix.ext
      intro i j
      rw [Matrix.map_apply, horbit]
      change Polynomial.toLaurent (if 0 ≤ w i j then
        Polynomial.C (m i j) * Polynomial.X ^ (w i j).toNat else 0) = _
      split_ifs with h
      · rw [Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg h]
      · rw [show m i j = 0 from hu ((hw i j).mp (lt_of_not_ge h)), map_zero, map_zero, zero_mul]
    have ha : a.det = 1 := by
      apply Polynomial.toLaurent_injective
      rw [(Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R).map_det a]
      change (a.map Polynomial.toLaurent).det = Polynomial.toLaurent 1
      rw [he, map_one]
      exact (s.hom.app (laurentAlgebra R) (orbit c g)).property
    let f := (s.app (polynomialAlgebra R)).groupIsoToMulEquiv.symm ⟨a, ha⟩
    refine ⟨mapPoints (polynomialEvaluate R 0) f, f, ?_, rfl⟩
    apply (s.app (laurentAlgebra R)).groupIsoToMulEquiv.injective
    change s.hom.app (laurentAlgebra R) (mapPoints (polynomialToLaurent R) f) = _
    rw [matrixPoints_map, show s.hom.app (polynomialAlgebra R) f = ⟨a, ha⟩ from
      (s.app (polynomialAlgebra R)).groupIsoToMulEquiv.apply_symm_apply _]
    exact Subtype.ext he

private theorem upperTriangularBorel_exists {T : DiagonalTorus s} {L : LatticeIdentification T}
    (M : RootIdentification T L) (hS : IsReductive S) (hT : IsGeometricallyMaximal T.subgroup) :
    Nonempty (UpperTriangularBorel T L M) := by
  let y := decreasingCocharacter r
  let c := matrixCocharacter L y
  have hpair (p : RootIndices (r + 1)) : pairing T.subgroup.group (M.indices p).val c =
      2 * ((p.val.2.val : ℤ) - p.val.1.val) := by
    rw [matrixCocharacter_pairing]
    change ((r : ℤ) - 2 * p.val.1.val) - ((r : ℤ) - 2 * p.val.2.val) = _
    ring
  have hc : Specs.BorelsAndChambers.IsRegular T.subgroup c := by
    intro α
    obtain ⟨p, rfl⟩ := M.indices.surjective α
    rw [hpair]
    have hne : p.val.1.val ≠ p.val.2.val := fun h => p.property (Fin.ext h)
    omega
  obtain ⟨D⟩ := CocharacterDynamics.existsLimitDecomposition S (c ≫ T.subgroup.inclusion)
  have hB := RootData.BorelsAndChambers.regularCocharacterBorel S hS
    T.subgroup T.split hT c hc D
  refine ⟨⟨hS, hT, y, rfl, D, hB.2.1, hB.2.2.1, ?_, ?_⟩⟩
  · intro R g
    exact (D.parabolic_points R g).symm.trans (matrixExtension_iff L R g)
  · intro p
    rw [hB.2.2.2.1]
    change 0 < pairing T.subgroup.group (M.indices p).val c ↔ _
    rw [hpair]
    change 0 < 2 * ((p.val.2.val : ℤ) - p.val.1.val) ↔ p.val.1.val < p.val.2.val
    omega

end MatrixBorel

section MatrixPinning

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue adjointWeightVectors)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.Pinning (RootCoordinate)
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open RootData.RootGroups (additivePoints)
open private additivePoints_add additivePoints_natural additiveLineGroup rootPoint_eq
  from LinearAlgebraicGroups.RootData.RootGroups
open private affine_tensor from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private comp_conjugateFamily from LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
  {s : SpecialMatrixPoints S (r + 1)}

private def elementaryPoints (A : AdditiveLine k) {i j : Index.{u} (r + 1)} (hij : i ≠ j) :
    (groupPointsFunctor k).obj A.group ⟶ specialLinearPoints k (Index.{u} (r + 1)) where
  app R := GrpCat.ofHom <| MonoidHom.mk'
    (fun a => Matrix.SpecialLinearGroup.transvection hij ((additivePoints A R).symm a))
    (by
      intro a b
      obtain ⟨a, rfl⟩ := (additivePoints A R).surjective a
      obtain ⟨b, rfl⟩ := (additivePoints A R).surjective b
      rw [← additivePoints_add, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact Subtype.ext (Matrix.transvection_mul_transvection_same (i := i) (j := j) hij a b).symm)
  naturality R B f := by
    apply GrpCat.ext
    intro x
    obtain ⟨a, rfl⟩ := (additivePoints A R).surjective x
    change Matrix.SpecialLinearGroup.transvection hij
        ((additivePoints A B).symm (mapPoints f (additivePoints A R a))) =
      Matrix.SpecialLinearGroup.map f.hom.toRingHom
        (Matrix.SpecialLinearGroup.transvection hij ((additivePoints A R).symm (additivePoints A R a)))
    rw [additivePoints_natural, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    apply Subtype.ext
    ext l m
    change Matrix.transvection i j (f.hom a) l m = f.hom (Matrix.transvection i j a l m)
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      map_add, apply_ite, map_one, map_zero]
    split_ifs <;> rfl

private def elementaryHom (A : AdditiveLine k) {i j : Index.{u} (r + 1)} (hij : i ≠ j) : A.group ⟶ S.val :=
  (AffineAlgebraicGroup.groupHomEquiv (additiveLineGroup A) S).symm
    (elementaryPoints A hij ≫ s.inv)

private theorem elementaryHom_point (A : AdditiveLine k) {i j : Index.{u} (r + 1)} (hij : i ≠ j)
    (R : TestAlgebra k) (a : R) :
    s.hom.app R (rootPoint (elementaryHom (s := s) A hij) R a) =
      Matrix.SpecialLinearGroup.transvection hij a := by
  have he := (AffineAlgebraicGroup.groupHomEquiv (additiveLineGroup A) S).apply_symm_apply
    (elementaryPoints A hij ≫ s.inv)
  have h := congrArg (fun τ => s.hom.app R (τ.app R (additivePoints A R a))) he
  rw [rootPoint_eq]
  change _ = Matrix.SpecialLinearGroup.transvection hij a
  refine h.trans ?_
  change (s.app R).groupIsoToMulEquiv
    ((s.app R).groupIsoToMulEquiv.symm
      (Matrix.SpecialLinearGroup.transvection hij ((additivePoints A R).symm (additivePoints A R a)))) = _
  rw [MulEquiv.apply_symm_apply, Equiv.symm_apply_apply]

private theorem elementaryHom_closed (A : AdditiveLine k) {i j : Index.{u} (r + 1)} (hij : i ≠ j) :
    IsClosedImmersion (elementaryHom (s := s) A hij).hom.hom.left := by
  apply RootData.RootGroups.isClosedImmersion_of_injectivePoints (additiveLineGroup A) S
  intro R a b h
  obtain ⟨a, rfl⟩ := (additivePoints A R).surjective a
  obtain ⟨b, rfl⟩ := (additivePoints A R).surjective b
  have he : rootPoint (elementaryHom (s := s) A hij) R a =
      rootPoint (elementaryHom (s := s) A hij) R b := by
    simpa only [rootPoint_eq] using h
  have h' := congrArg (fun x => (s.hom.app R x).val i j) he
  rw [elementaryHom_point, elementaryHom_point] at h'
  change (1 + Matrix.single i j a) i j = (1 + Matrix.single i j b) i j at h'
  have hab : a = b := by simpa [Matrix.one_apply_ne hij] using h'
  rw [hab]

private theorem matrixTransvection_scalar {T : DiagonalTorus s} (L : LatticeIdentification T)
    {A : AdditiveLine k} (f : A.group ⟶ S.val) (i j : Fin (r + 1))
    (hf : ∀ (R : TestAlgebra k) (a : R),
      (s.hom.app R (rootPoint f R a)).val = 1 + Matrix.single ⟨i⟩ ⟨j⟩ a) :
    HasScalarAction T.subgroup (matrixRootCharacter L i j) f := by
  intro R t a
  let d := determinantOneUnits (T.pointsIso.hom.app R t)
  let g : GroupPoints S.val R := t ≫ T.subgroup.inclusion.hom.hom
  change g * rootPoint f R a * g⁻¹ =
    rootPoint f R (characterValue (matrixRootCharacter L i j) R t * a)
  apply (s.app R).groupIsoToMulEquiv.injective
  change s.hom.app R (g * rootPoint f R a * g⁻¹) = s.hom.app R (rootPoint f R _)
  rw [map_mul, map_mul, map_inv]
  apply Subtype.ext
  apply Matrix.ext
  intro l m
  rw [diagonalConjugate_apply (T.matrix R t), hf, hf, matrixRootCharacter_value]
  change (d l : R) * (1 + Matrix.single ⟨i⟩ ⟨j⟩ a) l m * (↑(d m)⁻¹ : R) =
    (1 + Matrix.single ⟨i⟩ ⟨j⟩ ((↑(d ⟨i⟩ * (d ⟨j⟩)⁻¹) : R) * a)) l m
  have hd : (d l : R) * (1 : Matrix (Index.{u} (r + 1)) _ R) l m * (↑(d m)⁻¹ : R) =
      (1 : Matrix (Index.{u} (r + 1)) _ R) l m := by
    by_cases hlm : l = m
    · subst m
      simp
    · simp [Matrix.one_apply_ne hlm]
  rw [Matrix.add_apply, Matrix.add_apply, mul_add, add_mul, hd]
  congr 1
  by_cases hl : l = ⟨i⟩ <;> by_cases hm : m = ⟨j⟩
  · subst l
    subst m
    simp only [Matrix.single_apply_same, Units.val_mul]
    ring
  all_goals simp [hl, hm, Ne.symm]

private theorem conjugatesInto_of_affine_points {A H : GroupScheme k}
    {Y : SchemeOver k} (f : A ⟶ H) (g : Y ⟶ H.X) [IsAffine A.X.left] [IsAffine Y.left]
    (h : ∀ (R : TestAlgebra k) (t : Points Y R) (x : GroupPoints A R),
      let z : GroupPoints H R := t ≫ g
      let v : GroupPoints H R := x ≫ f.hom.hom
      ∃ y : GroupPoints A R, y ≫ f.hom.hom = z * v * z⁻¹) :
    ConjugateLe f g := by
  obtain ⟨P, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr
    (show IsAffine (A.X ⊗ Y).left from affine_tensor)
  obtain ⟨x, hx⟩ := h P.unop (e.hom ≫ snd A.X Y) (e.hom ≫ fst A.X Y)
  refine ⟨e.inv ≫ x, (cancel_epi e.hom).mp ?_⟩
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, comp_conjugateFamily] using hx

private theorem normalizes_of_scalar {T : DiagonalTorus s} (A : AdditiveLine k)
    (f : A.group ⟶ S.val) (hf : IsClosedImmersion f.hom.hom.left)
    {χ : Character T.subgroup.group} (h : HasScalarAction T.subgroup χ f) :
    Normalizes f T.subgroup.inclusion.hom.hom := by
  letI : IsAffine A.group.X.left := (additiveLineGroup A).property.1
  letI : IsAffine T.subgroup.group.X.left :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup).property.1
  apply (normalizesIff k f hf _ _).mpr
  have hconj (R : TestAlgebra k) (t : GroupPoints T.subgroup.group R)
      (x : GroupPoints A.group R) :
      let z : GroupPoints S.val R := t ≫ T.subgroup.inclusion.hom.hom
      let v : GroupPoints S.val R := x ≫ f.hom.hom
      ∃ y : GroupPoints A.group R, y ≫ f.hom.hom = z * v * z⁻¹ := by
    obtain ⟨a, rfl⟩ := (additivePoints A R).surjective x
    refine ⟨additivePoints A R (characterValue χ R t * a), ?_⟩
    simpa only [rootPoint_eq] using (h R t a).symm
  refine ⟨conjugatesInto_of_affine_points f _ hconj, conjugatesInto_of_affine_points f _ ?_⟩
  intro R t x
  have ht : (t⁻¹ : GroupPoints T.subgroup.group R) ≫ T.subgroup.inclusion.hom.hom =
      t ≫ (T.subgroup.inclusion.hom.hom)⁻¹ := by
    rw [GrpObj.inv_comp, GrpObj.comp_inv]
  simpa only [ht] using hconj R t⁻¹ x

private theorem elementaryHom_weight {T : DiagonalTorus s} (L : LatticeIdentification T)
    (A : AdditiveLine k) (i j : Fin (r + 1)) (hij : i ≠ j)
    (h := show (⟨i⟩ : Index.{u} (r + 1)) ≠ ⟨j⟩ from fun h => hij (congrArg ULift.down h)) :
    Set.range (mapPointKernel (elementaryHom (s := s) A h)) ⊆
      adjointWeightVectors T.subgroup (matrixRootCharacter L i j) := by
  rintro _ ⟨v, rfl⟩
  apply (matrixWeight_single L i j hij _).mpr
  let R := CommAlgCat.of k (DualNumber k)
  obtain ⟨a, ha⟩ := (additivePoints A R).surjective v.toMul.val
  refine ⟨a.snd, ?_⟩
  have hmat := elementaryHom_point (s := s) A h R a
  rw [rootPoint_eq, ha] at hmat
  ext l m
  change (((s.hom.app R) (v.toMul.val ≫ (elementaryHom (s := s) A h).hom.hom)).val l m).snd = _
  rw [hmat]
  change (((1 : Matrix (Index.{u} (r + 1)) (Index.{u} (r + 1)) (DualNumber k)) +
    Matrix.single (⟨i⟩ : Index.{u} (r + 1)) (⟨j⟩ : Index.{u} (r + 1)) a) l m).snd = _
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, TrivSqZeroExt.snd_add]
  split_ifs <;> simp

private theorem hasTransvectionPinning {T : DiagonalTorus s} {L : LatticeIdentification T}
    {M : RootIdentification T L} (B : UpperTriangularBorel T L M) :
    HasTransvectionPinning B := by
  let A := Classification.Pinning.standardAdditiveLine k
  have hsm : Smooth A.group.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (show Algebra.Smooth k (Polynomial k) from ⟨inferInstance, inferInstance⟩))
  let f (p : RootIndices (r + 1)) := elementaryHom (s := s) A
    (show (⟨p.val.1⟩ : Index.{u} (r + 1)) ≠ ⟨p.val.2⟩ from fun h => p.property (congrArg ULift.down h))
  have hf (p : RootIndices (r + 1)) : IsClosedImmersion (f p).hom.hom.left :=
    elementaryHom_closed A _
  have hχ (p : RootIndices (r + 1)) : (M.indices p).val = matrixRootCharacter L p.val.1 p.val.2 := by
    exact Additive.ofMul.injective (L.characters.injective
      ((M.character_eq p).trans (L.characters.apply_symm_apply _).symm))
  have ha (p : RootIndices (r + 1)) : HasScalarAction T.subgroup (M.indices p).val (f p) :=
    (hχ p).symm ▸ matrixTransvection_scalar L (f p) p.val.1 p.val.2
      (fun R a => congrArg Subtype.val (elementaryHom_point (s := s) A _ R a))
  let U₀ (p : RootIndices (r + 1)) : ClosedSubgroup S.val := ⟨A.group, f p, hf p⟩
  have hU (p : RootIndices (r + 1)) : IsRootSubgroup T.subgroup (U₀ p) (M.indices p).val := by
    exact ⟨hsm, ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨Iso.refl _⟩⟩,
      normalizes_of_scalar A _ (hf p) (ha p),
      (hχ p).symm ▸ elementaryHom_weight L A p.val.1 p.val.2 p.property⟩
  have hα (α : Specs.AbstractPairing.Root T.subgroup) :
      (M.indices (M.indices.symm α)).val = α.val :=
    congrArg Subtype.val (M.indices.apply_symm_apply α)
  let U : RootSubgroupFamily T.subgroup := fun α =>
    ⟨U₀ (M.indices.symm α), hα α ▸ hU (M.indices.symm α)⟩
  let x (α : Specs.AbstractPairing.Root T.subgroup) : RootCoordinate A T.subgroup (U α).val α.val :=
    ⟨Iso.refl _, by
      change HasScalarAction T.subgroup α.val (𝟙 A.group ≫ f (M.indices.symm α))
      rw [Category.id_comp, ← hα α]
      exact ha (M.indices.symm α)⟩
  refine ⟨A, U, x, ?_, fun α => x α.val, fun _ => rfl⟩
  intro p R a
  change (s.hom.app R (rootPoint (𝟙 A.group ≫ f (M.indices.symm (M.indices p))) R a)).val = _
  rw [Category.id_comp, Equiv.symm_apply_apply]
  exact congrArg Subtype.val (elementaryHom_point (s := s) A _ R a)

/-- The attached coroot, included into the matrix group, is the normalized word
in the indicated pair of transvection coordinates over each test algebra. -/
theorem attachedCorootPoint_eq_rootWord {T : DiagonalTorus s} {L : LatticeIdentification T}
    (M : RootIdentification T L) [IsCommMonObj T.subgroup.group.X] (D : Datum T.subgroup)
    (A : AdditiveLine k) (U : RootSubgroupFamily T.subgroup)
    (x : ∀ α : Specs.AbstractPairing.Root T.subgroup, RootCoordinate A T.subgroup (U α).val α.val)
    (hx : ∀ (p : RootIndices (r + 1)) (R : TestAlgebra k) (a : R),
      (s.hom.app R (rootPoint ((x (M.indices p)).val.hom ≫ (U (M.indices p)).val.inclusion)
        R a)).val = 1 + Matrix.single ⟨p.val.1⟩ ⟨p.val.2⟩ a)
    (p : RootIndices (r + 1)) (R : TestAlgebra k) (a : Rˣ) :
    let q : RootIndices (r + 1) := ⟨(p.val.2, p.val.1), p.property.symm⟩
    let point (l : RootIndices (r + 1)) (b : R) : GroupPoints S.val R :=
      rootPoint ((x (M.indices l)).val.hom ≫ (U (M.indices l)).val.inclusion) R b
    let word (b : Rˣ) := point p b * point q (-(↑b⁻¹ : R)) * point p b
    CocharacterDynamics.cocharacterPoint (Additive.toMul (D.rootDatum.coroot (M.indices p))) R a ≫
      T.subgroup.inclusion.hom.hom = word a * (word 1)⁻¹ := by
  intro q point word
  let i : Index.{u} (r + 1) := ⟨p.val.1⟩
  let j : Index.{u} (r + 1) := ⟨p.val.2⟩
  have hij : i ≠ j := fun h => p.property (congrArg ULift.down h)
  have hp (b : R) : s.hom.app R (point p b) = Matrix.SpecialLinearGroup.transvection hij b :=
    Subtype.ext (hx p R b)
  have hq (b : R) : s.hom.app R (point q b) = Matrix.SpecialLinearGroup.transvection hij.symm b :=
    Subtype.ext (hx q R b)
  have hw (b : Rˣ) : s.hom.app R (word b) = transvectionWord hij b := by
    simp only [word, map_mul, hp, hq, transvectionWord]
  apply (s.app R).groupIsoToMulEquiv.injective
  change s.hom.app R _ = s.hom.app R (word a * (word 1)⁻¹)
  rw [map_mul, map_inv, hw, hw, normalizedTransvectionWord]
  apply Subtype.ext
  rw [← L.cocharacters.symm_apply_apply (D.rootDatum.coroot (M.indices p)),
    corootsOfMatrixDatum M D p, L.cocharacterPoint_eq]
  change Matrix.diagonal (fun l : Index.{u} (r + 1) =>
      (↑(a ^ (coroot (r + 1) p.val.1 p.val.2).val l.down) : R)) =
    Matrix.diagonal (fun l => (coordinatePairUnits i j a l : R))
  congr 1
  funext l
  by_cases hi : l = i
  · subst l
    simp [i, coroot, coordinate, coordinatePairUnits, p.property]
  · by_cases hj : l = j
    · subst l
      simp [i, j, coroot, coordinate, coordinatePairUnits, p.property.symm]
    · have hi' : l.down ≠ p.val.1 := fun h => hi (ULift.ext h)
      have hj' : l.down ≠ p.val.2 := fun h => hj (ULift.ext h)
      simp [coroot, coordinate, coordinatePairUnits, hi, hj, hi', hj']

end MatrixPinning

theorem matrixPinnedDatum_conditional
    (adjoint : AdjointForm.{u}) (criterion : LatticeCriterion.{u}) (cover : SplitCover.{u}) :
    MatrixPinnedDatum.{u} := by
  intro k _ r S s
  have hS := semisimple_conditional adjoint criterion cover k r S s
  obtain ⟨T, hT⟩ := splitDiagonalTorus_conditional adjoint criterion cover k r S s
  let L := latticeIdentification T
  obtain ⟨M⟩ := matrixRoot_identification L
  obtain ⟨B⟩ := upperTriangularBorel_exists M (reductive_of_semisimple S hS) hT
  obtain ⟨D⟩ := Classification.Pinning.datumExists B.pair
  have hD := matrixBasedDatum_of_attachedDatum B D
  exact ⟨T, L, M, B, D, hD, hasTransvectionPinning B,
    simplyConnectedOfMatrixDatum criterion hS B D hD⟩

end

end LinearAlgebraicGroups.RootData.SpecialLinearDatum

universe v8_closure_957b2c92493b7ca6_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«adjacentPositiveRoots» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«AdjacentPositiveRoots» :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«adjacentPositiveRoots_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«matrixPinnedDatum» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«MatrixPinnedDatum».{v8_closure_957b2c92493b7ca6_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«matrixPinnedDatum_conditional».{v8_closure_957b2c92493b7ca6_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_957b2c92493b7ca6_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«normalizedWord» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«NormalizedWord».{v8_closure_957b2c92493b7ca6_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«normalizedWord_conditional».{v8_closure_957b2c92493b7ca6_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_957b2c92493b7ca6_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«rankOneTrivial» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«RankOneTrivial».{v8_closure_957b2c92493b7ca6_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«rankOneTrivial_conditional».{v8_closure_957b2c92493b7ca6_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_957b2c92493b7ca6_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«semisimple» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«Semisimple».{v8_closure_957b2c92493b7ca6_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«semisimple_conditional».{v8_closure_957b2c92493b7ca6_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_957b2c92493b7ca6_u0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«simpleCartanPairings» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«SimpleCartanPairings» :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«simpleCartanPairings_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«simpleCorootBasis» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«SimpleCorootBasis» :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«simpleCorootBasis_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«sizeOneLattices» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«SizeOneLattices» :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«sizeOneLattices_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«sizeTwoLattices» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«SizeTwoLattices» :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«sizeTwoLattices_conditional».{0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{0})
theorem _root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«splitDiagonalTorus» : _root_.«LinearAlgebraicGroups».«Specs».«SpecialLinearDatum».«SplitDiagonalTorus».{v8_closure_957b2c92493b7ca6_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SpecialLinearDatum».«splitDiagonalTorus_conditional».{v8_closure_957b2c92493b7ca6_u0} (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«adjointForm».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«latticeCriterion».{v8_closure_957b2c92493b7ca6_u0}) (@_root_.«LinearAlgebraicGroups».«Classification».«SimplyConnectedLattice».«splitCover».{v8_closure_957b2c92493b7ca6_u0})
