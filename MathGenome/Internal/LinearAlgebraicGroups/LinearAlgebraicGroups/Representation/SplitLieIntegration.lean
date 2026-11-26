import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SplitLieIntegration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FullyFaithfulDifferentiation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.LieHighestExistence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RationalHighestWeightComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleCorootTangents
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PBWSpecialization

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix

universe u

namespace LinearAlgebraicGroups.Representation.SplitLieIntegration

open Specs.SplitLieIntegration

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem orderedPBW : OrderedPBW.{u} := by
  intro k _ G s J _
  letI := s.lieRing
  letI := s.lieAlgebra
  intro b
  obtain ⟨B, hB, _, _⟩ :=
    LieAlgebrasAndRepresentations.PBW.orderedBasis_spec k (Specs.Lie k G.val) J b
  exact ⟨B, hB⟩


section CharacterDifferential

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue pairing)
open CocharacterDynamics (cocharacterPoint unitPoint unitCoordinates mapPoints_unitPoint
  mapPoints_cocharacterPoint)

open private unitEquiv unitEquiv_unitPoint from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private characterValue_one characterValue_mul from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction

variable {k : Type u} [Field k] {T : GroupScheme k}

private abbrev multiplicativeGroup (k : Type u) [Field k] :=
  specGroup (groupAlgebra k IntegerCharacters)

private abbrev changeTest (T : GroupScheme k) {R S : TestAlgebra k} (a : R ⟶ S) :=
  (((groupPointsFunctor k).obj T).map a).hom

private def characterUnit (χ : Character T) (R : TestAlgebra k) :
    GroupPoints T R →* Rˣ :=
  (unitEquiv R).toMonoidHom.comp (((groupPointsFunctor k).map χ).app R).hom

private theorem unitPoint_characterUnit (χ : Character T) (R : TestAlgebra k)
    (p : GroupPoints T R) :
    unitPoint R (characterUnit χ R p) = p ≫ χ.hom.hom := by
  apply (unitEquiv R).injective
  rw [unitEquiv_unitPoint]
  rfl

private theorem characterValue_eq_unit (χ : Character T) (R : TestAlgebra k)
    (p : GroupPoints T R) : characterValue χ R p = (characterUnit χ R p : R) := by
  unfold characterValue
  dsimp only
  rw [← unitPoint_characterUnit χ R p]
  unfold unitPoint
  rw [Functor.FullyFaithful.preimage_map]
  change unitCoordinates R (characterUnit χ R p) (MonoidAlgebra.single integerGenerator 1) = _
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change (↑(characterUnit χ R p ^ (1 : ℤ)) : R) = _
  rw [zpow_one]

private theorem characterUnit_natural (χ : Character T) {R S : TestAlgebra k}
    (a : R ⟶ S) (p : GroupPoints T R) :
    characterUnit χ S (changeTest T a p) =
      Units.map a.hom.toMonoidHom (characterUnit χ R p) := by
  apply (unitEquiv S).symm.injective
  rw [show (unitEquiv S).symm (characterUnit χ S (changeTest T a p)) =
    unitPoint S (characterUnit χ S (changeTest T a p)) from
      (unitEquiv S).symm_apply_eq.mpr (unitEquiv_unitPoint S _).symm,
    show (unitEquiv S).symm (Units.map a.hom.toMonoidHom (characterUnit χ R p)) =
    unitPoint S (Units.map a.hom.toMonoidHom (characterUnit χ R p)) from
      (unitEquiv S).symm_apply_eq.mpr (unitEquiv_unitPoint S _).symm]
  rw [unitPoint_characterUnit, ← mapPoints_unitPoint, unitPoint_characterUnit]
  change ((testSpec k).map a.op ≫ p) ≫ χ.hom.hom =
    (testSpec k).map a.op ≫ p ≫ χ.hom.hom
  rw [Category.assoc]

private theorem cocharacterPoint_one (c : Cocharacter T) (R : TestAlgebra k) :
    cocharacterPoint c R 1 = 1 := by
  have h : unitPoint R 1 = (1 : GroupPoints (multiplicativeGroup k) R) := by
    apply (unitEquiv R).injective
    rw [unitEquiv_unitPoint, map_one]
  unfold cocharacterPoint
  rw [h]
  exact map_one (((groupPointsFunctor k).map c).app R).hom

private theorem infinitesimalUnit_value :
    ((infinitesimalUnit k : (DualNumber k)ˣ) : DualNumber k) =
      1 + DualNumber.eps := by
  exact IsUnit.unit_spec _

private theorem infinitesimalUnit_reduction :
    Units.map (dualReduction k).hom.toMonoidHom (infinitesimalUnit k) = 1 := by
  apply Units.ext
  change ((infinitesimalUnit k : (DualNumber k)ˣ) : DualNumber k).fst = 1
  rw [infinitesimalUnit_value]
  simp

/-- Every cocharacter has a unique tangent at the standard first-order unit. -/
theorem cocharacterTangent_existsUnique (c : Cocharacter T) :
    ∃! x : Lie k T, IsCocharacterTangent c x := by
  let x : Lie k T := ⟨cocharacterPoint c (CommAlgCat.of k (DualNumber k)) (infinitesimalUnit k), by
    change mapPoints (dualReduction k)
      (cocharacterPoint c (CommAlgCat.of k (DualNumber k)) (infinitesimalUnit k)) =
        (1 : GroupPoints T (CommAlgCat.of k k))
    rw [mapPoints_cocharacterPoint, infinitesimalUnit_reduction, cocharacterPoint_one]⟩
  exact ⟨x, rfl, fun y hy => Subtype.ext hy⟩

private def firstOrderUnit (a : k) : (DualNumber k)ˣ where
  val := (1, a)
  inv := (1, -a)
  val_inv := by
    apply TrivSqZeroExt.ext
    · exact one_mul _
    · change 1 * -a + a * 1 = 0
      simp
  inv_val := by
    apply TrivSqZeroExt.ext
    · exact one_mul _
    · change 1 * a + -a * 1 = 0
      simp

private def firstOrderUnits : k →+ Additive (DualNumber k)ˣ where
  toFun a := Additive.ofMul (firstOrderUnit a)
  map_zero' := by
    apply Units.ext
    rfl
  map_add' a b := by
    apply Units.ext
    change (firstOrderUnit (a + b)).val = (firstOrderUnit a * firstOrderUnit b).val
    rw [Units.val_mul]
    apply TrivSqZeroExt.ext
    · exact (one_mul _).symm
    · change a + b = 1 * b + a * 1
      simp [add_comm]

private theorem infinitesimalUnit_zpow (n : ℤ) :
    (infinitesimalUnit k ^ n).val = ((1, (n : k)) : DualNumber k) := by
  have h : (firstOrderUnits (1 : k)).toMul = infinitesimalUnit k := by
    apply Units.ext
    rw [infinitesimalUnit_value]
    apply TrivSqZeroExt.ext <;> simp [firstOrderUnits, firstOrderUnit]
  have hn := (firstOrderUnits (k := k)).map_zsmul n (1 : k)
  change (firstOrderUnits (n • (1 : k))).toMul =
    (firstOrderUnits (1 : k)).toMul ^ n at hn
  rw [h, zsmul_one] at hn
  exact (congrArg Units.val hn).symm

/-- The evaluation on a cocharacter tangent is the integer character pairing. -/
theorem characterDifferential_apply_cocharacter (χ : Character T) (c : Cocharacter T)
    {h : Lie k T} (hh : IsCocharacterTangent c h) :
    characterDifferential χ h = (pairing T χ c : k) := by
  unfold characterDifferential
  rw [hh, (RootData.CharacterPairing.characterPairingComposition T χ c).2]
  rw [infinitesimalUnit_zpow]
  rfl

private theorem tangent_character_fst (χ : Character T) (x : Lie k T) :
    (characterValue χ (CommAlgCat.of k (DualNumber k)) x.toMul.val).fst = 1 := by
  rw [characterValue_eq_unit]
  have h := characterUnit_natural χ (dualReduction k) x.toMul.val
  have hx : changeTest T (dualReduction k) x.toMul.val = 1 := x.toMul.property
  rw [hx, map_one] at h
  exact (congrArg Units.val h).symm

set_option maxHeartbeats 800000 in
private def linearCharacterDifferential (t : IdentityLieStructure T) (χ : Character T) :
    Weight t := by
  letI := t.lieRing
  letI := t.lieAlgebra
  refine { toFun := characterDifferential χ, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    have hadd := congrArg (fun g : AddGroup (PointKernel T) => g.toAdd.add x y) t.group_law
    exact (congrArg (characterDifferential χ) hadd).trans (by
      change (characterValue χ _ (x.toMul.val * y.toMul.val)).snd =
        (characterValue χ _ x.toMul.val).snd + (characterValue χ _ y.toMul.val).snd
      simp only [characterValue_eq_unit, map_mul, Units.val_mul, TrivSqZeroExt.snd_mul]
      have hx := tangent_character_fst χ x
      have hy := tangent_character_fst χ y
      rw [characterValue_eq_unit] at hx hy
      rw [hx, hy]
      change 1 * (↑(characterUnit χ _ y.toMul.val) : DualNumber k).snd +
        (↑(characterUnit χ _ x.toMul.val) : DualNumber k).snd * 1 = _
      rw [one_mul, mul_one, add_comm])
  · intro a x
    have hsmul := congrFun (congrFun t.scalar_law a) x
    exact (congrArg (characterDifferential χ) hsmul).trans (by
      change (characterValue χ _ (changeTest T (CommAlgCat.ofHom (dualNumberScale a))
        x.toMul.val)).snd = a * (characterValue χ _ x.toMul.val).snd
      rw [characterValue_eq_unit, characterUnit_natural, characterValue_eq_unit]
      change (dualNumberScale a (↑(characterUnit χ _ x.toMul.val) : DualNumber k)).snd = _
      rw [dualNumberScale, TrivSqZeroExt.snd_map]
      rfl)

private def characterLatticeDifferential (t : IdentityLieStructure T) :
    Additive (Character T) →+ Weight t := by
  letI := t.lieRing
  letI := t.lieAlgebra
  refine
    { toFun := fun χ => linearCharacterDifferential t χ.toMul
      map_zero' := ?_
      map_add' := ?_ }
  · apply LinearMap.ext
    intro x
    change (characterValue (1 : Character T) (CommAlgCat.of k (DualNumber k)) x.toMul.val).snd = 0
    simp only [characterValue_one, TrivSqZeroExt.snd_one]
  · intro χ ψ
    apply LinearMap.ext
    intro x
    change characterDifferential (χ.toMul * ψ.toMul) x =
      characterDifferential χ.toMul x + characterDifferential ψ.toMul x
    unfold characterDifferential
    rw [characterValue_mul, TrivSqZeroExt.snd_mul, tangent_character_fst χ.toMul x,
      tangent_character_fst ψ.toMul x]
    change 1 * (characterValue ψ.toMul _ x.toMul.val).snd +
      (characterValue χ.toMul _ x.toMul.val).snd * 1 = _
    rw [one_mul, mul_one, add_comm]

theorem characterComparison : CharacterComparison.{u} := by
  intro k _ _ T hT t
  refine ⟨cocharacterTangent_existsUnique, ?_, ?_, fun χ c h hh =>
    characterDifferential_apply_cocharacter χ c hh⟩
  · intro χ ψ h
    obtain ⟨comm, _, _, _, _, P, hP, hpair⟩ :=
      RootData.CharacterPairing.perfectCharacterPairing T hT
    letI := comm
    letI := hP
    have hmap : P (Additive.ofMul χ) = P (Additive.ofMul ψ) := by
      ext y
      obtain ⟨x, hx, _⟩ := cocharacterTangent_existsUnique (Additive.toMul y)
      have he := congrFun h x
      rw [characterDifferential_apply_cocharacter χ _ hx,
        characterDifferential_apply_cocharacter ψ _ hx] at he
      exact (hpair χ (Additive.toMul y)).trans
        ((Int.cast_injective he).trans (hpair ψ (Additive.toMul y)).symm)
    exact congrArg Additive.toMul ((LinearMap.IsPerfPair.bijective_left P).1 hmap)
  · exact ⟨characterLatticeDifferential t, fun _ _ => rfl⟩

end
end CharacterDifferential

section Dominance

open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Cocharacter)
open Specs.RootWeightAction (SimpleRoot)

variable {k : Type u} [Field k] [CharZero k] {G : AffineAlgebraicGroup k}

/-- Dominance follows from a rank-one comparison over the ground field by
applying the finite-dimensional primitive-vector lemma to each triple. -/
theorem highestWeight_dominant_of_rankOne (rankOne : RankOneComparison.{u})
    (P : Specs.FlagLineBundle.OppositeBorelPair G) (s : IdentityLieStructure G.val)
    (t : IdentityLieStructure P.torus.group) (lam : Weight t) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V] {v : V},
      IsHighestVector P t lam v → IsDominant P t lam := by
  letI := s.lieRing
  letI := s.lieAlgebra
  intro V _ _ _ _ _ v hv α c h hc hh
  obtain ⟨h₀, e, f, hh₀, he, _, triple⟩ := rankOne G P s α c hc
  have eq : h₀ = h := Subtype.ext (hh₀.trans hh.symm)
  subst h₀
  let primitive : triple.HasPrimitiveVectorWith v (lam h) :=
    ⟨hv.1, hv.2.1 h, hv.2.2 α.val α.property.1 e he⟩
  exact primitive.exists_nat

end Dominance

open _root_.Shared.Lie.PBW

section GradedPBW

open Module

noncomputable section
set_option linter.unusedSectionVars false

variable {k L J V : Type u} [Field k] [CharZero k]
  [LieRing L] [LieAlgebra k L] [LinearOrder J]
  [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

private abbrev envelopingAction :=
  UniversalEnvelopingAlgebra.lift k (LieModule.toEnd k L V)

private abbrev wordAction (b : Basis J k L) (v : V) (l : List J) :=
  envelopingAction (monomial b l) v

private theorem wordAction_nil (b : Basis J k L) (v : V) :
    wordAction b v [] = v := by
  unfold wordAction monomial _root_.Shared.Lie.word
  simp

private theorem wordAction_cons (b : Basis J k L) (v : V) (i : J) (l : List J) :
    wordAction b v (i :: l) = ⁅b i, wordAction b v l⁆ := by
  unfold wordAction monomial _root_.Shared.Lie.word
  simp only [List.map_cons, List.prod_cons, map_mul, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private theorem wordAction_eigenvalue (b : Basis J k L) (d : J → ℤ) (z : L)
    (hz : ∀ j, ⁅z, b j⁆ = (d j : k) • b j) {v : V} {a : k} (hv : ⁅z, v⁆ = a • v)
    (l : List J) :
    ⁅z, wordAction b v l⁆ = (a + ((l.map d).sum : k)) • wordAction b v l := by
  induction l with
  | nil => simpa only [wordAction_nil, List.map_nil, List.sum_nil, Int.cast_zero, add_zero] using hv
  | cons j l ih =>
    simp only [wordAction_cons, leibniz_lie z (b j) (wordAction b v l), hz, ih,
      smul_lie, lie_smul, lie_add, List.map_cons, List.sum_cons, Int.cast_add, add_smul]
    ac_rfl

private theorem wordAction_zero_of_positive (b : Basis J k L) (d : J → ℤ)
    (hd : Monotone d) {v : V} (hv : ∀ j, 0 < d j → ⁅b j, v⁆ = 0)
    (l : List J) (hs : l.Pairwise (· ≤ ·)) (hp : ∃ j ∈ l, 0 < d j) :
    wordAction b v l = 0 := by
  induction l with
  | nil => simp at hp
  | cons j l ih =>
    rw [wordAction_cons]
    by_cases ht : ∃ i ∈ l, 0 < d i
    · rw [ih (List.pairwise_cons.mp hs).2 ht, lie_zero]
    · have hj : 0 < d j := by
        obtain ⟨i, hi, hpos⟩ := hp
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hpos
        · exact False.elim (ht ⟨i, hi, hpos⟩)
      have hl : l = [] := by
        by_contra hne
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil l hne
        exact ht ⟨i, hi, hj.trans_le (hd ((List.pairwise_cons.mp hs).1 _ hi))⟩
      rw [hl, wordAction_nil, hv j hj]

private theorem wordAction_mem_line_of_zero (b : Basis J k L) (d : J → ℤ)
    {v : V} (hv : ∀ j, d j = 0 → ⁅b j, v⁆ ∈ k ∙ v)
    (l : List J) (hl : ∀ i ∈ l, d i = 0) :
    wordAction b v l ∈ k ∙ v := by
  induction l with
  | nil => rw [wordAction_nil]; exact Submodule.mem_span_singleton_self v
  | cons j l ih =>
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)))
    rw [wordAction_cons, ← hc, lie_smul]
    exact Submodule.smul_mem _ _ (hv j (hl j (List.mem_cons_self ..)))

private theorem wordDegree_nonpos {d : J → ℤ} (l : List J) (h : ∀ i ∈ l, d i ≤ 0) :
    (l.map d).sum ≤ 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonpos (h j (List.mem_cons_self ..))
      (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))

private theorem wordDegree_neg {d : J → ℤ} (l : List J) (h : ∀ i ∈ l, d i ≤ 0)
    (hn : ∃ i ∈ l, d i < 0) : (l.map d).sum < 0 := by
  induction l with
  | nil => simp at hn
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht : ∀ i ∈ l, d i ≤ 0 := fun i hi => h i (List.mem_cons_of_mem _ hi)
    obtain ⟨i, hi, hneg⟩ := hn
    rcases List.mem_cons.mp hi with rfl | hi
    · exact add_neg_of_neg_of_nonpos hneg (wordDegree_nonpos l ht)
    · exact add_neg_of_nonpos_of_neg (h j (List.mem_cons_self ..)) (ih ht ⟨i, hi, hneg⟩)

private def cyclicEvaluation (v : V) : UniversalEnvelopingAlgebra k L →ₗ[k] V :=
  (LinearMap.applyₗ (R := k) (M := V) v).comp envelopingAction.toLinearMap

private theorem cyclicEvaluation_apply (v : V) (p : UniversalEnvelopingAlgebra k L) :
    cyclicEvaluation v p = envelopingAction p v := rfl

private def cyclicSubmodule (v : V) : LieSubmodule k L V where
  toSubmodule := LinearMap.range (cyclicEvaluation v)
  lie_mem := by
    rintro x _ ⟨p, rfl⟩
    refine ⟨UniversalEnvelopingAlgebra.ι k x * p, ?_⟩
    simp only [cyclicEvaluation_apply, map_mul, UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl

private theorem mem_cyclicSubmodule (v : V) : v ∈ cyclicSubmodule (k := k) (L := L) v := by
  refine ⟨1, ?_⟩
  rw [cyclicEvaluation_apply, map_one]
  rfl

private def lowerEigenspaces (z : L) (a : k) : Submodule k V :=
  ⨆ r ∈ {r : k | ∃ n : ℤ, n < 0 ∧ r = a + (n : k)}, (LieModule.toEnd k L V z).eigenspace r

private theorem disjoint_lowerEigenspaces (z : L) (a : k) :
    Disjoint ((LieModule.toEnd k L V z).eigenspace a) (lowerEigenspaces z a) := by
  apply (LieModule.toEnd k L V z).eigenspaces_iSupIndep.disjoint_biSup
  rintro ⟨n, hn, heq⟩
  have hn0 : (n : k) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_lt hn)
  exact hn0 ((add_eq_left.mp heq.symm))

/-- In a cyclic highest weight module, PBW gives only the highest line and
eigenspaces for shifts of its eigenvalue by strictly negative integers. -/
private theorem cyclicSubmodule_le_line_sup_lower (b : Basis J k L) (d : J → ℤ)
    (hd : Monotone d) (z : L) (hz : ∀ j, ⁅z, b j⁆ = (d j : k) • b j)
    {v : V} {a : k} (ha : ⁅z, v⁆ = a • v)
    (hpos : ∀ j, 0 < d j → ⁅b j, v⁆ = 0)
    (hzero : ∀ j, d j = 0 → ⁅b j, v⁆ ∈ k ∙ v) :
    (cyclicSubmodule (k := k) (L := L) v).toSubmodule ≤ k ∙ v ⊔ lowerEigenspaces z a := by
  obtain ⟨B, hB, _, _⟩ := LieAlgebrasAndRepresentations.PBW.orderedBasis_spec k L J b
  change LinearMap.range (cyclicEvaluation v) ≤ _
  rw [← Submodule.map_top, ← B.span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨⟨l, hs⟩, rfl⟩, rfl⟩
  rw [hB]
  change wordAction b v l ∈ _
  by_cases hp : ∃ i ∈ l, 0 < d i
  · rw [wordAction_zero_of_positive b d hd hpos l hs hp]
    exact Submodule.zero_mem _
  · by_cases hneg : ∃ i ∈ l, d i < 0
    · apply (le_sup_right : lowerEigenspaces z a ≤ k ∙ v ⊔ lowerEigenspaces z a)
      let n := (l.map d).sum
      have hn : n < 0 := wordDegree_neg l (by
        intro i hi
        exact le_of_not_gt (fun hgt => hp ⟨i, hi, hgt⟩)) hneg
      apply (le_iSup₂ (f := fun r (_ : r ∈ {r : k | ∃ n : ℤ, n < 0 ∧ r = a + (n : k)}) =>
        (LieModule.toEnd k L V z).eigenspace r) (a + (n : k)) (show _ from ⟨n, hn, rfl⟩))
      exact Module.End.mem_eigenspace_iff.mpr (wordAction_eigenvalue b d z hz ha l)
    · apply (le_sup_left : k ∙ v ≤ k ∙ v ⊔ lowerEigenspaces z a)
      apply wordAction_mem_line_of_zero b d hzero
      intro i hi
      exact le_antisymm (le_of_not_gt (fun hgt => hp ⟨i, hi, hgt⟩))
        (le_of_not_gt (fun hlt => hneg ⟨i, hi, hlt⟩))

/-- The cyclic submodule has only its generating line at the highest eigenvalue. -/
private theorem mem_highest_line_of_mem_cyclic (b : Basis J k L) (d : J → ℤ)
    (hd : Monotone d) (z : L) (hz : ∀ j, ⁅z, b j⁆ = (d j : k) • b j)
    {v w : V} {a : k} (ha : ⁅z, v⁆ = a • v)
    (hpos : ∀ j, 0 < d j → ⁅b j, v⁆ = 0)
    (hzero : ∀ j, d j = 0 → ⁅b j, v⁆ ∈ k ∙ v)
    (hw : w ∈ cyclicSubmodule (k := k) (L := L) v) (ha' : ⁅z, w⁆ = a • w) :
    w ∈ k ∙ v := by
  let E := (LieModule.toEnd k L V z).eigenspace a
  have hline : k ∙ v ≤ E := Submodule.span_le.mpr
    (Set.singleton_subset_iff.mpr (Module.End.mem_eigenspace_iff.mpr ha))
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp
    (cyclicSubmodule_le_line_sup_lower b d hd z hz ha hpos hzero hw)
  have hyE : y ∈ E := by
    rw [← add_sub_cancel_left x y]
    exact E.sub_mem (Module.End.mem_eigenspace_iff.mpr ha') (hline hx)
  have hy0 : y = 0 := (Submodule.disjoint_def.mp (disjoint_lowerEigenspaces z a)) y hyE hy
  simpa only [hy0, add_zero] using hx

private theorem weight_shift_of_mem_cyclic (b : Basis J k L) (d : J → ℤ)
    (hd : Monotone d) (z : L) (hz : ∀ j, ⁅z, b j⁆ = (d j : k) • b j)
    {v w : V} {a a' : k} (ha : ⁅z, v⁆ = a • v)
    (hpos : ∀ j, 0 < d j → ⁅b j, v⁆ = 0)
    (hzero : ∀ j, d j = 0 → ⁅b j, v⁆ ∈ k ∙ v)
    (hw : w ∈ cyclicSubmodule (k := k) (L := L) v) (hw0 : w ≠ 0)
    (ha' : ⁅z, w⁆ = a' • w) :
    ∃ n : ℤ, n ≤ 0 ∧ a' = a + (n : k) := by
  classical
  by_contra! h
  let E := (LieModule.toEnd k L V z).eigenspace
  let S : Set k := {r | ∃ n : ℤ, n ≤ 0 ∧ r = a + (n : k)}
  have haS : a ∈ S := ⟨0, le_rfl, by simp⟩
  have hspan : k ∙ v ⊔ lowerEigenspaces z a ≤ ⨆ r ∈ S, E r := by
    refine sup_le ((Submodule.span_le.mpr ?_).trans (le_iSup₂ (f := fun r (_ : r ∈ S) => E r) a haS)) ?_
    · exact Set.singleton_subset_iff.mpr (Module.End.mem_eigenspace_iff.mpr ha)
    · refine iSup₂_le fun r hr => ?_
      obtain ⟨n, hn, rfl⟩ := hr
      exact le_iSup₂ (f := fun r (_ : r ∈ S) => E r) _ ⟨n, hn.le, rfl⟩
  have ha'S : a' ∉ S := by
    rintro ⟨n, hn, he⟩
    exact h n hn he
  have hds := (LieModule.toEnd k L V z).eigenspaces_iSupIndep.disjoint_biSup ha'S
  exact hw0 (Submodule.disjoint_def.mp hds w (Module.End.mem_eigenspace_iff.mpr ha')
    (hspan (cyclicSubmodule_le_line_sup_lower b d hd z hz ha hpos hzero hw)))

private theorem cyclicSubmodule_eq_top [LieModule.IsIrreducible k L V] {v : V} (hv : v ≠ 0) :
    cyclicSubmodule (k := k) (L := L) v = ⊤ := by
  refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun h => hv ?_
  have hv' := mem_cyclicSubmodule (k := k) (L := L) v
  rw [h, LieSubmodule.mem_bot] at hv'
  exact hv'

/-- The highest eigenvalues of two cyclic highest vectors of the same simple
module agree, and the vectors are in a single line. -/
private theorem highestLine_eq_of_irreducible [LieModule.IsIrreducible k L V]
    (b : Basis J k L) (d : J → ℤ) (hd : Monotone d) (z : L)
    (hz : ∀ j, ⁅z, b j⁆ = (d j : k) • b j) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0)
    {a a' : k} (ha : ⁅z, v⁆ = a • v) (ha' : ⁅z, w⁆ = a' • w)
    (hp : ∀ j, 0 < d j → ⁅b j, v⁆ = 0) (hp' : ∀ j, 0 < d j → ⁅b j, w⁆ = 0)
    (h0 : ∀ j, d j = 0 → ⁅b j, v⁆ ∈ k ∙ v) (h0' : ∀ j, d j = 0 → ⁅b j, w⁆ ∈ k ∙ w) :
    a = a' ∧ w ∈ k ∙ v := by
  have hw' : w ∈ cyclicSubmodule (k := k) (L := L) v := by simp [cyclicSubmodule_eq_top hv]
  have hv' : v ∈ cyclicSubmodule (k := k) (L := L) w := by simp [cyclicSubmodule_eq_top hw]
  obtain ⟨n, hn, he⟩ := weight_shift_of_mem_cyclic b d hd z hz ha hp h0 hw' hw ha'
  obtain ⟨m, hm, he'⟩ := weight_shift_of_mem_cyclic b d hd z hz ha' hp' h0' hv' hv ha
  have hsumK : ((n + m : ℤ) : k) = 0 := by
    rw [Int.cast_add]
    linear_combination -he - he'
  have hsum := Int.cast_eq_zero.mp hsumK
  have hn0 : n = 0 := by omega
  have hea : a = a' := by simpa [hn0] using he.symm
  exact ⟨hea, mem_highest_line_of_mem_cyclic b d hd z hz ha hp h0 hw' (hea ▸ ha')⟩

variable {W : Type u} [AddCommGroup W] [Module k W] [LieRingModule L W] [LieModule k L W]

private theorem surjective_of_apply_ne_zero [LieModule.IsIrreducible k L W]
    (f : V →ₗ⁅k,L⁆ W) {v : V} (hv : f v ≠ 0) : Function.Surjective f := by
  apply (LieModuleHom.range_eq_top f).mp
  refine (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left fun h => hv ?_
  have hmem : f v ∈ f.range := ⟨v, rfl⟩
  rwa [h, LieSubmodule.mem_bot] at hmem

private theorem injective_of_apply_ne_zero [LieModule.IsIrreducible k L V]
    (f : V →ₗ⁅k,L⁆ W) {v : V} (hv : f v ≠ 0) : Function.Injective f := by
  apply (LieModuleHom.ker_eq_bot f).mp
  refine (IsSimpleOrder.eq_bot_or_eq_top f.ker).resolve_right fun h => hv ?_
  exact LieModuleHom.mem_ker.mp (by rw [h]; exact LieSubmodule.mem_top v)

private theorem lieEquiv_of_highest_pair [LieModule.IsIrreducible k L V]
    [LieModule.IsIrreducible k L W] (b : Basis J k L) (d : J → ℤ) (hd : Monotone d) (z : L)
    (hz : ∀ j, ⁅z, b j⁆ = (d j : k) • b j) {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0)
    {a : k} (hV : ⁅z, v⁆ = a • v) (hW : ⁅z, w⁆ = a • w)
    (hposV : ∀ j, 0 < d j → ⁅b j, v⁆ = 0) (hposW : ∀ j, 0 < d j → ⁅b j, w⁆ = 0)
    (hzero : ∀ j, d j = 0 → ∃ c : k, ⁅b j, v⁆ = c • v ∧ ⁅b j, w⁆ = c • w) :
    Nonempty (V ≃ₗ⁅k,L⁆ W) := by
  letI : LieRingModule L (V × W) :=
    { bracket := fun x m => (⁅x, m.1⁆, ⁅x, m.2⁆)
      add_lie := fun x y m => Prod.ext (add_lie x y m.1) (add_lie x y m.2)
      lie_add := fun x m n => Prod.ext (lie_add x m.1 n.1) (lie_add x m.2 n.2)
      leibniz_lie := fun x y m => Prod.ext (leibniz_lie x y m.1) (leibniz_lie x y m.2) }
  letI : LieModule k L (V × W) :=
    { smul_lie := fun a x m => Prod.ext (smul_lie a x m.1) (smul_lie a x m.2)
      lie_smul := fun a x m => Prod.ext (lie_smul a x m.1) (lie_smul a x m.2) }
  let C := cyclicSubmodule (k := k) (L := L) (v, w)
  let topVector : C := ⟨(v, w), mem_cyclicSubmodule (v, w)⟩
  let p : C →ₗ⁅k,L⁆ V :=
    { (LinearMap.fst k V W).comp C.toSubmodule.subtype with map_lie' := rfl }
  let q : C →ₗ⁅k,L⁆ W :=
    { (LinearMap.snd k V W).comp C.toSubmodule.subtype with map_lie' := rfl }
  have hp : Function.Surjective p :=
    surjective_of_apply_ne_zero p (v := topVector) hv
  have hp' : Function.Injective p := by
    apply (LieModuleHom.ker_eq_bot p).mp
    by_contra hne
    rw [LieSubmodule.eq_bot_iff] at hne
    push Not at hne
    obtain ⟨x, hx, hx0⟩ := hne
    let f := q.comp p.ker.incl
    have hxP : (x.val : V × W).1 = 0 := LieModuleHom.mem_ker.mp hx
    have hxQ : f ⟨x, hx⟩ ≠ 0 := by
      intro h
      apply hx0
      apply Subtype.ext
      exact Prod.ext hxP h
    obtain ⟨y, hy⟩ := surjective_of_apply_ne_zero f hxQ w
    have hyP : (y.val.val : V × W).1 = 0 := LieModuleHom.mem_ker.mp y.property
    have he : y.val.val = (0, w) := Prod.ext hyP hy
    have hyC : (0, w) ∈ C := he ▸ y.val.property
    have ha : ⁅z, (v, w)⁆ = a • (v, w) := Prod.ext hV hW
    have ha' : ⁅z, ((0 : V), w)⁆ = a • ((0 : V), w) :=
      Prod.ext (by change ⁅z, (0 : V)⁆ = a • (0 : V); simp) hW
    have hpos : ∀ j, 0 < d j → ⁅b j, (v, w)⁆ = 0 :=
      fun j hj => Prod.ext (hposV j hj) (hposW j hj)
    have hzero' : ∀ j, d j = 0 → ⁅b j, (v, w)⁆ ∈ k ∙ (v, w) := by
      intro j hj
      obtain ⟨c, hcV, hcW⟩ := hzero j hj
      exact Submodule.mem_span_singleton.mpr ⟨c, Prod.ext hcV.symm hcW.symm⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (mem_highest_line_of_mem_cyclic b d hd z hz ha hpos hzero' hyC ha')
    have hcV : c • v = 0 := congrArg Prod.fst hc
    have hc0 : c = 0 := (smul_eq_zero.mp hcV).resolve_right hv
    apply hw
    simpa [hc0] using (congrArg Prod.snd hc).symm
  let e : C ≃ₗ⁅k,L⁆ V :=
    { LinearEquiv.ofBijective p.toLinearMap ⟨hp', hp⟩ with map_lie' := p.map_lie _ _ }
  let g : V →ₗ⁅k,L⁆ W := q.comp e.symm.toLieModuleHom
  have hg : g v ≠ 0 := by
    have huv : e.symm v = topVector := e.symm_apply_eq.mpr rfl
    change q (e.symm v) ≠ 0
    rw [huv]
    exact hw
  exact ⟨{ LinearEquiv.ofBijective g.toLinearMap
            ⟨injective_of_apply_ne_zero g hg, surjective_of_apply_ne_zero g hg⟩ with
           map_lie' := g.map_lie _ _ }⟩

end
end GradedPBW

section HighestWeightUniqueness

open _root_.LinearAlgebraicGroups.Specs

private theorem triangularBasis_exists_preimage {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k} {P : FlagLineBundle.OppositeBorelPair G}
    {s : IdentityLieStructure G.val} (b : TriangularBasis P s) {j : b.J}
    (hj : b.degree j = 0) : ∃ h, mapPointKernel P.torus.inclusion h = b.basis j := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  have h : b.basis j ∈ Set.range (mapPointKernel P.torus.inclusion) := by
    rw [b.zero_part]
    intro i hi
    have hne : i ≠ j := fun he => hi (he ▸ hj)
    rw [Module.Basis.repr_self]
    exact Finsupp.single_eq_of_ne hne
  exact h

private theorem triangularBasis_mem_positive {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k} {P : FlagLineBundle.OppositeBorelPair G}
    {s : IdentityLieStructure G.val} (b : TriangularBasis P s) {j : b.J}
    (hj : 0 < b.degree j) :
    ∃ α ∈ BorelsAndChambers.subgroupRoots P.torus P.positive,
      b.basis j ∈ CharacterPairing.adjointWeightVectors P.torus α.val := by
  obtain ⟨α, hn, hm⟩ := b.root_part j (ne_of_gt hj)
  refine ⟨α, ?_, hm⟩
  rw [← b.positive]
  show 0 < CharacterPairing.pairing P.torus.group α.val b.cochar
  rwa [← hn]

theorem highestWeightUniqueness : HighestWeightUniqueness.{u} := by
  intro k _ _ G P s t b
  letI := s.lieRing
  letI := s.lieAlgebra
  intro V _ _ _ _ hV lam v hv
  letI := t.lieRing
  letI := t.lieAlgebra
  letI := hV
  let h := mapPointKernel P.torus.inclusion b.tangent
  have posV (j : b.J) (hj : 0 < b.degree j) : ⁅b.basis j, v⁆ = 0 := by
    obtain ⟨α, hp, hm⟩ := triangularBasis_mem_positive b hj
    exact hv.2.2 α hp (b.basis j) hm
  have lineV (j : b.J) (hj : b.degree j = 0) :
      ⁅b.basis j, v⁆ ∈ Submodule.span k {v} := by
    obtain ⟨x, hx⟩ := triangularBasis_exists_preimage b hj
    exact Submodule.mem_span_singleton.mpr ⟨lam x, by rw [← hx, hv.2.1]⟩
  refine ⟨?_, ?_⟩
  · intro mu w hw
    have posW (j : b.J) (hj : 0 < b.degree j) : ⁅b.basis j, w⁆ = 0 := by
      obtain ⟨α, hp, hm⟩ := triangularBasis_mem_positive b hj
      exact hw.2.2 α hp (b.basis j) hm
    have lineW (j : b.J) (hj : b.degree j = 0) :
        ⁅b.basis j, w⁆ ∈ Submodule.span k {w} := by
      obtain ⟨x, hx⟩ := triangularBasis_exists_preimage b hj
      exact Submodule.mem_span_singleton.mpr ⟨mu x, by rw [← hx, hw.2.1]⟩
    obtain ⟨_, hline⟩ := highestLine_eq_of_irreducible b.basis b.degree b.ordered h
      b.bracket hv.1 hw.1 (hv.2.1 b.tangent) (hw.2.1 b.tangent) posV posW lineV lineW
    refine ⟨?_, hline⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hline
    apply LinearMap.ext
    intro x
    apply (smul_left_injective k hw.1)
    change mu x • (c • v) = lam x • (c • v)
    rw [← hw.2.1 x, lie_smul, hv.2.1 x, smul_comm c (lam x)]
  · intro W _ _ _ _ hW
    letI := hW
    constructor
    · rintro ⟨w, hw⟩
      apply lieEquiv_of_highest_pair b.basis b.degree b.ordered h b.bracket hv.1 hw.1
        (hv.2.1 b.tangent) (hw.2.1 b.tangent) posV
      · intro j hj
        obtain ⟨α, hp, hm⟩ := triangularBasis_mem_positive b hj
        exact hw.2.2 α hp (b.basis j) hm
      · intro j hj
        obtain ⟨x, hx⟩ := triangularBasis_exists_preimage b hj
        exact ⟨lam x, by rw [← hx, hv.2.1], by rw [← hx, hw.2.1]⟩
    · rintro ⟨e⟩
      refine ⟨e v, ?_, ?_, ?_⟩
      · exact fun he => hv.1 (e.injective (he.trans (map_zero e).symm))
      · intro x
        calc
          _ = e ⁅mapPointKernel P.torus.inclusion x, v⁆ :=
            (e.toLieModuleHom.map_lie _ _).symm
          _ = _ := by rw [hv.2.1, map_smul]
      · intro α hα x hx
        calc
          _ = e ⁅x, v⁆ := (e.toLieModuleHom.map_lie _ _).symm
          _ = 0 := by rw [hv.2.2 α hα x hx, map_zero]

end HighestWeightUniqueness

section TriangularComparison

open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing characterValue adjointWeightVectors adjointWeightSpace)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.FlagLineBundle (OppositeBorelPair)

open private adjointWeightVectors_iff extendCoordinates canonicalZero_eq from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private torusWeightBasis pairing_trivial from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem snd_mul_constant (x : DualNumber k) (a : k) :
    (x * algebraMap k (DualNumber k) a).snd = x.snd * a := by
  change x.fst * 0 + x.snd * a = x.snd * a
  rw [mul_zero, zero_add]

private theorem snd_mulVec_constants {I : Type u} [Fintype I]
    (A : Matrix I I (DualNumber k)) (v : I → k) (i : I) :
    ((A *ᵥ fun j => algebraMap k (DualNumber k) (v j)) i).snd =
      ((fun i j => (A i j).snd : Matrix I I k) *ᵥ v) i := by
  unfold Matrix.mulVec dotProduct
  rw [TrivSqZeroExt.snd_sum]
  exact Finset.sum_congr rfl fun j _ => snd_mul_constant (A i j) (v j)

/-- In a torus weight space, bracketing with an actual cocharacter tangent
acts by the character–cocharacter pairing. -/
theorem lie_cocharacter_of_weight (s : IdentityLieStructure G.val) (T : ClosedSubgroup G.val)
    (χ : Character T.group) (c : Cocharacter T.group) {h : Lie k T.group}
    (hh : IsCocharacterTangent c h) (y : Lie k G.val)
    (hy : y ∈ adjointWeightVectors T χ) :
    letI := s.lieRing
    letI := s.lieAlgebra
    ⁅mapPointKernel T.inclusion h, y⁆ =
      s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul
        (pairing T.group χ c : k) y := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  let R := CommAlgCat.of k (DualNumber k)
  obtain ⟨_, b, C, L, l, Ad, hAd, hLie, _⟩ := adjointRepresentation k G s
  have w := (adjointWeightVectors_iff C l Ad hAd T χ y).mp hy R h.toMul.val
  let H := mapPointKernel T.inclusion h
  let A := (l.hom.app R).hom (mapPointKernel Ad H).toMul.val
  have hw : A.val *ᵥ extendCoordinates b R y =
      characterValue χ R h.toMul.val • extendCoordinates b R y := by
    dsimp only at w
    rw [Functor.map_comp, NatTrans.comp_app] at w
    exact w
  apply b.equivFun.injective
  rw [← hLie H y]
  funext i
  have e := congrArg (fun w : _ → R => (w i).snd) hw
  change ((A.val *ᵥ fun j => algebraMap k (DualNumber k) (b.equivFun y j)) i).snd =
    (characterValue χ R h.toMul.val * algebraMap k (DualNumber k) (b.equivFun y i)).snd at e
  rw [snd_mulVec_constants, snd_mul_constant] at e
  change (InfinitesimalCommutator.matrixDifferential Ad l H *ᵥ b.equivFun y) i =
    characterDifferential χ h * b.equivFun y i at e
  rw [characterDifferential_apply_cocharacter χ c hh] at e
  exact e.trans (congrFun (b.equivFun.map_smul (pairing T.group χ c : k) y) i).symm

theorem triangularPBW : TriangularPBW.{u} := by
  classical
  intro k _ _ G P _ s
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨c, _, hc, _, hpositive⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G P.reductive P.torus P.split P.maximal).1
      P.positive P.positiveBorel P.inPositive
  obtain ⟨h, hh, _⟩ := cocharacterTangent_existsUnique c
  obtain ⟨I, fin, b, χ, hweight, hsupport⟩ := torusWeightBasis G P.torus P.split s
  letI := fin
  let d (j : I) := pairing P.torus.group (χ j) c
  let ix := Fintype.equivFin I
  let key (j : I) : ℤ ×ₗ Fin (Fintype.card I) := (d j, ix j)
  letI : LinearOrder I := LinearOrder.lift' key (fun _ _ he =>
    ix.injective (congrArg Prod.snd he))
  have hd : Monotone d := by
    intro i j hij
    change key i ≤ key j at hij
    rcases Prod.Lex.le_iff.mp hij with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  have trivial_iff (j : I) : d j = 0 ↔ χ j = 1 := by
    refine ⟨fun hz => ?_, fun he => ?_⟩
    · by_contra hn
      have hr : χ j ∈ CharacterPairing.absoluteRoots P.torus :=
        ⟨hn, b j, hweight j, fun he => b.ne_zero j (he.trans (canonicalZero_eq s))⟩
      exact hc ⟨χ j, hr⟩ hz
    · change pairing P.torus.group (χ j) c = 0
      rw [he, pairing_trivial]
  have hzero := (RootData.RootGroups.rootSubgroups G P.reductive P.torus P.split P.maximal).1.2
  let W := adjointWeightSpace P.torus 1 s
  have hW : (W : Set (Lie k G.val)) = adjointWeightVectors P.torus 1 :=
    RootData.CharacterPairing.adjointWeightSpaceVectors G P.torus s 1
  have hzero' : Set.range (mapPointKernel P.torus.inclusion) =
      {x | ∀ j, d j ≠ 0 → b.repr x j = 0} := by
    rw [hzero, ← hW]
    ext x
    constructor
    · intro hx j hj
      exact hsupport 1 x (hW ▸ hx) j (fun he => hj ((trivial_iff j).mpr he))
    · intro hx
      have hsum := b.sum_repr x
      rw [← hsum]
      apply W.sum_mem
      intro j _
      by_cases hj : d j = 0
      · apply W.smul_mem
        rw [← SetLike.mem_coe, hW]
        exact (trivial_iff j).mp hj ▸ hweight j
      · rw [hx j hj, zero_smul]
        exact W.zero_mem
  let data : TriangularBasis P s :=
    { J := I
      basis := b
      cochar := c
      tangent := h
      tangent_spec := hh
      regular := hc
      positive := hpositive.symm
      degree := d
      ordered := hd
      zero_part := hzero'
      root_part := fun j hj => by
        have hn : χ j ≠ 1 := fun he => hj ((trivial_iff j).mpr he)
        have hr : χ j ∈ CharacterPairing.absoluteRoots P.torus :=
          ⟨hn, b j, hweight j, fun he => b.ne_zero j (he.trans (canonicalZero_eq s))⟩
        exact ⟨⟨χ j, hr⟩, rfl, hweight j⟩
      root_support := fun α x hx j hj =>
        hsupport α.val x hx j (fun he => hj (congrArg (fun ψ => pairing P.torus.group ψ c) he))
      bracket := fun j => lie_cocharacter_of_weight s P.torus (χ j) c hh (b j) (hweight j) }
  exact ⟨data, orderedPBW s b⟩

end TriangularComparison

section RankOneComparison

open _root_.LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue pairing adjointWeightVectors)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.RootGroups (AdditiveLine CorootReflection HasScalarAction rootPoint)
open InfinitesimalCommutator (TwoVariables liftS liftT liftST)
open CocharacterDynamics (cocharacterPoint mapPoints_cocharacterPoint)

open private rootPoint_zero mapPoints_rootPoint from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations
open private pairing_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private point_liftST_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LieBracket
open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private abbrev dualAlgebra (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private noncomputable def rootTangent {A : AdditiveLine k} {H : GroupScheme k} (x : A.group ⟶ H) :
    Lie k H := ⟨rootPoint x (dualAlgebra k) DualNumber.eps, by
  change mapPoints (dualReduction k) (rootPoint x (dualAlgebra k) DualNumber.eps) =
    (1 : GroupPoints H (CommAlgCat.of k k))
  rw [mapPoints_rootPoint]
  exact rootPoint_zero x _⟩

private theorem rootTangent_map {A : AdditiveLine k} {H I : GroupScheme k}
    (x : A.group ⟶ H) (f : H ⟶ I) :
    (mapPointKernel f (rootTangent x)).toMul.val =
      rootPoint (x ≫ f) (dualAlgebra k) DualNumber.eps := by
  change (_ ≫ x.hom.hom) ≫ f.hom.hom = _ ≫ (x.hom.hom ≫ f.hom.hom)
  rw [Category.assoc]

private theorem mixedEpsilon (k : Type u) [Field k] :
    liftST k DualNumber.eps = liftS k DualNumber.eps * liftT k DualNumber.eps := by
  have hs : liftS k DualNumber.eps = (⟨DualNumber.eps, 0⟩ : TwoVariables k) := rfl
  have ht : liftT k DualNumber.eps = (⟨0, 1⟩ : TwoVariables k) :=
    TrivSqZeroExt.ext (map_zero (algebraMap k (DualNumber k)))
      (map_one (algebraMap k (DualNumber k)))
  rw [hs, ht]
  apply TrivSqZeroExt.ext
  · change (0 : DualNumber k) = DualNumber.eps * 0
    rw [mul_zero]
  · change (DualNumber.eps : DualNumber k) = DualNumber.eps * 1 + 0 * 0
    rw [mul_one, zero_mul, add_zero]

private theorem lie_opposite_of_gauss (s : IdentityLieStructure G.val)
    (T : ClosedSubgroup G.val) (hT : GeometricRadicals.IsSplitTorus T.group)
    (hmax : RankOneFlag.IsGeometricallyMaximal T) (hG : GeometricRadicals.IsReductive G)
    (α : AbstractPairing.Root T) {A : AdditiveLine k} (xp xn : A.group ⟶ G.val)
    (r : CorootReflection T α.val xp xn)
    (hxp : HasScalarAction T α.val xp) (hxn : HasScalarAction T α.val⁻¹ xn)
    {h₀ : Lie k T.group} (hh : IsCocharacterTangent r.coroot h₀)
    {e f : Lie k G.val}
    (he : e.toMul.val = rootPoint xp (dualAlgebra k) DualNumber.eps)
    (hf : f.toMul.val = rootPoint xn (dualAlgebra k) DualNumber.eps) :
    s.lieRing.toBracket.bracket e f = mapPointKernel T.inclusion h₀ := by
  let R := CommAlgCat.of k (TwoVariables k)
  let S : dualAlgebra k ⟶ R := CommAlgCat.ofHom (liftS k)
  let D : dualAlgebra k ⟶ R := CommAlgCat.ofHom (liftT k)
  let SD : dualAlgebra k ⟶ R := CommAlgCat.ofHom (liftST k)
  let x : R := S.hom DualNumber.eps
  let y : R := D.hom DualNumber.eps
  let t : Rˣ := Units.map SD.hom.toMonoidHom (infinitesimalUnit k)
  have hx : x * x = 0 := by
    change S.hom DualNumber.eps * S.hom DualNumber.eps = _
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hy : y * y = 0 := by
    change D.hom DualNumber.eps * D.hom DualNumber.eps = _
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have ht : (t : R) = 1 + x * y := by
    change SD.hom (infinitesimalUnit k : DualNumber k) = _
    rw [infinitesimalUnit_value, map_add, map_one]
    exact congrArg (fun z : R => 1 + z) (mixedEpsilon k)
  have htinv : (↑t⁻¹ : R) = 1 - x * y := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ht]
    linear_combination -(y * y) * hx
  have hxt : x * (↑t⁻¹ : R) = x := by
    rw [htinv, mul_sub, mul_one, ← mul_assoc x x y, hx, zero_mul, sub_zero]
  have hyt : y * (↑t⁻¹ : R) = y := by
    rw [htinv, mul_sub, mul_one, mul_left_comm y x y, hy, mul_zero, sub_zero]
  let a := rootPoint xp R x
  let b := rootPoint xn R y
  let c : GroupPoints G.val R := cocharacterPoint r.coroot R t ≫ T.inclusion.hom.hom
  have hab : a * b = b * c * a := by
    have gauss := (Classification.RankOneRelations.oppositeRootRelations
      G hG T hT hmax α.val α.property xp xn r hxp hxn R).1 x y t ht
    rw [hxt, hyt] at gauss
    exact gauss
  have hbc : Commute b c := by
    have errorTerm := hxn R (cocharacterPoint r.coroot R t) y
    change c * b * c⁻¹ = rootPoint xn R
      (characterValue α.val⁻¹ R (cocharacterPoint r.coroot R t) * y) at errorTerm
    have hpow : t ^ (-2 : ℤ) = t⁻¹ ^ (2 : ℕ) := by rw [zpow_neg, zpow_ofNat, inv_pow]
    have hfix : (↑(t ^ (-2 : ℤ)) : R) * y = y := by
      rw [hpow, Units.val_pow_eq_pow_val, pow_two, mul_assoc,
        mul_comm (↑t⁻¹ : R) y, hyt, mul_comm (↑t⁻¹ : R) y, hyt]
    rw [(RootData.CharacterPairing.characterPairingComposition T.group _ _).2,
      pairing_inv _ hT, r.root_pairing, hfix] at errorTerm
    exact (mul_inv_eq_iff_eq_mul.mp errorTerm).symm
  have hcomm : a * b * a⁻¹ * b⁻¹ = c := by
    calc
      _ = b * c * b⁻¹ := by rw [hab]; group
      _ = c := by rw [hbc.eq, mul_inv_cancel_right]
  have hh' : (mapPointKernel T.inclusion h₀).toMul.val =
      cocharacterPoint r.coroot (dualAlgebra k) (infinitesimalUnit k) ≫ T.inclusion.hom.hom := by
    change h₀.toMul.val ≫ T.inclusion.hom.hom = _
    rw [hh]
  have htor : changeTest G.val SD (mapPointKernel T.inclusion h₀).toMul.val = c := by
    rw [hh']
    change (mapPoints SD (cocharacterPoint r.coroot (dualAlgebra k) (infinitesimalUnit k))) ≫
      T.inclusion.hom.hom = c
    rw [mapPoints_cocharacterPoint]
  letI : IsAffine G.val.X.left := G.property.1
  apply Subtype.ext
  apply point_liftST_injective G.val
  have hb := s.commutator_law e f
  unfold InfinitesimalCommutator.commutator at hb
  change changeTest G.val SD (s.lieRing.toBracket.bracket e f).toMul.val =
    changeTest G.val S e.toMul.val * changeTest G.val D f.toMul.val *
      (changeTest G.val S e.toMul.val)⁻¹ * (changeTest G.val D f.toMul.val)⁻¹ at hb
  rw [he, hf,
    show changeTest G.val S (rootPoint xp (dualAlgebra k) DualNumber.eps) = a
      from mapPoints_rootPoint xp S _,
    show changeTest G.val D (rootPoint xn (dualAlgebra k) DualNumber.eps) = b
      from mapPoints_rootPoint xn D _] at hb
  exact hb.trans (hcomm.trans htor.symm)

theorem rankOneComparison : RankOneComparison.{u} := by
  intro k _ _ G P s α c hc
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨C, _, _, _, D, E, _, _, _, _, _, p, n, hp, hn, hxp, hxn, r, hr⟩ := hc
  subst c
  obtain ⟨h₀, hh, _⟩ := cocharacterTangent_existsUnique r.coroot
  let e := mapPointKernel (D.contracting.inclusion ≫ C.subgroup.inclusion) (rootTangent p.root.hom)
  let f := mapPointKernel (E.contracting.inclusion ≫ C.subgroup.inclusion) (rootTangent n.root.hom)
  have he : e ∈ adjointWeightVectors P.torus α.val.val :=
    hp.2.2.2 ⟨rootTangent p.root.hom, rfl⟩
  have hf : f ∈ adjointWeightVectors P.torus α.val.val⁻¹ :=
    hn.2.2.2 ⟨rootTangent n.root.hom, rfl⟩
  refine ⟨h₀, e, f, hh, he, hf, ?_⟩
  have hop := lie_opposite_of_gauss s P.torus P.split P.maximal P.reductive α.val
    _ _ r hxp hxn hh (rootTangent_map p.root.hom _) (rootTangent_map n.root.hom _)
  have hb := lie_cocharacter_of_weight s P.torus α.val.val r.coroot hh e he
  have hb' := lie_cocharacter_of_weight s P.torus α.val.val⁻¹ r.coroot hh f hf
  rw [r.root_pairing] at hb
  rw [pairing_inv _ P.split, r.root_pairing] at hb'
  refine ⟨?_, hop, ?_, ?_⟩
  · intro hzero
    have h : mapPointKernel P.torus.inclusion h₀ =
        mapPointKernel P.torus.inclusion (0 : PointKernel P.torus.group) :=
      hzero.trans ((canonicalZero_eq s).symm.trans ((mapPointKernel P.torus.inclusion).map_zero).symm)
    have hinj := (RootData.RootGroups.rootSubgroups G P.reductive P.torus P.split P.maximal).1.1
    have hh₀ : h₀ = (0 : PointKernel P.torus.group) := hinj h
    have hval := characterDifferential_apply_cocharacter α.val.val r.coroot hh
    rw [hh₀, r.root_pairing] at hval
    have hval0 : characterDifferential α.val.val (0 : PointKernel P.torus.group) = 0 := by
      change (characterValue α.val.val (dualAlgebra k) 1).snd = 0
      rw [characterValue_eq_unit, map_one, Units.val_one]
      rfl
    rw [hval0, Int.cast_ofNat] at hval
    exact (two_ne_zero (α := k)) hval.symm
  · rw [Int.cast_ofNat] at hb
    exact hb.trans ((@two_smul k _ _ s.lieRing.toAddCommGroup.toAddCommMonoid
      s.lieAlgebra.toModule e).trans (@two_nsmul _ s.lieRing.toAddCommGroup.toAddMonoid e).symm)
  · rw [Int.cast_neg, Int.cast_ofNat] at hb'
    exact hb'.trans ((@neg_smul k _ _ s.lieRing.toAddCommGroup s.lieAlgebra.toModule 2 f).trans
      (congrArg (@Neg.neg _ s.lieRing.toAddCommGroup.toNeg)
        ((@two_smul k _ _ s.lieRing.toAddCommGroup.toAddCommMonoid s.lieAlgebra.toModule f).trans
          (@two_nsmul _ s.lieRing.toAddCommGroup.toAddMonoid f).symm)))

end RankOneComparison

section ComparisonAssembly

open _root_.LinearAlgebraicGroups.Specs
open AbstractPairing (Root)
open BorelsAndChambers (positiveRoots subgroupRoots)
open CharacterPairing (adjointWeightVectors pairing)
open RootWeightAction (SimpleRoot)

open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

private theorem highestWeightExistence : HighestWeightExistence.{u} := by
  classical
  intro k _ _ G hG P s t
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  intro V _ _ _ _ _ hV
  letI := hV
  letI : Nontrivial V := LieModule.nontrivial_of_isIrreducible k (Lie k G.val) V
  let Q : Pinning.SplitBorelPair k :=
    ⟨G, P.reductive, P.torus, P.split, P.maximal, P.positive, P.positiveBorel, P.inPositive⟩
  let D := Classification.Pinning.attachedDatum Q
  letI := D.comm
  letI : Finite (Root P.torus) := D.datum.finiteRoots
  letI : Finite (SimpleRoot P.torus P.positive) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨_, b, hb⟩ := SimpleCorootTangents.basisAndLattice Q hG D t
  obtain ⟨comm, inclusion, hinj, hmap⟩ :=
    SimpleCorootTangents.lieEmbedding G P.torus P.split t s
  letI : @IsLieAbelian (Lie k P.torus.group) t.lieRing.toBracket
      t.lieRing.toAddCommGroup.toZero :=
    @LieModule.IsTrivial.mk _ _ t.lieRing.toBracket t.lieRing.toAddCommGroup.toZero
      (fun x y => (comm x y).trans (canonicalZero_eq t))
  have htriple (α : SimpleRoot P.torus P.positive) :
      ∃ e f : Lie k G.val, IsSl2Triple (inclusion (b α)) e f := by
    obtain ⟨h, e, f, hh, _, _, hsl₂⟩ := rankOneComparison G P s α _ (D.datum.attached α.val)
    have heq : h = b α := Subtype.ext (hh.trans (hb α).symm)
    exact ⟨e, f, by rw [hmap, ← heq]; exact hsl₂⟩
  obtain ⟨B, _, _⟩ := triangularPBW G P hG s
  let J := Σ α : ↥(subgroupRoots P.torus P.positive),
    ↥(adjointWeightVectors P.torus α.val.val)
  let x (a : J) : Lie k G.val := a.2.val
  let degree (a : J) : ℤ := pairing P.torus.group a.1.val.val B.cochar
  have hpositive (a : J) : 0 < degree a ∧
      ⁅inclusion B.tangent, x a⁆ =
        s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul (degree a : k) (x a) := by
    constructor
    · change a.1.val ∈ positiveRoots P.torus B.cochar
      rw [B.positive]
      exact a.1.property
    · rw [hmap]
      exact lie_cocharacter_of_weight s P.torus _ B.cochar B.tangent_spec _ a.2.property
  obtain ⟨lam, v, hv, htorus, hroots⟩ :=
    LieHighestExistence.highestWeightExistence k (Lie k G.val) V (Lie k P.torus.group)
      inclusion hinj (SimpleRoot P.torus P.positive) b b.span_eq htriple B.tangent J x degree hpositive
  refine ⟨lam, v, hv, fun h => ?_, fun α hα y hy => ?_⟩
  · rw [← hmap]
    exact htorus h
  · exact hroots ⟨⟨α, hα⟩, ⟨y, hy⟩⟩

private theorem rationalHighestWeightComparison : RationalHighestWeightComparison.{u} := by
  intro k _ _ G hG P s t
  letI := s.lieRing
  letI := s.lieAlgebra
  have comparison := RationalHighestWeightComparison.rationalHighestWeightComparison G hG P s
  constructor
  · intro V _ _ _ _ _ hV h
    obtain ⟨A, e, δ, hδ⟩ := h
    obtain ⟨χ, v, hv⟩ := comparison.1 V hV A e δ hδ
    exact ⟨χ, linearCharacterDifferential t χ, v, hv, fun _ => rfl⟩
  · intro χ hχ
    obtain ⟨V, vAdd, vModule, vFinite, vLieRing, vLie, hV, A, e, δ, hδ, v, hv⟩ :=
      comparison.2 χ hχ
    exact ⟨V, vAdd, vModule, vFinite, vLieRing, vLie, hV, ⟨A, e, δ, hδ⟩,
      linearCharacterDifferential t χ, v, hv, fun _ => rfl⟩

end ComparisonAssembly

section IntegrationAssembly

open _root_.LinearAlgebraicGroups.Specs
open RationalRepresentations
open scoped TensorProduct

open private coassoc_after_projection contractRight_natural differentiatedCoaction_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FullyFaithfulDifferentiation

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
variable {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private theorem exists_transportCoaction (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A W) (e : V ≃ₗ[k] W) :
    ∃ σ : RightComodule k A V, IsEquivariant A σ ρ e.toLinearMap := by
  let δ := (e.rTensor A).symm.toLinearMap.comp (ρ.coaction.comp e.toLinearMap)
  have hδ : (e.toLinearMap.rTensor A).comp δ = ρ.coaction.comp e.toLinearMap := by
    ext x
    exact (e.rTensor A).apply_symm_apply _
  refine ⟨⟨δ, ?_, ?_⟩, hδ⟩
  · intro x
    apply (e.rTensor (A ⊗[k] A)).injective
    exact coassoc_after_projection e.toLinearMap δ ρ hδ x
  · intro x
    apply e.injective
    change e.toLinearMap (TensorProduct.rid k V _) = e.toLinearMap x
    have hx : e.toLinearMap.rTensor A (δ x) = ρ.coaction (e x) :=
      DFunLike.congr_fun hδ x
    rw [contractRight_natural, hx]
    exact ρ.counit _

private theorem integrates_of_lieEquiv [LieRing (Lie k G.val)]
    [LieRingModule (Lie k G.val) V] [LieRingModule (Lie k G.val) W]
    (e : V ≃ₗ⁅k, Lie k G.val⁆ W) (he : Integrates G W) : Integrates G V := by
  obtain ⟨A, iso, ρ, hρ⟩ := he
  obtain ⟨σ, hσ⟩ := exists_transportCoaction A ρ e.toLinearEquiv
  refine ⟨A, iso, σ, fun x v => e.injective ?_⟩
  calc
    e (differentiatedCoaction A σ _ v) = differentiatedCoaction A ρ _ (e v) :=
      differentiatedCoaction_natural A σ ρ _ e.toLinearEquiv.toLinearMap hσ v
    _ = ⁅x, e v⁆ := hρ x (e v)
    _ = e ⁅x, v⁆ := (e.toLieModuleHom.map_lie x v).symm

/-- Assemble the split criterion from highest vectors over the ground field
and the differentiation comparison for rational highest lines. -/
theorem splitIntegration_of_comparisons (existence : HighestWeightExistence.{u})
    (rational : RationalHighestWeightComparison.{u}) : SplitIntegration.{u} := by
  intro k _ _ G hG P s t
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  intro V _ _ _ _ _ hV
  obtain ⟨b, _, _⟩ := triangularPBW G P hG s
  obtain ⟨lam, v, hv⟩ := existence G hG P s t V hV
  refine ⟨⟨lam, ⟨v, hv⟩, ?_⟩, ?_⟩
  · rintro mu ⟨w, hw⟩
    exact ((highestWeightUniqueness P s t b hV hv).1 hw).1
  · rintro mu ⟨w, hw⟩
    have dom := highestWeight_dominant_of_rankOne rankOneComparison P s t mu hw
    have unique := highestWeightUniqueness P s t b hV hw
    refine ⟨dom, ?_, fun W _ _ _ _ _ hW => @unique.2 W _ _ _ _ hW⟩
    constructor
    · intro h
      obtain ⟨χ, nu, v', hv', hχ⟩ := (rational G hG P s t).1 V hV h
      have eq := (unique.1 hv').1
      exact ⟨χ, eq ▸ hχ⟩
    · rintro ⟨χ, hχ⟩
      have hdom : InducedNonvanishing.Dominant P χ := by
        intro α c hc
        obtain ⟨z, hz, _⟩ := cocharacterTangent_existsUnique c
        obtain ⟨n, hn⟩ := dom α c z hc hz
        have h := (characterDifferential_apply_cocharacter χ c hz).symm.trans ((hχ z).symm.trans hn)
        have hi : CharacterPairing.pairing P.torus.group χ c = (n : ℤ) :=
          Int.cast_injective (α := k) (h.trans (Int.cast_natCast n).symm)
        rw [hi]
        exact Int.natCast_nonneg n
      obtain ⟨W, Wadd, Wmodule, Wfinite, WlieRing, Wlie, hW, hInt, nu, w', hw', hnu⟩ :=
        (rational G hG P s t).2 χ hdom
      letI := Wadd
      letI := Wmodule
      letI := Wfinite
      letI := WlieRing
      letI := Wlie
      have eq : nu = mu := LinearMap.ext fun z => (hnu z).trans (hχ z).symm
      obtain ⟨f⟩ := (unique.2 hW).mp ⟨w', eq ▸ hw'⟩
      exact integrates_of_lieEquiv f hInt

/-- A finite-dimensional simple Lie module over the split field integrates
exactly when its highest weight differentiates from an actual torus character. -/
theorem splitIntegration : SplitIntegration.{u} :=
  splitIntegration_of_comparisons highestWeightExistence rationalHighestWeightComparison

end IntegrationAssembly

end LinearAlgebraicGroups.Representation.SplitLieIntegration
