import Specs.LinearAlgebraicGroups.Classification.IntegralFibreDatum
import LinearAlgebraicGroups.Classification.RationalRealization
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Classification.IntegralFibreDatum

open _root_.LinearAlgebraicGroups.Specs
open Specs.IntegralFibreDatum
open Specs.Pinning (BasedRootDatum AttachedDatum RootCoordinate IsSimple)
open Specs.RationalRealization (diagonalTorus)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup rootPoint rankOneWord)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue pairing)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.OrderedRootProducts (Enumerates RootSubgroupFamily product)
open Specs.AbstractPairing (Root Datum)
open LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.BorelsAndChambers (subgroupRoots positiveRoots IsRegular)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

open private diagonalCharacters diagonalCharacters_eq diagonalCocharacters diagonalCocharacters_eq
  diagonalPairing diagonalSplit from LinearAlgebraicGroups.Classification.RationalRealization
open private coroot_functional_of_reflection from LinearAlgebraicGroups.Classification.Pinning
open private additivePoints_natural rootPoint_eq rootPoint_natural rootPoint_zero
  rootPoint_injective_of_mono rootPoint_eps_reduces
  normalizes_of_point_conjugation tangent_weight_of_scalarAction
  rankOneRepresentative rankOneRepresentative_point
  from LinearAlgebraicGroups.RootData.RootGroups
open private characterValue_monomial from LinearAlgebraicGroups.RootData.CharacterPairing
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private cocharacter_ext_units from LinearAlgebraicGroups.RootData.RankOneFlag
open private conjugation_unique from LinearAlgebraicGroups.RootData.AbstractPairing

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}}
  {G : AffineAlgebraicGroup k} {A : AdditiveLine k}

private theorem character_marking (x : D.X) :
    Additive.toMul (diagonalCharacters k D x) = markedCharacter D x :=
  diagonalCharacters_eq k D x

private theorem cocharacter_marking (y : D.Y) :
    Additive.toMul (diagonalCocharacters k D y) = markedCocharacter (k := k) D y := by
  rw [diagonalCocharacters_eq]
  rfl

private theorem marked_pairing (x : D.X) (y : D.Y) :
    pairing (diagonalTorus k D).val (markedCharacter D x) (markedCocharacter D y) =
      D.datum.toLinearMap x y := by
  rw [← character_marking, ← cocharacter_marking]
  exact diagonalPairing k D x y

/-- The character comparison is evaluation of the monomial in the full group algebra. -/
theorem markedCharacter_value (x : D.X) (R : TestAlgebra k)
    (f : MonoidAlgebra k (Multiplicative D.X) →ₐ[k] R) :
    characterValue (markedCharacter D x) R ((testSpec k).map (CommAlgCat.ofHom f).op) =
      f (MonoidAlgebra.single (Multiplicative.ofAdd x) 1) :=
  characterValue_monomial R f (Multiplicative.ofAdd x)

variable (M : Marking D G A)

private def markedSubgroup (i : D.I) : ClosedSubgroup G.val :=
  ⟨A.group, M.root i, M.rootClosed i⟩

private theorem marked_isRootSubgroup (i : D.I) :
    IsRootSubgroup M.T (markedSubgroup M i) (markedCharacter D (D.datum.root i)) := by
  refine ⟨?_, ⟨A.operations, A.comultiplication, A.counit, A.antipode, ⟨Iso.refl _⟩⟩,
    ?_, ?_⟩
  · change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    apply RingHom.smooth_algebraMap.mpr
    exact (show Algebra.Smooth k (Polynomial k) from by constructor <;> infer_instance)
  · apply normalizes_of_point_conjugation
    intro R t p
    obtain ⟨a, rfl⟩ := (additivePoints A R).surjective p
    refine ⟨additivePoints A R (characterValue (markedCharacter D (D.datum.root i)) R t * a), ?_⟩
    change additivePoints A R _ ≫ (M.root i).hom.hom =
      (t ≫ M.torus.hom.hom : GroupPoints G.val R) * (additivePoints A R a ≫ (M.root i).hom.hom) *
        (t ≫ M.torus.hom.hom)⁻¹
    rw [← rootPoint_eq, ← rootPoint_eq]
    exact (M.scalar i R t a).symm
  · exact tangent_weight_of_scalarAction M.T (markedSubgroup M i) _ A (Iso.refl _)
      (by simpa only [Marking.T, markedSubgroup, Iso.refl_hom, Category.id_comp] using M.scalar i)

private theorem marked_isRoot (i : D.I) :
    markedCharacter (k := k) D (D.datum.root i) ∈ absoluteRoots M.T := by
  refine ⟨?_, ?_⟩
  · intro h
    apply D.datum.ne_zero i
    apply (diagonalCharacters k D).injective
    rw [map_zero]
    exact Additive.toMul.injective ((character_marking (k := k) (D.datum.root i)).trans h)
  · let p : Lie k A.group :=
      ⟨rootPoint (𝟙 A.group) (CommAlgCat.of k (DualNumber k)) DualNumber.eps,
        rootPoint_eps_reduces _⟩
    refine ⟨mapPointKernel (M.root i) p, (marked_isRootSubgroup M i).2.2.2 ⟨p, rfl⟩, ?_⟩
    intro h
    have he := congrArg (fun v : Lie k G.val => v.toMul.val) h
    change rootPoint (M.root i) (CommAlgCat.of k (DualNumber k)) DualNumber.eps = 1 at he
    rw [← rootPoint_zero (M.root i) (CommAlgCat.of k (DualNumber k))] at he
    letI := mono_over (M.root i).hom.hom (M.rootClosed i)
    exact one_ne_zero (congrArg TrivSqZeroExt.snd
      (rootPoint_injective_of_mono (M.root i) _ he))

section RankOne

private def matrixWord {R : Type u} [CommRing R] (s : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  upper (s : R) * lower (-(↑s⁻¹ : R)) * upper (s : R)

private theorem matrixWord_factor {R : Type u} [CommRing R] (s : Rˣ) :
    matrixWord s = diagonal s * matrixWord 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixWord, upper, lower, diagonal, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_mul]

private theorem rankOne_word (i : D.I) (R : TestAlgebra k) (s : Rˣ) :
    cocharacterPoint (markedCocharacter D (D.datum.coroot i)) R s ≫ M.torus.hom.hom =
      rankOneWord (M.root i) (M.root (oppositeIndex D i)) R s *
        (rankOneWord (M.root i) (M.root (oppositeIndex D i)) R 1)⁻¹ := by
  let f := ((M.rankOne i).app R).hom
  have h : f (matrixWord s) = f (diagonal s) * f (matrixWord 1) := by
    rw [matrixWord_factor s, map_mul]
  have hw (b : Rˣ) : f (matrixWord b) =
      rankOneWord (M.root i) (M.root (oppositeIndex D i)) R b := by
    unfold matrixWord rankOneWord
    rw [map_mul, map_mul]
    exact congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (M.upper i R b) (M.lower i R (-(↑b⁻¹ : R)))) (M.upper i R b)
  rw [hw, hw] at h
  exact (M.diagonal i R s).symm.trans (eq_mul_inv_of_mul_eq h.symm)

private theorem opposite_character (i : D.I) :
    markedCharacter (k := k) D (D.datum.root (oppositeIndex D i)) =
      (markedCharacter D (D.datum.root i))⁻¹ := by
  rw [← character_marking, ← character_marking]
  have he : D.datum.root (oppositeIndex D i) = - D.datum.root i := by
    rw [oppositeIndex, D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  rw [he, map_neg]
  rfl

private theorem marked_reflection (i : D.I) :
    ∃ r : Specs.RootGroups.CorootReflection M.T (markedCharacter D (D.datum.root i))
      (M.root i) (M.root (oppositeIndex D i)), r.coroot = markedCocharacter D (D.datum.coroot i) := by
  let x := M.root i
  let y := M.root (oppositeIndex D i)
  let α := markedCharacter (k := k) D (D.datum.root i)
  let c := markedCocharacter (k := k) D (D.datum.coroot i)
  have hy : HasScalarAction M.T α⁻¹ y :=
    opposite_character (k := k) i ▸ M.scalar (oppositeIndex D i)
  let n := rankOneRepresentative x y
  have hn (R : TestAlgebra k) : toUnit _ ≫ n = rankOneWord x y R (1 : Rˣ) :=
    rankOneRepresentative_point x y R
  have hc : pairing M.T.group α c = 2 := by
    change pairing (diagonalTorus k D).val (markedCharacter D (D.datum.root i))
        (markedCocharacter D (D.datum.coroot i)) = 2
    rw [marked_pairing, D.datum.root_coroot_eq_pairing, D.datum.pairing_same]
  obtain ⟨r⟩ := LinearAlgebraicGroups.RootData.RootGroups.corootReflection_of_word
    M.T (diagonalSplit k D) α x y (M.scalar i) hy c n hn (rankOne_word M i) hc
  refine ⟨r, ?_⟩
  apply cocharacter_ext_units
  intro R b
  letI := mono_over M.torus.hom.hom M.torusClosed
  apply (cancel_mono M.torus.hom.hom).mp
  exact (r.coroot_word R b).trans (rankOne_word M i R b).symm

private theorem marked_coroot [IsCommMonObj M.T.group.X] (P : Datum M.T)
    (i : D.I) (a : Root M.T) (ha : a.val = markedCharacter D (D.datum.root i)) :
    Additive.toMul (P.rootDatum.coroot a) = markedCocharacter D (D.datum.coroot i) := by
  obtain ⟨r, hr⟩ := marked_reflection M i
  obtain ⟨N, hN, act, hact⟩ := P.normalizerAction
  obtain ⟨n, hn⟩ := (hN _ r.representative).mp r.normalizes
  obtain ⟨e, he, heW, _⟩ := hact n
  have he' : e = r.conjugation := by
    apply conjugation_unique M.T
    exact (by simpa only [← Category.assoc, hn, Category.assoc] using he :
      (e.hom ≫ M.T.inclusion).hom.hom = _).trans r.conjugates.symm
  let p := P.rootDatum.toLinearMap.flip (Additive.ofMul r.coroot)
  have hp : p (P.rootDatum.root a) = 2 := by
    change P.rootDatum.toLinearMap (P.rootDatum.root a) (Additive.ofMul r.coroot) = 2
    rw [P.root_eq, P.pairing_eq, ha, r.root_pairing]
  have hW (x : Additive (Character M.T.group)) :
      (act n).weightEquiv x = x - p x • P.rootDatum.root a := by
    let χ := Additive.toMul x
    change (act n).weightEquiv (Additive.ofMul χ) = _
    rw [heW, he', r.reflection, P.root_eq, ha, sub_eq_add_neg, ← neg_smul]
    change _ = x + (-P.rootDatum.toLinearMap (Additive.ofMul χ) (Additive.ofMul r.coroot)) • _
    rw [P.pairing_eq]
    rfl
  have h := coroot_functional_of_reflection P.rootDatum a (act n) p hp hW
  have hc : P.rootDatum.coroot a = Additive.ofMul r.coroot := P.rootDatum.flip.toPerfPair.injective h
  exact (congrArg Additive.toMul hc).trans hr

end RankOne

section Cell

private def rootFactors (R : TestAlgebra k) (a : D.I → R) :
    (l : List D.I) → Points (product (fun _ : D.I => A.group.X) l) R
  | [] => toUnit _
  | i :: l => lift (additivePoints A R (a i)) (rootFactors R a l)

private theorem rootFactors_eq_iff (R : TestAlgebra k) (a b : D.I → R) (l : List D.I) :
    rootFactors (A := A) R a l = rootFactors (A := A) R b l ↔ ∀ i ∈ l, a i = b i := by
  induction l with
  | nil => simp [rootFactors]
  | cons j l ih =>
    constructor
    · intro h i hi
      rw [List.mem_cons] at hi
      rcases hi with rfl | hi
      · apply (additivePoints A R).injective
        simpa only [rootFactors, lift_fst] using congrArg (· ≫ fst _ _) h
      · apply ih.mp _ i hi
        simpa only [rootFactors, lift_snd] using congrArg (· ≫ snd _ _) h
    · intro h
      apply CartesianMonoidalCategory.hom_ext
      · simp only [rootFactors, lift_fst, h j List.mem_cons_self]
      · simp only [rootFactors, lift_snd]
        exact ih.mpr (fun i hi => h i (List.mem_cons_of_mem _ hi))

private theorem rootFactors_surjective (R : TestAlgebra k) (l : List D.I) (hl : l.Nodup) :
    Function.Surjective (fun a : D.I → R => rootFactors (A := A) R a l) := by
  classical
  induction l with
  | nil => exact fun p => ⟨0, toUnit_unique _ _⟩
  | cons j l ih =>
    intro p
    obtain ⟨a, ha⟩ := (additivePoints A R).surjective (p ≫ fst _ _)
    obtain ⟨b, hb⟩ := ih hl.of_cons (p ≫ snd _ _)
    refine ⟨Function.update b j a, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [rootFactors, lift_fst, Function.update_self] using ha
    · simp only [rootFactors, lift_snd]
      rw [← hb]
      apply (rootFactors_eq_iff R _ _ l).mpr
      intro i hi
      have hne : i ≠ j := fun he => (List.nodup_cons.mp hl).1 (by rwa [← he])
      exact Function.update_of_ne hne a b

private theorem rootFactors_map {R S : TestAlgebra k} (f : R ⟶ S) (a : D.I → R)
    (l : List D.I) :
    mapPoints f (rootFactors (A := A) R a l) =
      rootFactors (A := A) S (fun i => f.hom (a i)) l := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons i l ih =>
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [mapPoints, Category.assoc, rootFactors, lift_fst]
        using additivePoints_natural A f (a i)
    · simpa only [mapPoints, Category.assoc, rootFactors, lift_snd] using ih

private theorem rootFactors_eval (R : TestAlgebra k) (a : D.I → R)
    (l : List D.I) :
    rootFactors R a l ≫ rootProduct M.root l =
      (l.map fun i => rootPoint (M.root i) R (a i)).prod := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons i l ih =>
    simp only [rootFactors, rootProduct, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc,
      List.map_cons, List.prod_cons, ih]
    rfl

private def chartPoint (R : TestAlgebra k) (negative positive : List D.I)
    (an ap : D.I → R) (t : GroupPoints M.T.group R) :
    Points (product (fun _ : D.I => A.group.X) negative ⊗
      ((diagonalTorus k D).val.X ⊗ product (fun _ : D.I => A.group.X) positive)) R :=
  lift (rootFactors R an negative) (lift t (rootFactors R ap positive))

private theorem chartPoint_eval (R : TestAlgebra k) (negative positive : List D.I)
    (an ap : D.I → R) (t : GroupPoints M.T.group R) :
    chartPoint M R negative positive an ap t ≫ cellMap M.torus M.root negative positive =
      (negative.map fun i => rootPoint (M.root i) R (an i)).prod *
        ((((groupPointsFunctor k).map M.torus).app R t) *
        (positive.map fun i => rootPoint (M.root i) R (ap i)).prod) := by
  change _ = _ * ((show GroupPoints G.val R from t ≫ M.torus.hom.hom) * _)
  simp only [chartPoint, cellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, rootFactors_eval]

private theorem chartPoint_identity (R : TestAlgebra k) (negative positive : List D.I) :
    chartPoint M R negative positive 0 0 1 ≫ cellMap M.torus M.root negative positive = 1 := by
  rw [chartPoint_eval]
  have hT : ((groupPointsFunctor k).map M.torus).app R (1 : GroupPoints M.T.group R) = 1 :=
    map_one (((groupPointsFunctor k).map M.torus).app R).hom
  rw [hT]
  have h (l : List D.I) :
      (l.map fun i => rootPoint (M.root i) R 0).prod = 1 := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [rootPoint_zero]
  change (negative.map fun i => rootPoint (M.root i) R 0).prod *
      ((1 : GroupPoints G.val R) * (positive.map fun i => rootPoint (M.root i) R 0).prod) = 1
  rw [h, h, one_mul, one_mul]

private abbrev base (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev dual (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

private theorem reduction_surjective_on_spectra (k : Type u) [Field k] :
    Function.Surjective (((testSpec k).map (dualReduction k).op).left) := by
  let f := (TrivSqZeroExt.fstHom k k k).toRingHom
  change Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ f (fun x => ⟨⟨x, 0⟩, rfl⟩),
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  have h := Ideal.pow_mem_pow (I := TrivSqZeroExt.kerIdeal k k) hx 2
  rw [TrivSqZeroExt.kerIdeal_sq, Ideal.mem_bot] at h
  exact ⟨2, h⟩

private theorem lift_tangent_to_cell {negative positive : List D.I}
    (h : IsOpenImmersion (cellMap M.torus M.root negative positive).left)
    (v : Lie k G.val) :
    ∃ q : Points _ (dual k), q ≫ cellMap M.torus M.root negative positive = v.toMul.val := by
  let f := cellMap M.torus M.root negative positive
  letI : IsOpenImmersion f.left := h
  let q₀ := chartPoint M (base k) negative positive 0 0 1
  have h₀ : q₀ ≫ f = 1 := chartPoint_identity M _ _ _
  have hsub : Set.range v.toMul.val.left ⊆ Set.range f.left := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := (reduction_surjective_on_spectra k) j
    have h₁ := congrArg Over.Hom.left v.toMul.property
    have h₂ := congrArg Over.Hom.left h₀
    refine ⟨q₀.left i, ?_⟩
    exact (congrArg (fun a : _ ⟶ G.val.X.left => a i) (h₁.trans h₂.symm)).symm
  let q : Points _ (dual k) :=
    Over.homMk (IsOpenImmersion.lift f.left v.toMul.val.left hsub) (by
      rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w v.toMul.val]
      rfl)
  exact ⟨q, Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)⟩

private theorem chartPoint_covers_tangent {negative positive : List D.I}
    (hn : negative.Nodup) (hp : positive.Nodup)
    (h : IsOpenImmersion (cellMap M.torus M.root negative positive).left)
    (v : Lie k G.val) :
    ∃ (an ap : D.I → DualNumber k) (t : GroupPoints M.T.group (dual k)),
      chartPoint M (dual k) negative positive an ap t ≫
        cellMap M.torus M.root negative positive = v.toMul.val ∧
      (∀ i ∈ negative, (an i).fst = 0) ∧ (∀ i ∈ positive, (ap i).fst = 0) ∧
      mapPoints (dualReduction k) t = 1 := by
  let f := cellMap M.torus M.root negative positive
  letI : IsOpenImmersion f.left := h
  letI : Mono f := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono f.left))
  obtain ⟨q, hq⟩ := lift_tangent_to_cell M h v
  obtain ⟨an, han⟩ := rootFactors_surjective (A := A) (dual k) negative hn (q ≫ fst _ _)
  obtain ⟨ap, hap⟩ := rootFactors_surjective (A := A) (dual k) positive hp (q ≫ snd _ _ ≫ snd _ _)
  let t : GroupPoints M.T.group (dual k) := q ≫ snd _ _ ≫ fst _ _
  have hc : chartPoint M (dual k) negative positive an ap t = q := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [chartPoint, lift_fst] using han
    · simp only [chartPoint, lift_snd]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [t, lift_fst, Category.assoc]
      · simpa only [lift_snd, Category.assoc] using hap
  have hbase : mapPoints (dualReduction k) q = chartPoint M (base k) negative positive 0 0 1 := by
    apply (cancel_mono f).mp
    change (mapPoints (dualReduction k) q) ≫ f =
      chartPoint M (base k) negative positive 0 0 1 ≫ f
    rw [chartPoint_identity]
    exact (congrArg (mapPoints (dualReduction k)) hq).trans v.toMul.property
  rw [← hc] at hbase
  have hleft := congrArg (· ≫ fst _ _) hbase
  have hright := congrArg (· ≫ snd _ _) hbase
  have htorus := congrArg (· ≫ fst _ _) hright
  have hpos := congrArg (· ≫ snd _ _) hright
  simp only [mapPoints, chartPoint, Category.assoc, lift_fst, lift_snd] at hleft hpos htorus
  change mapPoints (dualReduction k) (rootFactors (A := A) (dual k) an negative) = _ at hleft
  change mapPoints (dualReduction k) (rootFactors (A := A) (dual k) ap positive) = _ at hpos
  rw [rootFactors_map] at hleft hpos
  exact ⟨an, ap, t, (congrArg (· ≫ f) hc).trans hq, (rootFactors_eq_iff _ _ _ _).mp hleft,
    (rootFactors_eq_iff _ _ _ _).mp hpos, htorus⟩

open private adjointWeightsInternal from LinearAlgebraicGroups.RootData.RootGroups

private theorem roots_surjective (hG : IsReductive G) (χ : Character M.T.group)
    (hχ : χ ∈ absoluteRoots M.T) : ∃ i, markedCharacter D (D.datum.root i) = χ := by
  classical
  by_contra! hmiss
  obtain ⟨hχ₁, v, hv, hv₀⟩ := hχ
  obtain ⟨negative, positive, hn, hp, ho⟩ := M.openCell
  obtain ⟨an, ap, t, he, han, hap, ht⟩ := chartPoint_covers_tangent M hn.1 hp.1 ho v
  let s := LinearAlgebraicGroups.identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  let W (α : Character M.T.group) := Specs.CharacterPairing.adjointWeightSpace M.T α s
  let S := ⨆ α ∈ ({χ} : Set (Character M.T.group))ᶜ, W α
  have hsub (α : Character M.T.group) (h : α ≠ χ) : W α ≤ S :=
    le_iSup_of_le α (le_iSup_of_le (by simpa using h) le_rfl)
  have hlift : ∀ (i : D.I) (d : DualNumber k) (hd : d.fst = 0),
      ∃ w : Lie k G.val, w ∈ S ∧ w.toMul.val = rootPoint (M.root i) (dual k) d := by
    intro i d hd
    have h : mapPoints (dualReduction k) (rootPoint (𝟙 A.group) (dual k) d) = 1 := by
      rw [rootPoint_natural, show (dualReduction k).hom d = 0 from hd, rootPoint_zero]
    let p : Lie k A.group := ⟨rootPoint (𝟙 A.group) (dual k) d, h⟩
    let w := mapPointKernel (M.root i) p
    refine ⟨w, hsub _ (hmiss i) ?_, rfl⟩
    exact Submodule.subset_span ((marked_isRootSubgroup M i).2.2.2 ⟨p, rfl⟩)
  have hprod (a : D.I → DualNumber k) (l : List D.I)
      (ha : ∀ i ∈ l, (a i).fst = 0) :
      ∃ w : Lie k G.val, w ∈ S ∧ w.toMul.val =
        (l.map fun i => rootPoint (M.root i) (dual k) (a i)).prod := by
    induction l with
    | nil => exact ⟨0, S.zero_mem, rfl⟩
    | cons i l ih =>
      obtain ⟨p, hp, hpe⟩ := hlift i (a i) (ha i List.mem_cons_self)
      obtain ⟨q, hq, hqe⟩ := ih (fun j hj => ha j (List.mem_cons_of_mem _ hj))
      refine ⟨p + q, S.add_mem hp hq, ?_⟩
      change p.toMul.val * q.toMul.val = _
      rw [hpe, hqe, List.map_cons, List.prod_cons]
  obtain ⟨vn, hvn, en⟩ := hprod an negative han
  obtain ⟨vp, hvp, ep⟩ := hprod ap positive hap
  let vT : Lie k M.T.group := ⟨t, ht⟩
  let vt := mapPointKernel M.T.inclusion vT
  have hvt : vt ∈ S := by
    apply hsub 1 (Ne.symm hχ₁)
    apply Submodule.subset_span
    rw [← (LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups
      G hG M.T (diagonalSplit k D) M.maximal).1.2]
    exact ⟨vT, rfl⟩
  have hvsum : v = vn + (vt + vp) := by
    apply Subtype.ext
    change v.toMul.val = vn.toMul.val * (vt.toMul.val * vp.toMul.val)
    rw [en, ep, ← he, chartPoint_eval]
    rfl
  have hS : v ∈ S := hvsum.symm ▸ S.add_mem hvn (S.add_mem hvt hvp)
  have hdis : Disjoint (W χ) S :=
    (adjointWeightsInternal G M.T (diagonalSplit k D) s).submodule_iSupIndep.disjoint_biSup (by simp)
  exact hv₀ ((Submodule.disjoint_def.mp hdis) v (Submodule.subset_span hv) hS)

private def rootIndex (M : Marking D G A) (hG : IsReductive G) : D.I ≃ Root M.T :=
  Equiv.ofBijective (fun i => ⟨markedCharacter D (D.datum.root i), marked_isRoot M i⟩)
    ⟨fun i j h => D.datum.root.injective ((diagonalCharacters k D).injective
      (Additive.toMul.injective ((character_marking _).trans
        ((congrArg Subtype.val h).trans (character_marking _).symm)))),
      fun a => by
        obtain ⟨i, hi⟩ := roots_surjective M hG a.val a.property
        exact ⟨i, Subtype.ext hi⟩⟩

end Cell

section Realization

private theorem marked_simple (e : D.I ≃ Root M.T) (B : ClosedSubgroup G.val)
    (hG : IsReductive G) (hT : IsSplitTorus M.T.group)
    (hB : Specs.GeometricBorelConjugacy.IsKBorel B)
    (hTB : Specs.SchemeDerivedGroup.IsSubgroupOf M.T B)
    (hα : ∀ i, (e i).val = markedCharacter D (D.datum.root i))
    (hpos : ∀ i, e i ∈ subgroupRoots M.T B ↔ D.base.IsPos i) (i : D.I) :
    IsSimple (M.pair hG hT B hB hTB) (e i) ↔ i ∈ D.base.support := by
  rw [LinearAlgebraicGroups.RationalRealization.simple_of_positive_height]
  change ((e i ∈ subgroupRoots M.T B) ∧
    ∀ β ∈ subgroupRoots M.T B, ∀ δ ∈ subgroupRoots M.T B, (e i).val ≠ β.val * δ.val) ↔ _
  have he (j : D.I) : (e j).val = Additive.toMul (diagonalCharacters k D (D.datum.root j)) :=
    (hα j).trans (character_marking _).symm
  have hsum (j l : D.I) : (e i).val = (e j).val * (e l).val ↔
      D.datum.root i = D.datum.root j + D.datum.root l := by
    rw [he i, he j, he l]
    change Additive.toMul (diagonalCharacters k D (D.datum.root i)) =
      Additive.toMul (diagonalCharacters k D (D.datum.root j) +
        diagonalCharacters k D (D.datum.root l)) ↔ _
    rw [← map_add]
    exact Additive.toMul.injective.eq_iff.trans (diagonalCharacters k D).injective.eq_iff
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨(hpos i).mp hi, fun j hj l hl h =>
      hs _ ((hpos j).mpr hj) _ ((hpos l).mpr hl) ((hsum j l).mpr h)⟩
  · rintro ⟨hi, hs⟩
    refine ⟨(hpos i).mpr hi, ?_⟩
    intro β hβ δ hδ
    obtain ⟨j, rfl⟩ := e.surjective β
    obtain ⟨l, rfl⟩ := e.surjective δ
    exact fun h => hs j ((hpos j).mp hβ) l ((hpos l).mp hδ) ((hsum j l).mp h)

set_option maxHeartbeats 1400000 in
private theorem realization_of_positive_roots (hG : IsReductive G) (hT : IsSplitTorus M.T.group)
    (B : ClosedSubgroup G.val) (hB : Specs.GeometricBorelConjugacy.IsKBorel B)
    (hTB : Specs.SchemeDerivedGroup.IsSubgroupOf M.T B) (e : D.I ≃ Root M.T)
    (he : ∀ i, (e i).val = markedCharacter D (D.datum.root i))
    (hp : ∀ i, e i ∈ subgroupRoots M.T B ↔ D.base.IsPos i) :
    Nonempty (FibreRealization M hG) := by
  classical
  let P := M.pair hG hT B hB hTB
  let E := LinearAlgebraicGroups.Classification.Pinning.attachedDatum P
  letI : IsCommMonObj P.T.group.X := E.comm
  letI : IsCommMonObj M.T.group.X := E.comm
  let f := diagonalCharacters k D
  let g := diagonalCocharacters k D
  have hcor (i : D.I) : E.datum.rootDatum.coroot (e i) = g (D.datum.coroot i) := by
    apply Additive.toMul.injective
    exact (marked_coroot M E.datum i (e i) (he i)).trans (cocharacter_marking _).symm
  let d : D.datum.Equiv E.toBased.datum :=
    { weightMap := f.toLinearMap
      coweightMap := g.symm.toLinearMap
      indexEquiv := e
      weight_coweight_transpose := by
        ext y x
        obtain ⟨z, rfl⟩ := g.surjective y
        change E.datum.rootDatum.toLinearMap (f x) (g z) =
          D.datum.toLinearMap x (g.symm (g z))
        rw [LinearEquiv.symm_apply_apply]
        exact (E.datum.pairing_eq (Additive.toMul (f x)) (Additive.toMul (g z))).trans
          (diagonalPairing k D x z)
      root_weightMap := by
        funext i
        change f (D.datum.root i) = E.datum.rootDatum.root (e i)
        rw [E.datum.root_eq]
        apply Additive.toMul.injective
        exact (character_marking _).trans (he i).symm
      coroot_coweightMap := by
        funext a
        obtain ⟨i, rfl⟩ := e.surjective a
        change g.symm (E.datum.rootDatum.coroot (e i)) = D.datum.coroot (e.symm (e i))
        rw [hcor i, LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply]
      bijective_weightMap := f.bijective
      bijective_coweightMap := g.symm.bijective }
  have hs (i : D.I) : e i ∈ E.base.support ↔ i ∈ D.base.support :=
    (E.simple_iff (e i)).trans (marked_simple M e B hG hT hB hTB he hp i)
  have hbase : e '' (D.base.support : Set D.I) = (E.toBased.base.support : Set E.toBased.I) := by
    ext a
    obtain ⟨i, rfl⟩ := e.surjective a
    constructor
    · rintro ⟨j, hj, h⟩
      exact (hs i).mpr (e.injective h ▸ hj)
    · intro hi
      exact ⟨i, (hs i).mp hi, rfl⟩
  let U : RootSubgroupFamily M.T := fun a =>
    ⟨markedSubgroup M (e.symm a), by
      rw [← show markedCharacter (k := k) D (D.datum.root (e.symm a)) = a.val from
        (he _).symm.trans (congrArg Subtype.val (e.apply_symm_apply a))]
      exact marked_isRootSubgroup M (e.symm a)⟩
  let x : ∀ a : Root M.T, RootCoordinate A M.T (U a).val a.val := fun a =>
    ⟨Iso.refl _, by
      simp only [Iso.refl_hom, Category.id_comp]
      change HasScalarAction M.T a.val (M.root (e.symm a))
      rw [← congrArg Subtype.val (e.apply_symm_apply a), he]
      exact M.scalar (e.symm a)⟩
  refine ⟨⟨hT, B, hB, hTB, U, x, E, ⟨d, hbase⟩, character_marking, ?_, hp, ?_⟩⟩
  · intro y
    have h : d.coweightEquiv.symm y = g y := d.coweightEquiv.injective
      ((d.coweightEquiv.apply_symm_apply y).trans (g.symm_apply_apply y).symm)
    exact (congrArg Additive.toMul h).trans (cocharacter_marking y)
  · intro i
    change 𝟙 A.group ≫ M.root (e.symm (e i)) = M.root i
    rw [Category.id_comp, e.symm_apply_apply]

/-- Identify the actual based datum of the marked field fibre and pin it by the original
simple coordinates. -/
theorem integralFibreDatum : Statement.{u} := by
  classical
  intro k _ D G hG A M
  let hT : IsSplitTorus M.T.group := diagonalSplit k D
  let e := rootIndex M hG
  have he (i : D.I) : (e i).val = markedCharacter D (D.datum.root i) := rfl
  obtain ⟨y, m, hm, hy⟩ := LinearAlgebraicGroups.RationalRealization.positiveIntegralCocharacter D
  let c : Cocharacter M.T.group := markedCocharacter D y
  have hc (i : D.I) : pairing M.T.group (e i).val c = m * D.base.height i := by
    rw [he]
    exact (marked_pairing (k := k) (D.datum.root i) y).trans (hy i)
  have hr : IsRegular M.T c := by
    intro α
    obtain ⟨i, rfl⟩ := e.surjective α
    rw [hc]
    exact mul_ne_zero hm.ne' (D.base.height_ne_zero i)
  obtain ⟨L⟩ := LinearAlgebraicGroups.CocharacterDynamics.existsLimitDecomposition G (c ≫ M.torus)
  obtain ⟨_, hB, hTB, hpos, _⟩ :=
    LinearAlgebraicGroups.RootData.BorelsAndChambers.regularCocharacterBorel
      G hG M.T hT M.maximal c hr L
  have hp (i : D.I) : e i ∈ subgroupRoots M.T L.parabolic ↔ D.base.IsPos i := by
    rw [hpos]
    change 0 < pairing M.T.group (e i).val c ↔ 0 < D.base.height i
    rw [hc]
    exact mul_pos_iff_of_pos_left hm
  exact realization_of_positive_roots M hG hT L.parabolic hB hTB e he hp

end Realization

end

end LinearAlgebraicGroups.Classification.IntegralFibreDatum
