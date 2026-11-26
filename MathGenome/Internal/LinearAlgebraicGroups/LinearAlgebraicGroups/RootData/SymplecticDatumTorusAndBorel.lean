import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Matrix Opposite
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel

open _root_.LinearAlgebraicGroups.Specs
open Specs.SymplecticDatumTorusAndBorel Specs.SymplecticMatrixStructure

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1400000
set_option maxRecDepth 768

section MatrixWeights

private lemma universal_left_entry (k : Type u) [Field k] (n : ℕ)
    (i : Indices (HyperbolicIndex.{u} n)) :
    (Sum.elim (fun j => (universalTorusUnits k n j : LaurentCoordinates k n))
      (fun j => (((universalTorusUnits k n j)⁻¹ : (LaurentCoordinates k n)ˣ) :
        LaurentCoordinates k n))) i = AddMonoidAlgebra.single (indexWeight i) (1 : k) := by
  cases i with
  | inl j => rfl
  | inr j =>
    change (↑(((AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits
      (Multiplicative.ofAdd (coordinate j.down)))⁻¹) : LaurentCoordinates k n) = _
    rw [← map_inv]
    rfl

private lemma universal_right_entry (k : Type u) [Field k] (n : ℕ)
    (i : Indices (HyperbolicIndex.{u} n)) :
    (Sum.elim (fun j => (↑(((universalTorusUnits k n j)⁻¹) :
        (LaurentCoordinates k n)ˣ) : LaurentCoordinates k n))
      (fun j => (universalTorusUnits k n j : LaurentCoordinates k n))) i =
      AddMonoidAlgebra.single (-indexWeight i) (1 : k) := by
  cases i with
  | inl j =>
    simpa only [Sum.elim_inr, Sum.elim_inl, indexWeight] using
      universal_left_entry k n (Sum.inr j)
  | inr j =>
    simp only [Sum.elim_inr, indexWeight, neg_neg]
    rfl

private lemma matrixWeightEntriesAux (k : Type u) [Field k] (n : ℕ)
    (x : Fin n → ℤ) (X : MatrixAlgebra (HyperbolicIndex.{u} n) k) :
    MatrixHasWeight x X ↔ ∀ i j,
      (AddMonoidAlgebra.single (indexWeight i - indexWeight j) (X i j) :
        LaurentCoordinates k n) = AddMonoidAlgebra.single x (X i j) := by
  unfold MatrixHasWeight
  rw [← Matrix.ext_iff]
  simp only [hyperbolicDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul, inv_inv, universal_left_entry, universal_right_entry,
    Matrix.map_apply]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change (AddMonoidAlgebra.single (indexWeight i) 1 *
    AddMonoidAlgebra.single 0 (X i j)) * AddMonoidAlgebra.single (-indexWeight j) 1 =
      AddMonoidAlgebra.single x 1 * AddMonoidAlgebra.single 0 (X i j) ↔ _
  simp [AddMonoidAlgebra.single_mul_single, sub_eq_add_neg]

theorem matrixWeightEntries : MatrixWeightEntries.{u} := by
  intro k _ n x X
  rw [matrixWeightEntriesAux]
  constructor
  · intro h i j hne
    by_contra h'
    have hcoeff := congrArg
      (fun p : LaurentCoordinates k n => p.coeff (indexWeight i - indexWeight j)) (h i j)
    apply hne
    simpa [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, h'] using hcoeff
  · intro h i j
    by_cases hzero : X i j = 0
    · simp [hzero]
    · rw [h i j hzero]

private lemma signedIndex_weight {n : ℕ} (i : Fin n) (s : Bool) :
    indexWeight (signedIndex.{u} i s) = sign s • coordinate i := by
  cases s <;> simp [signedIndex, indexWeight, sign]

private lemma sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> decide

private lemma signedWeight_difference {n : ℕ} (i j : Fin n) (s t : Bool)
    (h : indexWeight (signedIndex.{u} i s) - indexWeight (signedIndex.{u} j t) ≠ 0) :
    ∃ a : RootLabel n,
      indexWeight (signedIndex.{u} i s) - indexWeight (signedIndex.{u} j t) = rootVector a := by
  simp only [signedIndex_weight] at h ⊢
  rcases lt_trichotomy i j with hlt | heq | hgt
  · refine ⟨.short i j hlt s (!t), ?_⟩
    simp [rootVector, sign_not, sub_eq_add_neg]
  · subst j
    by_cases hst : s = t
    · subst t
      exact (h (sub_self _)).elim
    · refine ⟨.long i s, ?_⟩
      cases s <;> cases t <;> simp_all [sign, rootVector] <;>
        ext l <;> simp <;> ring
  · refine ⟨.short j i hgt (!t) s, ?_⟩
    simp [rootVector, sign_not, sub_eq_add_neg, add_comm]

private lemma signedIndex_surj {n : ℕ} (p : Indices (HyperbolicIndex.{u} n)) :
    ∃ i b, p = signedIndex i b := by
  rcases p with i | i
  · exact ⟨i.down, true, rfl⟩
  · exact ⟨i.down, false, rfl⟩

private lemma element_position_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    signedIndex.{u} i s ≠ signedIndex j t := by
  intro h
  apply hij
  have hp := congrArg (Sum.elim ULift.down ULift.down) h
  cases s <;> cases t <;> exact hp

private lemma J_mul_element {k : Type u} [Field k] {n : ℕ} (i : Fin n) (b : Bool)
    (q : Indices (HyperbolicIndex.{u} n)) (a : k) :
    Matrix.J _ k * Matrix.single (signedIndex i b) q a =
      Matrix.single (signedIndex i (!b)) q ((sign b : k) * a) := by
  ext r s
  by_cases hs : s = q
  · subst s
    rw [Matrix.mul_single_apply_same]
    rcases r with ⟨r⟩ | ⟨r⟩ <;> cases b <;>
      simp [Matrix.J, signedIndex, sign, Matrix.single_apply, Matrix.one_apply, eq_comm]
    split_ifs <;> simp_all
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hs]
    simp [Ne.symm hs]

theorem matrixLieWeights : MatrixLieWeights.{u} := by
  intro k _ n
  have he (a : RootLabel n) :
      elementaryDirection k a ∈ symplecticLieSubspace k (HyperbolicIndex.{u} n) ∧
      elementaryDirection k a ≠ 0 ∧ MatrixHasWeight (rootVector a) (elementaryDirection k a) := by
    cases a with
    | long i b =>
      refine ⟨?_, ?_, ?_⟩
      · change (Matrix.J _ k * elementaryDirection k (.long i b)).IsSymm
        simp only [elementaryDirection]
        rw [J_mul_element, Matrix.IsSymm, Matrix.transpose_single]
      · intro h
        have hx := congrFun (congrFun h (signedIndex.{u} i b)) (signedIndex i (!b))
        simp [elementaryDirection] at hx
      · apply (matrixWeightEntries k n _ _).mpr
        intro p q hp
        have hpq : signedIndex.{u} i b = p ∧ signedIndex.{u} i (!b) = q := by
          by_contra h
          exact hp (by simp [elementaryDirection, h])
        obtain ⟨rfl, rfl⟩ := hpq
        simp only [rootVector, signedIndex_weight, sign_not]
        ext j
        simp [Pi.smul_apply]
        ring
    | short i j hij b c =>
      have hne := element_position_ne.{u} (Fin.ne_of_lt hij) b c
      refine ⟨?_, ?_, ?_⟩
      · change (Matrix.J _ k * elementaryDirection k (.short i j hij b c)).IsSymm
        simp only [elementaryDirection]
        rw [Matrix.mul_add, J_mul_element, J_mul_element, Matrix.IsSymm, Matrix.transpose_add,
          Matrix.transpose_single, Matrix.transpose_single]
        cases b <;> cases c <;> simp [sign, add_comm]
      · intro h
        have hx := congrFun (congrFun h (signedIndex.{u} i b)) (signedIndex j (!c))
        simp [elementaryDirection, Ne.symm hne] at hx
      · apply (matrixWeightEntries k n _ _).mpr
        intro p q hp
        have hpq :
            (signedIndex.{u} i b = p ∧ signedIndex.{u} j (!c) = q) ∨
            (signedIndex.{u} j c = p ∧ signedIndex.{u} i (!b) = q) := by
          by_contra h
          have h₁ : ¬ (signedIndex.{u} i b = p ∧ signedIndex j (!c) = q) :=
            fun hz => h (Or.inl hz)
          have h₂ : ¬ (signedIndex.{u} j c = p ∧ signedIndex i (!b) = q) :=
            fun hz => h (Or.inr hz)
          exact hp (by simp [elementaryDirection, h₁, h₂])
        rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [rootVector, signedIndex_weight, sign_not, sub_eq_add_neg, add_comm]
  refine ⟨?_, he⟩
  intro x hx
  constructor
  · rintro ⟨X, hX, hw⟩
    have hex : ∃ i j, X.val i j ≠ 0 := by
      by_contra h
      apply hX
      push Not at h
      exact Matrix.ext h
    obtain ⟨p, q, hpq⟩ := hex
    have hd := (matrixWeightEntries k n x X.val).mp hw p q hpq
    obtain ⟨i, s, rfl⟩ := signedIndex_surj p
    obtain ⟨j, t, rfl⟩ := signedIndex_surj q
    rw [hd] at hx ⊢
    exact signedWeight_difference i j s t hx
  · rintro ⟨a, rfl⟩
    exact ⟨⟨_, (he a).1⟩, (he a).2⟩

end MatrixWeights

section Lattices

open Specs.StandardGroups (multiplicativePowerPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue pairing powerMorphism)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra groupAlgebraMap
  characterValuedPoints)
open CocharacterDynamics (cocharacterPoint unitPoint)
open LinearAlgebraicGroups.DiagonalizableGroups (groupAlgebraPointsIso)

open private integerHomEquiv pointsIso_precompose pointsIso_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private unitEquiv_unitPoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private exponentsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private charactersOfIso cocharactersOfIso homToDual integerExponent integerExponent_zpow
  pairing_eq_iff characterValue_monomial algebraPoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private isCommMonObj_of_groupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private abbrev Exponents (n : ℕ) := Multiplicative (HyperbolicIndex.{u} n → ℤ)

private def modelPoints (k : Type u) [Field k] (n : ℕ) :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k (Exponents.{u} n))) ≅
      multiplicativePowerPoints k (HyperbolicIndex.{u} n) :=
  groupAlgebraPointsIso k _ ≪≫ NatIso.ofComponents
    (fun R => (exponentsEquiv R).toGrpIso)
    (by intro R S f; apply GrpCat.ext; intro a; rfl)

private lemma pointIso_roundtrip {k : Type u} [Field k]
    {F H : TestAlgebra k ⥤ GrpCat.{u}} (p : F ≅ H) (R : TestAlgebra k) (t : H.obj R) :
    p.hom.app R (p.inv.app R t) = t :=
  (p.app R).inv_hom_id_apply t

private def schemeIsoOfPointIso {k : Type u} [Field k] {A B : GroupScheme k}
    (hA : IsAffine A.X.left) (hB : IsAffine B.X.left)
    (p : (groupPointsFunctor k).obj A ≅ (groupPointsFunctor k).obj B) :
    A ≅ B where
  hom := (groupHomEquiv A B hA).symm p.hom
  inv := (groupHomEquiv B A hB).symm p.inv
  hom_inv_id := by
    apply (groupHomEquiv A A hA).injective
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 A)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id]
    exact congrArg₂ (· ≫ ·) ((groupHomEquiv A B hA).apply_symm_apply p.hom)
      ((groupHomEquiv B A hB).apply_symm_apply p.inv) |>.trans p.hom_inv_id
  inv_hom_id := by
    apply (groupHomEquiv B B hB).injective
    change (groupPointsFunctor k).map (_ ≫ _) = (groupPointsFunctor k).map (𝟙 B)
    rw [Functor.map_comp, (groupPointsFunctor k).map_id]
    exact congrArg₂ (· ≫ ·) ((groupHomEquiv B A hB).apply_symm_apply p.inv)
      ((groupHomEquiv A B hA).apply_symm_apply p.hom) |>.trans p.inv_hom_id

private def exponentCoordinates (n : ℕ) : Additive (Exponents.{u} n) ≃ₗ[ℤ] (Fin n → ℤ) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun x i => x.toMul.toAdd ⟨i⟩
      invFun := fun a => Additive.ofMul (Multiplicative.ofAdd (fun i => a i.down))
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intros; rfl }

private def dualCoordinates (n : ℕ) :
    Module.Dual ℤ (Additive (Exponents.{u} n)) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (((Pi.basisFun ℤ (Fin n)).map (exponentCoordinates n).symm).dualBasis).equivFun

private lemma dualCoordinates_apply {n : ℕ} (f : Module.Dual ℤ (Additive (Exponents.{u} n)))
    (i : Fin n) :
    dualCoordinates n f i =
      f (Additive.ofMul (Multiplicative.ofAdd (Pi.single (⟨i⟩ : HyperbolicIndex.{u} n) 1))) := by
  rw [dualCoordinates, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr,
    Module.Basis.map_apply, Pi.basisFun_apply]
  apply congrArg f
  change (fun j : HyperbolicIndex.{u} n => (Pi.single i (1 : ℤ) : Fin n → ℤ) j.down) =
    Pi.single (⟨i⟩ : HyperbolicIndex.{u} n) 1
  funext j
  cases j
  simp [Pi.single_apply]

private lemma basis_sum {n : ℕ} (x : Fin n → ℤ) : ∑ i, x i • coordinate i = x := by
  ext j
  simp [coordinate, Finset.sum_apply, Pi.single_apply]

private lemma dot_dual {n : ℕ} (f : Module.Dual ℤ (Additive (Exponents.{u} n)))
    (m : Exponents.{u} n) :
    f (Additive.ofMul m) = ∑ i, exponentCoordinates n (Additive.ofMul m) i *
      dualCoordinates n f i := by
  let x := exponentCoordinates n (Additive.ofMul m)
  change f ((exponentCoordinates n).symm x) = _
  conv_lhs => rw [← basis_sum x]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change f ((exponentCoordinates n).symm (x i • coordinate i)) =
    x i * dualCoordinates n f i
  rw [LinearEquiv.map_smul, LinearMap.map_smul, zsmul_eq_mul]
  congr 1
  unfold dualCoordinates coordinate
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr,
    Module.Basis.map_apply, Pi.basisFun_apply]

private theorem latticeCoordinates {k : Type u} [Field k] {T : GroupScheme k}
    (hT : IsAffine T.X.left) (n : ℕ)
    (d : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (HyperbolicIndex.{u} n)) :
    Nonempty (LatticeCoordinates d) := by
  let M := Exponents.{u} n
  let A := specGroup (groupAlgebra k M)
  have hA : IsAffine A.X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M)))
    infer_instance
  let p := modelPoints k n ≪≫ d.symm
  let j : A ≅ T := schemeIsoOfPointIso hA hT p
  have jpoints : (groupPointsFunctor k).map j.hom = p.hom :=
    (groupHomEquiv A T hA).apply_symm_apply p.hom
  let hcomm : IsCommMonObj T.X := isCommMonObj_of_groupIso j inferInstance
  letI := hcomm
  let ch : M ≃* Character A :=
    (integerHomEquiv M).trans (splitGroupHomEquiv IntegerCharacters M)
  let co : (M →* IntegerCharacters.{u}) ≃* Cocharacter A := splitGroupHomEquiv M IntegerCharacters
  let chT := ch.trans (charactersOfIso j)
  let coT := co.trans (cocharactersOfIso j)
  let X : Additive (Character T) ≃ₗ[ℤ] (Fin n → ℤ) := chT.symm.toAdditive.toIntLinearEquiv.trans (exponentCoordinates n)
  let Y : Additive (Cocharacter T) ≃ₗ[ℤ] (Fin n → ℤ) := coT.symm.toAdditive.toIntLinearEquiv.trans ((homToDual M).trans (dualCoordinates n))
  refine ⟨⟨hcomm, X, Y, ?_, ?_, ?_⟩⟩
  · intro R t χ
    obtain ⟨m, rfl⟩ := chT.surjective χ
    have hX : X (Additive.ofMul (chT m)) = exponentCoordinates n (Additive.ofMul m) := by
      change exponentCoordinates n (Additive.ofMul (chT.symm (chT m))) = _
      rw [MulEquiv.symm_apply_apply]
    let a : Points A.X R := (modelPoints k n).inv.app R t
    have ha : a ≫ j.hom.hom.hom = d.inv.app R t := by
      change ((groupPointsFunctor k).map j.hom).app R a = _
      rw [jpoints]
      change d.inv.app R ((modelPoints k n).hom.app R a) = _
      have h := pointIso_roundtrip (modelPoints k n) R t
      exact congrArg (fun s : HyperbolicIndex.{u} n → Rˣ => d.inv.app R s) h
    rw [hX, ← ha]
    have hchar : characterValue (chT m) R (a ≫ j.hom.hom.hom) =
        characterValue (ch m) R a := by
      let B := specGroup (groupAlgebra k IntegerCharacters)
      let eval (x : Points B.X R) : R :=
        ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x).unop.hom
          (MonoidAlgebra.single integerGenerator 1)
      apply congrArg eval
      change (a ≫ j.hom.hom.hom) ≫ (j.inv.hom.hom ≫ (ch m).hom.hom) = a ≫ (ch m).hom.hom
      have hj : j.hom.hom.hom ≫ j.inv.hom.hom = 𝟙 A.X :=
        congrArg (fun f : A ⟶ A => f.hom.hom) j.hom_inv_id
      rw [Category.assoc, ← Category.assoc j.hom.hom.hom, hj, Category.id_comp]
    rw [hchar]
    let E := groupAlgebraPointsIso k M
    let g : M →* Rˣ := E.hom.app R a
    have hg : (exponentsEquiv R g : HyperbolicIndex.{u} n → Rˣ) = t :=
      pointIso_roundtrip (modelPoints k n) R t
    let alg : MonoidAlgebra k M →ₐ[k] R := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage a).unop.hom
    have hals : a = algebraPoint R alg := by
      exact ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage a).symm
    have heval : characterValue (ch m) R a = (g m).val := by
      calc
        characterValue (ch m) R a = characterValue (ch m) R (algebraPoint R alg) :=
          congrArg (characterValue (ch m) R) hals
        _ = alg (MonoidAlgebra.single m 1) := characterValue_monomial R alg m
        _ = (g m).val := ((congrArg
          (fun b => ((show M →* Rˣ from E.hom.app R b) m).val) hals).trans
            (pointsIso_spec M R alg m)).symm
    rw [heval]
    have hprod := (exponentsEquiv R).symm_apply_eq.mpr hg.symm
    have hp : (∏ i : HyperbolicIndex.{u} n, t i ^ m.toAdd i) = g m :=
      congrArg (fun f : M →* Rˣ => f m) hprod
    rw [← hp]
    exact congrArg Units.val (Equiv.prod_comp (Equiv.ulift.symm : Fin n ≃ HyperbolicIndex.{u} n)
      (fun i => t i ^ m.toAdd i)).symm
  · intro R z y i
    obtain ⟨f, rfl⟩ := coT.surjective y
    have hY : Y (Additive.ofMul (coT f)) = dualCoordinates n (homToDual M (Additive.ofMul f)) := by
      change dualCoordinates n (homToDual M (Additive.ofMul (coT.symm (coT f)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hY, dualCoordinates_apply]
    have hp : d.hom.app R (cocharacterPoint (coT f) R z) =
        (modelPoints k n).hom.app R (cocharacterPoint (co f) R z) := by
      change d.hom.app R (((groupPointsFunctor k).map (co f ≫ j.hom)).app R (unitPoint R z)) = _
      rw [Functor.map_comp, jpoints]
      change d.hom.app R (d.inv.app R ((modelPoints k n).hom.app R
        (cocharacterPoint (co f) R z))) = _
      exact pointIso_roundtrip d R _
    have hpre := pointsIso_precompose f R (unitPoint R z)
      (Multiplicative.ofAdd (Pi.single (⟨i⟩ : HyperbolicIndex.{u} n) 1))
    rw [hp]
    let a : M := Multiplicative.ofAdd (Pi.single (⟨i⟩ : HyperbolicIndex.{u} n) 1)
    let b : IntegerCharacters.{u} →* Rˣ :=
      (groupAlgebraPointsIso k IntegerCharacters).hom.app R (unitPoint R z)
    change _ = z ^ integerExponent (f a)
    refine hpre.trans ?_
    have hn : integerGenerator ^ integerExponent (f a) = f a :=
      (integerExponent.apply_eq_iff_eq).mp (integerExponent_zpow.{u} (integerExponent (f a)))
    calc
      b (f a) = b (integerGenerator ^ integerExponent (f a)) := congrArg b hn.symm
      _ = b integerGenerator ^ integerExponent (f a) := map_zpow _ _ _
      _ = z ^ integerExponent (f a) :=
        congrArg (fun w : Rˣ => w ^ integerExponent (f a)) (unitEquiv_unitPoint R z)

  · intro χ y
    obtain ⟨m, rfl⟩ := chT.surjective χ
    obtain ⟨f, rfl⟩ := coT.surjective y
    have hX : X (Additive.ofMul (chT m)) = exponentCoordinates n (Additive.ofMul m) := by
      change exponentCoordinates n (Additive.ofMul (chT.symm (chT m))) = _
      rw [MulEquiv.symm_apply_apply]
    have hY : Y (Additive.ofMul (coT f)) = dualCoordinates n (homToDual M (Additive.ofMul f)) := by
      change dualCoordinates n (homToDual M (Additive.ofMul (coT.symm (coT f)))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [hX, hY, ← dot_dual]
    apply (pairing_eq_iff _ _ _).mp
    change (co f ≫ j.hom) ≫ (j.inv ≫ ch m) = powerMorphism (integerExponent (f m))
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change specGroupMap (groupAlgebraMap k f) ≫
      specGroupMap (groupAlgebraMap k (integerHomEquiv M m)) = _
    rw [← specGroupMap_comp, powerMorphism]
    congr 1
    apply CommHopfAlgCat.hom_ext
    change (MonoidAlgebra.mapDomainBialgHom k f).comp
      (MonoidAlgebra.mapDomainBialgHom k (integerHomEquiv M m)) = _
    rw [← MonoidAlgebra.mapDomainBialgHom_comp]
    congr 1
    apply MonoidHom.ext
    intro z
    change f (m ^ z.down.toAdd) = (integerGenerator ^ integerExponent (f m)) ^ z.down.toAdd
    rw [map_zpow, (integerExponent.apply_eq_iff_eq).mp (integerExponent_zpow.{u} (integerExponent (f m)))]

end Lattices

section Positivity

private def dot {n : ℕ} (w : Fin n → ℤ) (x : Fin n → ℤ) : ℤ :=
  ∑ i, x i * w i

private lemma dot_add {n : ℕ} (w x y : Fin n → ℤ) :
    dot w (x + y) = dot w x + dot w y := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_smul_coordinate {n : ℕ} (w : Fin n → ℤ) (i : Fin n) (a : ℤ) :
    dot w (a • coordinate i) = a * w i := by
  unfold dot
  rw [Finset.sum_eq_single i]
  · simp [coordinate, Pi.smul_apply]
  · intro j _ hj
    simp [coordinate, Pi.smul_apply, Pi.single_eq_of_ne hj]
  · simp

private lemma dot_long {n : ℕ} (w : Fin n → ℤ) (i : Fin n) (s : Bool) :
    dot w (rootVector (.long i s)) = (2 * sign s) * w i :=
  dot_smul_coordinate w i _

private lemma dot_short {n : ℕ} (w : Fin n → ℤ) {i j : Fin n} (h : i < j) (s t : Bool) :
    dot w (rootVector (.short i j h s t)) = sign s * w i + sign t * w j := by
  rw [rootVector, dot_add, dot_smul_coordinate, dot_smul_coordinate]

private lemma descending_pos {n : ℕ} (i : Fin n) : 0 < descending n i := by
  have := i.isLt
  unfold descending
  omega

private lemma descending_lt {n : ℕ} {i j : Fin n} (h : i < j) :
    descending n j < descending n i := by
  have : i.val < j.val := h
  unfold descending
  omega

private lemma root_regular {n : ℕ} (a : RootLabel n) :
    dot (descending n) (rootVector a) ≠ 0 := by
  cases a with
  | long i s =>
    have := descending_pos i
    cases s <;> simp [dot_long, sign] <;> omega
  | short i j hij s t =>
    have := descending_pos j
    have := descending_lt hij
    cases s <;> cases t <;> simp [dot_short, sign] <;> omega

private lemma rootVector_ne_zero {n : ℕ} (a : RootLabel n) : rootVector a ≠ 0 := by
  intro h
  exact root_regular a (by simp [h, dot])

private lemma coordinate_apply {n : ℕ} (i j : Fin n) :
    coordinate i j = if j = i then 1 else 0 := by simp [coordinate, Pi.single_apply]

private lemma rootVector_injective (n : ℕ) : Function.Injective (rootVector (n := n)) := by
  intro a b h
  cases a with
  | long i s =>
    cases b with
    | long j t =>
      have hv := congrFun h i
      by_cases hij : i = j
      · subst j
        cases s <;> cases t <;> simp_all [rootVector, coordinate_apply, sign]
      · cases s <;> cases t <;>
          simp_all [rootVector, coordinate_apply, sign, Pi.smul_apply]
    | short j l hjl t r =>
      have hv := congrFun h i
      cases s <;> cases t <;> cases r <;>
        simp only [rootVector, Pi.smul_apply, Pi.add_apply, coordinate_apply, sign] at hv <;>
        split_ifs at hv <;> simp_all <;> omega
  | short i j hij s t =>
    cases b with
    | long l r =>
      have hv := congrFun h.symm l
      cases s <;> cases t <;> cases r <;>
        simp only [rootVector, Pi.smul_apply, Pi.add_apply, coordinate_apply, sign] at hv <;>
        split_ifs at hv <;> simp_all <;> omega
    | short l m hlm r w =>
      have hi : i = l ∨ i = m := by
        by_contra! hne
        have hv := congrFun h i
        cases s <;> cases t <;> cases r <;> cases w <;>
          simp_all [rootVector, Pi.add_apply, coordinate_apply, sign, hij.ne]
      have hj : j = l ∨ j = m := by
        by_contra! hne
        have hv := congrFun h j
        cases s <;> cases t <;> cases r <;> cases w <;>
          simp_all [rootVector, Pi.add_apply, coordinate_apply, sign, hij.ne']
      have hindices : i = l ∧ j = m := by
        rcases hi with hi | hi <;> rcases hj with hj | hj
        · exact False.elim (hij.ne (hi.trans hj.symm))
        · exact ⟨hi, hj⟩
        · subst l; subst m
          exact False.elim (hij.not_gt hlm)
        · exact False.elim (hij.ne (hi.trans hj.symm))
      obtain ⟨rfl, rfl⟩ := hindices
      have hv := congrFun h i
      have hw := congrFun h j
      cases s <;> cases t <;> cases r <;> cases w <;>
        simp [rootVector, Pi.add_apply, coordinate_apply, sign, hij.ne, hij.ne'] at hv hw <;>
        rfl

private def heightWeight (n : ℕ) (i : Fin n) : ℤ := 2 * descending n i - 1

private lemma simple_height {n : ℕ} (i : Fin (n + 1)) :
    0 < dot (descending (n + 1)) (rootVector (simpleLabel i)) ∧
    dot (heightWeight (n + 1)) (rootVector (simpleLabel i)) = 2 := by
  unfold simpleLabel
  split
  · simp [dot_short, sign, heightWeight, descending]
    omega
  · have := i.isLt
    simp [dot_long, sign, heightWeight, descending]
    omega

private lemma positive_height {n : ℕ} (a : RootLabel n)
    (h : 0 < dot (descending n) (rootVector a)) :
    2 ≤ dot (heightWeight n) (rootVector a) := by
  cases a with
  | long i s =>
    have := descending_pos i
    cases s <;> simp [dot_long, sign, heightWeight] at h ⊢ <;> omega
  | short i j hij s t =>
    have := descending_pos j
    have := descending_lt hij
    cases s <;> cases t <;> simp [dot_short, sign, heightWeight] at h ⊢ <;> omega

private lemma positive_decomposition {n : ℕ} (a : RootLabel (n + 1))
    (h : 0 < dot (descending (n + 1)) (rootVector a))
    (hs : ¬ ∃ i, a = simpleLabel i) :
    ∃ b c : RootLabel (n + 1),
      0 < dot (descending (n + 1)) (rootVector b) ∧
      0 < dot (descending (n + 1)) (rootVector c) ∧
      rootVector a = rootVector b + rootVector c := by
  cases a with
  | long i s =>
    cases s
    · have := descending_pos i
      simp [dot_long, sign] at h
      omega
    · have hi : i.val < n := by
        by_contra hn
        exact hs ⟨i, by simp [simpleLabel, hn]⟩
      let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      have hij : i < j := by change i.val < i.val + 1; omega
      refine ⟨.short i j hij true false, .short i j hij true true, ?_, ?_, ?_⟩
      · have := descending_lt hij
        simp [dot_short, sign]
        omega
      · have := descending_lt hij
        have := descending_pos j
        simp [dot_short, sign]
        omega
      · ext l
        simp [rootVector, sign, Pi.smul_apply]
        ring
  | short i j hij s t =>
    have hd := descending_lt hij
    have hp := descending_pos j
    cases s <;> cases t
    · simp [dot_short, sign] at h; omega
    · simp [dot_short, sign] at h; omega
    · have hgap : i.val + 1 < j.val := by
        have hij' : i.val < j.val := hij
        by_contra! hgap
        have heq : i.val + 1 = j.val := by omega
        have hi : i.val < n := by have := j.isLt; omega
        exact hs ⟨i, by
          simp only [simpleLabel, dite_eq_left hi]
          cases j with
          | mk j hj =>
            change i.val + 1 = j at heq
            subst j
            rfl⟩
      let l : Fin (n + 1) := ⟨i.val + 1, by have := j.isLt; omega⟩
      have hil : i < l := by change i.val < i.val + 1; omega
      have hlj : l < j := hgap
      refine ⟨.short i l hil true false, .short l j hlj true false, ?_, ?_, ?_⟩
      · have := descending_lt hil
        simp [dot_short, sign]; omega
      · have := descending_lt hlj
        simp [dot_short, sign]; omega
      · ext r
        simp [rootVector, sign]
    · refine ⟨.short i j hij true false, .long j true, ?_, ?_, ?_⟩
      · simp [dot_short, sign]; omega
      · simp [dot_long, sign]; omega
      · ext l
        simp [rootVector, sign]
        ring

end Positivity

section SchemeWeights

open Specs.StandardGroups (multiplicativePowerPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue adjointWeightVectors)
open Specs.AdjointRepresentation (GroupPoints dualMap constants scale)
open LinearAlgebraicGroups.SymplecticMatrixStructure (diagonalPoint)

open private basis_expansion from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

variable {k : Type u} [Field k] {n : ℕ} {G : GroupScheme k}

private def evaluateLaurent (R : TestAlgebra k) (t : HyperbolicIndex.{u} n → Rˣ) :
    LaurentCoordinates k n →ₐ[k] R :=
  AddMonoidAlgebra.lift k R (Fin n → ℤ) ((Units.coeHom R).comp
    { toFun := fun x => ∏ i, t ⟨i⟩ ^ x.toAdd i
      map_one' := by change (∏ i : Fin n, t ⟨i⟩ ^ (0 : ℤ)) = 1; simp
      map_mul' := by intro x y; change (∏ i, t ⟨i⟩ ^ (x.toAdd i + y.toAdd i)) = _
                     simp [zpow_add, Finset.prod_mul_distrib] })

private lemma evaluateLaurent_monomial (R : TestAlgebra k) (t : HyperbolicIndex.{u} n → Rˣ)
    (x : Fin n → ℤ) :
    evaluateLaurent R t (AddMonoidAlgebra.single x 1) = (↑(∏ i, t ⟨i⟩ ^ x i) : R) := by
  rw [evaluateLaurent, AddMonoidAlgebra.lift_single, one_smul]
  rfl

private lemma evaluateLaurent_unit (R : TestAlgebra k) (t : HyperbolicIndex.{u} n → Rˣ)
    (i : HyperbolicIndex.{u} n) :
    Units.map (evaluateLaurent R t).toMonoidHom (universalTorusUnits k n i) = t i := by
  apply Units.ext
  change evaluateLaurent R t (AddMonoidAlgebra.single (coordinate i.down) 1) = _
  rw [evaluateLaurent_monomial]
  congr 1
  rw [Finset.prod_eq_single i.down]
  · simp [coordinate]
  · intro j _ hj
    simp [coordinate, Pi.single_eq_of_ne hj]
  · simp

private lemma monomial_universal (x : Fin n → ℤ) :
    (↑(∏ i : Fin n, universalTorusUnits k n ⟨i⟩ ^ x i) : LaurentCoordinates k n) =
      AddMonoidAlgebra.single x 1 := by
  let f := (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits
  have h := congrArg f (basis_expansion (Multiplicative.ofAdd x))
  rw [map_prod] at h
  simp only [map_zpow] at h
  exact congrArg Units.val h

private lemma hyperbolicDiagonal_map {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (t : HyperbolicIndex.{u} n → Rˣ) :
    (hyperbolicDiagonal t).map f =
      hyperbolicDiagonal (fun i => Units.map f.toMonoidHom (t i)) := by
  rw [hyperbolicDiagonal, hyperbolicDiagonal, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  cases i
  · rfl
  · exact congrArg Units.val ((Units.map f.toMonoidHom).map_inv _).symm

private lemma universal_weight_iff (x : Fin n → ℤ) (X : MatrixAlgebra (HyperbolicIndex.{u} n) k) :
    MatrixHasWeight x X ↔ ∀ (R : TestAlgebra k) (t : HyperbolicIndex.{u} n → Rˣ),
      hyperbolicDiagonal t * X.map (algebraMap k R) * hyperbolicDiagonal (fun i => (t i)⁻¹) =
        (↑(∏ i : Fin n, t ⟨i⟩ ^ x i) : R) • X.map (algebraMap k R) := by
  constructor
  · intro h R t
    let f := evaluateLaurent R t
    have hm := congrArg (fun Z : MatrixAlgebra (HyperbolicIndex.{u} n) (LaurentCoordinates k n) =>
      Z.map f) h
    change (hyperbolicDiagonal (universalTorusUnits k n) * X.map (algebraMap k _) *
      hyperbolicDiagonal (fun i => (universalTorusUnits k n i)⁻¹)).map f =
        (AddMonoidAlgebra.single x (1 : k) • X.map (algebraMap k _)).map f at hm
    have hleft : (hyperbolicDiagonal (universalTorusUnits k n)).map f = hyperbolicDiagonal t := by
      change (hyperbolicDiagonal _).map f.toRingHom = _
      rw [hyperbolicDiagonal_map]
      exact congrArg hyperbolicDiagonal (funext (evaluateLaurent_unit R t))
    have hright : (hyperbolicDiagonal (fun i => (universalTorusUnits k n i)⁻¹)).map f =
        hyperbolicDiagonal (fun i => (t i)⁻¹) := by
      change (hyperbolicDiagonal _).map f.toRingHom = _
      rw [hyperbolicDiagonal_map]
      congr 1
      funext i
      rw [map_inv]
      exact congrArg Inv.inv (evaluateLaurent_unit R t i)
    have hX : (X.map (algebraMap k (LaurentCoordinates k n))).map f = X.map (algebraMap k R) := by
      exact Matrix.ext fun i j => f.commutes (X i j)
    rw [Matrix.map_mul (f := f), Matrix.map_mul (f := f), hleft, hright,
      Matrix.map_smul' f _ _ (map_mul f), hX, evaluateLaurent_monomial R t x] at hm
    exact hm
  · intro h
    have hu := h (CommAlgCat.of k (LaurentCoordinates k n)) (universalTorusUnits k n)
    rw [monomial_universal] at hu
    exact hu

private lemma point_matrix_naturality
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k (HyperbolicIndex.{u} n))
    {R S : TestAlgebra k} (f : R ⟶ S) (p : GroupPoints G R) :
    (show PointGroup _ S from c.hom.app S (mapPoints f p)).val =
      (show PointGroup _ R from c.hom.app R p).val.map f.hom := by
  exact (congrArg Subtype.val
    (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (c.hom.naturality f)) p))

private def dualMatrix {R : Type u} [CommRing R]
    (A B : MatrixAlgebra (HyperbolicIndex.{u} n) R) : MatrixAlgebra (HyperbolicIndex.{u} n) (DualNumber R) :=
  fun i j => (⟨A i j, B i j⟩ : DualNumber R)

private lemma dualMatrix_mul {R : Type u} [CommRing R]
    (A B C D : MatrixAlgebra (HyperbolicIndex.{u} n) R) :
    dualMatrix A B * dualMatrix C D = dualMatrix (A * C) (A * D + B * C) := by
  apply Matrix.ext
  intro i j
  apply TrivSqZeroExt.ext
  · simp only [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
    rfl
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact Finset.sum_add_distrib

private lemma point_matrix_weight
    (c : (groupPointsFunctor k).obj G ≅ symplecticPoints k (HyperbolicIndex.{u} n))
    (e : Lie k G ≃+ symplecticLieSubspace k (HyperbolicIndex.{u} n))
    (he : ∀ p i j, (e p).val i j =
      ((show PointGroup _ (DualNumber k) from
        c.hom.app (CommAlgCat.of k (DualNumber k)) p.toMul.val).val i j).snd)
    (T : ClosedSubgroup G)
    (d : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (HyperbolicIndex.{u} n))
    (hd : ∀ (R : TestAlgebra k) (t : HyperbolicIndex.{u} n → Rˣ),
      (show PointGroup _ R from
        c.hom.app R (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
        hyperbolicDiagonal t)
    (L : LatticeCoordinates d) (χ : Character T.group) (v : Lie k G) :
    v ∈ adjointWeightVectors T χ ↔ MatrixHasWeight (L.X (Additive.ofMul χ)) (e v).val := by
  rw [universal_weight_iff]
  change (∀ R (t : GroupPoints T.group R), _) ↔ _
  apply forall_congr'
  intro R
  let q := Equiv.ofBijective (d.inv.app R) (ConcreteCategory.bijective_of_isIso (d.inv.app R))
  rw [← q.forall_congr_right]
  apply forall_congr'
  intro t
  let t : HyperbolicIndex.{u} n → Rˣ := t
  let tG : GroupPoints G R := ((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t)
  let P := mapPoints (dualMap (CommAlgCat.ofHom (Algebra.ofId k R))) v.toMul.val
  let Q := mapPoints (constants R) tG
  let a := characterValue χ R (d.inv.app R t)
  let Rε := CommAlgCat.of k (DualNumber R)
  let kε := CommAlgCat.of k (DualNumber k)
  let cv := (c.hom.app Rε).hom
  let M := (e v).val.map (algebraMap k R)
  let B := hyperbolicDiagonal t
  let C := hyperbolicDiagonal (fun i => (t i)⁻¹)
  change (Q * P * Q⁻¹ : GroupPoints G Rε) = mapPoints (scale R a) P ↔
    B * M * C = _ • M
  rw [← L.characterEvaluation R t χ]
  change _ ↔ B * M * C = a • M
  have ht : c.hom.app R tG = diagonalPoint _ R t := Subtype.ext (hd R t)
  have hbase : (show PointGroup _ (DualNumber k) from c.hom.app kε v.toMul.val).val =
      dualMatrix 1 (e v).val := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · have h := point_matrix_naturality c (dualReduction k) v.toMul.val
      change (show PointGroup _ k from c.hom.app (CommAlgCat.of k k)
        (reduceTangentPoints G v.toMul.val)).val = _ at h
      rw [v.toMul.property] at h
      have ho := (c.hom.app (CommAlgCat.of k k)).hom.map_one
      change c.hom.app (CommAlgCat.of k k) 1 = _ at ho
      rw [ho] at h
      exact (congrFun (congrFun h i) j).symm
    · exact (he v i j).symm
  have hp : (cv P).val = dualMatrix 1 M := by
    change (show PointGroup _ Rε from c.hom.app Rε P).val = _
    rw [point_matrix_naturality, hbase]
    apply Matrix.ext
    intro i j
    change (⟨algebraMap k R ((1 : MatrixAlgebra _ k) i j), M i j⟩ : DualNumber R) = _
    rw [← Matrix.map_apply (f := algebraMap k R), Matrix.map_one (algebraMap k R) (map_zero _) (map_one _)]
    rfl
  have hq : (cv Q).val = dualMatrix B 0 := by
    change (show PointGroup _ Rε from c.hom.app Rε Q).val = _
    rw [point_matrix_naturality, ht]
    rfl
  have hqinv : (cv Q⁻¹).val = dualMatrix C 0 := by
    have hqi : (Q⁻¹ : GroupPoints G Rε) = mapPoints (constants R) tG⁻¹ :=
      ((((groupPointsFunctor k).obj G).map (constants R)).hom.map_inv tG).symm
    rw [hqi]
    change (show PointGroup _ Rε from c.hom.app Rε (mapPoints (constants R) tG⁻¹)).val = _
    rw [point_matrix_naturality]
    change (((c.hom.app R).hom tG⁻¹ : PointGroup _ R).val.map _) = _
    rw [map_inv]
    change ((c.hom.app R tG)⁻¹ : PointGroup _ R).val.map _ = _
    rw [ht, ← (diagonalPoint _ R).map_inv]
    rfl
  have hscale : (show PointGroup _ Rε from c.hom.app Rε (mapPoints (scale R a) P)).val =
      dualMatrix 1 (a • M) := by
    rw [point_matrix_naturality]
    change (cv P).val.map _ = _
    rw [hp]
    rfl
  have hBC : B * C = 1 :=
    congrArg Subtype.val (((diagonalPoint _ R).map_mul t t⁻¹).symm.trans
      (((congrArg (diagonalPoint _ R) (mul_inv_cancel t))).trans (map_one _)))
  constructor <;> intro h
  · have hm := congrArg (fun p => (cv p).val) h
    rw [map_mul, map_mul] at hm
    change ((cv Q).val * (cv P).val) * (cv Q⁻¹).val = _ at hm
    rw [hp, hq, hqinv, hscale, dualMatrix_mul, dualMatrix_mul] at hm
    simp only [mul_one, add_zero, zero_add, Matrix.mul_zero] at hm
    exact Matrix.ext fun i j => congrArg (fun H => (H i j).snd) hm
  · apply (ConcreteCategory.bijective_of_isIso (c.hom.app Rε)).1
    change cv (Q * P * Q⁻¹) = cv (mapPoints (scale R a) P)
    apply Subtype.ext
    rw [map_mul, map_mul]
    change ((cv Q).val * (cv P).val) * (cv Q⁻¹).val = _
    rw [hp, hq, hqinv, hscale, dualMatrix_mul, dualMatrix_mul]
    simp only [mul_one, add_zero, zero_add, Matrix.mul_zero, hBC, h]

end SchemeWeights

section BasedRootSystem

open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors pairing)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CocharacterDynamics (existsLimitDecomposition)

theorem torusAndBorel : TorusAndBorel.{u} := by
  intro k _ n G c
  let r := n + 1
  obtain ⟨T, d, hrank, hd, _, hmax⟩ :=
    SymplecticMatrixStructure.diagonalTorus k (HyperbolicIndex.{u} r) G c
  have hsplit : Specs.GeometricRadicals.IsSplitTorus T.group := ⟨_, hrank⟩
  have hT : IsAffine T.group.X.left := by
    letI := G.property.1
    letI := T.isClosedImmersion
    exact isAffine_of_isAffineHom T.inclusion.hom.hom.left
  obtain ⟨L⟩ := latticeCoordinates hT r d
  letI := L.comm
  obtain ⟨e, he, _⟩ :=
    SymplecticMatrixStructure.lieComparison k (HyperbolicIndex.{u} r) G.val c
  have hw : ∀ χ v, v ∈ adjointWeightVectors T χ ↔
      MatrixHasWeight (L.X (Additive.ofMul χ)) (e v).val :=
    point_matrix_weight c e he T d hd L
  obtain ⟨hweights, helem⟩ := matrixLieWeights k r
  have hχ (χ : Character T.group) :
      χ ∈ absoluteRoots T ↔ ∃ a : RootLabel r, L.X (Additive.ofMul χ) = rootVector a := by
    constructor
    · rintro ⟨hne, v, hv, hvne⟩
      have hx : L.X (Additive.ofMul χ) ≠ 0 := fun h =>
        hne (L.X.injective (h.trans L.X.map_zero.symm))
      have hvmat : (e v).val ≠ 0 := fun h => hvne (e.injective
        ((Subtype.ext h).trans e.map_zero.symm))
      exact (hweights _ hx).mp ⟨e v, hvmat, (hw χ v).mp hv⟩
    · rintro ⟨a, ha⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply rootVector_ne_zero a
        rw [← ha, h]
        exact L.X.map_zero
      · obtain ⟨hm, hne, hwt⟩ := helem a
        let v := e.symm ⟨elementaryDirection k a, hm⟩
        have hv : e v = ⟨elementaryDirection k a, hm⟩ := e.apply_symm_apply _
        refine ⟨v, (hw χ v).mpr ?_, ?_⟩
        · rw [hv, ha]
          exact hwt
        · intro h
          apply hne
          exact congrArg Subtype.val (hv.symm.trans (h ▸ e.map_zero))
  let f : RootLabel r → ↥(absoluteRoots T) := fun a =>
    ⟨Additive.toMul (L.X.symm (rootVector a)), (hχ _).mpr ⟨a, L.X.apply_symm_apply _⟩⟩
  have hf (a : RootLabel r) : L.X (Additive.ofMul (f a).val) = rootVector a :=
    L.X.apply_symm_apply _
  have hb : Function.Bijective f := by
    constructor
    · intro a b h
      apply rootVector_injective r
      rw [← hf a, ← hf b, h]
    · intro α
      obtain ⟨a, ha⟩ := (hχ α.val).mp α.property
      exact ⟨a, Subtype.ext (L.X.injective ((hf a).trans ha.symm))⟩
  let label := Equiv.ofBijective f hb
  let y : Cocharacter T.group := Additive.toMul (L.Y.symm (descending r))
  have hY : L.Y (Additive.ofMul y) = descending r := L.Y.apply_symm_apply _
  have hpair (a : RootLabel r) :
      pairing T.group (label a).val y = dot (descending r) (rootVector a) := by
    rw [L.compositionPairing, hY, show L.X (Additive.ofMul (label a).val) = rootVector a from hf a]
    rfl
  have hregular : IsRegular T y := by
    intro α
    obtain ⟨a, rfl⟩ := label.surjective α
    rw [hpair]
    exact root_regular a
  obtain ⟨D⟩ := existsLimitDecomposition G (y ≫ T.inclusion)
  have hred := SymplecticMatrixStructure.reductivity k (HyperbolicIndex.{u} r) G ⟨c⟩
  obtain ⟨_, hB, hTB, hroots, _⟩ :=
    BorelsAndChambers.regularCocharacterBorel G hred T hsplit hmax y hregular D
  refine ⟨T, d, L, e, label, y, D, hsplit, hmax, hd, he, hw, ?_, congrFun hY, hregular,
    hB, hTB, hroots, ?_⟩
  · intro a
    refine ⟨hf a, ?_⟩
    obtain ⟨hm, hne, hwt⟩ := helem a
    let v := e.symm ⟨elementaryDirection k a, hm⟩
    have hv : (e v).val = elementaryDirection k a := congrArg Subtype.val (e.apply_symm_apply _)
    refine ⟨v, (hw _ _).mpr ?_, ?_, hv⟩
    · rw [hv, show L.X (Additive.ofMul (label a).val) = rootVector a from hf a]
      exact hwt
    · intro h
      apply hne
      rw [← hv, h, e.map_zero]
      rfl
  · have hpos (a : RootLabel r) : label a ∈ subgroupRoots T D.parabolic ↔
        0 < dot (descending r) (rootVector a) := by
      rw [hroots]
      change 0 < pairing T.group (label a).val y ↔ _
      rw [hpair]
    have hadd (a b d : RootLabel r) :
        (label a).val = (label b).val * (label d).val ↔
          rootVector a = rootVector b + rootVector d := by
      have hl (j : RootLabel r) : L.X (Additive.ofMul (label j).val) = rootVector j := hf j
      rw [← hl a, ← hl b, ← hl d, ← L.X.map_add]
      exact L.X.injective.eq_iff.symm
    intro a
    constructor
    · rintro ⟨ha, hindecomp⟩
      by_contra hs
      obtain ⟨b, d, hb, hd, hadd'⟩ := positive_decomposition a ((hpos a).mp ha) hs
      exact hindecomp ⟨label b, label d, (hpos b).mpr hb, (hpos d).mpr hd,
        (hadd a b d).mpr hadd'⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨hp, hh⟩ := simple_height i
      refine ⟨(hpos _).mpr hp, ?_⟩
      rintro ⟨beta, gamma, hbeta, hgamma, hsum⟩
      obtain ⟨b, rfl⟩ := label.surjective beta
      obtain ⟨d, rfl⟩ := label.surjective gamma
      have hb := positive_height b ((hpos b).mp hbeta)
      have hd := positive_height d ((hpos d).mp hgamma)
      have h := congrArg (dot (heightWeight r)) ((hadd (simpleLabel i) b d).mp hsum)
      rw [dot_add, hh] at h
      omega

end BasedRootSystem


end
end LinearAlgebraicGroups.RootData.SymplecticDatumTorusAndBorel
