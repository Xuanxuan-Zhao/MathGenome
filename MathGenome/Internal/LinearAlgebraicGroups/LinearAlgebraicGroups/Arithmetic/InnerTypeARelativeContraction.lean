import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.RingTheory.SimpleRing.Matrix

open scoped TensorProduct BigOperators Matrix
open Algebra.TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction

noncomputable section

open LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction
open RM03.CSA (algEquiv_matrix_algebraicClosure degree_eq_matrix_size)
open RM03.CSA.NormOneGroup (changeCoefficients extendSplitting extendSplitting_tmul
  normAt normAt_eq_det normAt_natural)

variable {F B R S : Type*} [Field F] [Ring B] [Algebra F B]
  [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

/-- Scalar extension commutes with taking the full matrix algebra. -/
private def matrixBaseChange {m : ℕ} :
    R ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[R] Matrix (Fin m) (Fin m) (R ⊗[F] B) :=
  let e :=
    (Algebra.TensorProduct.congr (.refl : R ≃ₐ[F] R) (matrixEquivTensor (Fin m) F B)).trans
      (((Algebra.TensorProduct.assoc F F F R B (Matrix (Fin m) (Fin m) F)).symm).trans
        (matrixEquivTensor (Fin m) F (R ⊗[F] B)).symm)
  AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
    intro r
    change e (r ⊗ₜ[F] 1) = _
    simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.refl_toAlgHom, AlgHom.id_apply]
    rw [map_one, Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_symm_tmul,
      matrixEquivTensor_apply_symm]
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one]
    exact IsScalarTower.algebraMap_smul (R ⊗[F] B) r
      (1 : Matrix (Fin m) (Fin m) (R ⊗[F] B)))

private theorem matrixBaseChange_single {m : ℕ} (r : R) (i j : Fin m) (b : B) :
    matrixBaseChange (r ⊗ₜ[F] Matrix.single i j b) = Matrix.single i j (r ⊗ₜ[F] b) := by
  change (matrixEquivTensor (Fin m) F (R ⊗[F] B)).symm
    ((Algebra.TensorProduct.assoc F F F R B (Matrix (Fin m) (Fin m) F)).symm
      (r ⊗ₜ[F] matrixEquivTensor (Fin m) F B (Matrix.single i j b))) = _
  rw [matrixEquivTensor_apply_single, Algebra.TensorProduct.assoc_symm_tmul,
    matrixEquivTensor_apply_symm, Matrix.map_single _ _ _ (algebraMap F (R ⊗[F] B)),
    Matrix.smul_single]
  simp

private theorem matrixBaseChange_diagonal {m : ℕ} (t : Fin m → R) :
    matrixBaseChange (scalarDiagonal (F := F) (B := B) t) =
      Matrix.diagonal (fun i => t i ⊗ₜ[F] (1 : B)) := by
  simp only [scalarDiagonal, map_sum, matrixBaseChange_single, Matrix.sum_single_eq_diagonal]

private theorem matrixBaseChange_block {m : ℕ} (i j : Fin m) (x : R ⊗[F] B) :
    matrixBaseChange (blockEntry i j x) = Matrix.single i j x := by
  induction x using TensorProduct.inductionOn with
  | tmul r b => simpa [blockEntry] using matrixBaseChange_single r i j b
  | add x y hx hy => rw [map_add, map_add, hx, hy, Matrix.single_add]

private theorem matrixBaseChange_apply {m : ℕ}
    (x : R ⊗[F] Matrix (Fin m) (Fin m) B) (i j : Fin m) :
    matrixBaseChange x i j = blockProjection i j x := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    rw [Matrix.matrix_eq_sum_single M]
    simp only [TensorProduct.tmul_sum, map_sum, matrixBaseChange_single, Matrix.sum_apply,
      blockProjection, TensorProduct.map_tmul, LinearMap.id_apply, Matrix.entryLinearMap_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hi : a = i <;> by_cases hj : b = j <;> simp [Matrix.single, hi, hj]
  | add x y hx hy => simp only [map_add, Matrix.add_apply, hx, hy]

theorem diagonalAction : DiagonalAction := by
  intro F B R _ _ _ _ _ m t u x i j
  rw [← matrixBaseChange_apply, ← matrixBaseChange_apply, map_mul, map_mul,
    matrixBaseChange_diagonal, matrixBaseChange_diagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (algebraMap R (R ⊗[F] B) (t i) * matrixBaseChange x i j) *
      algebraMap R (R ⊗[F] B) (u j) = _
  rw [mul_assoc, ← Algebra.commutes (u j) (matrixBaseChange x i j),
    ← mul_assoc, ← map_mul, Algebra.smul_def]

private theorem changeCoefficients_block {m : ℕ} (f : R →ₐ[F] S) (i j : Fin m) (x : R ⊗[F] B) :
    changeCoefficients f (blockEntry i j x) = blockEntry i j (changeCoefficients f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem changeCoefficients_diagonal {m : ℕ} (f : R →ₐ[F] S) (t : Fin m → R) :
    changeCoefficients f (scalarDiagonal (F := F) (B := B) t) =
      scalarDiagonal (F := F) (B := B) (f ∘ t) := by
  simp [scalarDiagonal, changeCoefficients]

variable {K : Type*} [Field K] [Algebra F K] [Algebra K S] [IsScalarTower F K S]
  {m d : ℕ}

private def flattenSplitting (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K) :
    S ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[S] Matrix (Fin m × Fin d) (Fin m × Fin d) S :=
  matrixBaseChange.trans ((extendSplitting e).mapMatrix.trans
    (Matrix.compAlgEquiv (Fin m) (Fin d) S S))

private theorem flattenSplitting_tmul (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (s : S) (a : Matrix (Fin m) (Fin m) B) :
    flattenSplitting e (s ⊗ₜ[F] a) =
      s • (flattenSplitting (S := K) e (1 ⊗ₜ[F] a)).map (algebraMap K S) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single a]
  conv_rhs => rw [Matrix.matrix_eq_sum_single a]
  ext ⟨p, r⟩ ⟨q, t⟩
  simp only [TensorProduct.tmul_sum, map_sum, Matrix.smul_apply, Matrix.map_apply,
    Matrix.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [flattenSplitting, AlgEquiv.trans_apply, matrixBaseChange_single,
    AlgEquiv.mapMatrix_apply, Matrix.map_single, extendSplitting_tmul,
    one_smul, Algebra.algebraMap_self, Matrix.compAlgEquiv_apply, Matrix.comp_apply]
  by_cases hi : i = p <;> by_cases hj : j = q <;>
    simp [Matrix.single, hi, hj]

private theorem normAt_eq_flattenDet (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (hA : _root_.Specs.RM03.CSA.isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (x : S ⊗[F] Matrix (Fin m) (Fin m) B) :
    normAt hA b x = (flattenSplitting e x).det := by
  let e₀ := (flattenSplitting (S := K) (m := m) e).trans (Matrix.reindexAlgEquiv K K finProdFinEquiv)
  have hn := degree_eq_matrix_size hA e₀
  let r : (Fin m × Fin d) ≃ Fin (RM03.CSA.degree F (Matrix (Fin m) (Fin m) B)) :=
    finProdFinEquiv.trans (finCongr hn.symm)
  let e₁ := (flattenSplitting (S := K) (m := m) e).trans (Matrix.reindexAlgEquiv K K r)
  rw [normAt_eq_det hA b e₁]
  have hcomp : extendSplitting e₁ x =
      Matrix.reindexAlgEquiv S S r (flattenSplitting e x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a =>
      rw [extendSplitting_tmul, flattenSplitting_tmul]
      rfl
  exact (congrArg Matrix.det hcomp).trans (Matrix.det_reindexAlgEquiv S S r _)

private theorem flattenSplitting_diagonal
    (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K) (t : Fin m → S) :
    flattenSplitting e (scalarDiagonal (F := F) (B := B) t) =
      Matrix.diagonal (fun p : Fin m × Fin d => t p.1) := by
  simp only [flattenSplitting, AlgEquiv.trans_apply, matrixBaseChange_diagonal,
    AlgEquiv.mapMatrix_apply]
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j <;> by_cases h' : a = b <;>
    simp [Matrix.compAlgEquiv_apply, Matrix.comp_apply, Matrix.diagonal, h, h',
      extendSplitting_tmul, ← Algebra.TensorProduct.one_def]

private theorem sum_flattened_block (i j : Fin m) (M : Matrix (Fin d) (Fin d) S) :
    (∑ p : Fin d × Fin d, Matrix.single (i, p.1) (j, p.2) (M p.1 p.2)) =
      Matrix.comp (Fin m) (Fin m) (Fin d) (Fin d) S (Matrix.single i j M) := by
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  let L : Matrix (Fin d) (Fin d) S →+ Matrix (Fin m) (Fin m) (Matrix (Fin d) (Fin d) S) :=
    Matrix.singleAddMonoidHom i j
  change _ = Matrix.comp (Fin m) (Fin m) (Fin d) (Fin d) S (L _)
  rw [map_sum]
  simp only [map_sum]
  change _ = Matrix.compAddEquiv (Fin m) (Fin m) (Fin d) (Fin d) S (∑ a, ∑ b, L _)
  simp only [map_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    (Matrix.comp_single_single i j a b (M a b)).symm

private theorem flattened_block_product (i j : Fin m) (hij : i ≠ j)
    (M : Matrix (Fin d) (Fin d) S) (T : Finset (Fin d × Fin d)) :
    ∃ l : List (Fin d × Fin d), l.Nodup ∧ l.toFinset = T ∧
      (l.map (fun p => Matrix.transvection (i, p.1) (j, p.2) (M p.1 p.2))).prod =
        1 + ∑ p ∈ T, Matrix.single (i, p.1) (j, p.2) (M p.1 p.2) := by
  classical
  let N := fun p : Fin d × Fin d => Matrix.single (i, p.1) (j, p.2) (M p.1 p.2)
  have hzero (p q) : N p * N q = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ (fun h => hij (congrArg Prod.fst h).symm) _
  induction T using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨l, hl, hu, he⟩ := ih
    have hal : a ∉ l := by simpa [← hu] using ha
    refine ⟨a :: l, List.nodup_cons.mpr ⟨hal, hl⟩, by simp [hu], ?_⟩
    rw [List.map_cons, List.prod_cons, he, Finset.sum_insert ha]
    change (1 + N a) * (1 + ∑ p ∈ T, N p) = 1 + (N a + ∑ p ∈ T, N p)
    simp [add_mul, mul_add, Finset.mul_sum, hzero, add_assoc]

private theorem det_one_add_block (i j : Fin m) (hij : i ≠ j)
    (M : Matrix (Fin d) (Fin d) S) :
    (1 + Matrix.comp (Fin m) (Fin m) (Fin d) (Fin d) S (Matrix.single i j M)).det = 1 := by
  obtain ⟨l, hn, ht, hl⟩ := flattened_block_product i j hij M Finset.univ
  rw [← sum_flattened_block, ← hl]
  clear hn ht hl
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.det_mul, ih, mul_one]
    exact Matrix.det_transvection_of_ne _ _ (fun h => hij (congrArg Prod.fst h)) _


theorem blockTransvections : BlockTransvections := by
  classical
  intro F B R _ _ _ _ _ hB m hA ι _ b i j hij
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    have h' := congrArg (fun a => matrixBaseChange a i j) h
    simpa only [map_add, matrixBaseChange_block, Matrix.add_apply, Matrix.single_apply_same,
      add_right_inj] using h'
  · intro x
    obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hB
    let K := AlgebraicClosure F
    let S := K ⊗[F] R
    let f : R →ₐ[F] S := includeRight
    have hf : Function.Injective f := includeRight_injective (algebraMap F K).injective
    apply hf
    change f (normAt hA b (1 + blockEntry i j x)) = _
    rw [← normAt_natural hA b f, map_one f, map_add, map_one, changeCoefficients_block,
      normAt_eq_flattenDet e, map_add, map_one]
    simp only [flattenSplitting, AlgEquiv.trans_apply, matrixBaseChange_block,
      AlgEquiv.mapMatrix_apply, Matrix.map_single, Matrix.compAlgEquiv_apply]
    exact det_one_add_block i j hij _
  · intro x y
    apply (matrixBaseChange (R := R) (F := F) (B := B) (m := m)).injective
    simp only [map_add, map_mul, map_one, matrixBaseChange_block]
    rw [add_mul, mul_add, mul_add, Matrix.single_mul_single_of_ne x i j i hij.symm y]
    simp [add_assoc, add_comm]

theorem blockSplitting : BlockSplitting := by
  classical
  intro F B K R _ _ _ _ _ _ _ _ _ d m e hA ι _ b
  refine ⟨extendSplitting e, flattenSplitting e, extendSplitting_tmul e,
    normAt_eq_flattenDet e hA b, flattenSplitting_diagonal e, ?_⟩
  intro i j x hij
  obtain ⟨l, hl, ht, hp⟩ := flattened_block_product i j hij (extendSplitting e x) Finset.univ
  refine ⟨l, hl, ht, ?_⟩
  rw [hp, sum_flattened_block]
  simp only [map_add, map_one, flattenSplitting, AlgEquiv.trans_apply, matrixBaseChange_block,
    AlgEquiv.mapMatrix_apply, Matrix.map_single, Matrix.compAlgEquiv_apply]

private def differenceCocharacter {m : ℕ} (i j : Fin m) :
    DiagonalCocharacter m :=
  ⟨Pi.single i 1 - Pi.single j 1, by
    classical
    simp [Finset.sum_sub_distrib, Pi.single_apply]⟩

private theorem character_self {m : ℕ} {i j : Fin m} (h : i ≠ j) :
    blockCharacter i j (differenceCocharacter i j) = 2 := by
  simp [blockCharacter, differenceCocharacter, h, Ne.symm h]

private theorem character_le_two {m : ℕ} (i j k l : Fin m) :
    blockCharacter k l (differenceCocharacter i j) ≤ 2 := by
  simp only [blockCharacter, differenceCocharacter, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> omega

private theorem character_eq_two {m : ℕ} {i j k l : Fin m}
    (h : blockCharacter k l (differenceCocharacter i j) = 2) : i = k ∧ j = l := by
  simp only [blockCharacter, differenceCocharacter, Pi.sub_apply, Pi.single_apply] at h
  split_ifs at h <;> omega

theorem diagonalRootRays : DiagonalRootRays := by
  intro m i j k l hij hkl
  refine ⟨⟨differenceCocharacter i j, by simp [character_self hij]⟩, ?_⟩
  intro p q hp hq h
  have h₁ := h (differenceCocharacter i j)
  have h₂ := h (differenceCocharacter k l)
  rw [character_self hij] at h₁
  rw [character_self hkl] at h₂
  have hpq : p ≤ q := by
    have hle := mul_le_mul_of_nonneg_left (character_le_two i j k l) hq.le
    omega
  have hqp : q ≤ p := by
    have hle := mul_le_mul_of_nonneg_left (character_le_two k l i j) hp.le
    omega
  have heq := le_antisymm hpq hqp
  rw [heq] at h₁
  have hchar := (mul_left_cancel₀ hq.ne' h₁).symm
  obtain ⟨hi, hj⟩ := character_eq_two hchar
  exact ⟨hi, hj, heq⟩


section SchemePoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open LinearAlgebraicGroups.Specs.CharacterPairing (characterValue pairing adjointWeightVectors)
open LinearAlgebraicGroups.Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.Specs.Relative.RelativeChambers (relativeRoots)
open LinearAlgebraicGroups.Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open LinearAlgebraicGroups.CocharacterDynamics
open LinearAlgebraicGroups.Specs.Relative.RelativeReflections (RootCentralizer)
open private centralizes_iff_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private integerPointsIso pointsIso_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private characterValue_one from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

variable {k D₀ : Type u} [Field k] [DivisionRing D₀] [Algebra k D₀] {n : ℕ}
variable {hA : _root_.Specs.RM03.CSA.isCentralSimple k (Matrix (Fin n) (Fin n) D₀)}
variable {J : Type u} [Fintype J] {b : Module.Basis J k (Matrix (Fin n) (Fin n) D₀)}
variable {H : AffineAlgebraicGroup k} {S₀ : ClosedSubgroup H.val}
variable {P : NormOnePoints hA b H}

local notation "Gm" => specGroup (groupAlgebra k IntegerCharacters)

private def unitPresentation (k : Type u) [Field k] :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k IntegerCharacters)) ≅
      LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePoints k :=
  LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k _ ≪≫ integerPointsIso

private theorem unitPresentation_value (R : TestAlgebra k) (x : GroupPoints Gm R) :
    ((unitPresentation k).hom.app R x : Rˣ).val = characterValue (𝟙 Gm) R x := by
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((hopfSpecPointIso (groupAlgebra k IntegerCharacters)).hom.app R)).2 x
  rw [show characterValue (𝟙 Gm) R
      ((hopfSpecPointIso (groupAlgebra k IntegerCharacters)).hom.app R a) =
      a.ofConv (MonoidAlgebra.single integerGenerator 1) by
    unfold characterValue
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((show Points (Gm).X R from (hopfSpecPointIso (groupAlgebra k IntegerCharacters)).hom.app R a) ≫
        𝟙 (Gm).X)).unop.hom _ = _
    rw [Category.comp_id]
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((testSpec k).map (CommAlgCat.ofHom a.ofConv).op)).unop.hom _ = _
    rw [Functor.FullyFaithful.preimage_map]
    rfl]
  change ((show IntegerCharacters →* Rˣ from
    (LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters).hom.app R
      ((hopfSpecPointIso (groupAlgebra k IntegerCharacters)).hom.app R a)) integerGenerator).val = _
  exact pointsIso_spec _ R a.ofConv integerGenerator

private theorem unitPresentation_unitPoint (R : TestAlgebra k) (t : Rˣ) :
    (unitPresentation k).hom.app R (unitPoint R t) = t := by
  apply Units.ext
  rw [unitPresentation_value]
  unfold characterValue
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((show Points (Gm).X R from unitPoint R t) ≫ 𝟙 (Gm).X)).unop.hom _ = _
  rw [Category.comp_id]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom (unitCoordinates R t)).op)).unop.hom _ = _
  rw [Functor.FullyFaithful.preimage_map]
  change unitCoordinates R t (MonoidAlgebra.single integerGenerator 1) = _
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change ((t ^ (1 : ℤ) : Rˣ) : R) = _
  rw [zpow_one]

private def ratioPointHom (D : ScalarDiagonalModel P S₀) (i j : Fin n) (R : TestAlgebra k) :
    GroupPoints S₀.group R →* Rˣ where
  toFun t := (D.tuple R t).val i / (D.tuple R t).val j
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    change ((D.tuple R x).val i * (D.tuple R y).val i) /
      ((D.tuple R x).val j * (D.tuple R y).val j) = _
    exact mul_div_mul_comm _ _ _ _

private def ratioPoints (D : ScalarDiagonalModel P S₀) (i j : Fin n) :
    (groupPointsFunctor k).obj S₀.group ⟶
      LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePoints k where
  app R := GrpCat.ofHom (ratioPointHom D i j R)
  naturality R T f := by
    apply GrpCat.ext
    intro t
    change (D.tuple T (mapPoints f t)).val i / (D.tuple T (mapPoints f t)).val j =
      Units.map f.hom.toMonoidHom ((D.tuple R t).val i / (D.tuple R t).val j)
    rw [D.natural, D.natural, map_div]

private def ratioCharacter (D : ScalarDiagonalModel P S₀) (i j : Fin n) : Character S₀.group :=
  (groupHomEquiv S₀.group Gm
    (affineAlgebraicSubgroup S₀ H.property.1 H.property.2.1 H.property.2.2).property.1).symm
    (ratioPoints D i j ≫ (unitPresentation k).inv)

private theorem ratioCharacter_spec (D : ScalarDiagonalModel P S₀) (i j : Fin n) :
    IsBlockCharacter D i j (ratioCharacter D i j) := by
  intro R t
  have e : (groupPointsFunctor k).map (ratioCharacter D i j) =
      ratioPoints D i j ≫ (unitPresentation k).inv :=
    (groupHomEquiv S₀.group Gm _).apply_symm_apply _
  have et := congrArg (fun f => ((f ≫ (unitPresentation k).hom).app R) t) e
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at et
  simp only [NatTrans.comp_app, GrpCat.comp_apply] at et
  change ((unitPresentation k).hom.app R (t ≫ (ratioCharacter D i j).hom.hom)) =
    (ratioPointHom D i j R) t at et
  have hv := congrArg (fun z : Rˣ => z.val) et
  rw [unitPresentation_value] at hv
  simpa [characterValue, ratioPointHom] using hv

private def powerTuple (w : DiagonalCocharacter n) {R : Type u} [CommRing R]
    (t : Rˣ) : diagonalTuples n R :=
  ⟨fun i => t ^ w.val i, by
    change (∏ i, t ^ w.val i) = 1
    change (∏ i, zpowersHom Rˣ t (Multiplicative.ofAdd (w.val i))) = 1
    rw [← map_prod]
    change t ^ (∑ i, w.val i) = 1
    rw [w.property, zpow_zero]⟩

private def powerPoints (D : ScalarDiagonalModel P S₀) (w : DiagonalCocharacter n) :
    LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePoints k ⟶
      (groupPointsFunctor k).obj S₀.group where
  app R := GrpCat.ofHom {
    toFun := fun t => (D.tuple R).symm (powerTuple w t)
    map_one' := by apply (D.tuple R).injective; ext i; simp [powerTuple]
    map_mul' := fun x y => by
      apply (D.tuple R).injective
      rw [map_mul]
      simp only [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      funext i
      exact mul_zpow x y _ }
  naturality R T f := by
    apply GrpCat.ext
    intro t
    apply (D.tuple T).injective
    apply Subtype.ext
    funext i
    change (D.tuple T ((D.tuple T).symm (powerTuple w (Units.map f.hom.toMonoidHom t)))).val i =
      (D.tuple T (mapPoints f ((D.tuple R).symm (powerTuple w t)))).val i
    rw [D.natural, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact (map_zpow (Units.map f.hom.toMonoidHom) t (w.val i)).symm

private def diagonalCocharacter (D : ScalarDiagonalModel P S₀) (w : DiagonalCocharacter n) :
    Cocharacter S₀.group :=
  (groupHomEquiv Gm S₀.group
    (show IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters))) by infer_instance)).symm
    ((unitPresentation k).hom ≫ powerPoints D w)

private theorem diagonalCocharacter_spec (D : ScalarDiagonalModel P S₀) (w : DiagonalCocharacter n)
    (R : TestAlgebra k) (t : Rˣ) :
    D.tuple R (cocharacterPoint (diagonalCocharacter D w) R t) = powerTuple w t := by
  have e : (groupPointsFunctor k).map (diagonalCocharacter D w) =
      (unitPresentation k).hom ≫ powerPoints D w :=
    (groupHomEquiv Gm S₀.group _).apply_symm_apply _
  unfold cocharacterPoint
  rw [e]
  simp only [NatTrans.comp_app, GrpCat.comp_apply]
  change D.tuple R ((D.tuple R).symm (powerTuple w
    ((unitPresentation k).hom.app R (unitPoint R t)))) = _
  rw [unitPresentation_unitPoint, MulEquiv.apply_symm_apply]

open LinearAlgebraicGroups.Specs.AdjointRepresentation (dualMap reduction constants scale)
open LinearAlgebraicGroups.RootData.CharacterPairing (characterPairingComposition)
open private laurentParameter_zpow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLieWeights

variable {I : Type u} (v : Module.Basis I k D₀)

private def blockCoeff {R : Type u} [CommRing R] [Algebra k R]
    (i j : Fin n) (l : I) (x : R ⊗[k] Matrix (Fin n) (Fin n) D₀) : R :=
  (v.baseChange R).repr (blockProjection i j x) l

private theorem blockCoeff_ext {R : Type u} [CommRing R] [Algebra k R]
    {x y : R ⊗[k] Matrix (Fin n) (Fin n) D₀}
    (h : ∀ i j l, blockCoeff v i j l x = blockCoeff v i j l y) : x = y := by
  apply matrixBaseChange.injective
  ext i j
  rw [matrixBaseChange_apply, matrixBaseChange_apply]
  exact (v.baseChange R).repr.injective (Finsupp.ext (h i j))

private theorem blockCoeff_tmul {R : Type u} [CommRing R] [Algebra k R]
    (i j : Fin n) (l : I) (r : R) (x : Matrix (Fin n) (Fin n) D₀) :
    blockCoeff v i j l (r ⊗ₜ[k] x) = (algebraMap k R (v.repr (x i j) l)) * r := by
  simp [blockCoeff, blockProjection, TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def]

private theorem blockCoeff_natural {R T : Type u}
    [CommRing R] [Algebra k R] [CommRing T] [Algebra k T]
    (f : R →ₐ[k] T) (i j : Fin n) (l : I) (x : R ⊗[k] Matrix (Fin n) (Fin n) D₀) :
    blockCoeff v i j l (changeCoefficients f x) = f (blockCoeff v i j l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp [changeCoefficients, blockCoeff_tmul, f.commutes]
  | add x y hx hy =>
    simp only [map_add, blockCoeff, Finsupp.add_apply] at hx hy ⊢
    rw [hx, hy]

private theorem blockCoeff_add {R : Type u} [CommRing R] [Algebra k R]
    (i j : Fin n) (l : I) (x y : R ⊗[k] Matrix (Fin n) (Fin n) D₀) :
    blockCoeff v i j l (x + y) = blockCoeff v i j l x + blockCoeff v i j l y := by
  simp [blockCoeff]

private theorem blockCoeff_one {R : Type u} [CommRing R] [Algebra k R]
    (i j : Fin n) (l : I) :
    blockCoeff v i j l (1 : R ⊗[k] Matrix (Fin n) (Fin n) D₀) =
      algebraMap k R (v.repr ((1 : Matrix (Fin n) (Fin n) D₀) i j) l) := by
  rw [Algebra.TensorProduct.one_def, blockCoeff_tmul, mul_one]

private theorem blockCoeff_transvection {R : Type u} [CommRing R] [Algebra k R]
    (i j p q : Fin n) (l : I) (x : R ⊗[k] D₀) :
    blockCoeff v p q l (1 + blockEntry i j x) =
      blockCoeff v p q l (1 : R ⊗[k] Matrix (Fin n) (Fin n) D₀) +
      if p = i ∧ q = j then (v.baseChange R).repr x l else 0 := by
  rw [blockCoeff_add]
  congr 1
  rw [blockCoeff, ← matrixBaseChange_apply, matrixBaseChange_block]
  by_cases hp : p = i <;> by_cases hq : q = j <;>
    simp [Matrix.single, hp, hq, eq_comm (a := i), eq_comm (a := j)]

private theorem normPoint_val_injective (P : NormOnePoints hA b H) (R : TestAlgebra k) :
    Function.Injective (fun x : GroupPoints H.val R => (P.point R x).val) :=
  fun _ _ h => (P.point R).injective (Subtype.ext h)

private theorem normPoint_inv_diagonal (D : ScalarDiagonalModel P S₀)
    (R : TestAlgebra k) (t : GroupPoints S₀.group R) :
    (P.point R ((t ≫ S₀.inclusion.hom.hom)⁻¹)).val =
      scalarDiagonal fun i => (((D.tuple R t).val i)⁻¹ : Rˣ).val := by
  rw [← show t⁻¹ ≫ S₀.inclusion.hom.hom = (t ≫ S₀.inclusion.hom.hom)⁻¹ from
    (((groupPointsFunctor k).map S₀.inclusion).app R).hom.map_inv t, D.diagonal]
  simp [map_inv]
  
private theorem blockCoeff_conjugate (D : ScalarDiagonalModel P S₀)
    (R : TestAlgebra k) (t : GroupPoints S₀.group R) (g : GroupPoints H.val R)
    (i j : Fin n) (l : I) :
    blockCoeff v i j l
      (P.point R ((show GroupPoints H.val R from t ≫ S₀.inclusion.hom.hom) * g *
        (show GroupPoints H.val R from t ≫ S₀.inclusion.hom.hom)⁻¹)).val =
    (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R) *
      blockCoeff v i j l (P.point R g).val := by
  rw [P.mul, P.mul, D.diagonal, normPoint_inv_diagonal D]
  unfold blockCoeff
  rw [diagonalAction]
  simp [div_eq_mul_inv]

private theorem blockCoeff_pointMap {R T : TestAlgebra k} (f : R ⟶ T)
    (g : GroupPoints H.val R) (i j : Fin n) (l : I) :
    blockCoeff v i j l (P.point T (mapPoints f g)).val =
      f.hom (blockCoeff v i j l (P.point R g).val) := by
  rw [P.natural]
  exact blockCoeff_natural v f.hom i j l _

private abbrev base (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private def tangentCoeff (w : Lie k H.val) (i j : Fin n) (l : I) : k :=
  (blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).snd

private theorem tangentCoeff_fst (w : Lie k H.val) (i j : Fin n) (l : I) :
    (blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst =
      v.repr ((1 : Matrix (Fin n) (Fin n) D₀) i j) l := by
  have e := blockCoeff_pointMap (P := P) v (dualReduction k) w.toMul.val i j l
  change blockCoeff v i j l (P.point (base k) (mapPoints (dualReduction k) w.toMul.val)).val =
      (blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst at e
  have hw : mapPoints (dualReduction k) w.toMul.val = (1 : GroupPoints H.val (base k)) :=
    w.toMul.property
  rw [hw, P.one, blockCoeff_one] at e
  exact e.symm

private theorem tangentCoeff_nonzero (w : Lie k H.val) (hw : w ≠ 0) :
    ∃ i j l, tangentCoeff (P := P) v w i j l ≠ 0 := by
  by_contra! hz
  apply hw
  apply Additive.toMul.injective
  apply Subtype.ext
  apply normPoint_val_injective P
  apply blockCoeff_ext v
  intro i j l
  change blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val =
    blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) 1).val
  rw [P.one, blockCoeff_one]
  apply TrivSqZeroExt.ext
  · exact tangentCoeff_fst (P := P) v w i j l
  · exact hz i j l

private theorem adjointWeight_iff_coeff (D : ScalarDiagonalModel P S₀)
    (a : Character S₀.group) (w : Lie k H.val) :
    w ∈ adjointWeightVectors S₀ a ↔
      ∀ (R : TestAlgebra k) (t : GroupPoints S₀.group R) (i j : Fin n) (l : I),
        ((((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R)) *
          algebraMap k R (tangentCoeff (P := P) v w i j l) =
        characterValue a R t * algebraMap k R (tangentCoeff (P := P) v w i j l) := by
  change (∀ (R : TestAlgebra k) (t : GroupPoints S₀.group R), _) ↔ _
  have hc (R : TestAlgebra k) (t : GroupPoints S₀.group R) (i j : Fin n) (l : I) :
      let f := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
      let p : GroupPoints H.val (CommAlgCat.of k (DualNumber R)) := mapPoints f w.toMul.val
      let g : GroupPoints H.val (CommAlgCat.of k (DualNumber R)) :=
        mapPoints (constants R) (t ≫ S₀.inclusion.hom.hom)
      blockCoeff v i j l (P.point _ (g * p * g⁻¹)).val =
        blockCoeff v i j l (P.point _ (mapPoints (scale R (characterValue a R t)) p)).val ↔
        (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R) *
          algebraMap k R (tangentCoeff (P := P) v w i j l) =
        characterValue a R t * algebraMap k R (tangentCoeff (P := P) v w i j l) := by
    dsimp only
    rw [show mapPoints (constants R) (t ≫ S₀.inclusion.hom.hom) =
      mapPoints (constants R) t ≫ S₀.inclusion.hom.hom from Category.assoc ((testSpec k).map (constants R).op) t S₀.inclusion.hom.hom]
    rw [blockCoeff_conjugate (P := P) v D, blockCoeff_pointMap v, blockCoeff_pointMap v,
      blockCoeff_pointMap v]
    have he : ((D.tuple _ (mapPoints (constants R) t)).val i /
      (D.tuple _ (mapPoints (constants R) t)).val j) =
      Units.map (constants R).hom.toMonoidHom ((D.tuple R t).val i / (D.tuple R t).val j) := by
      rw [D.natural, D.natural, map_div]
    rw [he]
    constructor
    · intro e
      have hh := congrArg TrivSqZeroExt.snd e
      change (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R) *
        algebraMap k R (tangentCoeff (P := P) v w i j l) +
        0 * algebraMap k R (blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst =
        characterValue a R t * algebraMap k R (tangentCoeff (P := P) v w i j l) at hh
      simpa only [zero_mul, add_zero] using hh
    · intro e
      apply TrivSqZeroExt.ext
      · change (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R) *
          algebraMap k R ((blockCoeff v i j l
            (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst) = _
        change _ * algebraMap k R (blockCoeff v i j l
          (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst =
            algebraMap k R (blockCoeff v i j l
              (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst
        rw [tangentCoeff_fst]
        by_cases hij : i = j
        · subst j; simp
        · simp [Matrix.one_apply_ne hij]
      · change (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R) *
          algebraMap k R (tangentCoeff (P := P) v w i j l) +
          0 * algebraMap k R (blockCoeff v i j l (P.point (CommAlgCat.of k (DualNumber k)) w.toMul.val).val).fst =
          characterValue a R t * algebraMap k R (tangentCoeff (P := P) v w i j l)
        simpa only [zero_mul, add_zero] using e
  constructor
  · intro hw R t i j l
    exact (hc R t i j l).mp (congrArg (fun p => blockCoeff v i j l (P.point _ p).val) (hw R t))
  · intro hw R t
    apply normPoint_val_injective P
    apply blockCoeff_ext v
    intro i j l
    exact (hc R t i j l).mpr (hw R t i j l)

private theorem powerTuple_div (w : DiagonalCocharacter n) {R : Type u} [CommRing R]
    (t : Rˣ) (i j : Fin n) :
    (powerTuple w t).val i / (powerTuple w t).val j = t ^ blockCharacter i j w :=
  (zpow_sub t _ _).symm

private theorem laurentParameter_powers_injective {R : TestAlgebra k} [Nontrivial R] :
    Function.Injective (fun e : ℤ => laurentParameter R ^ e) := by
  intro a b h
  have e := congrArg Units.val h
  rw [laurentParameter_zpow, laurentParameter_zpow] at e
  exact (AddMonoidAlgebra.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp e

theorem relativeRootPairing : RelativeRootPairing.{u} := by
  intro k B _ _ _ n hA J _ b H P S₀ D
  have pair (i j) (w : DiagonalCocharacter n) :
      pairing S₀.group (ratioCharacter D i j) (diagonalCocharacter D w) =
        blockCharacter i j w := by
    let R := base k
    let t := laurentParameter R
    have h := (characterPairingComposition S₀.group (ratioCharacter D i j)
      (diagonalCocharacter D w)).2 (laurentAlgebra R) t
    rw [ratioCharacter_spec D i j, diagonalCocharacter_spec, powerTuple_div] at h
    exact laurentParameter_powers_injective (Units.ext h.symm)
  refine ⟨ratioCharacter D, diagonalCocharacter D, ratioCharacter_spec D, ?_, pair, ?_⟩
  · intro w R t i
    rw [diagonalCocharacter_spec]
    rfl
  · intro i j hij
    exact ⟨differenceCocharacter i j, (pair i j _).trans (character_self hij)⟩

theorem splitAbsoluteRootRestrictions : SplitAbsoluteRootRestrictions.{u} := by
  intro k _ m d p q _
  let R := base k
  let t := laurentParameter R
  constructor
  · constructor
    · intro h
      by_contra hne
      have e := h (laurentAlgebra R) (powerTuple (differenceCocharacter p.1 q.1) t)
      rw [powerTuple_div, character_self hne, ← zpow_zero t] at e
      have he : (2 : ℤ) = 0 := laurentParameter_powers_injective e
      omega
    · intro h T z
      simp [h]
  · intro i j hij a b ha hb
    constructor
    · intro h
      have he (w : DiagonalCocharacter m) :
          a * blockCharacter p.1 q.1 w = b * blockCharacter i j w := by
        have e := h (laurentAlgebra R) (powerTuple w t)
        rw [powerTuple_div, powerTuple_div, ← zpow_mul, ← zpow_mul] at e
        simpa only [mul_comm a, mul_comm b] using laurentParameter_powers_injective e
      have hpq : p.1 ≠ q.1 := by
        intro hq
        have e := he (differenceCocharacter i j)
        rw [character_self hij] at e
        simp [blockCharacter, hq] at e
        omega
      exact (diagonalRootRays hpq hij).2 a b ha hb he
    · rintro ⟨hi, hj, rfl⟩ T z
      simp [hi, hj]

private theorem ratioCharacter_ne_one (D : ScalarDiagonalModel P S₀) {i j : Fin n}
    (hij : i ≠ j) (a : Character S₀.group) (ha : IsBlockCharacter D i j a) : a ≠ 1 := by
  intro h
  let R := laurentAlgebra (base k)
  let w := differenceCocharacter i j
  let t := (D.tuple R).symm (powerTuple w (laurentParameter (base k)))
  have e := ha R t
  rw [h, characterValue_one, show D.tuple R t = powerTuple w (laurentParameter (base k)) from
    MulEquiv.apply_symm_apply _ _, powerTuple_div, character_self hij, laurentParameter_zpow] at e
  have he := congrArg (fun p : LaurentPolynomial k => p.coeff 2) e
  change (LaurentPolynomial.T 0 : LaurentPolynomial k).coeff 2 =
    (LaurentPolynomial.T 2 : LaurentPolynomial k).coeff 2 at he
  have h0 : (LaurentPolynomial.T 0 : LaurentPolynomial k).coeff 2 = 0 := by
    rw [LaurentPolynomial.T_apply]
    rfl
  have h2 : (LaurentPolynomial.T 2 : LaurentPolynomial k).coeff 2 = 1 := by
    rw [LaurentPolynomial.T_apply]
    rfl
  exact zero_ne_one (h0.symm.trans (he.trans h2))

private def transvectionPoint
    (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    (R : TestAlgebra k) (i j : Fin n) (hij : i ≠ j) (x : R ⊗[k] D₀) :
    GroupPoints H.val R :=
  (P.point R).symm ⟨1 + blockEntry i j x, (blockTransvections hB hA b i j hij).2.1 x⟩

private theorem transvectionPoint_val
    (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    (R : TestAlgebra k) (i j : Fin n) (hij : i ≠ j) (x : R ⊗[k] D₀) :
    (P.point R (transvectionPoint (P := P) hB R i j hij x)).val = 1 + blockEntry i j x := by
  unfold transvectionPoint
  rw [Equiv.apply_symm_apply]

private theorem rootCalculationOfSplitDiagonal
    (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    (hS : LinearAlgebraicGroups.Specs.GeometricRadicals.IsSplitTorus S₀.group)
    (D : ScalarDiagonalModel P S₀) (a : Character S₀.group) :
    a ∈ relativeRoots S₀ ↔ ∃ i j : Fin n, i ≠ j ∧ IsBlockCharacter D i j a := by
  classical
  let v := Module.Free.chooseBasis k D₀
  change (a ≠ 1 ∧ ∃ w ∈ adjointWeightVectors S₀ a, w ≠ 0) ↔ _
  constructor
  · rintro ⟨ha, w, hw, hn⟩
    obtain ⟨i, j, l, hl⟩ := tangentCoeff_nonzero (P := P) v w hn
    have he R t := (adjointWeight_iff_coeff v D a w).mp hw R t i j l
    have hc (R : TestAlgebra k) : IsUnit (algebraMap k R (tangentCoeff (P := P) v w i j l)) :=
      (isUnit_iff_ne_zero.mpr hl).map (algebraMap k R)
    have hp (R : TestAlgebra k) (t : GroupPoints S₀.group R) :=
      (hc R).mul_right_cancel (he R t)
    have hij : i ≠ j := by
      rintro rfl
      apply ha
      apply LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters hS
      intro R t
      rw [characterValue_one, ← hp R t]
      simp
    exact ⟨i, j, hij, fun R t => (hp R t).symm⟩
  · rintro ⟨i, j, hij, ha⟩
    refine ⟨ratioCharacter_ne_one D hij a ha, ?_⟩
    let R := CommAlgCat.of k (DualNumber k)
    let x : R ⊗[k] D₀ := DualNumber.eps ⊗ₜ[k] 1
    let g := transvectionPoint (P := P) hB R i j hij x
    have hv : mapPoints (dualReduction k) g = (1 : GroupPoints H.val (base k)) := by
      apply normPoint_val_injective P
      change (P.point (base k) (mapPoints (dualReduction k) g)).val =
        (P.point (base k) 1).val
      rw [P.one, P.natural, transvectionPoint_val]
      change changeCoefficients (dualReduction k).hom (1 + blockEntry i j x) = 1
      rw [map_add, map_one, changeCoefficients_block]
      change 1 + blockEntry i j (changeCoefficients (dualReduction k).hom
        (DualNumber.eps ⊗ₜ[k] 1)) = _
      rw [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change 1 + blockEntry i j ((0 : k) ⊗ₜ[k] (1 : D₀)) = _
      rw [TensorProduct.zero_tmul, map_zero, add_zero]
    let w : Lie k H.val := Additive.ofMul ⟨g, hv⟩
    have hcoeff (p q) l : tangentCoeff (P := P) v w p q l =
        if p = i ∧ q = j then v.repr 1 l else 0 := by
      change (blockCoeff v p q l (P.point R g).val).snd = _
      rw [transvectionPoint_val, blockCoeff_transvection, blockCoeff_one]
      by_cases h : p = i ∧ q = j
      · simp only [h, and_self, ite_true, x, Module.Basis.baseChange_repr_tmul, Algebra.smul_def]
        change (0 : k) + ((v.repr 1) l * 1 + 0 * 0) = _
        ring
      · simp only [h, ite_false, add_zero]
        rfl
    refine ⟨w, (adjointWeight_iff_coeff v D a w).mpr ?_, ?_⟩
    · intro T t p q l
      rw [hcoeff]
      by_cases h : p = i ∧ q = j
      · rcases h with ⟨rfl, rfl⟩
        simp [ha T t]
      · simp [h]
    · intro hz
      have hh (l) := hcoeff i j l
      rw [hz] at hh
      have hzero (l) : tangentCoeff (P := P) v (0 : Lie k H.val) i j l = 0 := by
        change (blockCoeff v i j l (P.point R 1).val).snd = 0
        rw [P.one, blockCoeff_one]
        rfl
      apply (one_ne_zero : (1 : D₀) ≠ 0)
      apply v.repr.injective
      ext l
      have h := hh l
      rw [hzero] at h
      simpa using h.symm

theorem relativeRootCalculation : RelativeRootCalculation.{u} := by
  intro k B _ _ _ n hB hA J _ b H P S₀ hS D a
  exact rootCalculationOfSplitDiagonal hB hS.1 D a

private def splitMatrixCoordinates (k : Type u) [Field k] (R : TestAlgebra k) (n : ℕ) :
    R ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
  extendSplitting (K := k) (Algebra.TensorProduct.lid k _)

private theorem splitMatrixCoordinates_tmul {R : TestAlgebra k} (r : R)
    (M : Matrix (Fin n) (Fin n) k) :
    splitMatrixCoordinates k R n (r ⊗ₜ[k] M) = r • M.map (algebraMap k R) := by
  unfold splitMatrixCoordinates
  rw [extendSplitting_tmul, Algebra.TensorProduct.lid_tmul, one_smul]

private theorem normAt_eq_splitDet {R : TestAlgebra k}
    (h : _root_.Specs.RM03.CSA.isCentralSimple k (Matrix (Fin n) (Fin n) k))
    {L : Type*} [Fintype L] (b : Module.Basis L k (Matrix (Fin n) (Fin n) k))
    (x : R ⊗[k] Matrix (Fin n) (Fin n) k) :
    normAt h b x = (splitMatrixCoordinates k R n x).det := by
  let E := Algebra.TensorProduct.lid k (Matrix (Fin n) (Fin n) k)
  let r := finCongr (degree_eq_matrix_size h E).symm
  let E' := E.trans (Matrix.reindexAlgEquiv k k r)
  rw [normAt_eq_det h b E']
  have he : extendSplitting E' x = Matrix.reindexAlgEquiv R R r (splitMatrixCoordinates k R n x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a M =>
      rw [extendSplitting_tmul, splitMatrixCoordinates_tmul]
      simp only [E', E, AlgEquiv.trans_apply, Algebra.TensorProduct.lid_tmul, one_smul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact (congrArg Matrix.det he).trans (Matrix.det_reindexAlgEquiv R R r _)

private theorem splitMatrixCoordinates_diagonal (R : TestAlgebra k) (t : Fin n → R) :
    splitMatrixCoordinates k R n (scalarDiagonal (F := k) (B := k) t) = Matrix.diagonal t := by
  simp only [scalarDiagonal, map_sum, splitMatrixCoordinates_tmul, Matrix.map_single,
    map_one, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_single_eq_diagonal]

private def reindexedSplitMatrixCoordinates {κ : Type u} [Fintype κ] [DecidableEq κ]
    (e : κ ≃ Fin n) (R : TestAlgebra k) :
    R ⊗[k] Matrix (Fin n) (Fin n) k ≃ₐ[R] Matrix κ κ R :=
  (splitMatrixCoordinates k R n).trans (Matrix.reindexAlgEquiv R R e.symm)

private theorem reindexedSplitMatrixCoordinates_natural
    {κ : Type u} [Fintype κ] [DecidableEq κ] (e : κ ≃ Fin n)
    {R S : TestAlgebra k} (f : R ⟶ S) (x : R ⊗[k] Matrix (Fin n) (Fin n) k) :
    reindexedSplitMatrixCoordinates e S (changeCoefficients f.hom x) =
      (reindexedSplitMatrixCoordinates e R x).map f.hom := by
  induction x using TensorProduct.inductionOn with
  | tmul r M =>
    simp only [reindexedSplitMatrixCoordinates, AlgEquiv.trans_apply, changeCoefficients,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, splitMatrixCoordinates_tmul]
    ext i j
    change f.hom r * algebraMap k S (M (e i) (e j)) =
      f.hom (r * algebraMap k R (M (e i) (e j)))
    rw [map_mul, AlgHom.commutes]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    ext i j
    exact (map_add f.hom _ _).symm

private theorem reindexedSplitMatrixCoordinates_diagonal
    {κ : Type u} [Fintype κ] [DecidableEq κ] (e : κ ≃ Fin n)
    (R : TestAlgebra k) (t : Fin n → R) :
    reindexedSplitMatrixCoordinates e R (scalarDiagonal (F := k) (B := k) t) =
      Matrix.diagonal (t ∘ e) := by
  simp only [reindexedSplitMatrixCoordinates, AlgEquiv.trans_apply, splitMatrixCoordinates_diagonal]
  ext i j
  change (Matrix.diagonal t) (e i) (e j) = Matrix.diagonal (t ∘ e) i j
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.diagonal, hij, e.injective.ne hij]

private theorem normOneMatrixModel {κ : Type u} [Fintype κ] [DecidableEq κ]
    (J : (groupPointsFunctor k).obj H.val ≅ LinearAlgebraicGroups.Specs.StandardGroups.specialLinearPoints k κ)
    (E : ∀ R : TestAlgebra k, R ⊗[k] Matrix (Fin n) (Fin n) D₀ ≃ₐ[R] Matrix κ κ R)
    (hNorm : ∀ (R : TestAlgebra k) x, normAt hA b x = (E R x).det)
    (hChange : ∀ {R T : TestAlgebra k} (f : R ⟶ T) x,
      E T (changeCoefficients f.hom x) = (E R x).map f.hom) :
    ∃ Q : NormOnePoints hA b H, ∀ (R : TestAlgebra k) (x : GroupPoints H.val R),
      E R (Q.point R x).val = (show Matrix.SpecialLinearGroup κ R from J.hom.app R x).val := by
  let φ (R : TestAlgebra k) :
      {x : R ⊗[k] Matrix (Fin n) (Fin n) D₀ //
        _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b x = 1} ≃
        Matrix.SpecialLinearGroup κ R :=
    (E R).toEquiv.subtypeEquiv (fun x => by
      change normAt hA b x = 1 ↔ (E R x).det = 1
      rw [hNorm R])
  let points (R : TestAlgebra k) := (J.app R).groupIsoToMulEquiv.toEquiv.trans (φ R).symm
  have eval (R : TestAlgebra k) (x : GroupPoints H.val R) :
      E R (points R x).val = (show Matrix.SpecialLinearGroup κ R from J.hom.app R x).val :=
    (E R).apply_symm_apply _
  refine ⟨⟨points, ?_, ?_, ?_⟩, eval⟩
  · intro R
    apply (E R).injective
    exact (eval R 1).trans
      ((congrArg Subtype.val (J.hom.app R).hom.map_one).trans (map_one (E R)).symm)
  · intro R x y
    apply (E R).injective
    calc
      _ = (show Matrix.SpecialLinearGroup κ R from J.hom.app R (x * y)).val := eval R _
      _ = (show Matrix.SpecialLinearGroup κ R from J.hom.app R x).val *
          (show Matrix.SpecialLinearGroup κ R from J.hom.app R y).val :=
        congrArg Subtype.val ((J.hom.app R).hom.map_mul x y)
      _ = E R (points R x).val * E R (points R y).val :=
        congrArg₂ (· * ·) (eval R x).symm (eval R y).symm
      _ = _ := (map_mul (E R) _ _).symm
  · intro R T f x
    apply (E T).injective
    have h := congrArg (fun q : ((groupPointsFunctor k).obj H.val).obj R ⟶
      (LinearAlgebraicGroups.Specs.StandardGroups.specialLinearPoints k κ).obj T => q x)
      (J.hom.naturality f)
    change E T (points T (mapPoints f x)).val = E T (changeCoefficients f.hom (points R x).val)
    rw [eval, hChange f, eval]
    exact congrArg (fun y : Matrix.SpecialLinearGroup κ T => y.val) h

theorem splitAbsoluteRootCalculation : SplitAbsoluteRootCalculation.{u} := by
  intro k _ κ _ _ hκ n e G J T t hT ht hdiag
  letI : Nonempty (Fin n) := Nonempty.map e hκ
  have hk : _root_.Specs.RM03.CSA.isCentralSimple k k :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hM : _root_.Specs.RM03.CSA.isCentralSimple k (Matrix (Fin n) (Fin n) k) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  let b := (Matrix.stdBasis k (Fin n) (Fin n)).reindex
    (Equiv.ulift.symm : (Fin n × Fin n) ≃ ULift.{u} (Fin n × Fin n))
  have hNorm (R : TestAlgebra k) (x : R ⊗[k] Matrix (Fin n) (Fin n) k) :
      normAt hM b x = (reindexedSplitMatrixCoordinates e R x).det := by
    exact (normAt_eq_splitDet hM b x).trans (Matrix.det_reindexAlgEquiv R R e.symm _).symm
  obtain ⟨P, hP⟩ := normOneMatrixModel (D₀ := k) (hA := hM) (b := b) J
    (reindexedSplitMatrixCoordinates e) hNorm
    (reindexedSplitMatrixCoordinates_natural e)
  let D : ScalarDiagonalModel P T := {
    tuple := t
    natural := ht
    diagonal := by
      intro R x
      apply (reindexedSplitMatrixCoordinates e R).injective
      exact (hP R (x ≫ T.inclusion.hom.hom)).trans
        ((hdiag R x).trans (reindexedSplitMatrixCoordinates_diagonal e R
          (fun i => ((t R x).val i : R))).symm) }

  refine ⟨fun p q => ratioCharacter D (e p) (e q), fun p q => ratioCharacter_spec D (e p) (e q), ?_⟩
  intro a
  change a ∈ relativeRoots T ↔ _
  have hroot := rootCalculationOfSplitDiagonal hk hT D a
  constructor
  · intro h
    obtain ⟨i, j, hij, ha⟩ := hroot.mp h
    refine ⟨e.symm i, e.symm j, e.symm.injective.ne hij, ?_⟩
    change a = ratioCharacter D (e (e.symm i)) (e (e.symm j))
    rw [e.apply_symm_apply, e.apply_symm_apply]
    apply LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters hT
    intro R x
    exact (ha R x).trans (ratioCharacter_spec D i j R x).symm
  · rintro ⟨p, q, hpq, rfl⟩
    exact (rootCalculationOfSplitDiagonal hk hT D _).mpr
      ⟨e p, e q, e.injective.ne hpq, ratioCharacter_spec D _ _⟩

omit v in
private theorem kernelExponent_separates {i j p q : Fin n} (hij : i ≠ j) (hpq : p ≠ q)
    (hf : ¬ (p = i ∧ q = j)) (hr : ¬ (p = j ∧ q = i)) :
    ∃ w : DiagonalCocharacter n, blockCharacter i j w = 0 ∧ blockCharacter p q w ≠ 0 := by
  let doubleDifference (r : Fin n) : DiagonalCocharacter n :=
    ⟨(differenceCocharacter r i).val + (differenceCocharacter r j).val, by
      rw [show (∑ a, ((differenceCocharacter r i).val + (differenceCocharacter r j).val) a) =
        (∑ a, (differenceCocharacter r i).val a) + (∑ a, (differenceCocharacter r j).val a)
        from Finset.sum_add_distrib]
      rw [(differenceCocharacter r i).property, (differenceCocharacter r j).property, add_zero]⟩
  by_cases hp : p = i ∨ p = j
  · have hqi : q ≠ i := by rintro rfl; rcases hp with h | h; exacts [hpq h, hr ⟨h,rfl⟩]
    have hqj : q ≠ j := by rintro rfl; rcases hp with h | h; exacts [hf ⟨h,rfl⟩, hpq h]
    refine ⟨doubleDifference q, ?_, ?_⟩
    · simp [doubleDifference, blockCharacter, differenceCocharacter, hij, hqi, hqj, Ne.symm hij,
        Ne.symm hqi, Ne.symm hqj]
    · rcases hp with rfl | rfl <;>
        simp [doubleDifference, blockCharacter, differenceCocharacter, hij, hqi, hqj, Ne.symm hij,
          Ne.symm hqi, Ne.symm hqj]
  · push_neg at hp
    by_cases hq : q = i ∨ q = j
    · refine ⟨doubleDifference p, ?_, ?_⟩
      · simp [doubleDifference, blockCharacter, differenceCocharacter, hij, hp.1, hp.2,
          Ne.symm hij, Ne.symm hp.1, Ne.symm hp.2]
      · rcases hq with rfl | rfl <;>
          simp [doubleDifference, blockCharacter, differenceCocharacter, hij, hp.1, hp.2,
            Ne.symm hij, Ne.symm hp.1, Ne.symm hp.2]
    · push_neg at hq
      refine ⟨differenceCocharacter p q, ?_, by rw [character_self hpq]; decide⟩
      simp [blockCharacter, differenceCocharacter, hp.1, hp.2, hq.1, hq.2,
        Ne.symm hp.1, Ne.symm hp.2, Ne.symm hq.1, Ne.symm hq.2]

private abbrev onGroupPoints {G L : GroupScheme k} (f : G ⟶ L) (R : TestAlgebra k) :
    GroupPoints G R →* GroupPoints L R :=
  ((groupPointsFunctor k).map f |>.app R).hom

private theorem kernel_point_value (a : relativeRoots S₀) (C : RootCentralizer S₀ a)
    (R : TestAlgebra k) (d : GroupPoints C.kernel.subgroup.group R) :
    characterValue a.val R (onGroupPoints C.kernel.subgroup.inclusion R d) = 1 := by
  have e : onGroupPoints a.val R (onGroupPoints C.kernel.subgroup.inclusion R d) = 1 := by
    change d ≫ C.kernel.subgroup.inclusion.hom.hom ≫ a.val.hom.hom = _
    rw [C.kernel.isKernel.w]
    rw [← Category.assoc, Subsingleton.elim (d ≫ toUnit _) (toUnit _)]
    rfl
  change characterValue (𝟙 (Gm)) R (onGroupPoints a.val R
    (onGroupPoints C.kernel.subgroup.inclusion R d)) = 1
  rw [e, ← unitPresentation_value]
  exact congrArg Units.val ((unitPresentation k).hom.app R).hom.map_one

private theorem kernel_point_lift (a : relativeRoots S₀) (C : RootCentralizer S₀ a)
    (R : TestAlgebra k) (t : GroupPoints S₀.group R) (ht : characterValue a.val R t = 1) :
    ∃ d : GroupPoints C.kernel.subgroup.group R, onGroupPoints C.kernel.subgroup.inclusion R d = t := by
  have e : onGroupPoints a.val R t = 1 := by
    apply (ConcreteCategory.bijective_of_isIso ((unitPresentation k).hom.app R)).1
    apply Units.ext
    rw [unitPresentation_value]
    change characterValue a.val R t = _
    rw [ht]
    exact (congrArg Units.val ((unitPresentation k).hom.app R).hom.map_one).symm
  have hw : t ≫ a.val.hom.hom = toUnit _ ≫ η[(Gm).X] := e
  exact ⟨C.kernel.isKernel.lift t (toUnit _) hw, C.kernel.isKernel.lift_fst ..⟩

private theorem centralizesCharacterKernel_iff (a : relativeRoots S₀) (C : RootCentralizer S₀ a)
    {R : TestAlgebra k} (g : GroupPoints H.val R) :
    CentralizesCharacterKernel S₀ a.val g ↔ Centralizes (C.kernel.subgroup.inclusion ≫ S₀.inclusion) g := by
  constructor
  · intro h
    apply (centralizes_iff_affine _ _).mpr
    intro T t d
    let f : R ⟶ T := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage t).unop
    have ht : (testSpec k).map f.op = t := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage t
    change Commute (t ≫ g) (onGroupPoints S₀.inclusion T (onGroupPoints C.kernel.subgroup.inclusion T d))
    rw [← ht]
    exact h T f _ (kernel_point_value a C T d)
  · intro h T f t ht
    obtain ⟨d, hd⟩ := kernel_point_lift a C T t ht
    have hcomm := (centralizes_iff_affine _ _).mp h T ((testSpec k).map f.op) d
    change Commute (show GroupPoints H.val T from mapPoints f g)
      (onGroupPoints S₀.inclusion T (onGroupPoints C.kernel.subgroup.inclusion T d)) at hcomm
    rw [hd] at hcomm
    exact hcomm

private def blockOffset {R : Type u} [CommRing R] [Algebra k R]
    (i j : Fin n) (l : I) (M : R ⊗[k] Matrix (Fin n) (Fin n) D₀) : R :=
  blockCoeff v i j l M - blockCoeff v i j l 1

private theorem blockOffset_pointMap {R T : TestAlgebra k} (f : R ⟶ T)
    (g : GroupPoints H.val R) (i j : Fin n) (l : I) :
    blockOffset v i j l (P.point T (mapPoints f g)).val =
      f.hom (blockOffset v i j l (P.point R g).val) := by
  unfold blockOffset
  rw [map_sub, blockCoeff_pointMap v, blockCoeff_one, blockCoeff_one, AlgHom.commutes]

private theorem blockOffset_conjugate (D : ScalarDiagonalModel P S₀)
    (R : TestAlgebra k) (t : GroupPoints S₀.group R) (g : GroupPoints H.val R)
    (i j : Fin n) (l : I) :
    blockOffset v i j l
        (P.point R (onGroupPoints S₀.inclusion R t * g * (onGroupPoints S₀.inclusion R t)⁻¹)).val =
      (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R) *
        blockOffset v i j l (P.point R g).val := by
  unfold blockOffset
  have h := blockCoeff_conjugate v D R t g i j l
  change blockCoeff v i j l
      (P.point R (onGroupPoints S₀.inclusion R t * g * (onGroupPoints S₀.inclusion R t)⁻¹)).val =
    _ at h
  rw [h]
  by_cases h : i = j
  · subst j
    simp
  · simp [blockCoeff_one, Matrix.one_apply_ne h]

private theorem blockOffset_transvection {R : Type u} [CommRing R] [Algebra k R]
    (i j p q : Fin n) (l : I) (x : R ⊗[k] D₀) :
    blockOffset v p q l (1 + blockEntry i j x) =
      if p = i ∧ q = j then (v.baseChange R).repr x l else 0 := by
  rw [blockOffset, blockCoeff_transvection]
  abel

private theorem blockOffset_one {R : Type u} [CommRing R] [Algebra k R]
    (p q : Fin n) (l : I) :
    blockOffset v p q l (1 : R ⊗[k] Matrix (Fin n) (Fin n) D₀) = 0 := sub_self _

private theorem blockOffset_ext {R : Type u} [CommRing R] [Algebra k R]
    {x y : R ⊗[k] Matrix (Fin n) (Fin n) D₀}
    (h : ∀ i j l, blockOffset v i j l x = blockOffset v i j l y) : x = y :=
  blockCoeff_ext v fun i j l => sub_left_inj.mp (h i j l)

private theorem laurent_monomial_coeff {R : Type*} [CommRing R] (x : R) (a b : ℤ) :
    (LaurentPolynomial.T a * LaurentPolynomial.C x).coeff b = if b = a then x else 0 := by
  rw [LaurentPolynomial.T_mul, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  simp only [eq_comm (a := a) (b := b)]

private theorem kernel_centralizer_offBlock (D : ScalarDiagonalModel P S₀)
    {i j : Fin n} (hij : i ≠ j) (a : relativeRoots S₀) (ha : IsBlockCharacter D i j a.val)
    {R : TestAlgebra k} (g : GroupPoints H.val R)
    (hg : CentralizesCharacterKernel S₀ a.val g)
    {p q : Fin n} (hpq : p ≠ q) (hf : ¬ (p = i ∧ q = j)) (hr : ¬ (p = j ∧ q = i))
    (l : I) : blockOffset v p q l (P.point R g).val = 0 := by
  obtain ⟨w, hzero, hsep⟩ := kernelExponent_separates hij hpq hf hr
  let T := laurentAlgebra R
  let t := (D.tuple T).symm (powerTuple w (laurentParameter R))
  have ht : D.tuple T t = powerTuple w (laurentParameter R) := MulEquiv.apply_symm_apply _ _
  have hv : characterValue a.val T t = 1 := by
    rw [ha, ht, powerTuple_div, hzero, zpow_zero, Units.val_one]
  have hc : Commute (show GroupPoints H.val T from mapPoints (laurentConstants R) g)
      (onGroupPoints S₀.inclusion T t) := hg T (laurentConstants R) t hv
  have he := congrArg (fun z : GroupPoints H.val T => blockOffset v p q l (P.point T z).val)
    (mul_inv_eq_iff_eq_mul.mpr hc.symm.eq)
  dsimp only at he
  rw [blockOffset_conjugate v D, blockOffset_pointMap v, ht, powerTuple_div, laurentParameter_zpow] at he
  change LaurentPolynomial.T (blockCharacter p q w) *
    LaurentPolynomial.C (blockOffset v p q l (P.point R g).val) =
    LaurentPolynomial.C (blockOffset v p q l (P.point R g).val) at he
  have e := congrArg (fun z : LaurentPolynomial R => z.coeff (blockCharacter p q w)) he
  change (LaurentPolynomial.T (blockCharacter p q w) *
    LaurentPolynomial.C (blockOffset v p q l (P.point R g).val)).coeff (blockCharacter p q w) =
    (LaurentPolynomial.C (blockOffset v p q l (P.point R g).val)).coeff (blockCharacter p q w) at e
  rw [laurent_monomial_coeff, if_pos rfl, LaurentPolynomial.C_apply, if_neg hsep] at e
  exact e

private theorem orbit_blockOffset (D : ScalarDiagonalModel P S₀) (c : Cocharacter S₀.group)
    {R : TestAlgebra k} (g : GroupPoints H.val R) (p q : Fin n) (l : I) :
    blockOffset v p q l (P.point (laurentAlgebra R) (orbit (c ≫ S₀.inclusion) g)).val =
      (((D.tuple (laurentAlgebra R)
        (cocharacterPoint c (laurentAlgebra R) (laurentParameter R))).val p /
        (D.tuple (laurentAlgebra R)
        (cocharacterPoint c (laurentAlgebra R) (laurentParameter R))).val q :
        (laurentAlgebra R)ˣ) : LaurentPolynomial R) *
        LaurentPolynomial.C (blockOffset v p q l (P.point R g).val) := by
  change blockOffset v p q l (P.point (laurentAlgebra R)
    (onGroupPoints S₀.inclusion _ (cocharacterPoint c _ (laurentParameter R)) *
      (show GroupPoints H.val (laurentAlgebra R) from mapPoints (laurentConstants R) g) *
      (onGroupPoints S₀.inclusion _ (cocharacterPoint c _ (laurentParameter R)))⁻¹)).val = _
  rw [blockOffset_conjugate v D, blockOffset_pointMap v]
  rfl

private theorem cocharacter_ratio (D : ScalarDiagonalModel P S₀) {i j : Fin n}
    {a : Character S₀.group} (ha : IsBlockCharacter D i j a) (c : Cocharacter S₀.group)
    (R : TestAlgebra k) :
    let t := cocharacterPoint c (laurentAlgebra R) (laurentParameter R)
    (D.tuple (laurentAlgebra R) t).val i / (D.tuple (laurentAlgebra R) t).val j =
      laurentParameter R ^ pairing S₀.group a c := by
  apply Units.ext
  exact (ha _ _).symm.trans ((characterPairingComposition S₀.group a c).2 _ _)

private theorem negative_monomial_of_polynomial {R : Type*} [CommRing R] {n : ℤ}
    (hn : n < 0) (p : Polynomial R) (x : R)
    (h : p.toLaurent = LaurentPolynomial.T n * LaurentPolynomial.C x) : x = 0 := by
  have hp := congrArg LaurentPolynomial.trunc h
  rw [LaurentPolynomial.T_mul, Polynomial.trunc_toLaurent, LaurentPolynomial.trunc_C_mul_T,
    if_neg (not_le.mpr hn)] at hp
  have e := congrArg (fun z : LaurentPolynomial R => z.coeff n) h
  change p.toLaurent.coeff n = (LaurentPolynomial.T n * LaurentPolynomial.C x).coeff n at e
  rw [hp, map_zero, laurent_monomial_coeff, if_pos rfl] at e
  exact e.symm

private theorem contracted_block_support (D : ScalarDiagonalModel P S₀)
    {i j : Fin n} (hij : i ≠ j) (a : relativeRoots S₀) (ha : IsBlockCharacter D i j a.val)
    (c : Cocharacter S₀.group) (hc : 0 < pairing S₀.group a.val c)
    {R : TestAlgebra k} (g : GroupPoints H.val R)
    (hg : CentralizesCharacterKernel S₀ a.val g)
    (hl : HasLimit (c ≫ S₀.inclusion) g 1)
    {p q : Fin n} (hf : ¬ (p = i ∧ q = j)) (l : I) :
    blockOffset v p q l (P.point R g).val = 0 := by
  obtain ⟨f, he, hz⟩ := hl
  let z := blockOffset v p q l (P.point (polynomialAlgebra R) f).val
  have hp : Polynomial.toLaurent z =
      blockOffset v p q l (P.point (laurentAlgebra R) (orbit (c ≫ S₀.inclusion) g)).val := by
    rw [← he, blockOffset_pointMap v]
    rfl
  have hzero : (polynomialEvaluate R 0).hom z = 0 := by
    rw [← blockOffset_pointMap v, hz, P.one, blockOffset_one]
  by_cases hpq : p = q
  · subst q
    rw [orbit_blockOffset v D] at hp
    have hp' : Polynomial.toLaurent z =
        LaurentPolynomial.C (blockOffset v p p l (P.point R g).val) := by simpa using hp
    have hz' : z = Polynomial.C (blockOffset v p p l (P.point R g).val) :=
      Polynomial.toLaurent_injective (hp'.trans (Polynomial.toLaurent_C _).symm)
    rw [hz'] at hzero
    change Polynomial.aevalTower (AlgHom.id k R) 0
      (Polynomial.C (blockOffset v p p l (P.point R g).val)) = 0 at hzero
    rw [Polynomial.aevalTower_C] at hzero
    exact hzero
  · by_cases hr : p = j ∧ q = i
    · obtain ⟨rfl, rfl⟩ := hr
      rw [orbit_blockOffset v D] at hp
      rw [← inv_div, cocharacter_ratio D ha, ← zpow_neg, laurentParameter_zpow] at hp
      exact negative_monomial_of_polynomial (neg_neg_of_pos hc) _ _ hp
    · exact kernel_centralizer_offBlock v D hij a ha g hg hpq hf hr l

private theorem baseChange_parameter_coeff {R T : Type u} [CommRing R] [Algebra k R]
    [CommRing T] [Algebra k T] (f : R →ₐ[k] T) (x : R ⊗[k] D₀) (l : I) :
    (v.baseChange T).repr (changeCoefficients f x) l = f ((v.baseChange R).repr x l) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Module.Basis.baseChange_repr_tmul, Algebra.smul_def, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, Finsupp.add_apply, hx, hy]

private theorem transvection_map (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    {R T : TestAlgebra k} (f : R ⟶ T) (i j : Fin n) (hij : i ≠ j) (x : R ⊗[k] D₀) :
    (P.point T (mapPoints f (transvectionPoint (P := P) hB R i j hij x))).val =
      1 + blockEntry i j (changeCoefficients f.hom x) := by
  rw [P.natural, transvectionPoint_val]
  change changeCoefficients f.hom (1 + blockEntry i j x) = _
  rw [map_add, map_one, changeCoefficients_block]

open private polynomialConstants from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem block_transvection_limit_path (v : Module.Basis I k D₀) (D : ScalarDiagonalModel P S₀)
    (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    {i j : Fin n} (hij : i ≠ j) (a : relativeRoots S₀) (ha : IsBlockCharacter D i j a.val)
    (c : Cocharacter S₀.group) (hc : 0 < pairing S₀.group a.val c)
    (R : TestAlgebra k) (x : R ⊗[k] D₀) :
    ∃ y : polynomialAlgebra R ⊗[k] D₀,
      let f := transvectionPoint (P := P) hB (polynomialAlgebra R) i j hij y
      mapPoints (polynomialToLaurent R) f =
        orbit (c ≫ S₀.inclusion) (transvectionPoint (P := P) hB R i j hij x) ∧
      mapPoints (polynomialEvaluate R 0) f = 1 := by
  classical
  let N := (pairing S₀.group a.val c).toNat
  have hN : (N : ℤ) = pairing S₀.group a.val c := Int.toNat_of_nonneg hc.le
  have hNp : N ≠ 0 := by omega
  let y : (polynomialAlgebra R) ⊗[k] D₀ :=
    (Polynomial.X ^ N : Polynomial R) • changeCoefficients (polynomialConstants R).hom x
  let f := transvectionPoint (P := P) hB (polynomialAlgebra R) i j hij y
  let g := transvectionPoint (P := P) hB R i j hij x
  have hy (l : I) : (v.baseChange (Polynomial R)).repr y l =
      Polynomial.X ^ N * Polynomial.C ((v.baseChange R).repr x l) := by
    unfold y
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, baseChange_parameter_coeff v]
    rfl
  refine ⟨y, ?_, ?_⟩
  · apply normPoint_val_injective P
    change (P.point (laurentAlgebra R) (mapPoints (polynomialToLaurent R) f)).val =
      (P.point (laurentAlgebra R) (orbit (c ≫ S₀.inclusion) g)).val
    apply blockOffset_ext v
    intro p q l
    rw [blockOffset_pointMap v, transvectionPoint_val, orbit_blockOffset v D,
      transvectionPoint_val, blockOffset_transvection, blockOffset_transvection]
    by_cases hp : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := hp
      simp only [true_and, ite_true]
      rw [cocharacter_ratio D ha, laurentParameter_zpow, hy]
      change (Polynomial.toLaurent ((Polynomial.X : Polynomial R) ^ N *
        Polynomial.C ((v.baseChange R).repr x l))) = _
      rw [map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, hN]
    · simp [hp]
  · apply normPoint_val_injective P
    change (P.point R (mapPoints (polynomialEvaluate R 0) f)).val = (P.point R 1).val
    rw [P.one]
    apply blockOffset_ext v
    intro p q l
    rw [blockOffset_pointMap v, transvectionPoint_val, blockOffset_transvection, blockOffset_one]
    by_cases hp : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := hp
      simp only [true_and, ite_true]
      rw [hy, map_mul, map_pow]
      change (Polynomial.aevalTower (AlgHom.id k R) 0 Polynomial.X) ^ N * _ = _
      rw [Polynomial.aevalTower_X, zero_pow hNp, zero_mul]
    · simp [hp]

private theorem transvection_centralizes (v : Module.Basis I k D₀) (D : ScalarDiagonalModel P S₀)
    (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    {i j : Fin n} (hij : i ≠ j) (a : relativeRoots S₀) (ha : IsBlockCharacter D i j a.val)
    (R : TestAlgebra k) (x : R ⊗[k] D₀) :
    CentralizesCharacterKernel S₀ a.val (transvectionPoint (P := P) hB R i j hij x) := by
  classical
  intro T f s hd
  let g : GroupPoints H.val T := mapPoints f (transvectionPoint (P := P) hB R i j hij x)
  change Commute g (onGroupPoints S₀.inclusion T s)
  apply Commute.symm
  apply mul_inv_eq_iff_eq_mul.mp
  apply normPoint_val_injective P
  change (P.point T (onGroupPoints S₀.inclusion T s * g *
      (onGroupPoints S₀.inclusion T s)⁻¹)).val = (P.point T g).val
  apply blockOffset_ext v
  intro p q l
  rw [blockOffset_conjugate v D]
  have hg : (P.point T g).val = 1 + blockEntry i j (changeCoefficients f.hom x) :=
    transvection_map hB f i j hij x
  rw [hg, blockOffset_transvection]
  by_cases hp : p = i ∧ q = j
  · obtain ⟨rfl, rfl⟩ := hp
    rw [ha] at hd
    rw [hd, one_mul]
  · simp [hp]

private theorem point_factors_component {G : GroupScheme k} (C : ClosedSubgroup G)
    (hC : LinearAlgebraicGroups.Specs.GeometricBorelConjugacy.IsReducedIdentityComponent C)
    (ho : IsOpenImmersion C.inclusion.hom.hom.left)
    (R : TestAlgebra k) (f : GroupPoints G R)
    [IsDomain R]
    (aug : R ⟶ base k) (haug : mapPoints aug f = (1 : GroupPoints G (base k))) :
    ∃ fb : GroupPoints C.group R, fb ≫ C.inclusion.hom.hom = f := by
  let f' : Points G.X R := f
  letI := ho
  have hs : Set.range f'.left ⊆ Set.range C.inclusion.hom.hom.left := by
    rw [hC.2, ← Set.image_univ]
    haveI : ConnectedSpace ((testSpec k).obj (op R)).left :=
      inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
    apply (isConnected_univ.image _ f'.left.continuous.continuousOn).subset_connectedComponent
    rw [Set.image_univ]
    refine ⟨((testSpec k).map aug.op).left (IsLocalRing.closedPoint k), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
    change (mapPoints aug f : Points G.X (base k)).left _ = _
    rw [haug]
    rfl
  let q := IsOpenImmersion.lift C.inclusion.hom.hom.left f'.left hs
  have hq : q ≫ C.inclusion.hom.hom.left = f'.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk q ?_, Over.OverMorphism.ext hq⟩
  calc
    q ≫ C.group.X.hom = q ≫ C.inclusion.hom.hom.left ≫ G.X.hom :=
      congrArg (q ≫ ·) (Over.w C.inclusion.hom.hom).symm
    _ = ((testSpec k).obj (op R)).hom := by rw [← Category.assoc, hq, Over.w f']

private theorem transvection_in_component (v : Module.Basis I k D₀) (D : ScalarDiagonalModel P S₀)
    (hB : _root_.Specs.RM03.CSA.isCentralSimple k D₀)
    {i j : Fin n} (hij : i ≠ j) (a : relativeRoots S₀) (ha : IsBlockCharacter D i j a.val)
    (C : RootCentralizer S₀ a) (R : TestAlgebra k) (x : R ⊗[k] D₀) :
    ∃ q : GroupPoints C.component.group R,
      q ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom =
        transvectionPoint (P := P) hB R i j hij x := by
  classical
  letI : FiniteDimensional k D₀ := hB.2.2
  letI : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let A := CommAlgCat.of k (MvPolynomial I k)
  let y : A ⊗[k] D₀ := ∑ l, MvPolynomial.X l ⊗ₜ[k] v l
  let f := transvectionPoint (P := P) hB A i j hij y
  obtain ⟨fc, hfc⟩ := (C.represents _ _).mp ((centralizesCharacterKernel_iff a C f).mp
    (transvection_centralizes v D hB hij a ha A y))
  let aug : A ⟶ base k := CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : I => (0 : k)))
  have hf0 : mapPoints aug f = (1 : GroupPoints H.val (base k)) := by
    apply normPoint_val_injective P
    change (P.point (base k) (mapPoints aug f)).val = (P.point (base k) 1).val
    rw [transvection_map, P.one]
    have hy : changeCoefficients aug.hom y = 0 := by
      dsimp only [y]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro l _
      rw [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change MvPolynomial.aeval (fun _ : I => (0 : k)) (MvPolynomial.X l) ⊗ₜ[k] v l = 0
      rw [MvPolynomial.aeval_X, TensorProduct.zero_tmul]
    rw [hy, map_zero, add_zero]
  letI : Mono C.centralizer.inclusion.hom.hom :=
    mono_over _ C.centralizer.isClosedImmersion
  have hfc0 : mapPoints aug fc = (1 : GroupPoints C.centralizer.group (base k)) := by
    apply (cancel_mono C.centralizer.inclusion.hom.hom).mp
    change ((testSpec k).map aug.op ≫ fc) ≫ C.centralizer.inclusion.hom.hom =
      onGroupPoints C.centralizer.inclusion (base k) 1
    rw [Category.assoc, hfc, map_one]
    exact hf0
  obtain ⟨q, hq⟩ := point_factors_component C.component C.isIdentityComponent C.isOpen A fc aug hfc0
  let e : A ⟶ R :=
    CommAlgCat.ofHom (MvPolynomial.aeval (fun l => (v.baseChange R).repr x l))
  have he : changeCoefficients e.hom y = x := by
    dsimp only [y]
    rw [map_sum]
    conv_rhs => rw [← (v.baseChange R).sum_repr x]
    apply Finset.sum_congr rfl
    intro l _
    rw [changeCoefficients, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change MvPolynomial.aeval (fun r => (v.baseChange R).repr x r) (MvPolynomial.X l) ⊗ₜ[k] v l =
      ((v.baseChange R).repr x l) • (v.baseChange R) l
    rw [MvPolynomial.aeval_X, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨mapPoints e q, ?_⟩
  change ((testSpec k).map e.op ≫ q) ≫ C.component.inclusion.hom.hom ≫
    C.centralizer.inclusion.hom.hom = _
  rw [Category.assoc, ← Category.assoc q, hq, hfc]
  apply normPoint_val_injective P
  change (P.point R (mapPoints e f)).val =
    (P.point R (transvectionPoint (P := P) hB R i j hij x)).val
  rw [transvection_map, he, transvectionPoint_val]

theorem fullKernelContraction : FullKernelContraction.{u} := by
  classical
  intro k B _ _ _ n hB hA J _ b H P S₀ _ D i j hij a ha c hc R g
  let v := Module.Free.chooseBasis k B
  constructor
  · rintro ⟨he, hlimit⟩
    let x := blockProjection i j (P.point R g).val
    have hx : (P.point R g).val = 1 + blockEntry i j x := by
      apply blockOffset_ext v
      intro p q l
      rw [blockOffset_transvection]
      by_cases hp : p = i ∧ q = j
      · obtain ⟨rfl, rfl⟩ := hp
        simp only [true_and, ite_true]
        unfold blockOffset
        rw [blockCoeff_one, Matrix.one_apply_ne hij, map_zero, Finsupp.zero_apply, map_zero, sub_zero]
        rfl
      · rw [if_neg hp]
        exact contracted_block_support v D hij a ha c hc g he hlimit hp l
    exact ⟨x, hx, fun y hy => (blockTransvections hB hA b i j hij).1 (hy.symm.trans hx)⟩
  · rintro ⟨x, hx, _⟩
    have hg : g = transvectionPoint (P := P) hB R i j hij x :=
      normPoint_val_injective P R (hx.trans (transvectionPoint_val hB R i j hij x).symm)
    subst g
    obtain ⟨y, hLaurent, hZero⟩ := block_transvection_limit_path v D hB hij a ha c hc R x
    exact ⟨transvection_centralizes v D hB hij a ha R x, _, hLaurent, hZero⟩

theorem relativeContraction : RelativeContraction.{u} := by
  intro k B _ _ _ n hB hA J _ b H P S₀ hS D i j hij a ha C c hc R g
  have full := fullKernelContraction hB hA b H P S₀ hS D i j hij a ha c hc R g
  constructor
  · rintro ⟨⟨q, hq⟩, hlimit⟩
    have he : Centralizes (C.kernel.subgroup.inclusion ≫ S₀.inclusion) g :=
      (C.represents _ _).mpr ⟨q ≫ C.component.inclusion.hom.hom, by rw [Category.assoc, hq]⟩
    exact full.mp ⟨(centralizesCharacterKernel_iff a C g).mpr he, hlimit⟩
  · intro h
    have hlimit := (full.mpr h).2
    obtain ⟨x, hx, _⟩ := h
    have hg : g = transvectionPoint (P := P) hB R i j hij x :=
      normPoint_val_injective P R (hx.trans (transvectionPoint_val hB R i j hij x).symm)
    rw [hg]
    exact ⟨transvection_in_component (Module.Free.chooseBasis k B) D hB hij a ha C R x,
      hg ▸ hlimit⟩

private theorem onGroupPoints_mapPoints {G L : GroupScheme k} (f : G ⟶ L)
    {R T : TestAlgebra k} (e : R ⟶ T) (p : GroupPoints G R) :
    onGroupPoints f T (mapPoints e p) = mapPoints e (onGroupPoints f R p) :=
  Category.assoc ((testSpec k).map e.op) p f.hom.hom

private theorem onGroupPoints_orbit {G L : GroupScheme k} (f : G ⟶ L) (c : Cocharacter G)
    {R : TestAlgebra k} (p : GroupPoints G R) :
    onGroupPoints f (laurentAlgebra R) (orbit c p) = orbit (c ≫ f) (onGroupPoints f R p) := by
  have ht : onGroupPoints f (laurentAlgebra R)
      (cocharacterPoint c (laurentAlgebra R) (laurentParameter R)) =
      cocharacterPoint (c ≫ f) (laurentAlgebra R) (laurentParameter R) :=
    Category.assoc (unitPoint (laurentAlgebra R) (laurentParameter R)) c.hom.hom f.hom.hom
  simp only [orbit, map_mul, map_inv, ht, onGroupPoints_mapPoints]

theorem componentContraction : ComponentContraction.{u} := by
  classical
  intro k B _ _ _ n hB hA J _ b H P S₀ hS D i j hij a ha C c hc R g
  let v := Module.Free.chooseBasis k B
  let jC := C.component.inclusion ≫ C.centralizer.inclusion
  let cC := c ≫ C.torusIso.hom ≫ C.torus.inclusion
  have hcomp : cC ≫ jC = c ≫ S₀.inclusion := by
    simpa only [cC, jC, Category.assoc] using
      congrArg (c ≫ ·) C.torusInclusion
  have injective (T : TestAlgebra k) : Function.Injective (onGroupPoints jC T) := by
    letI : Mono C.component.inclusion.hom.hom := mono_over _ C.component.isClosedImmersion
    letI : Mono C.centralizer.inclusion.hom.hom := mono_over _ C.centralizer.isClosedImmersion
    intro p q h
    change p ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom =
      q ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom at h
    rw [← Category.assoc, ← Category.assoc, cancel_mono, cancel_mono] at h
    exact h
  constructor
  · rintro ⟨q, hq, s, hs, hs₀⟩
    apply (relativeContraction hB hA b H P S₀ hS D i j hij a ha C c hc R g).mp
    refine ⟨⟨q, hq⟩, onGroupPoints jC (polynomialAlgebra R) s, ?_, ?_⟩
    · change onGroupPoints jC R q = g at hq
      rw [← onGroupPoints_mapPoints, hs, onGroupPoints_orbit, hcomp, hq]
    · rw [← onGroupPoints_mapPoints, hs₀, map_one]
  · rintro ⟨x, hx, _⟩
    have hg : g = transvectionPoint (P := P) hB R i j hij x :=
      normPoint_val_injective P R (hx.trans (transvectionPoint_val hB R i j hij x).symm)
    subst g
    obtain ⟨q, hq⟩ := transvection_in_component v D hB hij a ha C R x
    obtain ⟨y, hLaurent, hZero⟩ := block_transvection_limit_path v D hB hij a ha c hc R x
    obtain ⟨s, hs⟩ := transvection_in_component v D hB hij a ha C (polynomialAlgebra R) y
    refine ⟨q, hq, s, injective _ ?_, injective _ ?_⟩
    · change onGroupPoints jC R q = _ at hq
      change onGroupPoints jC (polynomialAlgebra R) s = _ at hs
      rw [onGroupPoints_mapPoints, hs, onGroupPoints_orbit, hcomp, hq]
      exact hLaurent
    · change onGroupPoints jC (polynomialAlgebra R) s = _ at hs
      rw [onGroupPoints_mapPoints, hs, map_one]
      exact hZero

end SchemePoints

open AlgebraicGeometry CategoryTheory WithConv
open LinearAlgebraicGroups.Specs.AdjointRepresentation (GroupPoints)

theorem f05NormOnePoints : F05NormOnePoints.{u} := by
  intro k B _ _ _ n hA J _ b
  obtain ⟨h, F, point, hone, hmul, hnatural, e, he, c, hc⟩ :=
    LinearAlgebraicGroups.Descent.InnerTypeA.normOneRepresentability hA b
  refine ⟨h, ⟨fun R => (c.app R).groupIsoToMulEquiv.toEquiv.trans (point R), ?_, ?_, ?_⟩, ?_⟩
  · intro R
    change (point R (c.hom.app R 1)).val = 1
    rw [(c.hom.app R).hom.map_one, hone]
  · intro R x y
    change (point R (c.hom.app R (x * y))).val = _
    rw [(c.hom.app R).hom.map_mul, hmul]
    rfl
  · intro R T f x
    have natural := congrArg (fun j : _ ⟶ F.obj T => j x) (c.hom.naturality f)
    exact (congrArg (fun y => (point T y).val) natural).trans (hnatural f (c.hom.app R x))
  · intro R f g hg l
    have hpoint : e.hom.app R (toConv f) = g := Over.OverMorphism.ext ((he R f).trans hg.symm)
    change (b.baseChange R).repr (point R (c.hom.app R g)).val l = _
    rw [← hpoint]
    exact hc R f l

open private baseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.InnerTypeA

theorem blockSplitPoints : BlockSplitPoints.{u} := by
  intro k B K _ _ _ _ _ m d e hA J _ b H P
  let A := restrictTestAlgebra k K
  let κ := ULift.{u} (Fin m × Fin d)
  let E (R : TestAlgebra K) :
      A.obj R ⊗[k] Matrix (Fin m) (Fin m) B ≃ₐ[R] Matrix κ κ R :=
    (flattenSplitting (S := A.obj R) e).trans (Matrix.reindexAlgEquiv R R Equiv.ulift.symm)
  have hmap {R S : TestAlgebra K} (f : R ⟶ S) (x : A.obj R ⊗[k] Matrix (Fin m) (Fin m) B) :
      E S (changeCoefficients (A.map f).hom x) = (E R x).map f.hom := by
    induction x using TensorProduct.inductionOn with
    | tmul r M =>
      dsimp only [E]
      rw [show changeCoefficients (A.map f).hom (r ⊗ₜ[k] M) = (A.map f).hom r ⊗ₜ[k] M from rfl]
      simp only [AlgEquiv.trans_apply]
      rw [flattenSplitting_tmul (S := A.obj S), flattenSplitting_tmul (S := A.obj R)]
      ext i j
      change f.hom r * algebraMap K S (flattenSplitting (S := K) e (1 ⊗ₜ[k] M) i.down j.down) =
        f.hom (r * algebraMap K R (flattenSplitting (S := K) e (1 ⊗ₜ[k] M) i.down j.down))
      rw [map_mul, AlgHom.commutes]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      ext i j
      exact (map_add f.hom _ _).symm
  have norm (R : TestAlgebra K) (x : A.obj R ⊗[k] Matrix (Fin m) (Fin m) B) :
      normAt hA b x = (E R x).det := by
    rw [normAt_eq_flattenDet e hA b]
    exact (Matrix.det_reindexAlgEquiv R R Equiv.ulift.symm _).symm
  let eqv (R : TestAlgebra K) : GroupPoints H.val (A.obj R) ≃ Matrix.SpecialLinearGroup κ R :=
    (P.point (A.obj R)).trans ((E R).toEquiv.subtypeEquiv (fun x => by
      change normAt hA b x = 1 ↔ (E R x).det = 1
      rw [norm]))
  let equiv (R : TestAlgebra K) : GroupPoints H.val (A.obj R) ≃* Matrix.SpecialLinearGroup κ R :=
    { eqv R with
      map_mul' := fun x y => Subtype.ext (by
        change E R (P.point (A.obj R) (x * y)).val =
          E R (P.point (A.obj R) x).val * E R (P.point (A.obj R) y).val
        rw [P.mul, map_mul]) }
  let M : A ⋙ (groupPointsFunctor k).obj H.val ≅
      LinearAlgebraicGroups.Specs.StandardGroups.specialLinearPoints K κ :=
    NatIso.ofComponents (fun R => (equiv R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      apply Subtype.ext
      change E S (P.point (A.obj S) (mapPoints (A.map f) x)).val =
        (E R (P.point (A.obj R) x).val).map f.hom
      rw [P.natural]
      exact hmap f _)
  refine ⟨baseChangePointIso (K := K) H.val ≪≫ M, ?_⟩
  intro S D R t
  let s : GroupPoints S.group (A.obj R) := baseChangePoint k K S.group.X R t
  change E R (P.point (A.obj R) (baseChangePoint k K H.val.X R
      (t ≫ ((groupBaseChange k K).map S.inclusion).hom.hom))).val =
    Matrix.diagonal (fun p : κ => ((D.tuple (A.obj R) s).val p.down.1 : R))
  calc
    _ = E R (P.point (A.obj R) (s ≫ S.inclusion.hom.hom)).val :=
      congrArg (fun p : GroupPoints H.val (A.obj R) => E R (P.point (A.obj R) p).val)
        (baseChangePointsSchemeNaturality k K S.inclusion.hom.hom R t)
    _ = E R (scalarDiagonal fun i => ((D.tuple (A.obj R) s).val i : A.obj R)) :=
      congrArg (E R) (D.diagonal (A.obj R) s)
    _ = _ := by
      simp only [E, AlgEquiv.trans_apply, flattenSplitting_diagonal]
      ext p q
      change Matrix.diagonal (fun p : Fin m × Fin d => ((D.tuple (A.obj R) s).val p.1 : R))
        p.down q.down = Matrix.diagonal _ p q
      have he : p.down = q.down ↔ p = q := ULift.down_injective.eq_iff
      simp [Matrix.diagonal, he]

end
end LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
