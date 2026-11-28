import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.MatrixSpecialization
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.TriangularPBW
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Hopf
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PBWSpecialization
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-! Level-one specialization of the type-A₂ quantum enveloping algebra. -/

noncomputable section

namespace LieNotes.Quantum.MatrixSpecialization

open Specs.LieNotes.Quantum.MatrixSpecialization
open scoped Specs.LieNotes.Quantum.MatrixSpecialization TensorProduct
open Specs.LieNotes.Quantum.Presentation
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)
open Specs.LieNotes.Quantum.Coproduct (H)
open Specs.LieNotes.Quantum.TriangularPBW (zMinus zPlus)
open _root_.Shared.Lie.PBW (OrderedWord orderedMonomial)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

set_option maxHeartbeats 1600000

section LevelOne

variable {k : Type u} [Field k] [CharZero k]

local notation "A₁" => Truncations.A k 1
local notation "C₁" => truncated k 1
local notation "E₁" => E C₁
local notation "F₁" => F C₁
local notation "H₁" => H k 1

omit [CharZero k] in
private theorem truncate_one (p : PowerSeries k) :
    Truncations.truncate 1 p = algebraMap k A₁ (PowerSeries.constantCoeff p) := by
  simp [Truncations.truncate_eq_sum]

omit [CharZero k] in
private theorem cartanTruncate_one (p : PowerSeries (PolynomialCartan k)) :
    Truncations.cartanTruncate Root 1 p =
      MvPolynomial.map (algebraMap k A₁) (PowerSeries.constantCoeff p) := by
  simp [Truncations.cartanTruncate_eq_sum]

private theorem exponential_constant {R : Type u} [CommRing R] [Algebra ℚ R] (x : R) :
    PowerSeries.constantCoeff (↑(exponentialUnit x) : PowerSeries R) = 1 := by
  simp [Presentation.exponentialUnit_val, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    Truncations.coeff_expH]

private theorem quantumParameter_one : (C₁).q = 1 := by
  apply Units.ext
  change Truncations.truncate 1 (↑(exponentialUnit (1 : k)) : PowerSeries k) = 1
  rw [truncate_one, exponential_constant, map_one]

private theorem cartanUnit_one (i : Root) : (C₁).K i = 1 := by
  let x : PolynomialCartan k := MvPolynomial.X i
  let p : PowerSeries (PolynomialCartan k) := ↑(exponentialUnit x)
  have hp : Truncations.cartanTruncate (R := k) Root 1 p = (1 : TruncatedCartan k 1) := by
    rw [cartanTruncate_one, show PowerSeries.constantCoeff p = 1 from exponential_constant x,
      map_one]
  exact Units.ext hp

private theorem dividedCartan_one (i : Root) : (C₁).D i = MvPolynomial.X i := by
  change Truncations.cartanTruncate Root 1 (sinhRatio (MvPolynomial.X i : PolynomialCartan k)) = _
  rw [cartanTruncate_one, Presentation.sinhRatio_constantCoeff, MvPolynomial.map_X]

private theorem shiftedCartan (l i : Root) :
    cartan C₁ (((C₁).tau i).symm (MvPolynomial.X l)) =
      H₁ l - (cartanMatrix l i : LevelOne k) := by
  change cartan C₁ ((translation _).symm (MvPolynomial.X l)) = _
  rw [translation_symm_X, map_sub]
  congr 1
  rw [← MvPolynomial.algebraMap_eq]
  simp

private theorem serre_one {A B : Type*} [CommRing A] [Ring B] [Algebra A B] (x y : B) :
    serrePolynomial (1 : Aˣ) x y = ⁅x, ⁅x, y⁆⁆ := by
  simp only [serrePolynomial, inv_one, Units.val_one, add_smul, one_smul,
    LieRing.of_associative_ring_bracket]
  noncomm_ring

private theorem ordinaryLevelOne : OrdinaryRelations (k := k) E₁ F₁ H₁ := by
  constructor
  · intro l i
    apply sub_eq_zero.mpr
    exact (Commute.all (MvPolynomial.X l : TruncatedCartan k 1) (MvPolynomial.X i)).map (cartan (truncated k 1))
  · intro l i
    have h := (relations (truncated k 1)).eCartan i (MvPolynomial.X l)
    change E₁ i * H₁ l = _ at h
    rw [shiftedCartan, sub_mul] at h
    change H₁ l * E₁ i - E₁ i * H₁ l = _
    rw [h, sub_sub_cancel, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  · intro l i
    have h := (relations (truncated k 1)).cartanF (MvPolynomial.X l) i
    change H₁ l * F₁ i = _ at h
    rw [shiftedCartan, mul_sub] at h
    change H₁ l * F₁ i - F₁ i * H₁ l = _
    rw [h, sub_sub_cancel_left, neg_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul, Int.cast_comm]
  · intro i j
    change E₁ i * F₁ j - F₁ j * E₁ i = _
    rw [(relations (truncated k 1)).comm]
    by_cases h : i = j <;> simp [mixed, h, dividedCartan_one, H]
  · intro i j hij
    have h := (serre_relations (truncated k 1)).pos i j hij
    rwa [quantumParameter_one, serre_one] at h
  · intro i j hij
    have h := (serre_relations (truncated k 1)).neg i j hij
    rwa [quantumParameter_one, serre_one] at h

theorem levelOne_relations : LevelOneRelations.{u} :=
  fun _ _ _ => ⟨quantumParameter_one, fun i => ⟨cartanUnit_one i, dividedCartan_one i⟩,
    ordinaryLevelOne⟩

end LevelOne

section Matrices

variable {k : Type u} [Field k]

private theorem matrixRelations_aux :
    OrdinaryRelations (k := k) (matrixE k) (matrixF k) (matrixH k) ∧
    ⁅matrixE k 0, matrixE k 1⁆ = matrixUnit k 0 2 (by decide) ∧
    ⁅matrixF k 0, matrixF k 1⁆ = -matrixUnit k 2 0 (by decide) := by
  constructor
  · constructor
    all_goals
      intro l i
      fin_cases l <;> fin_cases i
    all_goals
      try intro hij
      try exact (hij rfl).elim
    all_goals
      apply Subtype.ext
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [LieAlgebra.SpecialLinear.sl_bracket, LieRing.of_associative_ring_bracket, matrixE, matrixF, matrixH, matrixUnit,
          Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three, cartanMatrix,
          Matrix.smul_apply]
  · constructor <;> apply Subtype.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [LieAlgebra.SpecialLinear.sl_bracket, LieRing.of_associative_ring_bracket, matrixE, matrixF, matrixUnit,
        Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem matrix_relations : MatrixRelations.{u} :=
  fun _ _ _ => matrixRelations_aux

private def matrixFromCoordinates (a : Fin 8 → k) : Sl3 k := by
  let m : Matrix (Fin 3) (Fin 3) k :=
    !![a 3, a 5, a 6; a 0, a 4 - a 3, a 7; -a 1, a 2, -a 4]
  have hm : Matrix.trace m = 0 := by
    simp [m, Matrix.trace, Fin.sum_univ_three]
  exact ⟨m, hm⟩

private def matrixCoordinates : Sl3 k ≃ₗ[k] (Fin 8 → k) where
  toFun x := ![x.val 1 0, -x.val 2 0, x.val 2 1, x.val 0 0, -x.val 2 2,
    x.val 0 1, x.val 0 2, x.val 1 2]
  invFun := matrixFromCoordinates
  left_inv x := by
    have htrace : x.val 0 0 + x.val 1 1 + x.val 2 2 = 0 := by
      have hx : Matrix.trace x.val = 0 := x.property
      simpa [Matrix.trace, Fin.sum_univ_three] using hx
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixFromCoordinates]
    linear_combination -htrace
  right_inv a := by
    funext i
    fin_cases i <;> simp [matrixFromCoordinates]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.add_apply, Pi.add_apply, add_comm]
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [Matrix.smul_apply, Pi.smul_apply]

private def matrixBasis : Module.Basis (Fin 8) k (Sl3 k) :=
  (Pi.basisFun k (Fin 8)).map matrixCoordinates.symm

private theorem matrixBasis_apply (i : Fin 8) :
    matrixBasis i = matrixBasisVector k i := by
  apply matrixCoordinates.injective
  rw [matrixBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCoordinates, matrixBasisVector, matrixE, matrixF, matrixH, matrixUnit,
      Matrix.single_apply, Pi.single_apply]

end Matrices

section Words

private def indexOfCounts (a : Fin 8 → ℕ) : Index :=
  (((a 0, a 1, a 2), ![a 3, a 4]), (a 5, a 6, a 7))

private theorem counts_indexOfCounts (a : Fin 8 → ℕ) :
    exponentCounts (indexOfCounts a) = a := by
  funext j
  fin_cases j <;> rfl

private theorem indexOfCounts_counts (i : Index) :
    indexOfCounts (exponentCounts i) = i := by
  rcases i with ⟨⟨⟨a, b, c⟩, h⟩, ⟨d, e, f⟩⟩
  have hh : (![h 0, h 1] : Root → ℕ) = h := by
    funext j
    fin_cases j <;> rfl
  change (((a, b, c), ![h 0, h 1]), (d, e, f)) = _
  rw [hh]

private def repeatOrdered (a : Fin 8 → ℕ) : List (Fin 8) :=
  List.replicate (a 0) 0 ++ List.replicate (a 1) 1 ++ List.replicate (a 2) 2 ++
  List.replicate (a 3) 3 ++ List.replicate (a 4) 4 ++ List.replicate (a 5) 5 ++
  List.replicate (a 6) 6 ++ List.replicate (a 7) 7

private theorem repeatOrdered_sorted (a : Fin 8 → ℕ) :
    (repeatOrdered a).Pairwise (· ≤ ·) := by
  simp [repeatOrdered, List.pairwise_append, and_imp, or_imp, forall_and]

private theorem repeatOrdered_count (a : Fin 8 → ℕ) (j : Fin 8) :
    (repeatOrdered a).count j = a j := by
  fin_cases j <;> simp [repeatOrdered, List.count_append, List.count_replicate]

private def wordsEquiv : OrderedWord (Fin 8) ≃ Index where
  toFun w := indexOfCounts (fun j => w.val.count j)
  invFun i := ⟨repeatOrdered (exponentCounts i), repeatOrdered_sorted _⟩
  left_inv w := by
    apply Subtype.ext
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (repeatOrdered_sorted _) w.property
    apply List.perm_iff_count.mpr
    intro j
    change (repeatOrdered (exponentCounts (indexOfCounts _))).count j = _
    rw [repeatOrdered_count, counts_indexOfCounts]
  right_inv i := by
    change indexOfCounts (fun j => (repeatOrdered (exponentCounts i)).count j) = i
    simp only [repeatOrdered_count, indexOfCounts_counts]

private theorem wordsEquiv_count (w : OrderedWord (Fin 8)) (j : Fin 8) :
    exponentCounts (wordsEquiv w) j = w.val.count j := by
  change exponentCounts (indexOfCounts _) j = _
  rw [counts_indexOfCounts]

end Words

section AlgebraMap

variable {k : Type u} [Field k] [CharZero k]

local notation "A₁" => Truncations.A k 1
local notation "C₁" => truncated k 1
local notation "E₁" => E C₁
local notation "F₁" => F C₁
local notation "H₁" => H k 1
local notation "j" => UniversalEnvelopingAlgebra.ι k

omit [CharZero k] in
private theorem coefficient_back (a : A₁) :
    algebraMap k A₁ (coefficientEquiv k a) = a :=
  (coefficientEquiv k).injective (by simp)

local instance classicalOverTruncation : Algebra A₁ (Classical k) :=
  Algebra.compHom _ (coefficientEquiv k).toRingHom

local instance classicalScalarTower : IsScalarTower k A₁ (Classical k) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := A₁) (A := Classical k) fun r => by
    change algebraMap k (Classical k) r =
      algebraMap k (Classical k) (coefficientEquiv k (algebraMap k A₁ r))
    simp

private theorem polynomial_commute {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    (f g : MvPolynomial Root A →ₐ[A] B) (b : B)
    (h : ∀ i, f (MvPolynomial.X i) * b = b * g (MvPolynomial.X i))
    (p : MvPolynomial Root A) : f p * b = b * g p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, f.commutes, g.commutes]
    exact Algebra.commutes a b
  | add p q hp hq => simp [map_add, add_mul, mul_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [mul_assoc, h i, ← mul_assoc, hp, mul_assoc]


omit [CharZero k] in
private theorem ordinaryClassical :
    OrdinaryRelations (k := k) (fun i => j (matrixE k i))
      (fun i => j (matrixF k i)) (fun i => j (matrixH k i)) := by
  have h := (matrixRelations_aux (k := k)).1
  constructor
  · intro l i
    rw [← LieHom.map_lie, h.cartan, map_zero]
  · intro l i
    rw [← LieHom.map_lie, h.cartanE, map_smul]
  · intro l i
    rw [← LieHom.map_lie, h.cartanF, map_smul]
  · intro i j'
    rw [← LieHom.map_lie, h.mixed]
    split_ifs <;> simp
  · intro i j' hij
    rw [← LieHom.map_lie, ← LieHom.map_lie, h.serreE i j' hij, map_zero]
  · intro i j' hij
    rw [← LieHom.map_lie, ← LieHom.map_lie, h.serreF i j' hij, map_zero]

private def cartanSubalgebra : Subalgebra A₁ (Classical k) :=
  Algebra.adjoin A₁ (Set.range (fun i => j (matrixH k i)))

local instance cartanSubalgebra_commutative : IsMulCommutative (cartanSubalgebra (k := k)) := by
  apply Algebra.isMulCommutative_adjoin
  rintro _ ⟨i, rfl⟩ _ ⟨l, rfl⟩ _
  exact sub_eq_zero.mp ((ordinaryClassical (k := k)).cartan i l)

open scoped IsMulCommutative in
private def classicalCartan : TruncatedCartan k 1 →ₐ[A₁] Classical k :=
  (cartanSubalgebra (k := k)).val.comp (MvPolynomial.aeval (fun i =>
    ⟨j (matrixH k i), Algebra.subset_adjoin ⟨i, rfl⟩⟩))

open scoped IsMulCommutative in
omit [CharZero k] in
@[simp] private theorem classicalCartan_X (i : Root) :
    classicalCartan (k := k) (MvPolynomial.X i) = j (matrixH k i) := by
  simp only [classicalCartan, AlgHom.comp_apply, MvPolynomial.aeval_X]
  rfl

private theorem classicalCartan_shift (l i : Root) :
    classicalCartan (k := k) (((C₁).tau i).symm (MvPolynomial.X l)) =
      j (matrixH k l) - (cartanMatrix l i : Classical k) := by
  change classicalCartan ((translation _).symm (MvPolynomial.X l)) = _
  rw [translation_symm_X, map_sub, classicalCartan_X, ← MvPolynomial.algebraMap_eq]
  simp

private theorem classicalBasic :
    SatisfiesBasic C₁ classicalCartan (fun i => j (matrixE k i)) (fun i => j (matrixF k i)) := by
  let t := classicalCartan (k := k)
  let ts (i : Root) := t.comp ((C₁).tau i).symm.toAlgHom
  have h := ordinaryClassical (k := k)
  constructor
  · intro p i
    apply polynomial_commute t (ts i)
    intro l
    change classicalCartan (MvPolynomial.X l) * j (matrixF k i) =
      j (matrixF k i) * classicalCartan (((C₁).tau i).symm (MvPolynomial.X l))
    rw [classicalCartan_X, classicalCartan_shift, mul_sub]
    have hl := h.cartanF l i
    change j (matrixH k l) * j (matrixF k i) -
      j (matrixF k i) * j (matrixH k l) = _ at hl
    rw [neg_smul, Int.cast_smul_eq_zsmul, zsmul_eq_mul, Int.cast_comm] at hl
    exact (sub_eq_iff_eq_add.mp hl).trans (by abel)
  · intro i p
    symm
    apply polynomial_commute (ts i) t
    intro l
    change classicalCartan (((C₁).tau i).symm (MvPolynomial.X l)) * j (matrixE k i) =
      j (matrixE k i) * classicalCartan (MvPolynomial.X l)
    rw [classicalCartan_shift, classicalCartan_X, sub_mul]
    have hl := h.cartanE l i
    change j (matrixH k l) * j (matrixE k i) -
      j (matrixE k i) * j (matrixH k l) = _ at hl
    rw [Int.cast_smul_eq_zsmul, zsmul_eq_mul] at hl
    exact sub_eq_of_eq_add (sub_eq_iff_eq_add.mp hl |>.trans (add_comm _ _))
  · intro i j'
    change ⁅j (matrixE k i), j (matrixF k j')⁆ = _
    rw [h.mixed]
    by_cases heq : i = j' <;> simp [mixed, heq, dividedCartan_one]

private theorem classicalSerre :
    SatisfiesSerre (C₁).q (fun i => j (matrixE k i)) (fun i => j (matrixF k i)) := by
  have h := ordinaryClassical (k := k)
  constructor
  · intro i j' hij
    rw [quantumParameter_one, serre_one]
    exact h.serreE i j' hij
  · intro i j' hij
    rw [quantumParameter_one, serre_one]
    exact h.serreF i j' hij

private def toClassical : LevelOne k →ₐ[k] Classical k :=
  (liftU C₁ classicalCartan _ _ classicalBasic classicalSerre).restrictScalars k

@[simp] private theorem toClassical_E (i : Root) : toClassical (E₁ i) = j (matrixE k i) :=
  liftU_E C₁ _ _ _ classicalBasic classicalSerre i

@[simp] private theorem toClassical_F (i : Root) : toClassical (F₁ i) = j (matrixF k i) :=
  liftU_F C₁ _ _ _ classicalBasic classicalSerre i

@[simp] private theorem toClassical_H (i : Root) : toClassical (H₁ i) = j (matrixH k i) := by
  change liftU C₁ classicalCartan _ _ classicalBasic classicalSerre
    (cartan C₁ (MvPolynomial.X i)) = _
  rw [liftU_cartan, classicalCartan_X]

@[simp] private theorem toClassical_zPlus :
    toClassical (zPlus C₁) = j (matrixUnit k 0 2 (by decide)) := by
  rw [zPlus, quantumParameter_one, inv_one, Units.val_one]
  have h : (1 : A₁) • (E₁ 1 * E₁ 0) = E₁ 1 * E₁ 0 := one_smul A₁ (E₁ 1 * E₁ 0)
  rw [h]
  simp only [map_sub, map_mul, toClassical_E]
  change ⁅j (matrixE k 0), j (matrixE k 1)⁆ = _
  rw [← LieHom.map_lie, (matrixRelations_aux (k := k)).2.1]

@[simp] private theorem toClassical_zMinus :
    toClassical (zMinus C₁) = j (-matrixUnit k 2 0 (by decide)) := by
  rw [zMinus, quantumParameter_one, inv_one, Units.val_one]
  have h : (1 : A₁) • (F₁ 1 * F₁ 0) = F₁ 1 * F₁ 0 := one_smul A₁ (F₁ 1 * F₁ 0)
  rw [h]
  simp only [map_sub, map_mul, toClassical_F]
  change ⁅j (matrixF k 0), j (matrixF k 1)⁆ = _
  rw [← LieHom.map_lie, (matrixRelations_aux (k := k)).2.2]

end AlgebraMap

section PBW

variable {k : Type u} [Field k] [CharZero k]

local notation "A₁" => Truncations.A k 1
local notation "C₁" => truncated k 1

private theorem toClassical_PBW (i : Index) :
    toClassical (quantumMonomial k i) =
      orderedMonomial (matrixBasis (k := k)) (wordsEquiv.symm i) := by
  change _ = _root_.Shared.Lie.PBW.monomial _ (repeatOrdered (exponentCounts i))
  have hc (l : Root) : toClassical (cartan C₁ (MvPolynomial.X l)) =
      UniversalEnvelopingAlgebra.ι k (matrixH k l) := toClassical_H l
  simp only [quantumMonomial, Specs.LieNotes.Quantum.TriangularPBW.orderedMonomial,
    Fin.prod_univ_two, map_mul, map_pow, hc, toClassical_F, toClassical_E, toClassical_zMinus,
    toClassical_zPlus, _root_.Shared.Lie.PBW.monomial, _root_.Shared.Lie.word,
    repeatOrdered, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate,
    matrixBasis_apply]
  simp [exponentCounts, matrixBasisVector, _root_.Shared.Lie.inclusion, mul_assoc]

private theorem coefficient_smul (a : A₁) (x : LevelOne k) :
    coefficientEquiv k a • x = a • x := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k A₁ (LevelOne k), coefficient_back]
  exact (Algebra.smul_def a x).symm

private theorem existsQuantumBasis :
    ∃ Q : Module.Basis Index k (LevelOne k), ∀ i, Q i = quantumMonomial k i := by
  obtain ⟨Q, hQ⟩ := (LieNotes.Quantum.TriangularPBW.truncated k 1 (by decide)).2
  let Qk : Module.Basis Index k (LevelOne k) :=
    Q.mapCoeffs (coefficientEquiv k).toRingEquiv (coefficient_smul (k := k))
  exact ⟨Qk, fun i => (Module.Basis.mapCoeffs_apply _ _ _ _).trans (hQ i)⟩

private theorem toClassical_bijective :
    ∃ B : Module.Basis (OrderedWord (Fin 8)) k (Classical k),
      (∀ w, B w = orderedMonomial (matrixBasis (k := k)) w) ∧
      Function.Bijective (toClassical (k := k)) := by
  obtain ⟨Qk, h⟩ := existsQuantumBasis (k := k)
  obtain ⟨B, hB, _, _⟩ := _root_.LieAlgebrasAndRepresentations.PBW.orderedBasis_spec
    k (Sl3 k) (Fin 8) (matrixBasis (k := k))
  let f := Qk.equiv B wordsEquiv.symm
  have hf : toClassical.toLinearMap = f.toLinearMap := Qk.ext fun i => by
    change toClassical (Qk i) = f (Qk i)
    calc
      toClassical (Qk i) = orderedMonomial (matrixBasis (k := k)) (wordsEquiv.symm i) :=
        (congrArg (toClassical (k := k)) (h i)).trans (toClassical_PBW i)
      _ = B (wordsEquiv.symm i) := (hB _).symm
      _ = f (Qk i) := (Module.Basis.equiv_apply _ _ _ _).symm
  refine ⟨B, hB, ?_⟩
  have heq (x : LevelOne k) : toClassical x = f x := DFunLike.congr_fun hf x
  simpa only [show (⇑(toClassical (k := k))) = (⇑f) from funext heq] using f.bijective

end PBW

section ClassicalHopf

open Algebra.TensorProduct (includeLeft includeRight tmul_mul_tmul)
open private leftProduct rightProduct leftProduct_tmul rightProduct_tmul
  convolutionSubalgebra from MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Hopf

variable {k : Type u} [Field k]

local notation "U" => Classical k
local notation "j" => UniversalEnvelopingAlgebra.ι k

private def primitiveLieMap : Sl3 k →ₗ⁅k⁆ U ⊗[k] U := by
  let l := (includeLeft : U →ₐ[k] U ⊗[k] U).toLieHom.comp j
  let r := (includeRight : U →ₐ[k] U ⊗[k] U).toLieHom.comp j
  refine { l.toLinearMap + r.toLinearMap with map_lie' := ?_ }
  intro x y
  change l ⁅x, y⁆ + r ⁅x, y⁆ = ⁅l x + r x, l y + r y⁆
  have h (a b : Sl3 k) : ⁅l a, r b⁆ = 0 := by
    change ⁅j a ⊗ₜ[k] (1 : U), (1 : U) ⊗ₜ[k] j b⁆ = 0
    simp [LieRing.of_associative_ring_bracket, tmul_mul_tmul]
  have h' : ⁅r x, l y⁆ = 0 := by rw [← lie_skew, h, neg_zero]
  rw [l.map_lie, r.map_lie, add_lie, lie_add, lie_add, h, h', zero_add, add_zero]

private def classicalDelta : U →ₐ[k] U ⊗[k] U :=
  UniversalEnvelopingAlgebra.lift k primitiveLieMap

@[simp] private theorem classicalDelta_ι (x : Sl3 k) :
    classicalDelta (j x) = j x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] j x := by
  rw [classicalDelta, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private def classicalCounit : U →ₐ[k] k :=
  _root_.Shared.Lie.augmentation k (Sl3 k)

@[simp] private theorem classicalCounit_ι (x : Sl3 k) :
    classicalCounit (j x) = 0 := by
  rw [classicalCounit, _root_.Shared.Lie.augmentation, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private def oppositeAntipode : U →ₐ[k] Uᵐᵒᵖ :=
  UniversalEnvelopingAlgebra.lift k
    { -((MulOpposite.opLinearEquiv k).toLinearMap.comp (j).toLinearMap) with
      map_lie' := by
        intro x y
        apply MulOpposite.unop_injective
        change -j ⁅x, y⁆ = (⁅-MulOpposite.op (j x), -MulOpposite.op (j y)⁆).unop
        simp [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      }

private def classicalS : U →ₗ[k] U :=
  (MulOpposite.opLinearEquiv k).symm.toLinearMap.comp oppositeAntipode.toLinearMap

@[simp] private theorem classicalS_ι (x : Sl3 k) : classicalS (j x) = -j x := by
  change (oppositeAntipode (j x)).unop = _
  rw [oppositeAntipode, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private theorem classicalS_one : classicalS (1 : U) = 1 := by
  change (oppositeAntipode (1 : U)).unop = 1
  rw [map_one, MulOpposite.unop_one]

private theorem classicalS_mul (x y : U) : classicalS (x * y) = classicalS y * classicalS x := by
  change (oppositeAntipode (x * y)).unop = _
  rw [map_mul]
  rfl

private theorem enveloping_generated (P : Subalgebra k U) (h : ∀ x : Sl3 k, j x ∈ P) :
    ∀ x : U, x ∈ P := by
  let f : Sl3 k →ₗ⁅k⁆ P :=
    { (j).toLinearMap.codRestrict P.toSubmodule h with
      map_lie' := fun {x y} => Subtype.ext ((j).map_lie x y) }
  let g := UniversalEnvelopingAlgebra.lift k f
  have hg : P.val.comp g = AlgHom.id k U := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change (g (j x) : U) = j x
    rw [show g (j x) = f x from UniversalEnvelopingAlgebra.lift_ι_apply k f x]
    rfl
  intro z
  have heq : (g z : U) = z := DFunLike.congr_fun hg z
  exact heq ▸ (g z).property

private theorem classical_convolution (x : U) :
    leftProduct classicalS (classicalDelta x) = algebraMap k U (classicalCounit x) ∧
    rightProduct classicalS (classicalDelta x) = algebraMap k U (classicalCounit x) := by
  apply enveloping_generated (convolutionSubalgebra classicalDelta classicalCounit
    classicalS_one classicalS_mul) _ x
  intro y
  change leftProduct classicalS (classicalDelta (j y)) = _ ∧
    rightProduct classicalS (classicalDelta (j y)) = _
  simp only [classicalDelta_ι, map_add, leftProduct_tmul, rightProduct_tmul,
    classicalS_ι, classicalS_one, mul_one, one_mul, neg_add_cancel, add_neg_cancel,
    classicalCounit_ι, map_zero, and_self]

variable (k) in
private def standardHopf : ClassicalHopf k where
  comul := classicalDelta
  counit := classicalCounit
  antipode := classicalS
  comul_ι := classicalDelta_ι
  counit_ι := classicalCounit_ι
  antipode_ι := classicalS_ι
  coassoc := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change Algebra.TensorProduct.assoc k k k _ _ _
      (Algebra.TensorProduct.map classicalDelta (.id k _) (classicalDelta (j x))) =
        Algebra.TensorProduct.map (.id k _) classicalDelta (classicalDelta (j x))
    simp only [classicalDelta_ι, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      map_one, Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add,
      Algebra.TensorProduct.assoc_tmul, add_assoc]
  left_counit := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change Algebra.TensorProduct.map classicalCounit (.id k _) (classicalDelta (j x)) =
      (Algebra.TensorProduct.lid k _).symm (j x)
    simp only [classicalDelta_ι, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      classicalCounit_ι, map_one, TensorProduct.zero_tmul, zero_add,
      Algebra.TensorProduct.lid_symm_apply]
  right_counit := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro x
    change Algebra.TensorProduct.map (.id k _) classicalCounit (classicalDelta (j x)) =
      (Algebra.TensorProduct.rid k k _).symm (j x)
    simp only [classicalDelta_ι, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      classicalCounit_ι, map_one, TensorProduct.tmul_zero, add_zero,
      Algebra.TensorProduct.rid_symm_apply]
  left_antipode := LinearMap.ext fun x => (classical_convolution x).1
  right_antipode := LinearMap.ext fun x => (classical_convolution x).2

end ClassicalHopf

section Comparison

open Specs.LieNotes.Quantum

variable {k : Type u} [Field k] [CharZero k]

local notation "A₁" => Truncations.A k 1
local notation "C₁" => truncated k 1
local notation "E₁" => E C₁
local notation "F₁" => F C₁
local notation "H₁" => H k 1
local notation "U₁" => LevelOne k
local notation "V" => Classical k
local notation "j" => UniversalEnvelopingAlgebra.ι k

private theorem levelOne_hom_ext {B : Type*} [Ring B] [Algebra k B]
    {f g : U₁ →ₐ[k] B}
    (he : ∀ i, f (E₁ i) = g (E₁ i)) (hf : ∀ i, f (F₁ i) = g (F₁ i))
    (hh : ∀ i, f (H₁ i) = g (H₁ i)) : f = g := by
  obtain ⟨b, hb⟩ := existsQuantumBasis (k := k)
  have hplus : f (zPlus C₁) = g (zPlus C₁) := by
    have h : (1 : A₁) • (E₁ 1 * E₁ 0) = E₁ 1 * E₁ 0 := one_smul A₁ (E₁ 1 * E₁ 0)
    simp only [zPlus, quantumParameter_one, inv_one, Units.val_one, h, map_sub, map_mul, he]
  have hminus : f (zMinus C₁) = g (zMinus C₁) := by
    have h : (1 : A₁) • (F₁ 1 * F₁ 0) = F₁ 1 * F₁ 0 := one_smul A₁ (F₁ 1 * F₁ 0)
    simp only [zMinus, quantumParameter_one, inv_one, Units.val_one, h, map_sub, map_mul, hf]
  apply AlgHom.toLinearMap_injective
  apply b.ext
  intro i
  change f (b i) = g (b i)
  have hc (l : Root) : f (cartan C₁ (MvPolynomial.X l)) = g (cartan C₁ (MvPolynomial.X l)) :=
    hh l
  simp only [hb, quantumMonomial, Specs.LieNotes.Quantum.TriangularPBW.orderedMonomial,
    Fin.prod_univ_two, map_mul, map_pow, he, hf, hc, hplus, hminus]

local instance : TensorProduct.CompatibleSMul k A₁ U₁ U₁ where
  smul_tmul a x y := by
    rw [← coefficient_smul a x, ← coefficient_smul a y,
      TensorProduct.smul_tmul (R := k)]

private def tensorComparison (e : U₁ ≃ₐ[k] V) : (U₁ ⊗[A₁] U₁) ≃ₐ[k] (V ⊗[k] V) :=
  (Algebra.TensorProduct.equivOfCompatibleSMul k A₁ k U₁ U₁).trans
    (Algebra.TensorProduct.congr e e)

@[simp] private theorem tensorComparison_tmul (e : U₁ ≃ₐ[k] V) (x y : U₁) :
    tensorComparison e (x ⊗ₜ[A₁] y) = e x ⊗ₜ[k] e y := by
  simp [tensorComparison, Algebra.TensorProduct.equivOfCompatibleSMul]

private theorem levelOne_K (i : Root) : Coproduct.K C₁ i = 1 := by
  unfold Coproduct.K
  rw [cartanUnit_one, map_one]

private theorem preserves_standardHopf (e : U₁ ≃ₐ[k] V) (h : GeneratorImages e)
    (d : Coproduct.TruncatedData k 1) (s : Hopf.TruncatedData k 1 d) :
    PreservesHopf e (standardHopf k) d s := by
  let t := tensorComparison e
  have hΔ : t.toAlgHom.comp (d.comul.restrictScalars k) = classicalDelta.comp e.toAlgHom := by
    apply levelOne_hom_ext
    · intro i
      change t (d.comul (E₁ i)) = classicalDelta (e (E₁ i))
      rw [h.map_E, classicalDelta_ι, d.comul_E]
      simp [t, levelOne_K, h.map_E]
    · intro i
      change t (d.comul (F₁ i)) = classicalDelta (e (F₁ i))
      rw [h.map_F, classicalDelta_ι, d.comul_F]
      simp [t, levelOne_K, h.map_F]
    · intro i
      change t (d.comul (H₁ i)) = classicalDelta (e (H₁ i))
      rw [h.map_H, classicalDelta_ι, d.comul_H]
      simp [t, h.map_H]
  have hε : (coefficientEquiv k).toAlgHom.comp (d.counit.restrictScalars k) =
      classicalCounit.comp e.toAlgHom := by
    apply levelOne_hom_ext
    · intro i
      change coefficientEquiv k (d.counit (E₁ i)) = classicalCounit (e (E₁ i))
      rw [d.counit_E, map_zero, h.map_E, classicalCounit_ι]
    · intro i
      change coefficientEquiv k (d.counit (F₁ i)) = classicalCounit (e (F₁ i))
      rw [d.counit_F, map_zero, h.map_F, classicalCounit_ι]
    · intro i
      change coefficientEquiv k (d.counit (H₁ i)) = classicalCounit (e (H₁ i))
      rw [d.counit_H, map_zero, h.map_H, classicalCounit_ι]
  have hS : e.toAlgHom.op.comp (s.antipode.restrictScalars k) =
      oppositeAntipode.comp e.toAlgHom := by
    apply levelOne_hom_ext
    · intro i
      apply MulOpposite.unop_injective
      change e (s.antipode (E₁ i)).unop = classicalS (e (E₁ i))
      rw [h.map_E, classicalS_ι, s.generatorFormulas.2.1]
      simp [cartanUnit_one, h.map_E]
    · intro i
      apply MulOpposite.unop_injective
      change e (s.antipode (F₁ i)).unop = classicalS (e (F₁ i))
      rw [h.map_F, classicalS_ι, s.generatorFormulas.2.2]
      simp [cartanUnit_one, h.map_F]
    · intro i
      apply MulOpposite.unop_injective
      change e (s.antipode (H₁ i)).unop = classicalS (e (H₁ i))
      rw [h.map_H, classicalS_ι, s.antipode_H, map_neg, h.map_H]
  refine ⟨t.toRingEquiv, tensorComparison_tmul e, fun x => ⟨?_, ?_, ?_⟩⟩
  · exact DFunLike.congr_fun hΔ x
  · exact DFunLike.congr_fun hε x
  · exact congrArg MulOpposite.unop (DFunLike.congr_fun hS x)

end Comparison

theorem specialization : Specialization.{u} := by
  intro k _ _
  obtain ⟨B, hB, hbij⟩ := toClassical_bijective (k := k)
  let e := AlgEquiv.ofBijective toClassical hbij
  have he : GeneratorImages e :=
    ⟨toClassical_E, toClassical_F, toClassical_H, toClassical_zPlus, toClassical_zMinus⟩
  refine ⟨e, he, ?_, standardHopf k, preserves_standardHopf e he⟩
  refine ⟨matrixBasis, matrixBasis_apply, wordsEquiv, wordsEquiv_count, B, hB, fun w => ?_⟩
  change toClassical (quantumMonomial k (wordsEquiv w)) = B w
  rw [toClassical_PBW, Equiv.symm_apply_apply, hB]

end LieNotes.Quantum.MatrixSpecialization
