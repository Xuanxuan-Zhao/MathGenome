import Specs.LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum
import LinearAlgebraicGroups.RootData.AbstractPairing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum

open Specs.Arithmetic.OddSpinOrthogonalRootDatum
open Specs.AdjointRepresentation (GroupPoints constants scale dualMap)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors pairing characterValue)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.AbstractPairing (Datum Root)
open private matrixDual from LinearAlgebraicGroups.Affine.LieBracket
open private infinitesimalMatrix det_infinitesimalMatrix from LinearAlgebraicGroups.Affine.LieLeftExact

noncomputable section

variable {k : Type u} [Field k] {n : ℕ} {O : Specs.AffineAlgebraicGroup k}
  {T : ClosedSubgroup O.val}

set_option quotPrecheck false
set_option hygiene false

local notation "J" => Index.{u} n
local notation "e" i => (⟨Sum.inl (Sum.inl i)⟩ : J)
local notation "f_idx" i => (⟨Sum.inl (Sum.inr i)⟩ : J)
local notation "r" => (⟨Sum.inr ()⟩ : J)
local notation "b" => gramCoefficient
local notation "ε" => coordinate n

set_option hygiene true
set_option quotPrecheck true

@[simp] private theorem partner_partner (i : J) : partner (partner i) = i := by
  rcases i with ⟨(i | i) | ⟨⟩⟩ <;> rfl

private theorem partner_injective : Function.Injective (partner : J → J) :=
  Function.Involutive.injective partner_partner

@[simp] private theorem gramCoefficient_partner (R : Type u) [CommRing R] (i : J) :
    b R (partner i) = b R i := by
  rcases i with ⟨(i | i) | ⟨⟩⟩ <;> rfl

private theorem gramCoefficient_ne_zero (h₂ : (2 : k) ≠ 0) (i : J) : b k i ≠ 0 := by
  rcases i with ⟨(i | i) | ⟨⟩⟩
  · exact one_ne_zero
  · exact one_ne_zero
  · exact h₂

private theorem gram_mul_apply {R : Type u} [CommRing R] (M : Matrix J J R) (i j : J) :
    (gram n R * M) i j = b R i * M (partner i) j := by
  classical
  simp [Matrix.mul_apply, gram, ite_mul]

private theorem transpose_mul_gram_apply {R : Type u} [CommRing R]
    (M : Matrix J J R) (i j : J) :
    (Mᵀ * gram n R) i j = b R j * M (partner j) i := by
  classical
  have h (l : J) : partner l = j ↔ l = partner j :=
    ⟨fun hl => partner_injective (hl.trans (partner_partner j).symm), fun hl => by simp [hl]⟩
  simp [Matrix.mul_apply, gram, h, mul_ite, Finset.sum_ite_eq', mul_comm]

private theorem gram_dual :
    matrixDual (gram n (DualNumber k) : Matrix J J (DualNumber k)) =
      (gram n k, 0) := by
  apply TrivSqZeroExt.ext
  · ext i j
    change (gram n (DualNumber k) i j).fst = gram n k i j
    by_cases h : partner i = j <;> rcases i with ⟨(i | i) | ⟨⟩⟩ <;>
      simp [gram, gramCoefficient, h]; rfl
  · ext i j
    change (gram n (DualNumber k) i j).snd = 0
    by_cases h : partner i = j <;> rcases i with ⟨(i | i) | ⟨⟩⟩ <;>
      simp [gram, gramCoefficient, h]; rfl

private def Skew (M : Matrix J J k) : Prop :=
  ∀ i j, b k i * M (partner i) j + b k j * M (partner j) i = 0

private theorem matrixDual_injective (R : Type u) [CommRing R] :
    Function.Injective (matrixDual : Matrix J J (DualNumber R) →+* _) := by
  intro P Q h
  apply Matrix.ext
  intro i j
  exact TrivSqZeroExt.ext
    (congrArg (fun x : DualNumber (Matrix J J R) => x.fst i j) h)
    (congrArg (fun x : DualNumber (Matrix J J R) => x.snd i j) h)

/-- The polar form equation on a lift reducing to the identity. -/
private theorem infinitesimal_orthogonal (M : Matrix J J k) :
    (infinitesimalMatrix M)ᵀ * gram n (DualNumber k) * infinitesimalMatrix M =
      gram n (DualNumber k) ↔ Skew M := by
  rw [← (matrixDual_injective (n := n) k).eq_iff, map_mul, map_mul, gram_dual]
  have hM : matrixDual (infinitesimalMatrix M) = (1, M) := rfl
  have ht : matrixDual (infinitesimalMatrix M)ᵀ = (1, Mᵀ) := by
    apply TrivSqZeroExt.ext
    · exact transpose_one
    · rfl
  rw [hM, ht]
  let B : Matrix J J k := gram n k
  let L : DualNumber (Matrix J J k) := (1, Mᵀ)
  let Q : DualNumber (Matrix J J k) := (B, 0)
  let R : DualNumber (Matrix J J k) := (1, M)
  have hm : L * Q * R = (B, B * M + Mᵀ * B) := by
    apply TrivSqZeroExt.ext
    · change 1 * B * 1 = B
      simp
    · change (1 * B) * M + (1 * 0 + Mᵀ * B) * 1 = B * M + Mᵀ * B
      simp
  change L * Q * R = Q ↔ Skew M
  rw [hm]
  constructor
  · intro h i j
    have h' := congrArg (fun x : DualNumber (Matrix J J k) => x.snd i j) h
    change (B * M + Mᵀ * B) i j = 0 at h'
    simpa [B, gram_mul_apply, transpose_mul_gram_apply] using h'
  · intro h
    apply TrivSqZeroExt.ext
    · rfl
    · change B * M + Mᵀ * B = 0
      ext i j
      simpa [B, gram_mul_apply, transpose_mul_gram_apply] using h i j

variable (p : PointCoordinates T n)

private abbrev mat (R : TestAlgebra k) (g : GroupPoints O.val R) : Matrix J J R :=
  (p.orthogonal R g).val.val

private theorem mat_injective (R : TestAlgebra k) : Function.Injective (mat p R) :=
  fun _ _ h => (p.orthogonal R).injective (Subtype.ext (Subtype.ext h))

private theorem mat_one (R : TestAlgebra k) : mat p R 1 = 1 := by
  simp [mat, SpecialLinearGroup.coe_one]

private theorem mat_mul (R : TestAlgebra k) (g h : GroupPoints O.val R) :
    mat p R (g * h) = mat p R g * mat p R h := by
  simp [mat, SpecialLinearGroup.coe_mul]

private abbrev base := CommAlgCat.of k k
private abbrev dual (R : TestAlgebra k) := CommAlgCat.of k (DualNumber R)

private def tangentMatrix (v : Specs.Lie k O.val) : Matrix J J k :=
  (matrixDual (mat p (dual base) v.toMul.val)).snd

private theorem tangent_fst (v : Specs.Lie k O.val) :
    (matrixDual (mat p (dual base) v.toMul.val)).fst = 1 := by
  have h := p.orthogonal_natural (dualReduction k) v.toMul.val
  change mat p base (reduceTangentPoints O.val v.toMul.val) = _ at h
  rw [v.toMul.property, mat_one] at h
  exact h.symm

private theorem tangent_matrix_eq (v : Specs.Lie k O.val) :
    mat p (dual base) v.toMul.val = infinitesimalMatrix (tangentMatrix p v) := by
  apply Matrix.ext
  intro i j
  exact TrivSqZeroExt.ext (congrFun (congrFun (tangent_fst p v) i) j) rfl

private theorem tangent_skew (v : Specs.Lie k O.val) : Skew (tangentMatrix p v) := by
  have h := (p.orthogonal (dual base) v.toMul.val).property
  change (mat p (dual base) v.toMul.val)ᵀ * gram n (DualNumber k) *
    mat p (dual base) v.toMul.val = gram n (DualNumber k) at h
  rw [tangent_matrix_eq] at h
  exact (infinitesimal_orthogonal _).mp h

private theorem tangent_injective : Function.Injective (tangentMatrix p) := by
  intro v w h
  apply Subtype.ext
  change v.toMul.val = w.toMul.val
  apply mat_injective p (dual base)
  rw [tangent_matrix_eq, tangent_matrix_eq, h]

private theorem tangent_zero : tangentMatrix p 0 = 0 := by
  unfold tangentMatrix
  change (matrixDual (mat p (dual base) 1)).snd = 0
  rw [mat_one, map_one]
  rfl

private theorem tangent_exists (M : Matrix J J k) (hM : Skew M) (htrace : M.trace = 0) :
    ∃ v : Specs.Lie k O.val, tangentMatrix p v = M := by
  let g : orthogonalMatrices.{u,u} n (DualNumber k) :=
    ⟨⟨infinitesimalMatrix M, by rw [det_infinitesimalMatrix, htrace]; rfl⟩,
      (infinitesimal_orthogonal M).mpr hM⟩
  let x := (p.orthogonal (dual base)).symm g
  have hg : mat p (dual base) x = infinitesimalMatrix M :=
    congrArg (fun y : orthogonalMatrices.{u,u} n (DualNumber k) => y.val.val)
      ((p.orthogonal (dual base)).apply_symm_apply g)
  have hx : reduceTangentPoints O.val x = 1 := by
    apply mat_injective p base
    rw [mat_one]
    refine (p.orthogonal_natural (dualReduction k) x).trans ?_
    change (dualReduction k).hom.toRingHom.mapMatrix (mat p (dual base) x) = 1
    rw [hg]
    rfl
  exact ⟨⟨x, hx⟩, congrArg (fun A : Matrix J J (DualNumber k) => (matrixDual A).snd) hg⟩

/-- Diagonal conjugation on the entries of the relative tangent over each test algebra. -/
private theorem weight_iff (χ : Character T.group) (v : Specs.Lie k O.val) :
    v ∈ adjointWeightVectors T χ ↔
      ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (i j : J),
        (diagonalUnit (p.torus R t) i : R) * algebraMap k R (tangentMatrix p v i j) =
          characterValue χ R t * algebraMap k R (tangentMatrix p v i j) *
            (diagonalUnit (p.torus R t) j : R) := by
  classical
  change (∀ (R : TestAlgebra k) (t : GroupPoints T.group R), _) ↔ _
  let entryLaw (R : TestAlgebra k) (t : GroupPoints T.group R) :=
    ∀ i j : J, (diagonalUnit (p.torus R t) i : R) * algebraMap k R (tangentMatrix p v i j) =
      characterValue χ R t * algebraMap k R (tangentMatrix p v i j) *
        (diagonalUnit (p.torus R t) j : R)
  have h (R : TestAlgebra k) (t : GroupPoints T.group R) :
      let a := CommAlgCat.ofHom (Algebra.ofId k R)
      let x : GroupPoints O.val (dual R) := mapPoints (dualMap a) v.toMul.val
      let g : GroupPoints O.val (dual R) := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
      let y : GroupPoints O.val (dual R) := mapPoints (scale R (characterValue χ R t)) x
      g * x * g⁻¹ = y ↔ entryLaw R t := by
    dsimp only
    let a : base (k := k) ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    let x : GroupPoints O.val (dual R) := mapPoints (dualMap a) v.toMul.val
    let g : GroupPoints O.val (dual R) := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
    let y : GroupPoints O.val (dual R) := mapPoints (scale R (characterValue χ R t)) x
    change g * x * g⁻¹ = y ↔ _
    have hmul : g * x * g⁻¹ = y ↔ g * x = y * g := by
      constructor
      · intro h
        simpa using congrArg (· * g) h
      · intro h
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hmul]
    have hmat : g * x = y * g ↔ mat p (dual R) g * mat p (dual R) x =
        mat p (dual R) y * mat p (dual R) g := by
      rw [← mat_mul p (dual R) g x, ← mat_mul p (dual R) y g]
      exact (mat_injective p (dual R)).eq_iff.symm
    rw [hmat]
    let D := diagonal (fun i : J => (diagonalUnit (p.torus R t) i : R))
    let M : Matrix J J R := (algebraMap k R).mapMatrix (tangentMatrix p v)
    have hx : matrixDual (mat p (dual R) x) = (1, M) := by
      have hx' : mat p (dual R) x =
          (dualMap a).hom.toRingHom.mapMatrix (mat p (dual base) v.toMul.val) :=
        p.orthogonal_natural (dualMap a) v.toMul.val
      rw [hx', tangent_matrix_eq]
      apply TrivSqZeroExt.ext
      · ext i j
        change a.hom ((1 : Matrix J J k) i j) = (1 : Matrix J J R) i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      · rfl
    have hg : matrixDual (mat p (dual R) g) = (D, 0) := by
      have hg' : mat p (dual R) g =
          (constants R).hom.toRingHom.mapMatrix (mat p R (t ≫ T.inclusion.hom.hom)) :=
        p.orthogonal_natural (constants R) _
      have hd : mat p R (t ≫ T.inclusion.hom.hom) = D := p.inclusion R t
      rw [hg', hd]
      rfl
    have hy : matrixDual (mat p (dual R) y) =
        (1, characterValue χ R t • M) := by
      have hy' : mat p (dual R) y =
          (scale R (characterValue χ R t)).hom.toRingHom.mapMatrix (mat p (dual R) x) :=
        p.orthogonal_natural (scale R (characterValue χ R t)) x
      rw [hy']
      apply TrivSqZeroExt.ext
      · change (matrixDual (mat p (dual R) x)).fst = 1
        exact congrArg (fun z : DualNumber (Matrix J J R) => z.fst) hx
      · change characterValue χ R t • (matrixDual (mat p (dual R) x)).snd =
          characterValue χ R t • M
        exact congrArg (fun z : DualNumber (Matrix J J R) =>
          characterValue χ R t • z.snd) hx
    rw [← (matrixDual_injective (n := n) R).eq_iff, map_mul, map_mul, hx, hg, hy]
    let N : Matrix J J R := characterValue χ R t • M
    let A : DualNumber (Matrix J J R) := (D, 0)
    let X : DualNumber (Matrix J J R) := (1, M)
    let Y : DualNumber (Matrix J J R) := (1, N)
    have hL : A * X = (D, D * M) := by
      apply TrivSqZeroExt.ext
      · change D * 1 = D
        exact mul_one D
      · change D * M + 0 * 1 = D * M
        simp
    have hR : Y * A = (D, N * D) := by
      apply TrivSqZeroExt.ext
      · change 1 * D = D
        exact one_mul D
      · change 1 * 0 + N * D = N * D
        simp
    change A * X = Y * A ↔ entryLaw R t
    rw [hL, hR]
    constructor
    · intro hEq i j
      have h' : (D * M) i j = (N * D) i j :=
        congrArg (fun z : DualNumber (Matrix J J R) => z.snd i j) hEq
      simpa [D, M, N, Matrix.diagonal_mul, Matrix.mul_diagonal] using h'
    · intro hEq
      apply TrivSqZeroExt.ext
      · rfl
      · change D * M = N * D
        ext i j
        simpa [D, M, N, Matrix.diagonal_mul, Matrix.mul_diagonal] using hEq i j

  exact ⟨fun hw R t => (h R t).mp (hw R t), fun hw R t => (h R t).mpr (hw R t)⟩

private def vectorWeight (i : J) : Fin n → ℤ :=
  i.down.elim (fun j => j.elim (coordinate n) (fun a => -ε a)) (fun _ => 0)

@[simp] private theorem vectorWeight_partner (i : J) :
    vectorWeight (partner i) = -vectorWeight i := by
  rcases i with ⟨(i | i) | ⟨⟩⟩ <;> simp [vectorWeight, partner]

private theorem vectorWeight_injective : Function.Injective (vectorWeight : J → _) := by
  rintro ⟨(i | i) | ⟨⟩⟩ ⟨(j | j) | ⟨⟩⟩ h
  all_goals first
    | rfl
    | have he := congrFun h i
      first
      | by_cases hij : i = j
        · subst j
          first | rfl | simp [vectorWeight, coordinate] at he
        · simp [vectorWeight, coordinate, hij] at he
      | simp [vectorWeight, coordinate] at he
    | have he := congrFun h j
      simp [vectorWeight, coordinate] at he

private theorem roots_iff_entries (a : Fin n → ℤ) :
    a ∈ roots n ↔ ∃ i j : J, i ≠ j ∧ i ≠ partner j ∧ a = vectorWeight i - vectorWeight j := by
  change ((∃ i, a = ε i ∨ a = -ε i) ∨
    ∃ i j, i ≠ j ∧ (a = ε i - ε j ∨ a = ε i + ε j ∨ a = -(ε i + ε j))) ↔ _
  constructor
  · rintro (⟨i, rfl | rfl⟩ | ⟨i, j, hij, rfl | rfl | rfl⟩)
    · exact ⟨e i, r, by simp, by simp [partner], by simp [vectorWeight]⟩
    · exact ⟨f_idx i, r, by simp, by simp [partner], by simp [vectorWeight]⟩
    · exact ⟨e i, e j, by simpa, by simp [partner], rfl⟩
    · exact ⟨e i, f_idx j, by simp, by simpa [partner], by simp [vectorWeight, sub_neg_eq_add]⟩
    · exact ⟨f_idx i, e j, by simp, by simpa [partner], by simp [vectorWeight, sub_eq_add_neg, add_comm]⟩
  · rintro ⟨⟨(i | i) | ⟨⟩⟩, ⟨(j | j) | ⟨⟩⟩, h, h', rfl⟩
    · exact Or.inr ⟨i, j, by simpa using h, Or.inl rfl⟩
    · exact Or.inr ⟨i, j, by simpa [partner] using h',
        Or.inr (Or.inl (by simp [vectorWeight, sub_neg_eq_add]))⟩
    · exact Or.inl ⟨i, Or.inl (by simp [vectorWeight])⟩
    · exact Or.inr ⟨i, j, by simpa [partner] using h',
        Or.inr (Or.inr (by simp [vectorWeight, sub_eq_add_neg, add_comm]))⟩
    · exact Or.inr ⟨j, i, Ne.symm (by simpa using h), Or.inl (by
        simp [vectorWeight, sub_eq_add_neg, add_comm])⟩
    · exact Or.inl ⟨i, Or.inr (by simp [vectorWeight])⟩
    · exact Or.inl ⟨j, Or.inr (by simp [vectorWeight])⟩
    · exact Or.inl ⟨j, Or.inl (by simp [vectorWeight])⟩
    · exact (h rfl).elim

private def monomial {R : Type u} [CommRing R] (t : Fin n → Rˣ) (a : Fin n → ℤ) : Rˣ :=
  ∏ i, t i ^ a i

private theorem monomial_add {R : Type u} [CommRing R] (t : Fin n → Rˣ)
    (a c : Fin n → ℤ) : monomial t (a + c) = monomial t a * monomial t c := by
  simp [monomial, zpow_add, Finset.prod_mul_distrib]

private theorem monomial_sub {R : Type u} [CommRing R] (t : Fin n → Rˣ)
    (a c : Fin n → ℤ) : monomial t (a - c) = monomial t a * (monomial t c)⁻¹ := by
  have h := monomial_add t (a - c) c
  rw [sub_add_cancel] at h
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

private theorem monomial_vectorWeight {R : Type u} [CommRing R] (t : Fin n → Rˣ) (i : J) :
    monomial t (vectorWeight i) = diagonalUnit t i := by
  classical
  rcases i with ⟨(i | i) | ⟨⟩⟩
  · simp [monomial, vectorWeight, diagonalUnit, coordinate, Pi.single_apply, apply_ite]
  · simp [monomial, vectorWeight, diagonalUnit, coordinate, Pi.single_apply, apply_ite]
  · simp [monomial, vectorWeight, diagonalUnit]

variable [IsCommMonObj T.group.X] (l : LatticeCoordinates p)

private theorem coordinates_eq_of_evaluation (hT : IsSplitTorus T.group)
    (χ : Character T.group) (a : Fin n → ℤ)
    (h : ∀ (R : TestAlgebra k) (t : GroupPoints T.group R),
      characterValue χ R t = (monomial (p.torus R t) a : R)) :
    l.characters (Additive.ofMul χ) = a := by
  let ψ : Character T.group := Additive.toMul (l.characters.symm a)
  have he := l.characters.apply_symm_apply a
  have hh : χ = ψ := RootData.CharacterPairing.characterValuesDetectCharacters hT (by
    intro R t
    rw [h R t, l.character_eval R t ψ]
    exact congrArg (fun v => (monomial (p.torus R t) v : R)) he.symm)
  rw [hh]
  exact he

private theorem root_entry_coordinates (hT : IsSplitTorus T.group)
    {χ : Character T.group} {v : Specs.Lie k O.val}
    (hv : v ∈ adjointWeightVectors T χ) {i j : J}
    (hij : tangentMatrix p v i j ≠ 0) :
    l.characters (Additive.ofMul χ) = vectorWeight i - vectorWeight j := by
  apply coordinates_eq_of_evaluation p l hT
  intro R t
  have hu := (isUnit_iff_ne_zero.mpr hij).map (algebraMap k R)
  have h := (weight_iff p χ v).mp hv R t i j
  rw [mul_right_comm] at h
  have h' := hu.mul_left_inj.mp h
  rw [monomial_sub, monomial_vectorWeight, monomial_vectorWeight, Units.val_mul]
  apply (diagonalUnit (p.torus R t) j).mul_left_inj.mp
  simpa [mul_assoc] using h'.symm

private def rootMatrix (i j : J) : Matrix J J k :=
  Matrix.single i j (b k j) - Matrix.single (partner j) (partner i) (b k i)

private theorem rootMatrix_skew {i j : J} (hij : i ≠ partner j) : Skew (rootMatrix (k := k) i j) := by
  intro a c
  have hp (x y : J) : x = partner y ↔ partner x = y :=
    ⟨fun h => by rw [h, partner_partner], fun h => by rw [← h, partner_partner]⟩
  have he (x y : J) : rootMatrix (k := k) i j (partner x) y =
      (if partner i = x ∧ j = y then b k j else 0) -
        (if j = x ∧ partner i = y then b k i else 0) := by
    simp only [rootMatrix, Matrix.sub_apply, Matrix.single_apply, hp, partner_partner]
  rw [he, he]
  simp only [@and_comm (partner i = c) (j = a), @and_comm (j = c) (partner i = a)]
  by_cases h₁ : partner i = a ∧ j = c
  · by_cases h₂ : j = a ∧ partner i = c
    · exact (hij (partner_injective ((h₁.1.trans h₂.1.symm).trans (partner_partner j).symm))).elim
    · simp only [ite_eq_left h₁, ite_eq_right h₂]
      rw [← h₁.1, ← h₁.2, gramCoefficient_partner]
      ring
  · by_cases h₂ : j = a ∧ partner i = c
    · simp only [ite_eq_right h₁, ite_eq_left h₂]
      rw [← h₂.1, ← h₂.2, gramCoefficient_partner]
      ring
    · simp [h₁, h₂]

private theorem rootMatrix_trace {i j : J} (h : i ≠ j) :
    (rootMatrix (k := k) i j).trace = 0 := by
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro a _
  have h' : partner j ≠ partner i := fun eq => h (partner_injective eq).symm
  simp only [rootMatrix, Matrix.diag_apply, Matrix.sub_apply, Matrix.single_apply]
  rw [ite_eq_right (fun he => h (he.1.trans he.2.symm)),
    ite_eq_right (fun he => h' (he.1.trans he.2.symm)), sub_zero]

private theorem weight_of_rootMatrix {i j : J} (χ : Character T.group)
    (hχ : l.characters (Additive.ofMul χ) = vectorWeight i - vectorWeight j)
    (v : Specs.Lie k O.val) (hv : tangentMatrix p v = rootMatrix i j) :
    v ∈ adjointWeightVectors T χ := by
  apply (weight_iff p χ v).mpr
  intro R t a c
  rw [hv, l.character_eval, hχ]
  change _ = (monomial (p.torus R t) (vectorWeight i - vectorWeight j) : R) * _ * _
  have he (x y : J) (hx : vectorWeight x - vectorWeight y = vectorWeight i - vectorWeight j)
      (m : R) :
      (diagonalUnit (p.torus R t) x : R) * m =
        (monomial (p.torus R t) (vectorWeight i - vectorWeight j) : R) * m *
          (diagonalUnit (p.torus R t) y : R) := by
    rw [← hx, monomial_sub, monomial_vectorWeight, monomial_vectorWeight, Units.val_mul]
    let u := diagonalUnit (p.torus R t) x
    let v := diagonalUnit (p.torus R t) y
    change (u : R) * m = (u * ↑v⁻¹) * m * v
    calc
      _ = (u * m) * (↑v⁻¹ * (v : R)) := by simp
      _ = _ := by ring
  have hp : vectorWeight (partner j) - vectorWeight (partner i) =
      vectorWeight i - vectorWeight j := by simp [sub_eq_add_neg, add_comm]
  by_cases h₁ : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h₁
    apply he _ _ rfl
  by_cases h₂ : partner j = a ∧ partner i = c
  · obtain ⟨rfl, rfl⟩ := h₂
    apply he _ _ hp
  simp [rootMatrix, h₁, h₂]

/-- A nonzero tangent entry detects a root, and each allowed entry gives a tangent vector. -/
private theorem roots_eq (h₂ : (2 : k) ≠ 0) (hT : IsSplitTorus T.group) :
    (fun χ => l.characters (Additive.ofMul χ)) '' absoluteRoots T = roots n := by
  classical
  ext a
  rw [roots_iff_entries]
  constructor
  · rintro ⟨χ, ⟨hχ, v, hv, hvne⟩, rfl⟩
    have hne : tangentMatrix p v ≠ 0 := fun he =>
      hvne (tangent_injective p (he.trans (tangent_zero p).symm))
    have hex : ∃ i j : J, tangentMatrix p v i j ≠ 0 := by
      by_contra! h
      exact hne (Matrix.ext h)
    obtain ⟨i, j, hij⟩ := hex
    have hwt := root_entry_coordinates p l hT hv hij
    refine ⟨i, j, ?_, ?_, hwt⟩
    · rintro rfl
      rw [sub_self] at hwt
      exact hχ (l.characters.injective (hwt.trans l.characters.map_zero.symm))
    · rintro rfl
      have he := tangent_skew p v j j
      rw [← two_mul, ← mul_assoc] at he
      exact hij ((mul_eq_zero.mp he).resolve_left (mul_ne_zero h₂ (gramCoefficient_ne_zero h₂ j)))
  · rintro ⟨i, j, hij, hij', rfl⟩
    let a := vectorWeight i - vectorWeight j
    let χ : Character T.group := Additive.toMul (l.characters.symm a)
    have hχ : l.characters (Additive.ofMul χ) = a := l.characters.apply_symm_apply _
    have hne : χ ≠ 1 := by
      intro he
      have hz : a = 0 := hχ.symm.trans (by rw [he]; exact l.characters.map_zero)
      exact hij (vectorWeight_injective (sub_eq_zero.mp hz))
    obtain ⟨v, hv⟩ := tangent_exists p (rootMatrix i j) (rootMatrix_skew hij')
      (rootMatrix_trace hij)
    have hnon : rootMatrix (k := k) i j i j ≠ 0 := by
      have hh : ¬ (partner j = i ∧ partner i = j) := fun he => hij' he.1.symm
      simpa [rootMatrix, Matrix.single_apply, hh] using gramCoefficient_ne_zero h₂ j
    refine ⟨χ, ⟨hne, v, weight_of_rootMatrix p l χ hχ v hv, ?_⟩, hχ⟩
    intro he
    rw [he, tangent_zero] at hv
    exact hnon (congrArg (fun m : Matrix J J k => m i j) hv.symm)

open private constantPoint comp_constantPoint pointConj comp_pointConj
  from LinearAlgebraicGroups.RootData.AbstractPairing

private def IsAxis (a : Fin n → ℤ) : Prop :=
  ∀ i j, i ≠ j → a i = 0 ∨ a j = 0

private theorem vectorWeight_isAxis (a : J) : IsAxis (vectorWeight a) := by
  intro i j hij
  rcases a with ⟨(a | a) | ⟨⟩⟩
  · by_cases hi : a = i
    · right
      simp [vectorWeight, coordinate, hi, hij]
    · left
      simp [vectorWeight, coordinate, Ne.symm hi]
  · by_cases hi : a = i
    · right
      simp [vectorWeight, coordinate, hi, hij]
    · left
      simp [vectorWeight, coordinate, Ne.symm hi]
  · left
    rfl

omit [IsCommMonObj T.group.X] in
private theorem mat_column_nonzero (g₀ : GroupPoints O.val base) (j : J) :
    ∃ i : J, mat p base g₀ i j ≠ 0 := by
  by_contra! h
  have hA : mat p base g₀⁻¹ * mat p base g₀ = 1 := by
    rw [← mat_mul p base g₀⁻¹ g₀, inv_mul_cancel, mat_one]
  have hz : (mat p base g₀⁻¹ * mat p base g₀) j j = 0 := by simp [Matrix.mul_apply, h]
  rw [hA, Matrix.one_apply_eq] at hz
  exact one_ne_zero hz

omit [IsCommMonObj T.group.X] in
private theorem normalizer_matrix (s : T.group ≅ T.group)
    (g : 𝟙_ (SchemeOver k) ⟶ O.val.X)
    (hconj : (s.hom ≫ T.inclusion).hom.hom = pointConj g T.inclusion.hom.hom)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let t' : GroupPoints T.group R := t ≫ s.inv.hom.hom
    let gR : GroupPoints O.val R := constantPoint g _
    let A := mat p R gR
    diagonal (fun i : J => (diagonalUnit (p.torus R t) i : R)) * A =
      A * diagonal (fun i : J => (diagonalUnit (p.torus R t') i : R)) := by
  dsimp only
  let t' : GroupPoints T.group R := t ≫ s.inv.hom.hom
  let gR : GroupPoints O.val R := constantPoint g _
  let x : GroupPoints O.val R := t ≫ T.inclusion.hom.hom
  let y : GroupPoints O.val R := t' ≫ T.inclusion.hom.hom
  have hiso : s.inv ≫ s.hom ≫ T.inclusion = T.inclusion := s.inv_hom_id_assoc _
  have hcomp' : t ≫ (s.inv ≫ s.hom ≫ T.inclusion).hom.hom = x :=
    congrArg (fun f : T.group ⟶ O.val => t ≫ f.hom.hom) hiso
  have hcomp : t' ≫ (s.hom ≫ T.inclusion).hom.hom = x :=
    (Category.assoc t s.inv.hom.hom (s.hom ≫ T.inclusion).hom.hom).trans hcomp'
  have h1 : t' ≫ (s.hom ≫ T.inclusion).hom.hom =
      t' ≫ pointConj g T.inclusion.hom.hom :=
    congrArg (fun f => t' ≫ f) hconj
  have h2 : t' ≫ pointConj g T.inclusion.hom.hom = gR * y * gR⁻¹ :=
    comp_pointConj g t' T.inclusion.hom.hom
  have hx : x = gR * y * gR⁻¹ := hcomp.symm.trans (h1.trans h2)
  have hp : x * gR = gR * y :=
    (congrArg (fun z : GroupPoints O.val R => z * gR) hx).trans (inv_mul_cancel_right _ _)
  let Dx : Matrix J J R := diagonal (fun i => (diagonalUnit (p.torus R t) i : R))
  let Dy : Matrix J J R := diagonal (fun i => (diagonalUnit (p.torus R t') i : R))
  have hxD : mat p R x = Dx := p.inclusion R t
  have hyD : mat p R y = Dy := p.inclusion R t'
  change Dx * mat p R gR = mat p R gR * Dy
  calc
    _ = mat p R x * mat p R gR := congrArg (· * mat p R gR) hxD.symm
    _ = mat p R (x * gR) := (mat_mul p R x gR).symm
    _ = mat p R (gR * y) := congrArg (mat p R) hp
    _ = mat p R gR * mat p R y := mat_mul p R gR y
    _ = _ := congrArg (mat p R gR * ·) hyD

/-- A nonzero entry in a column of the normalizer matrix identifies the pulled-back weight. -/
private theorem normalizer_weights (hT : IsSplitTorus T.group)
    (s : T.group ≅ T.group) (g : 𝟙_ (SchemeOver k) ⟶ O.val.X)
    (hconj : (s.hom ≫ T.inclusion).hom.hom = pointConj g T.inclusion.hom.hom)
    (j : J) (χ : Character T.group)
    (hχ : l.characters (Additive.ofMul χ) = vectorWeight j) :
    ∃ i : J, l.characters (Additive.ofMul (s.inv ≫ χ)) = vectorWeight i := by
  let g₀ : GroupPoints O.val base := constantPoint g _
  let A := mat p base g₀
  obtain ⟨i, hi⟩ := mat_column_nonzero p g₀ j
  refine ⟨i, coordinates_eq_of_evaluation p l hT (s.inv ≫ χ) _ ?_⟩
  intro R t
  let t' : GroupPoints T.group R := t ≫ s.inv.hom.hom
  let gR : GroupPoints O.val R := constantPoint g _
  have hgR : mat p R gR = (algebraMap k R).mapMatrix A := by
    let a : base (k := k) ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have h : mapPoints a g₀ = gR := comp_constantPoint g _
    exact (congrArg (mat p R) h).symm.trans (p.orthogonal_natural a g₀)
  have he : diagonal (fun i : J => (diagonalUnit (p.torus R t) i : R)) * mat p R gR =
      mat p R gR * diagonal (fun i : J => (diagonalUnit (p.torus R t') i : R)) :=
    normalizer_matrix p s g hconj R t
  rw [hgR] at he
  have hij := congrArg (fun M : Matrix J J R => M i j) he
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, RingHom.mapMatrix_apply, Matrix.map_apply] at hij
  change (diagonalUnit (p.torus R t) i : R) * algebraMap k R (A i j) =
    algebraMap k R (A i j) * (diagonalUnit (p.torus R t') j : R) at hij
  rw [mul_comm (algebraMap k R (A i j)) _] at hij
  have hcancel := ((isUnit_iff_ne_zero.mpr hi).map (algebraMap k R)).mul_left_inj.mp hij
  have hc : characterValue (s.inv ≫ χ) R t = characterValue χ R t' := by
    unfold characterValue t'
    congr 2
  rw [hc, l.character_eval, hχ]
  change (monomial (p.torus R t') (vectorWeight j) : R) = _
  rw [monomial_vectorWeight, monomial_vectorWeight]
  exact hcancel.symm

private theorem attached_reflection_coordinates (hT : IsSplitTorus T.group)
    (d : Datum T) (α : Root T) :
    let a := l.characters (Additive.ofMul α.val)
    let c := l.cocharacters (d.rootDatum.coroot α)
    (∑ i, a i * c i) = 2 ∧ ∀ i, IsAxis (ε i - c i • a) := by
  dsimp only
  obtain ⟨C, cochar, hC, hcochar, D, E, hDE, Q, F, P, A, xpos, xneg, hpos, hneg,
    hscalarpos, hscalarneg, reflection, hr⟩ := d.attached α
  have hc : Additive.ofMul reflection.coroot = d.rootDatum.coroot α := congrArg Additive.ofMul hr
  refine ⟨?_, ?_⟩
  · rw [← hc, ← l.pairing_eq]
    exact reflection.root_pairing
  · intro i
    let χ : Character T.group := Additive.toMul (l.characters.symm (ε i))
    have hχ : l.characters (Additive.ofMul χ) = ε i := l.characters.apply_symm_apply _
    obtain ⟨j, hj⟩ := normalizer_weights p l hT reflection.conjugation reflection.representative
      reflection.conjugates (e i) χ hχ
    have hrefl := congrArg (fun ψ : Character T.group => l.characters (Additive.ofMul ψ))
      (reflection.reflection χ)
    change _ = l.characters (Additive.ofMul χ +
      (-pairing T.group χ reflection.coroot) • Additive.ofMul α.val) at hrefl
    rw [hj, map_add, map_smul, hχ, l.pairing_eq, hχ, hc] at hrefl
    have hsum : (∑ j, ε i j * l.cocharacters (d.rootDatum.coroot α) j) =
        l.cocharacters (d.rootDatum.coroot α) i := by
      classical
      simp [coordinate, Pi.single_apply, ite_mul]
    rw [hsum, neg_smul, ← sub_eq_add_neg] at hrefl
    rw [← hrefl]
    exact vectorWeight_isAxis j

private theorem short_coroot {a c : Fin n → ℤ} (i : Fin n) (s : ℤ) (hs : s * s = 1)
    (ha : a = s • ε i) (hp : ∑ j, a j * c j = 2)
    (haxis : ∀ j, IsAxis (ε j - c j • a)) :
    c = 2 • a := by
  classical
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hi : s * c i = 2 := by
    simpa [ha, coordinate, Pi.single_apply, mul_ite, ite_mul] using hp
  ext j
  by_cases hj : j = i
  · subst j
    have hh : c i = s * 2 := calc
      c i = s * (s * c i) := by rw [← mul_assoc, hs, one_mul]
      _ = s * 2 := congrArg (s * ·) hi
    simpa [ha, coordinate, Pi.single_apply, mul_comm] using hh
  · have hh := haxis j j i hj
    have hz : c j = 0 := by
      simpa [ha, coordinate, Pi.single_apply, hj, Ne.symm hj, hs0] using hh
    simp [ha, hz, coordinate, hj]

private theorem long_coroot {a c : Fin n → ℤ} (i j : Fin n) (hij : i ≠ j)
    (s t : ℤ) (hs : s * s = 1) (ht : t * t = 1)
    (ha : a = s • ε i + t • ε j)
    (hp : ∑ x, a x * c x = 2) (haxis : ∀ x, IsAxis (ε x - c x • a)) : c = a := by
  classical
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hi : a i = s := by simp [ha, coordinate, hij]
  have hj : a j = t := by simp [ha, coordinate, Ne.symm hij]
  have hp' : s * c i + t * c j = 2 := by
    simpa [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul, coordinate, Pi.single_apply,
      add_mul, mul_ite, ite_mul, Finset.sum_add_distrib] using hp
  have hci : c i = 0 ∨ c i = s := by
    rcases haxis i i j hij with h | h
    · right
      have he : c i * s = 1 := by
        have hh : 1 - c i * s = 0 := by simpa [coordinate, hi] using h
        exact (sub_eq_zero.mp hh).symm
      calc
        c i = (c i * s) * s := by rw [mul_assoc, hs, mul_one]
        _ = s := by rw [he, one_mul]
    · left
      simpa [coordinate, hj, hij, ht0] using h
  have hcj : c j = 0 ∨ c j = t := by
    rcases haxis j j i hij.symm with h | h
    · right
      have he : c j * t = 1 := by
        have hh : 1 - c j * t = 0 := by simpa [coordinate, hj] using h
        exact (sub_eq_zero.mp hh).symm
      calc
        c j = (c j * t) * t := by rw [mul_assoc, ht, mul_one]
        _ = t := by rw [he, one_mul]
    · left
      simpa [coordinate, hi, hij, hs0] using h
  have hci' : c i = s := by
    rcases hci with h | h
    · rcases hcj with h' | h' <;> simp [h, h', ht] at hp'
    · exact h
  have hcj' : c j = t := by
    rcases hcj with h | h
    · simp [h, hci', hs] at hp'
    · exact h
  ext x
  by_cases hxi : x = i
  · simpa [hxi, hi] using hci'
  by_cases hxj : x = j
  · simpa [hxj, hj] using hcj'
  have hcx : c x = 0 := by
    have h := haxis x x i hxi
    have hz : a x = 0 := by
      simp [ha, coordinate, hxi, hxj]
    simpa [coordinate, Pi.single_apply, hxi, hi, hz, hs0] using h
  simp [ha, hcx, coordinate, hxi, hxj]

private theorem markedCoroot {a c : Fin n → ℤ}
    (hp : ∑ i, a i * c i = 2) (haxis : ∀ i, IsAxis (ε i - c i • a)) :
    ∀ c', (a,c') ∈ corootPairs n ↔ a ∈ roots n ∧ c = c' := by
  intro c'
  have hs (i : Fin n) (h : a = ε i) : c = 2 • ε i := by
    have h' := short_coroot i 1 (by decide) (by simpa using h) hp haxis
    simpa [h] using h'
  have hsn (i : Fin n) (h : a = -ε i) : c = -(2 • ε i) := by
    have h' := short_coroot i (-1) (by decide) (by simpa using h) hp haxis
    simpa [h, smul_neg] using h'
  have hd (i j : Fin n) (hij : i ≠ j) (h : a = ε i - ε j) : c = a :=
    long_coroot i j hij 1 (-1) (by decide) (by decide) (by simpa [sub_eq_add_neg] using h) hp haxis
  have ha (i j : Fin n) (hij : i ≠ j) (h : a = ε i + ε j) : c = a :=
    long_coroot i j hij 1 1 (by decide) (by decide) (by simpa using h) hp haxis
  have han (i j : Fin n) (hij : i ≠ j) (h : a = -(ε i + ε j)) : c = a :=
    long_coroot i j hij (-1) (-1) (by decide) (by decide) (by simpa [neg_add, add_comm] using h) hp haxis
  change ((∃ i, (a = ε i ∧ c' = 2 • ε i) ∨ (a = -ε i ∧ c' = -(2 • ε i))) ∨
    ∃ i j, i ≠ j ∧ a = c' ∧ (a = ε i - ε j ∨ a = ε i + ε j ∨
      a = -(ε i + ε j))) ↔ a ∈ roots n ∧ c = c'
  constructor
  · rintro (⟨i, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ | ⟨i, j, hij, rfl, h | h | h⟩)
    · exact ⟨Or.inl ⟨i, Or.inl h⟩, hs i h⟩
    · exact ⟨Or.inl ⟨i, Or.inr h⟩, hsn i h⟩
    · exact ⟨Or.inr ⟨i, j, hij, Or.inl h⟩, hd i j hij h⟩
    · exact ⟨Or.inr ⟨i, j, hij, Or.inr (Or.inl h)⟩, ha i j hij h⟩
    · exact ⟨Or.inr ⟨i, j, hij, Or.inr (Or.inr h)⟩, han i j hij h⟩
  · rintro ⟨(⟨i, h | h⟩ | ⟨i, j, hij, h | h | h⟩), rfl⟩
    · exact Or.inl ⟨i, Or.inl ⟨h, hs i h⟩⟩
    · exact Or.inl ⟨i, Or.inr ⟨h, hsn i h⟩⟩
    · exact Or.inr ⟨i, j, hij, (hd i j hij h).symm, Or.inl h⟩
    · exact Or.inr ⟨i, j, hij, (ha i j hij h).symm, Or.inr (Or.inl h)⟩
    · exact Or.inr ⟨i, j, hij, (han i j hij h).symm, Or.inr (Or.inr h)⟩

theorem orthogonalRootDatum : Statement.{u} := by
  intro k _ n h₂ _ O T hO hT hmax hcomm p l
  have hroots := roots_eq p l h₂ hT
  refine ⟨hroots, ?_⟩
  obtain ⟨_, ⟨d⟩⟩ := RootData.AbstractPairing.abstractPairing O hO T hT hmax
  refine ⟨d, ?_⟩
  ext ⟨a, c⟩
  constructor
  · rintro ⟨α, h⟩
    rw [← h]
    change (l.characters (d.rootDatum.root α), _) ∈ _
    rw [d.root_eq]
    obtain ⟨hp, haxis⟩ := attached_reflection_coordinates p l hT d α
    exact (markedCoroot hp haxis _).mpr
      ⟨hroots ▸ ⟨α.val, α.property, rfl⟩, rfl⟩
  · intro h
    have ha : a ∈ roots n := by
      rcases h with (⟨i, ⟨he, _⟩ | ⟨he, _⟩⟩ | ⟨i, j, hij, _, he⟩)
      · exact Or.inl ⟨i, Or.inl he⟩
      · exact Or.inl ⟨i, Or.inr he⟩
      · exact Or.inr ⟨i, j, hij, he⟩
    have ha' : a ∈ (fun χ => l.characters (Additive.ofMul χ)) '' absoluteRoots T :=
      hroots.symm ▸ ha
    obtain ⟨χ, hχ, he⟩ := ha'
    let α : Root T := ⟨χ, hχ⟩
    obtain ⟨hp, haxis⟩ := attached_reflection_coordinates p l hT d α
    have he' : l.characters (Additive.ofMul α.val) = a := he
    have hm : (l.characters (Additive.ofMul α.val), c) ∈ corootPairs n := by
      rw [he']
      exact h
    have hc := ((markedCoroot hp haxis c).mp hm).2
    exact ⟨α, Prod.ext ((congrArg l.characters (d.root_eq α)).trans he) hc⟩

end

end LinearAlgebraicGroups.Arithmetic.OddSpinOrthogonalRootDatum
