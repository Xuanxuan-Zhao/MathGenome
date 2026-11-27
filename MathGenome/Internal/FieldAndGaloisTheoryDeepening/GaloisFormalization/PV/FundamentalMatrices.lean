import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LinearSystem

namespace GaloisFormalization.PV
namespace LinearSystem

open Matrix Function
open scoped BigOperators Matrix

universe u v

section Fundamental

variable {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
  {S : Type v} [CommRing S] [Algebra K S]

private theorem inv_mulVec (Y : GL (Fin n) S) (x : Fin n → S) :
    (Y⁻¹).val *ᵥ (Y.val *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Y.inv_mul, Matrix.one_mulVec]

private theorem mulVec_inv (Y : GL (Fin n) S) (x : Fin n → S) :
    Y.val *ᵥ ((Y⁻¹).val *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Y.mul_inv, Matrix.one_mulVec]

private theorem mulVec_injective (Y : GL (Fin n) S) :
    Function.Injective (fun x => Y.val *ᵥ x) := by
  intro x z h
  simpa only [inv_mulVec] using congrArg (fun w => (Y⁻¹).val *ᵥ w) h

private theorem derivation_mulVec (E : Operator .differential S)
    (M : Matrix (Fin n) (Fin n) S) (c : Fin n → S) :
    (fun i => E ((M *ᵥ c) i)) = M *ᵥ (fun i => E (c i)) + M.map E *ᵥ c := by
  funext i
  change E.toDerivation (∑ j, M i j * c j) =
    (∑ j, M i j * E.toDerivation (c j)) + ∑ j, E.toDerivation (M i j) * c j
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, mul_comm]

/-- In the coordinates of a fundamental matrix, the column equation is constancy. -/
private theorem isSolution_mulVec_iff (A : LinearSystem kind K n) (E : Operator kind S)
    (Y : GL (Fin n) S) (hY : A.IsFundamental E Y) (c : Fin n → S) :
    A.IsSolution E (Y.val *ᵥ c) ↔ ∀ i, c i ∈ E.constantSubring := by
  change _ = _ at hY
  unfold IsSolution
  simp only [Operator.mem_constantSubring]
  cases kind with
  | differential =>
    have h := derivation_mulVec E Y.val c
    rw [hY, ← Matrix.mulVec_mulVec] at h
    rw [h]
    constructor
    · intro hsol
      have hzero : (Y.val *ᵥ fun i => E (c i)) = 0 :=
        add_right_cancel (hsol.trans (zero_add _).symm)
      rw [← Matrix.mulVec_zero Y.val, (mulVec_injective Y).eq_iff] at hzero
      exact fun i => congr_fun hzero i
    · intro hc
      have hzero : (fun i => E (c i)) = 0 := funext hc
      rw [hzero, Matrix.mulVec_zero, zero_add]
  | difference =>
    let U : GL (Fin n) S := GeneralLinearGroup.map (algebraMap K S) (show GL (Fin n) K from A) * Y
    have h : (fun i => E ((Y.val *ᵥ c) i)) = U.val *ᵥ (fun i => E (c i)) := by
      have hU : Y.val.map E = U.val := hY
      funext i
      rw [← hU]
      exact RingHom.map_mulVec E.toRingEquiv.toRingHom Y.val c i
    have hU : A.mapCoefficients S *ᵥ (Y.val *ᵥ c) = U.val *ᵥ c :=
      Matrix.mulVec_mulVec c (A.mapCoefficients S) Y.val
    rw [h, hU, (mulVec_injective U).eq_iff]
    exact ⟨fun hc i => congr_fun hc i, fun hc => funext hc⟩

private theorem inverseCoordinates_mem (A : LinearSystem kind K n) (E : Operator kind S)
    (Y : GL (Fin n) S) (hY : A.IsFundamental E Y) {x : Fin n → S}
    (hx : A.IsSolution E x) (i : Fin n) :
    ((Y⁻¹).val *ᵥ x) i ∈ E.constantSubring := by
  apply (isSolution_mulVec_iff A E Y hY ((Y⁻¹).val *ᵥ x)).mp
  simpa only [mulVec_inv] using hx

/-- The change of coordinates from constant columns to solution columns. -/
def fundamentalSolutionEquiv (A : LinearSystem kind K n) (E : Operator kind S)
    (Y : GL (Fin n) S) (hY : A.IsFundamental E Y) :
    (Fin n → E.constantSubring) ≃ A.Solution E where
  toFun c := ⟨Y.val *ᵥ (fun i => (c i : S)),
    (isSolution_mulVec_iff A E Y hY _).mpr (fun i => (c i).property)⟩
  invFun x i := ⟨((Y⁻¹).val *ᵥ x.val) i, inverseCoordinates_mem A E Y hY x.property i⟩
  left_inv _c := funext fun i => Subtype.ext (congr_fun (inv_mulVec Y _) i)
  right_inv x := Subtype.ext (mulVec_inv Y x.val)

theorem fundamentalColumnEquivalence
    (D : OperatorField kind K) (_ : D.IsBaseField) (E : Operator kind S)
    (_ : D.IsExtension E) (A : LinearSystem kind K n)
    (Y : GL (Fin n) S) (hY : A.IsFundamental E Y) :
    ∃ e : (Fin n → E.constantSubring) ≃ A.Solution E,
      (∀ c, (e c).val = Y.val *ᵥ (fun i => (c i : S))) ∧
      (∀ x i, (e.symm x i : S) = ((Y⁻¹).val *ᵥ x.val) i) :=
  ⟨fundamentalSolutionEquiv A E Y hY, fun _ => rfl, fun _ _ => rfl⟩

private theorem relativeMatrix_mem (A : LinearSystem kind K n) (E : Operator kind S)
    (Y Z : GL (Fin n) S) (hY : A.IsFundamental E Y) (hZ : A.IsFundamental E Z)
    (i j : Fin n) : (Y⁻¹ * Z : GL (Fin n) S).val i j ∈ E.constantSubring := by
  have hcol : A.IsSolution E (fun l => Z.val l j) := by
    funext l
    exact congrArg (fun M : Matrix (Fin n) (Fin n) S => M l j) hZ
  exact inverseCoordinates_mem A E Y hY hcol i

private def restrictMatrix (E : Operator kind S) (M : Matrix (Fin n) (Fin n) S)
    (h : ∀ i j, M i j ∈ E.constantSubring) : Matrix (Fin n) (Fin n) E.constantSubring :=
  Matrix.of fun i j => ⟨M i j, h i j⟩

/-- The ratio of two fundamental matrices is a unique matrix unit over the constants. -/
theorem fundamentalRightMultiplier
    (D : OperatorField kind K) (_ : D.IsBaseField) (E : Operator kind S)
    (_ : D.IsExtension E) (A : LinearSystem kind K n)
    (Y Z : GL (Fin n) S) (hY : A.IsFundamental E Y) (hZ : A.IsFundamental E Z) :
    ∃! B : GL (Fin n) E.constantSubring,
      Z = Y * GeneralLinearGroup.map E.constantSubring.subtype B := by
  let W := Y⁻¹ * Z
  have hW : ∀ i j, W.val i j ∈ E.constantSubring := relativeMatrix_mem A E Y Z hY hZ
  have hW' : ∀ i j, (W⁻¹).val i j ∈ E.constantSubring := by
    simpa only [W, _root_.mul_inv_rev, inv_inv] using relativeMatrix_mem A E Z Y hZ hY
  let M := restrictMatrix E W.val hW
  let N := restrictMatrix E (W⁻¹).val hW'
  let f : Matrix (Fin n) (Fin n) E.constantSubring →+* Matrix (Fin n) (Fin n) S :=
    E.constantSubring.subtype.mapMatrix
  have hf : Function.Injective f := fun P Q hpq => Matrix.ext fun i j =>
    Subtype.ext (congrArg (fun T : Matrix (Fin n) (Fin n) S => T i j) hpq)
  have hM : f M = W.val := rfl
  have hN : f N = (W⁻¹).val := rfl
  let B : GL (Fin n) E.constantSubring :=
    ⟨M, N, hf (by rw [map_mul, hM, hN, W.mul_inv, map_one]),
      hf (by rw [map_mul, hM, hN, W.inv_mul, map_one])⟩
  have hB : GeneralLinearGroup.map E.constantSubring.subtype B = W := Units.ext hM
  refine ⟨B, ?_, ?_⟩
  · change Z = Y * GeneralLinearGroup.map E.constantSubring.subtype B
    rw [hB, show W = Y⁻¹ * Z from rfl, ← mul_assoc, mul_inv_cancel, one_mul]
  · intro B' hB'
    apply Units.ext
    apply hf
    change (GeneralLinearGroup.map E.constantSubring.subtype B').val = (GeneralLinearGroup.map E.constantSubring.subtype B).val
    rw [hB]
    exact congrArg Units.val (eq_inv_mul_of_mul_eq hB'.symm)

theorem orderZeroFundamental (A : LinearSystem kind K 0) (E : Operator kind S) :
    A.IsFundamental E 1 ∧ ∀ Y : GL (Fin 0) S, Y = 1 := by
  exact ⟨Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

end Fundamental

section Scalar

/-- The companion matrix of a positive-order monic scalar equation. -/
def companionMatrix {K : Type u} [CommRing K] {n : ℕ}
    (a : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of (Fin.lastCases (fun j => -a j) (fun i j => if i.succ = j then 1 else 0))

@[simp] private theorem companionMatrix_castSucc {K : Type u} [CommRing K] {n : ℕ}
    (a : Fin (n + 1) → K) (i : Fin n) (j : Fin (n + 1)) :
    companionMatrix a i.castSucc j = if i.succ = j then 1 else 0 := by
  simp [companionMatrix]

@[simp] private theorem companionMatrix_last {K : Type u} [CommRing K] {n : ℕ}
    (a : Fin (n + 1) → K) (j : Fin (n + 1)) :
    companionMatrix a (Fin.last n) j = -a j := by
  simp [companionMatrix]

/-- A column of the successive derivatives or iterates, starting with the element itself. -/
def scalarColumn {kind : OperatorKind} {S : Type v} [CommRing S] {n : ℕ}
    (E : Operator kind S) (x : S) (i : Fin n) : S :=
  (fun y => E y)^[i.val] x

/-- The monic scalar equation with lower coefficients indexed by increasing order. -/
def IsScalarSolution {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
    {S : Type v} [CommRing S] [Algebra K S]
    (a : Fin n → K) (E : Operator kind S) (x : S) : Prop :=
  (fun y => E y)^[n] x + ∑ i : Fin n, algebraMap K S (a i) * (fun y => E y)^[i.val] x = 0

/-- The differential system of a positive-order monic scalar equation. -/
def differentialCompanion {K : Type u} [Field K] {n : ℕ} (a : Fin (n + 1) → K) :
    LinearSystem .differential K (n + 1) :=
  differential (companionMatrix a)

theorem companionDeterminant {K : Type u} [CommRing K] {n : ℕ} (a : Fin (n + 1) → K) :
    (companionMatrix a).det = (-1 : K) ^ (n + 1) * a 0 := by
  -- The only surviving minor in the first-column expansion is the identity.
  have hminor : (companionMatrix a).submatrix Fin.castSucc Fin.succ =
      (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp [Matrix.one_apply, Fin.succ_inj]
  rw [Matrix.det_succ_column _ 0, Fin.sum_univ_castSucc]
  simp [hminor, pow_succ]

private theorem companion_det_ne_zero {K : Type u} [Field K] {n : ℕ} (a : Fin (n + 1) → K) :
    (companionMatrix a).det ≠ 0 ↔ a 0 ≠ 0 := by
  simp [companionDeterminant]

/-- The difference system exists when the coefficient of the zeroth iterate is nonzero. -/
def differenceCompanion {K : Type u} [Field K] {n : ℕ} (a : Fin (n + 1) → K)
    (ha : a 0 ≠ 0) : LinearSystem .difference K (n + 1) :=
  difference (GeneralLinearGroup.mkOfDetNeZero (companionMatrix a) ((companion_det_ne_zero a).2 ha))

@[simp] theorem coefficientMatrix_differenceCompanion {K : Type u} [Field K] {n : ℕ}
    (a : Fin (n + 1) → K) (ha : a 0 ≠ 0) :
    (differenceCompanion a ha).coefficientMatrix = companionMatrix a := rfl

theorem differenceCompanionExists {K : Type u} [Field K] {n : ℕ} (a : Fin (n + 1) → K) :
    (∃ A : LinearSystem .difference K (n + 1), A.coefficientMatrix = companionMatrix a) ↔
      a 0 ≠ 0 := by
  constructor
  · rintro ⟨A, hA⟩
    apply (companion_det_ne_zero a).mp
    rw [← hA]
    exact (show GL (Fin (n + 1)) K from A).det_ne_zero
  · intro ha
    exact ⟨differenceCompanion a ha, coefficientMatrix_differenceCompanion a ha⟩

variable {kind : OperatorKind} {K : Type u} [Field K] {n : ℕ}
  {S : Type v} [CommRing S] [Algebra K S]

private theorem isSolution_companion_iff (a : Fin (n + 1) → K) (E : Operator kind S)
    (A : LinearSystem kind K (n + 1)) (hA : A.coefficientMatrix = companionMatrix a)
    (w : Fin (n + 1) → S) :
    A.IsSolution E w ↔
      (∀ i : Fin n, E (w i.castSucc) = w i.succ) ∧
      E (w (Fin.last n)) + ∑ i, algebraMap K S (a i) * w i = 0 := by
  have hshift (i : Fin n) : (A.mapCoefficients S *ᵥ w) i.castSucc = w i.succ := by
    simp [mapCoefficients, hA, Matrix.mulVec, dotProduct, apply_ite, ite_mul]
  have hlast : (A.mapCoefficients S *ᵥ w) (Fin.last n) =
      - ∑ i, algebraMap K S (a i) * w i := by
    simp [mapCoefficients, hA, Matrix.mulVec, dotProduct, ← Finset.sum_neg_distrib]
  constructor
  · intro hw
    refine ⟨fun i => (congr_fun hw i.castSucc).trans (hshift i), ?_⟩
    rw [(congr_fun hw (Fin.last n)).trans hlast, neg_add_cancel]
  · rintro ⟨hs, hl⟩
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (eq_neg_of_add_eq_zero_left hl).trans hlast.symm
    · exact (hs j).trans (hshift j).symm

private theorem scalarColumn_succ (E : Operator kind S) (x : S) (i : Fin n) :
    scalarColumn E x i.succ = E (scalarColumn E x i.castSucc) := by
  simp only [scalarColumn, Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']

private theorem eq_scalarColumn_of_shift (E : Operator kind S) (w : Fin (n + 1) → S)
    (hw : ∀ i : Fin n, E (w i.castSucc) = w i.succ) :
    w = scalarColumn E (w 0) := by
  funext i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [← hw i, ih, scalarColumn_succ]

private theorem isScalarSolution_iff_last (a : Fin (n + 1) → K) (E : Operator kind S) (x : S) :
    IsScalarSolution a E x ↔
      E (scalarColumn E x (Fin.last n)) + ∑ i, algebraMap K S (a i) * scalarColumn E x i = 0 := by
  rw [IsScalarSolution, Function.iterate_succ_apply']
  rfl

/-- A positive-order scalar solution and its companion-system column determine one another. -/
def companionSolutionEquiv (E : Operator kind S) (a : Fin (n + 1) → K)
    (A : LinearSystem kind K (n + 1)) (hA : A.coefficientMatrix = companionMatrix a) :
    {x // IsScalarSolution a E x} ≃ A.Solution E where
  toFun x := ⟨scalarColumn E x.val, (isSolution_companion_iff a E A hA _).mpr
    ⟨fun i => (scalarColumn_succ E x.val i).symm,
      (isScalarSolution_iff_last a E x.val).mp x.property⟩⟩
  invFun w := ⟨w.val 0, by
    obtain ⟨hs, hl⟩ := (isSolution_companion_iff a E A hA w.val).mp w.property
    exact (isScalarSolution_iff_last a E _).mpr (by
      rw [eq_scalarColumn_of_shift E w.val hs] at hl
      exact hl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv w := Subtype.ext (eq_scalarColumn_of_shift E w.val
    ((isSolution_companion_iff a E A hA w.val).mp w.property).1).symm

theorem companionColumnEquivalence
    (D : OperatorField kind K) (_ : D.IsBaseField) (E : Operator kind S) (_ : D.IsExtension E)
    (a : Fin (n + 1) → K) (A : LinearSystem kind K (n + 1))
    (hA : A.coefficientMatrix = companionMatrix a) :
    ∃ e : {x // IsScalarSolution a E x} ≃ A.Solution E,
      (∀ x, (e x).val = scalarColumn E x.val) ∧ (∀ w, (e.symm w).val = w.val 0) :=
  ⟨companionSolutionEquiv E a A hA, fun _ => rfl, fun _ => rfl⟩

theorem orderZeroScalarSolutions (E : Operator kind S) (a : Fin 0 → K) (x : S) :
    IsScalarSolution a E x ↔ x = 0 := by
  simp [IsScalarSolution]

theorem orderZeroColumnEquivalence (E : Operator kind S) (a : Fin 0 → K)
    (A : LinearSystem kind K 0) :
    ∃ e : {x // IsScalarSolution a E x} ≃ A.Solution E,
      (∀ x, (e x).val = scalarColumn E x.val) ∧ (∀ w, (e.symm w).val = 0) := by
  let e : {x // IsScalarSolution a E x} ≃ A.Solution E :=
    { toFun := fun x => ⟨scalarColumn E x.val, Subsingleton.elim _ _⟩
      invFun := fun _ => ⟨0, (orderZeroScalarSolutions E a 0).mpr rfl⟩
      left_inv := fun x => Subtype.ext ((orderZeroScalarSolutions E a x.val).mp x.property).symm
      right_inv := fun w => Subtype.ext (Subsingleton.elim _ w.val) }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end Scalar
end LinearSystem
end GaloisFormalization.PV
