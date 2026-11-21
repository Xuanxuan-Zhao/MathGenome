import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2InvariantForms
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2SimpleModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TensorDualHom
import Mathlib.Tactic.LinearCombination

/-! The antidiagonal form (3.9) on the standard modules of LA-C06.
We check invariance on e,f,h, then use h and f to classify all forms. -/

noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.Sl2InvariantForms
open Module
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
open Specs.LieAlgebrasAndRepresentations.Sl2InvariantForms

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
variable {n : ℕ} (b : Basis (Fin (n + 1)) k M)

def invariantForm (k : Type u) [Field k] (M : Type v) [AddCommGroup M] [Module k M]
    (n : ℕ) (b : Basis (Fin (n + 1)) k M) : LinearMap.BilinForm k M := form b

@[simp] theorem form_basis (i j : Fin (n + 1)) :
    form b (b i) (b j) = if i.val + j.val = n then (-1 : k)^i.val else 0 := by
  have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) k => A i j)
    (LinearMap.BilinForm.toMatrix_toBilin b
      (Matrix.of fun i j => if i.val + j.val = n then (-1 : k)^i.val else 0))
  simpa only [LinearMap.BilinForm.toMatrix_apply, form, Matrix.of_apply] using h

theorem entries_spec : entriesExpected.{u,v} := by
  intro k _ M _ _ n b i j
  exact form_basis b i j

/-- Antidiagonal evaluation reads a single coordinate. -/
theorem form_basis_right (i : Fin (n+1)) (v : M) :
    form b v (b i) = b.repr v ⟨n-i.val, by omega⟩ * (-1 : k)^(n-i.val) := by
  have hh (j : Fin (n+1)) : (j.val + i.val = n) ↔ j = (⟨n-i.val, Nat.lt_succ_of_le (Nat.sub_le n i.val)⟩ : Fin (n+1)) := by
    rw [Fin.ext_iff]
    simp only [Fin.val_mk]
    omega
  calc
    _ = ∑ j : Fin (n+1), b.repr v j * (if j.val+i.val=n then (-1:k)^j.val else 0) := by
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, form_basis]
    _ = _ := by simp_rw [hh, mul_ite, mul_zero]; simp

/-- The transpose likewise reads the opposite coordinate. -/
theorem form_basis_left (i : Fin (n+1)) (v : M) :
    form b (b i) v = (-1 : k)^i.val * b.repr v ⟨n-i.val, by omega⟩ := by
  have hh (j : Fin (n+1)) : (i.val + j.val = n) ↔ j = (⟨n-i.val, Nat.lt_succ_of_le (Nat.sub_le n i.val)⟩ : Fin (n+1)) := by
    rw [Fin.ext_iff]
    simp only [Fin.val_mk]
    omega
  calc
    _ = ∑ j : Fin (n+1), b.repr v j * (if i.val+j.val=n then (-1:k)^i.val else 0) := by
      conv_lhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul, smul_eq_mul, form_basis]
    _ = _ := by simp_rw [hh, mul_ite, mul_zero]; simp [mul_comm]

theorem form_nondegenerate : (form b).Nondegenerate := by
  constructor
  · intro v hv
    apply b.repr.injective
    ext i
    have h := hv (b ⟨n-i.val, by omega⟩)
    rw [form_basis_right] at h
    have hi : n - (n - i.val) = i.val := by omega
    simpa [hi] using (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · intro v hv
    apply b.repr.injective
    ext i
    have h := hv (b ⟨n-i.val, by omega⟩)
    rw [form_basis_left] at h
    have hi : n - (n - i.val) = i.val := by omega
    simpa [hi] using (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

theorem form_ne_zero : form b ≠ 0 := by
  intro h
  have hh := congrArg (fun B : LinearMap.BilinForm k M => B (b 0) (b ⟨n, by omega⟩)) h
  simp [form_basis] at hh

/-- Extending the basis by zero gives the same antidiagonal formula. -/
theorem form_vectors (i j : ℕ) :
    form b (basisVector b i) (basisVector b j) =
      if i+j=n then (-1 : k)^i else 0 := by
  by_cases hi : i < n+1
  · by_cases hj : j < n+1
    · simpa only [basisVector, dite_eq_left hi, dite_eq_left hj] using form_basis b ⟨i,hi⟩ ⟨j,hj⟩
    · have hn : i+j ≠ n := by omega
      simp [basisVector, hi, hj, hn]
  · have hn : i+j ≠ n := by omega
    simp [basisVector, hi, hn]

/-- Transposition introduces precisely the parity sign of the highest weight. -/
theorem form_transpose (v w : M) : form b w v = (-1:k)^n * form b v w := by
  have heq : (form b).flip = (-1:k)^n • form b := by
    apply LinearMap.ext_basis b b
    intro i j
    change form b (b j) (b i) = (-1:k)^n * form b (b i) (b j)
    rw [form_basis, form_basis]
    by_cases hij : i.val+j.val=n
    · rw [ite_eq_left hij, ite_eq_left (show j.val+i.val=n by omega)]
      have hpown : (-1:k)^n = (-1:k)^i.val * (-1:k)^j.val := by
        rw [← pow_add, hij]
      rw [hpown]
      have hp : (-1:k)^i.val * (-1:k)^i.val = 1 := by
        rw [← mul_pow]
        simp
      calc
        _ = 1 * (-1:k)^j.val := (one_mul _).symm
        _ = ((-1:k)^i.val * (-1:k)^i.val) * (-1:k)^j.val := by rw [hp]
        _ = _ := by ring
    · rw [ite_eq_right hij, ite_eq_right (show j.val+i.val≠n by omega), mul_zero]
  exact congrArg (fun B : LinearMap.BilinForm k M => B v w) heq

theorem form_symmetric (hn : Even n) : (form b).IsSymm := by
  refine ⟨fun v w => ?_⟩
  simpa only [hn.neg_one_pow, one_mul] using (form_transpose b w v)

theorem form_alternating [CharZero k] (hn : Odd n) : (form b).IsAlt := by
  intro v
  have h := form_transpose b v v
  rw [hn.neg_one_pow, neg_one_mul] at h
  have htwo : (2:k) * form b v v = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

variable [LieRingModule (Model k) M] [LieModule k (Model k) M]

/-- Invariance for one operator can be checked on a basis in both variables. -/
theorem invariant_operator (B : LinearMap.BilinForm k M) (x : Model k)
    (h : ∀ i j, B ⁅x, b i⁆ (b j) + B (b i) ⁅x, b j⁆ = 0) :
    ∀ v w, B ⁅x, v⁆ w + B v ⁅x, w⁆ = 0 := by
  have heq : B.compLeft (LieModule.toEnd k (Model k) M x) +
      B.compRight (LieModule.toEnd k (Model k) M x) = 0 := by
    apply LinearMap.ext_basis b b
    exact h
  intro v w
  exact congrArg (fun C : LinearMap.BilinForm k M => C v w) heq

theorem form_invariant [CharZero k] (hb : IsStandardBasis b) : Invariant (form b) := by
  have hh : ∀ v w, form b ⁅H k, v⁆ w + form b v ⁅H k, w⁆ = 0 := by
    apply invariant_operator b
    intro i j
    rw [(hb i).1, (hb j).1]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_basis]
    split_ifs with hij
    · have he : (i.val : k) + (j.val : k) = (n : k) := by exact_mod_cast hij
      linear_combination (-2 * (-1 : k)^i.val) * he
    · ring
  have hf : ∀ v w, form b ⁅F k, v⁆ w + form b v ⁅F k, w⁆ = 0 := by
    apply invariant_operator b
    intro i j
    rw [(hb i).2.1, (hb j).2.1]
    have hi : basisVector b i.val = b i := by simp [basisVector, i.isLt]
    have hj : basisVector b j.val = b j := by simp [basisVector, j.isLt]
    rw [← hi, ← hj, form_vectors, form_vectors]
    have he : (i.val+1+j.val=n) ↔ (i.val+(j.val+1)=n) := by omega
    simp only [he]
    split_ifs <;> simp [pow_succ]
  have he : ∀ v w, form b ⁅E k, v⁆ w + form b v ⁅E k, w⁆ = 0 := by
    apply invariant_operator b
    intro i j
    rw [(hb i).2.2, (hb j).2.2]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hi : basisVector b i.val = b i := by simp [basisVector, i.isLt]
    have hj : basisVector b j.val = b j := by simp [basisVector, j.isLt]
    rw [← hi, ← hj, form_vectors, form_vectors]
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · simp [hi0, hj0]
      · have hn : j.val-1 ≠ n := by omega
        simp [hi0, hn]
    by_cases hj0 : j.val = 0
    · have hn : i.val-1 ≠ n := by omega
      simp [hj0, hn]
    have ht : (i.val-1+j.val=n) ↔ (i.val+(j.val-1)=n) := by omega
    simp only [ht]
    split_ifs with hij
    · have hc : (i.val : k) + (j.val : k) = (n : k) + 1 := by
        exact_mod_cast (show i.val+j.val=n+1 by omega)
      have hp : (-1 : k)^i.val = -((-1 : k)^(i.val-1)) := by
        conv_lhs => rw [show i.val = (i.val-1)+1 by omega, pow_succ]
        ring
      rw [hp]
      linear_combination -((-1 : k)^(i.val-1) * ((i.val : k)-(j.val : k))) * hc
    · ring
  intro x v w
  rw [sl2_expansion k x]
  simp only [add_lie, smul_lie, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, sl2_e, sl2_f, sl2_h]
  linear_combination (x.val 0 1) * he v w + (x.val 1 0) * hf v w + (x.val 0 0) * hh v w

/-- The h-equation forces every invariant form to be antidiagonal. -/
theorem invariant_off_antidiagonal [CharZero k] (hb : IsStandardBasis b)
    (C : LinearMap.BilinForm k M) (hC : Invariant C)
    (i j : Fin (n+1)) (hij : i.val+j.val ≠ n) : C (b i) (b j) = 0 := by
  have h := hC (H k) (b i) (b j)
  rw [(hb i).1, (hb j).1] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hc : (n:k) - (i.val:k) - (j.val:k) ≠ 0 := by
    intro hc
    have hn : (i.val:k)+(j.val:k)=(n:k) := by linear_combination -hc
    exact hij (by exact_mod_cast hn)
  have he : (2 * ((n:k)-(i.val:k)-(j.val:k))) * C (b i) (b j) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hc)

/-- Moving f between the two arguments determines successive rows. -/
theorem invariant_entries [CharZero k] (hb : IsStandardBasis b)
    (C : LinearMap.BilinForm k M) (hC : Invariant C) :
    ∀ (i j : Fin (n+1)), C (b i) (b j) =
      C (b 0) (b ⟨n, by omega⟩) * (if i.val+j.val=n then (-1:k)^i.val else 0) := by
  have step : ∀ (a : ℕ) (ha : a < n+1) (j : Fin (n+1)),
      C (b ⟨a,ha⟩) (b j) =
        C (b 0) (b ⟨n, by omega⟩) * (if a+j.val=n then (-1:k)^a else 0) := by
    intro a
    induction a with
    | zero =>
      intro ha j
      by_cases hj : j.val=n
      · have hj' : j = ⟨n, by omega⟩ := Fin.ext hj
        rw [hj']
        simp
      · rw [invariant_off_antidiagonal b hb C hC _ _ (by simpa using hj)]
        simp [hj]
    | succ a ih =>
      intro ha j
      by_cases hj : j.val=n
      · rw [invariant_off_antidiagonal b hb C hC _ _ (by change a+1+j.val ≠ n; omega)]
        simp only [ite_eq_right (show a+1+j.val ≠ n by omega), mul_zero]
      · have h := hC (F k) (b ⟨a, by omega⟩) (b j)
        rw [(hb ⟨a, by omega⟩).2.1, (hb j).2.1] at h
        simp only [basisVector, dite_eq_left (show a+1<n+1 by omega),
          dite_eq_left (show j.val+1<n+1 by omega)] at h
        rw [ih (by omega) ⟨j.val+1, by omega⟩] at h
        have ht : (a+(j.val+1)=n) ↔ (a+1+j.val=n) := by omega
        simp only [ht] at h
        simp only [pow_succ]
        split_ifs with heq
        · rw [ite_eq_left heq] at h
          linear_combination h
        · rw [ite_eq_right heq, mul_zero, add_zero] at h
          simpa using h
  intro i j
  exact step i.val i.isLt j

theorem invariant_scalar [CharZero k] (hb : IsStandardBasis b)
    (C : LinearMap.BilinForm k M) (hC : Invariant C) :
    C = C (b 0) (b ⟨n, by omega⟩) • form b := by
  apply LinearMap.ext_basis b b
  intro i j
  simpa only [LinearMap.smul_apply, smul_eq_mul, form_basis] using
    invariant_entries b hb C hC i j

theorem uniqueness_spec : uniquenessExpected.{u,v} := by
  intro k _ _ _ M _ _ _ _ n b hb C hC
  refine ⟨C (b 0) (b ⟨n, by omega⟩), invariant_scalar b hb C hC, ?_⟩
  intro c hc
  have h := congrArg (fun B : LinearMap.BilinForm k M => B (b 0) (b ⟨n, by omega⟩)) hc
  simpa [form_basis] using h.symm

theorem properties_spec : propertiesExpected.{u,v} := by
  intro k _ _ _ M _ _ _ _ n b hb
  exact ⟨form_invariant b hb, form_nondegenerate b, form_ne_zero b,
    form_symmetric b, form_alternating b⟩

theorem nonzero_spec : nonzeroExpected.{u,v} := by
  intro k _ _ _ M _ _ _ _ n b hb C hC hC0
  obtain ⟨c, hc, _⟩ := uniqueness_spec k M n b hb C hC
  have hc0 : c ≠ 0 := by
    intro h
    apply hC0
    simpa [h] using hc
  refine ⟨?_, c, hc0, hc⟩
  rw [hc]
  constructor
  · intro v hv
    apply (form_nondegenerate b).1 v
    intro w
    have h := hv w
    change c * form b v w = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hc0
  · intro v hv
    apply (form_nondegenerate b).2 v
    intro w
    have h := hv w
    change c * form b w v = 0 at h
    exact (mul_eq_zero.mp h).resolve_left hc0

theorem selfDual_spec : selfDualExpected.{u,v} := by
  intro k _ _ _ M _ _ _ _ n b hb
  let : FiniteDimensional k M := Module.Finite.of_basis b
  let φ := (form b).toDual (form_nondegenerate b)
  refine ⟨{ φ with map_lie' := ?_ }, ?_⟩
  · intro x v
    ext w
    change form b ⁅x, v⁆ w = ⁅x, (form b) v⁆ w
    rw [Module.Dual.lie_apply]
    exact eq_neg_of_add_eq_zero_left (form_invariant b hb x v w)
  · intro v w
    rfl

theorem models_spec : Specs.LieAlgebrasAndRepresentations.Sl2InvariantForms.modelsExpected.{u} := by
  intro k _ _ _ n
  refine ⟨Sl2SimpleModules.standardLieRingModule k n,
    Sl2SimpleModules.standardLieModule k n, ?_⟩
  let b := Pi.basisFun k (Fin (n+1))
  have hb : IsStandardBasis b := Sl2SimpleModules.standardBasis_isStandard k n
  obtain ⟨hI, hN, h0, hS, hA⟩ := properties_spec k (Fin (n+1) → k) n b hb
  exact ⟨hb, hI, hN, h0, hS, hA,
    uniqueness_spec k (Fin (n+1) → k) n b hb,
    selfDual_spec k (Fin (n+1) → k) n b hb⟩

end LieAlgebrasAndRepresentations.Sl2InvariantForms
