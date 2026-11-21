import MathGenome.Internal.Specs.D07.Ch07.IntegerPresentationsSmithBridge
import MathGenome.Internal.D07.Ch16.IntegerPresentationCokernel
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.Basis

namespace D07.Ch07.IntegerPresentationsSmithBridge
open Module
open scoped DirectSum

/-- Rescale the nonzero source basis vectors by integer units, making all
diagonal entries positive. The target basis is unchanged. -/
theorem positiveSourceBasis {m n r k t : ℕ}
    (A : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (b : Basis (Fin r ⊕ Fin k) ℤ (Fin m → ℤ))
    (e : Basis (Fin r ⊕ Fin t) ℤ (Fin n → ℤ)) (a : Fin r → ℤ)
    (ha : ∀ i, A (b (Sum.inl i)) = a i • e (Sum.inl i))
    (hz : ∀ j, A (b (Sum.inr j)) = 0) :
    ∃ b' : Basis (Fin r ⊕ Fin k) ℤ (Fin m → ℤ),
      (∀ i, A (b' (Sum.inl i)) = ((a i).natAbs : ℤ) • e (Sum.inl i)) ∧
      (∀ j, A (b' (Sum.inr j)) = 0) := by
  classical
  let u : (Fin r ⊕ Fin k) → ℤˣ :=
    Sum.elim (fun i => if a i < 0 then -1 else 1) (fun _ => 1)
  refine ⟨b.unitsSMul u, ?_, ?_⟩
  · intro i
    simp only [Basis.unitsSMul_apply, Units.smul_def, map_smul, ha, smul_smul]
    change (((if a i < 0 then (-1 : ℤˣ) else 1 : ℤˣ) : ℤ) * a i) • _ = _
    split_ifs with h
    · simp only [Units.val_neg, Units.val_one, neg_mul, one_mul]
      rw [Int.natCast_natAbs, abs_of_neg h]
    · simp only [Units.val_one, one_mul]
      rw [Int.natCast_natAbs, abs_of_nonneg (le_of_not_gt h)]
  · intro j
    simp [Basis.unitsSMul_apply, hz, u]

/-- Integral bases give unimodular matrices in the original finite ranks. -/
theorem matricesOfDiagonalBases {r k t : ℕ}
    (B : Matrix (Fin (r + t)) (Fin (r + k)) ℤ)
    (b : Basis (Fin r ⊕ Fin k) ℤ (Fin (r + k) → ℤ))
    (e : Basis (Fin r ⊕ Fin t) ℤ (Fin (r + t) → ℤ)) (d : Fin r → ℕ)
    (ha : ∀ i, B.mulVecLin (b (Sum.inl i)) = (d i : ℤ) • e (Sum.inl i))
    (hz : ∀ j, B.mulVecLin (b (Sum.inr j)) = 0) :
    ∃ (P : Matrix (Fin (r + t)) (Fin (r + t)) ℤ)
      (Q : Matrix (Fin (r + k)) (Fin (r + k)) ℤ),
      IsUnit P ∧ IsUnit Q ∧
      (∀ i j, (P * B * Q) i j =
        if h : i.val = j.val ∧ i.val < r then (d ⟨i.val, h.2⟩ : ℤ) else 0) := by
  classical
  let b' := b.reindex finSumFinEquiv
  let e' := e.reindex finSumFinEquiv
  let bm := Pi.basisFun ℤ (Fin (r + k))
  let bn := Pi.basisFun ℤ (Fin (r + t))
  let P := e'.toMatrix bn
  let Q := bm.toMatrix b'
  have hP : IsUnit P := IsUnit.of_mul_eq_one (bn.toMatrix e')
    (e'.toMatrix_mul_toMatrix_flip bn)
  have hQ : IsUnit Q := IsUnit.of_mul_eq_one (b'.toMatrix bm)
    (bm.toMatrix_mul_toMatrix_flip b')
  refine ⟨P, Q, hP, hQ, ?_⟩
  have hmat : P * B * Q = LinearMap.toMatrix b' e' B.mulVecLin := by
    have hB : LinearMap.toMatrix bm bn B.mulVecLin = B := by
      ext i j
      simp [LinearMap.toMatrix_apply, bm, bn, Pi.basisFun_apply]
    calc
      P * B * Q = P * LinearMap.toMatrix bm bn B.mulVecLin * Q := by rw [hB]
      _ = _ := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' bm e' bn _
  intro i j
  rw [hmat, LinearMap.toMatrix_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [b', e', Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
      ha, Basis.repr_reindex_apply, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Sum.inl.injEq, smul_eq_mul]
    by_cases hij : i = j
    · subst j; simp
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [Ne.symm hij, hv]
  · have hv : i.val ≠ r + j.val := by omega
    simp [b', e', Basis.reindex_apply, hz, hv]
  · simp only [b', e', Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, ha, Basis.repr_reindex_apply, map_smul,
      Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, Sum.inl_ne_inr,
      ite_false, smul_zero]
    simp
  · simp [b', e', Basis.reindex_apply, hz]

theorem integerPresentationSmithBridge :
    Specs.D07.Ch07.IntegerPresentationsSmithBridge.IntegerPresentationSmithBridge := by
  intro m n B
  classical
  obtain ⟨r, k, t, b, e, a, hm, hn, hne, hchain, hb, he, ⟨E⟩, _⟩ :=
    D07.Ch16.Smith.smithDecomposition ℤ m n B.mulVecLin
  let d : Fin r → ℕ := fun i => (a i).natAbs
  have hd : ∀ i, 0 < d i := fun i => Int.natAbs_pos.mpr (hne i)
  have hdc : ∀ i j, i ≤ j → d i ∣ d j := fun i j hij =>
    Int.natAbs_dvd_natAbs.mpr (hchain i j hij)
  obtain ⟨b', hb', hz'⟩ := positiveSourceBasis B.mulVecLin b e a hb he
  subst m
  subst n
  obtain ⟨P, Q, hP, hQ, hdiag⟩ := matricesOfDiagonalBases B b' e d (by
    exact hb') hz'
  let Z : (∀ i : Fin r, ℤ ⧸ Ideal.span {a i}) ≃ₗ[ℤ]
      (∀ i : Fin r, ZMod (d i)) :=
    (AddEquiv.piCongrRight fun i => (Int.quotientSpanEquivZMod (a i)).toAddEquiv).toIntLinearEquiv
  let F := E.trans ((LinearEquiv.refl ℤ (Fin t → ℤ)).prodCongr Z)
  have ht : r + t - r = t := by omega
  obtain ⟨U, _⟩ := D07.Ch16.IntegerPresentationCokernel.unitFactorDeletion r d
  refine ⟨r, d, P, Q, by omega, by omega, hd, hdc, hP, hQ,
    Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp hP),
    Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp hQ), hdiag, ?_⟩
  rw [ht]
  exact ⟨⟨F⟩, ⟨F.trans ((LinearEquiv.refl ℤ _).prodCongr
    (DirectSum.linearEquivFunOnFintype ℤ (Fin r) (fun i => ZMod (d i))).symm)⟩,
    ⟨F.trans ((LinearEquiv.refl ℤ _).prodCongr U)⟩⟩

theorem unitFactorZero : Specs.D07.Ch07.IntegerPresentationsSmithBridge.UnitFactorZero :=
  D07.Ch16.IntegerPresentationCokernel.unitFactorZero

end D07.Ch07.IntegerPresentationsSmithBridge
