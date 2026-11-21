import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.MonicCoordinate
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.Algebra.MvPolynomial.Nilpotent

namespace P103.Ch06.MonicCoordinate

open MvPolynomial

private lemma rotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := by
  exact finRotate_of_lt i.isLt

private lemma rotate_symm_zero (n : ℕ) :
    (finRotate (n + 1)).symm 0 = Fin.last n :=
  (finRotate (n + 1)).symm_apply_eq.mpr (finRotate_last (n := n)).symm

private lemma rotate_symm_succ {n : ℕ} (i : Fin n) :
    (finRotate (n + 1)).symm i.succ = i.castSucc :=
  (finRotate (n + 1)).symm_apply_eq.mpr (rotate_castSucc i).symm

/-- The separated polynomial variable is exactly the last source variable. -/
lemma lastVariableEquiv_X_last (k : Type*) [CommSemiring k] (n : ℕ) :
    Specs.lastVariableEquiv k n (X (Fin.last n)) = Polynomial.X := by
  simp only [Specs.lastVariableEquiv, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X, finRotate_last, finSuccEquiv_X_zero]

/-- The preceding source variables remain coefficient variables in their original order. -/
lemma lastVariableEquiv_X_castSucc (k : Type*) [CommSemiring k] {n : ℕ} (i : Fin n) :
    Specs.lastVariableEquiv k n (X i.castSucc) = Polynomial.C (X i) := by
  simp only [Specs.lastVariableEquiv, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X, rotate_castSucc, finSuccEquiv_X_succ]

/-- The two coordinate presentations agree on their scalar coefficients. -/
private lemma lastVariableEquiv_C {k : Type*} [Field k] (n : ℕ) (a : k) :
    Specs.lastVariableEquiv k n (C a) = Polynomial.C (C a) := by
  simp [Specs.lastVariableEquiv, finSuccEquiv_apply]

/-- Making a nonconstant polynomial monic, over any field. -/
theorem makingPolynomialMonic : Specs.makingPolynomialMonic := by
  intro k _ n f hf
  let e := renameEquiv k (finRotate (n + 1))
  let g := e f
  let τ := NoetherNormalization.varChange g
  let σ := (e.trans τ).trans e.symm
  let b := 2 + g.totalDegree
  have hg : g ≠ 0 := by
    intro h
    apply hf 0
    apply e.injective
    simpa [g] using h
  let p := finSuccEquiv k n (τ g)
  have hpunit : IsUnit p.leadingCoeff :=
    NoetherNormalization.varChange_leadingCoeff_isUnit g hg
  obtain ⟨a, ha, hpa⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hpunit
  have ha0 : a ≠ 0 := ha.ne_zero
  have hσlast : σ (X (Fin.last n)) = X (Fin.last n) := by
    simp [-finRotate_symm_apply, σ, e, τ, NoetherNormalization.varChange, NoetherNormalization.T1,
      rotate_symm_zero]
  have hσi (i : Fin n) :
      σ (X i.castSucc) = X i.castSucc + X (Fin.last n) ^ (b ^ (i.val + 1)) := by
    simp [-finRotate_symm_apply, σ, e, τ, b, NoetherNormalization.varChange, NoetherNormalization.T1,
      rotate_symm_zero, rotate_symm_succ]
  have hσinvlast : σ.symm (X (Fin.last n)) = X (Fin.last n) := by
    apply σ.injective
    simp [hσlast]
  have hσinvi (i : Fin n) :
      σ.symm (X i.castSucc) = X i.castSucc - X (Fin.last n) ^ (b ^ (i.val + 1)) := by
    apply σ.injective
    simp [hσi, hσlast]
  have hpview : Specs.lastVariableEquiv k n (σ f) = p := by
    simp [Specs.lastVariableEquiv, σ, p, g, e]
  have hscaled : Specs.lastVariableEquiv k n (a⁻¹ • σ f) =
      Polynomial.C (C a⁻¹) * p := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, lastVariableEquiv_C, hpview]
  have hmonic : (Polynomial.C (C a⁻¹) * p).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hpa,
      ← map_mul, inv_mul_cancel₀ ha0, map_one]
  have hpos : 0 < p.natDegree := by
    by_contra h
    have hz : p.natDegree = 0 := Nat.eq_zero_of_not_pos h
    have hpc : p = Polynomial.C (C a) := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hz] at hpa ⊢
      simpa using congrArg Polynomial.C hpa
    apply hf a
    apply σ.injective
    apply (Specs.lastVariableEquiv k n).injective
    rw [hpview]
    simpa only [show σ (C a) = C a from σ.commutes a, lastVariableEquiv_C] using hpc
  refine ⟨b, by dsimp [b]; omega, σ, a⁻¹, inv_ne_zero ha0,
    hσlast, hσi, hσinvlast, hσinvi, ?_, ?_⟩
  · rwa [hscaled]
  · rw [hscaled, Polynomial.natDegree_C_mul (by simpa using inv_ne_zero ha0)]
    exact hpos

/-- With one variable, scalar rescaling alone suffices. -/
theorem one_variable (k : Type*) [Field k] (f : MvPolynomial (Fin 1) k)
    (hf : ∀ a : k, f ≠ C a) :
    ∃ c : k, c ≠ 0 ∧ (Specs.lastVariableEquiv k 0 (c • f)).Monic ∧
      0 < (Specs.lastVariableEquiv k 0 (c • f)).natDegree := by
  obtain ⟨b, hb, σ, c, hc, hfix, _, _, _, hm, hd⟩ := makingPolynomialMonic k 0 f hf
  have hid : σ.toAlgHom = AlgHom.id k (MvPolynomial (Fin 1) k) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      have := i.isLt
      simp only [Fin.val_last]
      omega
    simpa only [hi, AlgEquiv.coe_toAlgHom, AlgHom.id_apply] using hfix
  have hσf : σ f = f := DFunLike.congr_fun hid f
  exact ⟨c, hc, hσf ▸ hm, hσf ▸ hd⟩

end P103.Ch06.MonicCoordinate
