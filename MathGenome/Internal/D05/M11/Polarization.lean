import MathGenome.Internal.D05.M11.SymmetricQuadratic
import MathGenome.Internal.Specs.D05.M11.Polarization
import Mathlib.Tactic.Ring

/-! K05.11.polarization: inverse diagonal/polar constructions and weak homogeneity. -/

namespace D05.M11.Polarization

/-- Half of the upstream full polar form; its bilinearity is part of its type. -/
def polarForm {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : LinearMap.BilinForm K V :=
  (2 : K)⁻¹ • Q.polarBilin

theorem polarForm_apply : Specs.D05.M11.Polarization.polarForm_apply := by
  intro K V _ _ _ Q x y
  change (2 : K)⁻¹ * (Q (x + y) - Q x - Q y) = _
  rw [div_eq_mul_inv, mul_comm]

theorem polarForm_symmetric : Specs.D05.M11.Polarization.polarForm_symmetric := by
  intro K V _ _ _ Q
  refine ⟨fun x y => ?_⟩
  change (2 : K)⁻¹ * QuadraticMap.polar Q x y =
    (2 : K)⁻¹ * QuadraticMap.polar Q y x
  rw [QuadraticMap.polar_comm Q x y]

theorem polarization_formula : Specs.D05.M11.Polarization.polarization_formula := by
  intro K V _ _ _ hTwo B hB x y
  have hpol := SymmetricQuadratic.diagonal_polar B x y
  change B (x + y) (x + y) - B x x - B y y = B x y + B y x at hpol
  rw [hpol, ← hB.eq x y]
  apply (eq_div_iff hTwo).2
  ring

theorem diagonal_polarForm : Specs.D05.M11.Polarization.diagonal_polarForm := by
  intro K V _ _ _ hTwo Q
  apply QuadraticMap.ext
  intro x
  change (2 : K)⁻¹ * QuadraticMap.polar Q x x = Q x
  rw [QuadraticMap.polar_self, two_smul, ← two_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hTwo, one_mul]

theorem polarForm_diagonal : Specs.D05.M11.Polarization.polarForm_diagonal := by
  intro K V _ _ _ hTwo B hB
  apply LinearMap.ext₂
  intro x y
  rw [polarForm_apply]
  exact (polarization_formula hTwo B hB x y).symm

theorem exists_unique_symmetric : Specs.D05.M11.Polarization.exists_unique_symmetric := by
  intro K V _ _ _ hTwo Q
  refine ⟨polarForm Q, ⟨polarForm_symmetric Q, ?_⟩, ?_⟩
  · intro x
    exact congrArg (fun R : QuadraticForm K V => R x) (diagonal_polarForm hTwo Q)
  · rintro B ⟨hB, hdiag⟩
    have hQ : Specs.D05.M11.SymmetricQuadratic.diagonal_value B = Q :=
      QuadraticMap.ext hdiag
    calc
      B = polarForm (Specs.D05.M11.SymmetricQuadratic.diagonal_value B) :=
        (polarForm_diagonal hTwo B hB).symm
      _ = polarForm Q := congrArg polarForm hQ

theorem weak_polarization : Specs.D05.M11.Polarization.weak_polarization := by
  intro K V _ _ _ hTwo q P hP hDouble
  have hdiag : ∀ x, ((2 : K)⁻¹ • P) x x = q x := by
    intro x
    change (2 : K)⁻¹ * P x x = q x
    rw [hP, ← two_smul K x, hDouble]
    have hcalc : (4 : K) * q x - q x - q x = 2 * q x := by ring
    rw [hcalc, ← mul_assoc, inv_mul_cancel₀ hTwo, one_mul]
  refine ⟨⟨fun x y => ?_⟩, hdiag, ?_⟩
  · change (2 : K)⁻¹ * P x y = (2 : K)⁻¹ * P y x
    rw [hP, hP, add_comm y x]
    ring
  · intro a x
    calc
      q (a • x) = ((2 : K)⁻¹ • P).toQuadraticMap (a • x) := (hdiag _).symm
      _ = a ^ 2 * ((2 : K)⁻¹ • P).toQuadraticMap x := by
        simpa only [pow_two, smul_eq_mul] using
          ((2 : K)⁻¹ • P).toQuadraticMap.map_smul a x
      _ = a ^ 2 * q x := by rw [LinearMap.BilinMap.toQuadraticMap_apply, hdiag]

theorem quadratic_iff_weak_axioms :
    Specs.D05.M11.Polarization.quadratic_iff_weak_axioms := by
  intro K V _ _ _ hTwo q
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨?_, Q.polarBilin, ?_⟩
    · intro x
      have h := Q.map_smul (2 : K) x
      simpa only [hQ, smul_eq_mul, show (2 : K) * 2 = 4 by ring] using h
    · intro x y
      change Q (x + y) - Q x - Q y = _
      rw [hQ, hQ, hQ]
  · rintro ⟨hDouble, P, hP⟩
    exact ⟨((2 : K)⁻¹ • P).toQuadraticMap,
      (weak_polarization hTwo q P hP hDouble).2.1⟩

end D05.M11.Polarization
