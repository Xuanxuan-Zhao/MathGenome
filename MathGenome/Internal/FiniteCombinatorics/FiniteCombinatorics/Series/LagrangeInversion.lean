import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.LagrangeInversion
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.LagrangeSolution
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.LaurentResidueSubstitution

/-!
Lagrange–Bürmann inversion, paper.tex, p204:W18. We apply the accepted
Laurent change of variable theorem to X^(-n) (H(F))′ under g = X/φ.
The chain rule and F(g) = X reduce the transformed residue to the
coefficient of degree n-1 of H′ φ^n. Division by n takes place in ℚ,
then passes through the algebra map, so no domain hypothesis is needed.
-/

noncomputable section
universe u
namespace FiniteCombinatorics.Series
variable {R : Type u} [CommRing R]

/-- Reading an ordinary coefficient as a Laurent residue. -/
theorem residue_shift_coefficient (A : PowerSeries R) (m : ℕ) :
    Laurent.residue (HahnSeries.single (-((m+1 : ℕ) : ℤ)) 1 *
      (A : LaurentSeries R)) = PowerSeries.coeff m A := by
  unfold Laurent.residue Specs.FiniteCombinatorics.Series.LaurentResidueSubstitution.residueValue
  rw [HahnSeries.coeff_single_mul, one_mul]
  have h : (-1 : ℤ) - -((m+1 : ℕ) : ℤ) = (m : ℤ) := by omega
  rw [h, LaurentSeries.coeff_coe_powerSeries]

/-- The negative powers of X/V have unit part V to the positive power. -/
theorem power_inverse_unit_neg_nat (V : (PowerSeries R)ˣ) (n : ℕ) :
    Laurent.power V⁻¹ (-(n : ℤ)) =
      HahnSeries.single (-(n : ℤ)) 1 *
        (((V : PowerSeries R)^n : PowerSeries R) : LaurentSeries R) := by
  simp [Laurent.power, Specs.FiniteCombinatorics.Series.LaurentResidueSubstitution.powerValue]

/-- The residue computation for a zero-constant inverse of X/V. -/
theorem lagrange_inversion_mul_succ [Algebra ℚ R]
    (V : (PowerSeries R)ˣ) (H F : PowerSeries R)
    (hF : PowerSeries.constantCoeff F = 0)
    (hFg : compose F (PowerSeries.X * (↑V⁻¹ : PowerSeries R)) = PowerSeries.X)
    (m : ℕ) :
    (m+1 : R) * PowerSeries.coeff (m+1) (compose H F) =
      PowerSeries.coeff m (PowerSeries.derivative H * (V : PowerSeries R)^(m+1)) := by
  let g : PowerSeries R := PowerSeries.X * (↑V⁻¹ : PowerSeries R)
  have hg : PowerSeries.constantCoeff g = 0 := by simp [g]
  have hchain : compose (PowerSeries.derivative F) g * PowerSeries.derivative g = 1 := by
    rw [← derivative_compose F g hg, hFg, PowerSeries.derivative_X]
  let A : PowerSeries R := PowerSeries.derivative (compose H F)
  let L : LaurentSeries R :=
    HahnSeries.single (-((m+1 : ℕ) : ℤ)) 1 * (A : LaurentSeries R)
  have hsub := Laurent.residue_substitution L V⁻¹
  have hcomp : compose A g * PowerSeries.derivative g = PowerSeries.derivative H := by
    dsimp [A]
    rw [derivative_compose H F hF, compose_mul _ _ g hg,
      compose_assoc _ F g hF hg, hFg, compose_X, mul_assoc, hchain, mul_one]
  have htrans : Laurent.compose L V⁻¹ *
      ((PowerSeries.derivative g) : LaurentSeries R) =
      HahnSeries.single (-((m+1 : ℕ) : ℤ)) 1 *
        ((PowerSeries.derivative H * (V : PowerSeries R)^(m+1) : PowerSeries R) :
          LaurentSeries R) := by
    change Laurent.compose (HahnSeries.single (-((m+1 : ℕ) : ℤ)) 1 *
      (A : LaurentSeries R)) V⁻¹ * ((PowerSeries.derivative g) : LaurentSeries R) = _
    rw [Laurent.compose_shift, Laurent.compose_powerSeries, power_inverse_unit_neg_nat V (m+1)]
    change (HahnSeries.single (-((m+1 : ℕ) : ℤ)) 1 *
      (((V : PowerSeries R)^(m+1) : PowerSeries R) : LaurentSeries R)) *
      ((compose A g) : LaurentSeries R) *
      ((PowerSeries.derivative g) : LaurentSeries R) = _
    rw [mul_assoc, mul_assoc, ← PowerSeries.coe_mul, hcomp]
    rw [← PowerSeries.coe_mul, mul_comm ((V : PowerSeries R)^(m+1))]
  change Laurent.residue (Laurent.compose L V⁻¹ *
    ((PowerSeries.derivative g) : LaurentSeries R)) = Laurent.residue L at hsub
  rw [htrans, residue_shift_coefficient] at hsub
  have hres : Laurent.residue L =
      (m+1 : R) * PowerSeries.coeff (m+1) (compose H F) := by
    rw [show L = HahnSeries.single (-((m+1 : ℕ) : ℤ)) 1 * (A : LaurentSeries R) from rfl,
      residue_shift_coefficient]
    exact FiniteCombinatorics.Series.coeff_derivative _ m
  exact hres.symm.trans hsub.symm

/-- Lagrange–Bürmann for the canonical solution, in every commutative ℚ-algebra. -/
theorem lagrange_inversion_canonical [Algebra ℚ R]
    (φ H : PowerSeries R) (a₀ : Rˣ)
    (hφ : PowerSeries.constantCoeff φ = (a₀ : R)) (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (compose H (lagrangeSolution φ a₀)) =
      algebraMap ℚ R ((n : ℚ)⁻¹) *
        PowerSeries.coeff (n-1) (PowerSeries.derivative H * φ^n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let V : (PowerSeries R)ˣ :=
    ⟨φ, PowerSeries.invOfUnit φ a₀,
      PowerSeries.mul_invOfUnit φ a₀ hφ, PowerSeries.invOfUnit_mul φ a₀ hφ⟩
  have hc := lagrange_inversion_mul_succ V H (lagrangeSolution φ a₀)
    (lagrange_solution_properties φ a₀ hφ).1 (lagrange_inverse_relations φ a₀ hφ).2 m
  have hi : algebraMap ℚ R ((m+1 : ℚ)⁻¹) * (m+1 : R) = 1 := by
    rw [show (m+1 : R) = algebraMap ℚ R (m+1 : ℚ) by simp,
      ← map_mul, inv_mul_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero m)), map_one]
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  change PowerSeries.coeff (m+1) (compose H (lagrangeSolution φ a₀)) =
    algebraMap ℚ R ((m+1 : ℚ)⁻¹) *
      PowerSeries.coeff m (PowerSeries.derivative H * φ^(m+1))
  calc
    _ = (algebraMap ℚ R ((m+1 : ℚ)⁻¹) * (m+1 : R)) *
        PowerSeries.coeff (m+1) (compose H (lagrangeSolution φ a₀)) := by rw [hi, one_mul]
    _ = _ := by rw [mul_assoc, hc]

/-- The full coefficient formula for every zero-constant solution of F = X φ(F). -/
theorem lagrange_inversion [Algebra ℚ R] (φ H F : PowerSeries R)
    (hφ : IsUnit (PowerSeries.constantCoeff φ))
    (hF : PowerSeries.constantCoeff F = 0)
    (heq : F = PowerSeries.X * compose φ F) (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n (compose H F) =
      algebraMap ℚ R ((n : ℚ)⁻¹) *
        PowerSeries.coeff (n-1) (PowerSeries.derivative H * φ^n) := by
  have hφ' : PowerSeries.constantCoeff φ = (hφ.unit : R) := hφ.unit_spec.symm
  rw [lagrange_solution_unique φ hφ.unit hφ' F hF heq]
  exact lagrange_inversion_canonical φ H hφ.unit hφ' n hn

end FiniteCombinatorics.Series
