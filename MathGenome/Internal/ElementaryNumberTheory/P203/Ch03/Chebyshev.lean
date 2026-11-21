import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Chebyshev
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.PrimeProduct

namespace P203.Chebyshev

open Filter Asymptotics
open P203Specs.Chebyshev

private theorem theta_eq (x : ℝ) :
    P203Specs.PrimeProduct.theta x = Chebyshev.theta x :=
  (P203.PrimeProduct.identifications x).2.1

private theorem psi_eq (x : ℝ) :
    P203Specs.PrimeProduct.psi x = Chebyshev.psi x :=
  (P203.PrimeProduct.identifications x).2.2.1

private theorem piCount_eq (x : ℝ) :
    P203Specs.PrimeProduct.piCount x = Nat.primeCounting ⌊x⌋₊ :=
  (P203.PrimeProduct.identifications x).2.2.2.2

theorem psiSubTheta : PsiSubTheta := by
  exact Chebyshev.isBigO_psi_sub_theta_sqrt.congr
    (fun x => by simp [theta_eq, psi_eq]) (fun _ => rfl)

/-- The linear lower bound follows from the explicit lower bound for psi,
a logarithmic error and the O(sqrt x) difference. -/
private theorem eventually_theta_lower :
    ∀ᶠ x : ℝ in atTop, (Real.log 2 / 2) * x ≤ Chebyshev.theta x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hs : Real.sqrt =o[atTop] (fun x : ℝ => x) := by
    apply isLittleO_of_tendsto' (Eventually.of_forall (fun x hx => by simp [hx]))
    exact Real.tendsto_sqrt_atTop.inv_tendsto_atTop.congr'
      (Eventually.of_forall (fun x => Real.sqrt_div_self.symm))
  have he : (fun x : ℝ => 2 * Real.log 2 + Real.log x + C * Real.sqrt x)
      =o[atTop] (fun x : ℝ => x) :=
    ((isLittleO_const_id_atTop (2 * Real.log 2)).add
      Real.isLittleO_log_id_atTop).add (hs.const_mul_left C)
  have hl : 0 < Real.log 2 / 2 := by positivity
  filter_upwards [he.bound hl, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hx0 : 0 ≤ x := by linarith
  have hlog : Real.log (x + 2) ≤ Real.log x + Real.log 2 := by
    calc
      Real.log (x + 2) ≤ Real.log (x * 2) :=
        Real.log_le_log (by linarith) (by linarith)
      _ = Real.log x + Real.log 2 := Real.log_mul (by linarith) (by norm_num)
  have hb : 2 * Real.log 2 + Real.log x + C * Real.sqrt x ≤
      (Real.log 2 / 2) * x := by
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx)
  have hp := Chebyshev.psi_ge' hx0
  have hd := hC x
  linarith

theorem thetaAsymp : ThetaAsymp := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp eventually_theta_lower
  refine ⟨Real.log 2 / 2, Real.log 4, by positivity, by positivity,
    max X 0, ?_⟩
  intro x hx
  rw [theta_eq]
  exact ⟨hX x (le_trans (le_max_left _ _) hx),
    Chebyshev.theta_le_log4_mul_x (le_trans (le_max_right _ _) hx)⟩

theorem psiAsymp : PsiAsymp := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp eventually_theta_lower
  refine ⟨Real.log 2 / 2, Real.log 4 + 4, by positivity, by positivity,
    max X 0, ?_⟩
  intro x hx
  rw [psi_eq]
  exact ⟨(hX x (le_trans (le_max_left _ _) hx)).trans (Chebyshev.theta_le_psi x),
    Chebyshev.psi_le_const_mul_self (le_trans (le_max_right _ _) hx)⟩

theorem piCountAsymp : PiCountAsymp := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (eventually_theta_lower.and (Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one))
  refine ⟨Real.log 2 / 2, Real.log 4 + 1, by positivity, by positivity,
    max X 2, ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨hl, hu⟩ := hX x (le_trans (le_max_left _ _) hx)
  dsimp only
  rw [piCount_eq]
  constructor
  · have h := hl.trans (Chebyshev.theta_le_pi_mul_log' x)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hlog).mpr h
  · simpa only [mul_div_assoc] using hu

end P203.Chebyshev
