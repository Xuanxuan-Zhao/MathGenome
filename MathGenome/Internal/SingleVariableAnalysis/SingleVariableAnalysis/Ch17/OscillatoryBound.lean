import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.OscillatoryBound
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Euler
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import Batteries.Tactic.OpenPrivate

noncomputable section
namespace SingleVariableAnalysis.Riemann
open Set
open private parts_continuous_complex_integrable parts_c1_derivative
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts

theorem oscillatory_phase_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch17.OscillatoryBound.phaseDerivative := by
  intro lam x
  have hd := expSeries_real_parameter_hasDerivAt (Complex.I * (lam : ℂ)) x
  change HasDerivAt (fun t : ℝ => seriesExp ((t : ℂ) * (Complex.I * (lam : ℂ))))
    (Complex.I * (lam : ℂ) * seriesExp ((x : ℂ) * (Complex.I * (lam : ℂ)))) x at hd
  have hexp (z : ℂ) : seriesExp z = Complex.exp z := expSeries_eq_complexExp z
  simpa only [hexp, mul_comm, mul_left_comm, mul_assoc] using hd

private theorem phase_norm (lam x : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))‖ = 1 := by
  rw [mul_assoc, ← Complex.ofReal_mul]
  rw [← expSeries_eq_complexExp]
  exact expSeries_imaginary_norm (lam * x)

/-- Integral values agree under equality of functions, including their proof arguments. -/
private theorem complexIntegral_congr {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) (hfg : f = g) :
    complexIntegral f hf = complexIntegral g hg := by
  subst g
  rfl

private theorem realIntegral_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) (hfg : f = g) :
    realIntegral f hf = realIntegral g hg := by
  subst g
  rfl

theorem oscillatory_integral_bound :
    Specs.SingleVariableAnalysis.Ch17.OscillatoryBound.oscillatoryBound := by
  intro h a b lam hab hh hlam
  let e : ℝ → ℂ := fun x => Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))
  let c : ℂ := Complex.I * (lam : ℂ)
  let dh := derivWithin h (Icc a b)
  have he (x : ℝ) : ‖e x‖ = 1 := phase_norm lam x
  have hed (x : ℝ) : HasDerivAt e (c * e x) x :=
    oscillatory_phase_hasDerivAt lam x
  have hec : ContinuousOn e (Icc a b) := (continuous_iff_continuousAt.mpr
    (fun x => (hed x).continuousAt)).continuousOn
  obtain ⟨hdc, hdd⟩ := parts_c1_derivative hab hh
  have hdi := parts_continuous_complex_integrable hab hdc
  have hei := parts_continuous_complex_integrable hab hec
  have hi := parts_continuous_complex_integrable hab (hh.continuousOn.mul hec)
  obtain ⟨hdvi, _⟩ := complex_mul_value hei c
  obtain ⟨hci, hcval⟩ := complex_mul_value hi c
  obtain ⟨h₁, h₂, hparts⟩ := complex_parts h e dh (fun x => c * e x)
    a b hab hh.continuousOn hec hdd (fun x _ => hed x) hdi hdvi
  change complexIntegral _ h₁ = h b * e b - h a * e a - complexIntegral _ h₂ at hparts
  have hfun : (fun x => h x * (c * e x)) = (fun x => c * (h x * e x)) := by
    funext x; ring
  have hvalue : complexIntegral _ h₁ = c * complexIntegral _ hi := by
    exact (complexIntegral_congr h₁ hci hfun).trans hcval
  have hnormfun : (fun x => ‖dh x * e x‖) = (fun x => ‖dh x‖) := by
    funext x; simp only [norm_mul, he, mul_one]
  obtain ⟨hn₀, hnorm₀, _⟩ := complex_norm_estimate (fun x => dh x * e x) h₂
  have hn : RealIntegrable (fun x => ‖dh x‖) a b := hnormfun ▸ hn₀
  have hnorm : ‖complexIntegral _ h₂‖ ≤ realIntegral _ hn :=
    hnorm₀.trans_eq (realIntegral_congr hn₀ hn hnormfun)
  refine ⟨hdi, hi, hn, ?_⟩
  have hcnorm : ‖c‖ = |lam| := by simp [c, Complex.norm_real]
  have hbound : |lam| * ‖complexIntegral _ hi‖ ≤
      ‖h a‖ + ‖h b‖ + realIntegral _ hn := by
    calc
      _ = ‖complexIntegral _ h₁‖ := by rw [hvalue, norm_mul, hcnorm]
      _ = ‖h b * e b - h a * e a - complexIntegral _ h₂‖ := by rw [hparts]
      _ ≤ ‖h b * e b - h a * e a‖ + ‖complexIntegral _ h₂‖ := norm_sub_le _ _
      _ ≤ (‖h b * e b‖ + ‖h a * e a‖) + realIntegral _ hn :=
        add_le_add (norm_sub_le _ _) hnorm
      _ = _ := by simp only [norm_mul, he, mul_one]; ring
  apply (le_div_iff₀ (abs_pos.mpr hlam)).mpr
  change ‖complexIntegral _ hi‖ * |lam| ≤ ‖h a‖ + ‖h b‖ + realIntegral _ hn
  exact (mul_comm _ _).le.trans hbound

end SingleVariableAnalysis.Riemann
