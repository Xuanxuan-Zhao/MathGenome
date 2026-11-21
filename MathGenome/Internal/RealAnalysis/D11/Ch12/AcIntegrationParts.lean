import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcIntegrationParts
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcFtc
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcBasic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace D11.Ch12.AcIntegrationParts

/-- The product rule is used only at the common a.e. differentiability points.
The FTC is applied to the AC product, without any everywhere differentiability
assumption or any assumed integral reconstruction. -/
lemma parts_of_ftc {K : Type*} [RCLike K]
    (hftc : Specs.D11.Ch12.AcFtc.ftc_statement K) :
    Specs.D11.Ch12.AcIntegrationParts.bilinear_statement K := by
  intro F G a b hab hF hG
  obtain ⟨hdF, hiF, _⟩ := ((hftc F hab).2.1).mp hF
  obtain ⟨hdG, hiG, _⟩ := ((hftc G hab).2.1).mp hG
  have hcF : ContinuousOn F (uIcc a b) := by
    simpa [uIcc_of_le hab.le] using (AcBasic.uniformContinuousOn hab.le hF).continuousOn
  have hcG : ContinuousOn G (uIcc a b) := by
    simpa [uIcc_of_le hab.le] using (AcBasic.uniformContinuousOn hab.le hG).continuousOn
  have hif : IntervalIntegrable (deriv F) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hiF
  have hig : IntervalIntegrable (deriv G) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hiG
  have hiFG := hif.mul_continuousOn hcG
  have hiGF := hig.continuousOn_mul hcF
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hiFG,
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hiGF, ?_⟩
  have hprod := AcBasic.mul hab.le hF hG
  have hr := (((hftc (fun x => F x * G x) hab).2.1).mp hprod).2.2 b
    (right_mem_Icc.mpr hab.le)
  have heq : (∫ x in a..b, deriv (fun y => F y * G y) x) =
      ∫ x in a..b, deriv F x * G x + F x * deriv G x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdF, hdG, volume.ae_ne b] with x hxF hxG hxb hx
    rw [uIoc_of_le hab.le] at hx
    have hxi : x ∈ Ioo a b := ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩
    exact ((hxF hxi).mul (hxG hxi)).deriv
  rw [heq, intervalIntegral.integral_add hiFG hiGF] at hr
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hr.symm))

theorem real_parts : Specs.D11.Ch12.AcIntegrationParts.real_parts :=
  parts_of_ftc AcFtc.ftc_real

theorem complex_parts : Specs.D11.Ch12.AcIntegrationParts.complex_parts :=
  parts_of_ftc AcFtc.ftc_complex

/-- Conjugation preserves exactly the shared disjoint-interval AC condition. -/
lemma conjugate_ac {G : ℝ → ℂ} {a b : ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (fun x => conj (G x)) a b := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hG ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n u v huv hends hdis hlen
  simpa only [← map_sub, RCLike.norm_conj] using hh n u v huv hends hdis hlen

theorem sesquilinear_parts : Specs.D11.Ch12.AcIntegrationParts.sesquilinear_parts := by
  intro F G a b hab hF hG
  have h := complex_parts F (fun x => conj (G x)) hab hF (conjugate_ac hG)
  simpa only [show (deriv fun x => conj (G x)) = (fun x => conj (deriv G x)) from
    funext fun x => deriv.star] using h

end D11.Ch12.AcIntegrationParts
