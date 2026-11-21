import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.AtomicIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
Atomic integrals, paper.tex:1703–1733. The upstream bridge identifies the
source's nonnegative integral with the library lower integral. Integration
commutes with measure sums and scalar multiplication, including infinite
scalars. The measurable Dirac formula then evaluates each summand without
any singleton-measurability assumption. No disjointness of the locations,
summability of the weights, or finiteness of the resulting measure is used.
-/

open Set MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace D11.Ch05.AtomicIntegrals

open NonnegativeIntegral

theorem dirac_integral : Specs.D11.Ch05.AtomicIntegrals.dirac_integral := by
  intro X _ p f hf
  change nonnegativeIntegral (Measure.dirac p) f = f p
  rw [integral_eq_lintegral]
  exact lintegral_dirac' p hf

theorem counting_integral : Specs.D11.Ch05.AtomicIntegrals.counting_integral := by
  intro X _ f
  let : MeasurableSpace X := ⊤
  change nonnegativeIntegral Measure.count f = ∑' x, f x
  rw [integral_eq_lintegral]
  exact lintegral_count' (measurable_of_countable f)

theorem atomic_integral : Specs.D11.Ch05.AtomicIntegrals.atomic_integral := by
  intro X _ p a f hf
  change nonnegativeIntegral (Measure.sum (fun n => a n • Measure.dirac (p n))) f = _
  rw [integral_eq_lintegral, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_dirac' (p n) hf, smul_eq_mul]

theorem atomic_integral_of_values :
    Specs.D11.Ch05.AtomicIntegrals.atomic_integral_of_values := by
  intro X _ μ p a f hf hμ
  have hmeasure : μ = Measure.sum (fun n => a n • Measure.dirac (p n)) := by
    apply Measure.ext
    intro E hE
    rw [hμ E hE, Measure.sum_apply _ hE]
    apply tsum_congr
    intro n
    rw [Measure.smul_apply, Measure.dirac_apply' (p n) hE, smul_eq_mul]
    rfl
  change nonnegativeIntegral μ f = _
  rw [hmeasure]
  exact atomic_integral p a f hf

end D11.Ch05.AtomicIntegrals
