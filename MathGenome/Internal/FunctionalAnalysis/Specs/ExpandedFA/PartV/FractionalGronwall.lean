import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeakVolterraResolvent

/-! Fractional comparison on every finite closed interval, including T = 0.
The fractional integral and Mittag--Leffler terms are the shared, normalized
objects. No smallness hypothesis or assumed convergence certificate is used. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ExpandedFA.PartV.FractionalGronwall.Spec
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.WeakVolterraResolvent.Spec

/-- The real Mittag--Leffler function, with the n=0 term equal to one at zero. -/
def mittagLeffler (α x : ℝ) : ℝ :=
  ∑' n : ℕ, x^n / Real.Gamma ((n : ℝ)*α+1)

/-- The explicit Gamma-denominator bound for the iteration remainder vanishes
for every b and every finite interval; convergence is uniform in time. -/
def GammaRemainder : Prop := ∀ (α b T C : ℝ),
  0 < α → 0 ≤ b → 0 ≤ T →
  TendstoUniformly
    (fun (n : ℕ) (t : Icc (0 : ℝ) T) =>
      C * (b^n * (t : ℝ)^((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1)))
    (fun _ => 0) atTop

/-- The finite iteration inequality and its nonnegative, explicitly bounded
remainder, using any realization of the actual normalized fractional integral. -/
def IterationBound : Prop := ∀ (α b T a : ℝ),
  0 < α → 0 ≤ b → ∀ hT : 0 ≤ T, 0 ≤ a →
  ∀ (J : C(Icc (0 : ℝ) T, ℝ) →L[ℝ] C(Icc (0 : ℝ) T, ℝ)),
  (∀ f t, J f t = fractionalValue α (continuousExtension hT f) t) →
  ∀ z : C(Icc (0 : ℝ) T, ℝ), (∀ t, 0 ≤ z t) →
  (∀ t, z t ≤ a + b * fractionalValue α (continuousExtension hT z) t) →
  ∀ n (t : Icc (0 : ℝ) T),
    z t ≤ a * (∑ j ∈ Finset.range n, mittagTerm α b j (t : ℝ)) +
      ((b • J)^n) z t ∧
    0 ≤ ((b • J)^n) z t ∧
    ((b • J)^n) z t ≤
      ‖z‖ * (b^n * (t : ℝ)^((n : ℝ)*α) / Real.Gamma ((n : ℝ)*α+1))

/-- Fractional Gronwall with all original hypotheses and the full interval. -/
def ComparisonBound : Prop := ∀ (α T a b : ℝ),
  0 < α → ∀ hT : 0 ≤ T, 0 ≤ a → 0 ≤ b →
  ∀ z : C(Icc (0 : ℝ) T, ℝ), (∀ t, 0 ≤ z t) →
  (∀ t, z t ≤ a + b * fractionalValue α (continuousExtension hT z) t) →
  ∀ t : Icc (0 : ℝ) T, z t ≤ a * mittagLeffler α (b * (t : ℝ)^α)

end ExpandedFA.PartV.FractionalGronwall.Spec
