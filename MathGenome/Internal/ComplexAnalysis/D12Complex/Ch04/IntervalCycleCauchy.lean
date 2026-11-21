import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.IntervalChains
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.FiniteCycleCauchy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations

/-!
Winding and the Cauchy theorems for chains on intrinsic interval maps. The
trace here is computed after combining the coefficients of equal interval maps.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex

namespace IntervalChain

def index (Γ : IntervalChain) (a : ℂ) : ℂ := Γ.toIntegralChain.index a

theorem index_eq_integral (Γ : IntervalChain) (a : ℂ) (ha : a ∉ Γ.trace) :
    Γ.index a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Γ.integral (fun z => 1 / (z - a)) :=
  Γ.toIntegralChain.index_eq_integral a ha

@[simp] theorem zero_index (a : ℂ) : (0 : IntervalChain).index a = 0 := by
  simp [index, toIntegralChain]

end IntervalChain

theorem IntegralChain.toIntervalChain_index (Γ : IntegralChain) (a : ℂ)
    (ha : a ∉ Γ.trace) : Γ.toIntervalChain.index a = Γ.index a := by
  rw [Γ.toIntervalChain.index_eq_integral a (fun h => ha (Γ.toIntervalChain_trace_subset h)),
    Γ.index_eq_integral a ha,
    Γ.toIntervalChain_integral _ (Γ.reciprocal_continuousOn_trace a ha)]

/-- Opposite contributions from interval-equivalent representatives leave the
unit circle's active trace and its winding about the center unchanged. -/
theorem unitCircle_cancel_sameInterval {γ δ : PiecewiseC1Path}
    (ha : γ.path.a = δ.path.a) (hb : γ.path.b = δ.path.b)
    (h : EqOn γ δ (Icc γ.path.a γ.path.b)) (m : ℤ) :
    let Γ : IntegralChain := Finsupp.single (DiskCauchyFormula.circlePath 0 1) 1
    let Δ := (Γ + Finsupp.single γ m - Finsupp.single δ m).toIntervalChain
    (0 : ℂ) ∉ Δ.trace ∧ Δ.index 0 = 1 := by
  dsimp only
  rw [IntegralChain.toIntervalChain_add_sub_eq _ ha hb h]
  let p := DiskCauchyFormula.circlePath 0 1
  let Γ : IntegralChain := Finsupp.single p 1
  change (0 : ℂ) ∉ Γ.toIntervalChain.trace ∧ Γ.toIntervalChain.index 0 = 1
  have htrace : Γ.trace = p.trace := by
    classical
    ext z
    simp [Γ, IntegralChain.mem_trace_iff]
  have hzero : (0 : ℂ) ∉ p.trace := by
    rw [DiskCauchyFormula.circlePath_trace 0 1 (by norm_num)]
    simp
  constructor
  · simpa only [Γ, IntegralChain.toIntervalChain_single_trace] using hzero
  · rw [Γ.toIntervalChain_index 0 (by simpa only [htrace] using hzero)]
    change p.index 0 = 1
    exact IndexComputations.circle_index_interior 0 0 1 (by norm_num) (by simp)

namespace IntervalCycle

def index (Γ : IntervalCycle) (a : ℂ) : ℂ := Γ.chain.index a

theorem index_eq_integral (Γ : IntervalCycle) (a : ℂ) (ha : a ∉ Γ.trace) :
    Γ.index a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      Γ.integral (fun z => 1 / (z - a)) :=
  Γ.chain.index_eq_integral a ha

theorem index_integer (Γ : IntervalCycle) (a : ℂ) (ha : a ∉ Γ.trace) :
    ∃ n : ℤ, Γ.index a = (n : ℂ) :=
  IndexProperties.cycle_index_integer Γ.toIntegralCycle a ha

theorem index_continuousOn (Γ : IntervalCycle) : ContinuousOn Γ.index Γ.traceᶜ :=
  IndexProperties.cycle_index_continuousOn Γ.toIntegralCycle

theorem index_locally_constant (Γ : IntervalCycle) (a : ℂ) (ha : a ∉ Γ.trace) :
    ∀ᶠ b in 𝓝 a, b ∉ Γ.trace ∧ Γ.index b = Γ.index a :=
  IndexProperties.cycle_index_locally_constant Γ.toIntegralCycle a ha

theorem index_zero_on_unbounded_component (Γ : IntervalCycle) (a : ℂ) (ha : a ∉ Γ.trace)
    (h : ¬ Bornology.IsBounded (connectedComponentIn Γ.traceᶜ a)) : Γ.index a = 0 :=
  IndexProperties.cycle_index_zero_on_unbounded_component Γ.toIntegralCycle a ha h

theorem cauchy_theorem (U : Set ℂ) (f : ℂ → ℂ) (Γ : IntervalCycle)
    (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ w, w ∉ U → Γ.index w = 0) : Γ.integral f = 0 :=
  FiniteCycleCauchy.cycle_cauchy_theorem U f Γ.toIntegralCycle hf hΓ hnull

theorem cauchy_formula (U : Set ℂ) (f : ℂ → ℂ) (Γ : IntervalCycle)
    (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ w, w ∉ U → Γ.index w = 0) (a : ℂ) (ha : a ∈ U) (hat : a ∉ Γ.trace) :
    Γ.index a * f a = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      Γ.integral (fun z => f z / (z - a)) :=
  FiniteCycleCauchy.cycle_cauchy_formula U f Γ.toIntegralCycle hf hΓ hnull a ha hat

theorem cauchy_derivatives (U : Set ℂ) (f : ℂ → ℂ) (Γ : IntervalCycle)
    (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ w, w ∉ U → Γ.index w = 0) (a : ℂ) (ha : a ∈ U) (hat : a ∉ Γ.trace) (n : ℕ) :
    Γ.index a * iteratedDeriv n f a =
      (n.factorial : ℂ) / (2 * Real.pi * Complex.I) *
        Γ.integral (fun z => f z / (z - a) ^ (n + 1)) :=
  FiniteCycleCauchy.cycle_cauchy_derivatives U f Γ.toIntegralCycle hf hΓ hnull a ha hat n

end IntervalCycle
end D12Complex
