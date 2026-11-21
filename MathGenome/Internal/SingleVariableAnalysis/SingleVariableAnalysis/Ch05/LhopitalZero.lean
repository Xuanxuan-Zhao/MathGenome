import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.LhopitalZero
import Mathlib.Analysis.Calculus.LHopital

/-!
K03.05.lhopital_zero. The quotient limits reuse Mathlib's 0/0 theorem,
which follows from the real Cauchy mean value theorem (and changes of
variable for left and infinite approaches). Its arbitrary output filter
covers finite limits and both infinite limits without any sign assumption
on the derivatives. For the denominator apply that theorem to g/g first:
the derivative quotient is eventually 1, so g/g tends to 1 and is eventually
positive. At a zero of g its total real quotient would be zero, a contradiction.
This derives nonvanishing rather than assuming it in quotient notation.
-/

namespace SingleVariableAnalysis

open Set Filter
open scoped Topology

private theorem eventually_ne_zero_of_self_div_tendsto_one
    (g : ℝ → ℝ) (F : Filter ℝ)
    (h : Tendsto (fun x => g x / g x) F (𝓝 1)) :
    ∀ᶠ x in F, g x ≠ 0 := by
  have hp : ∀ᶠ x in F, 0 < g x / g x :=
    h.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hp] with x hx
  intro hz
  simp [hz] at hx

private theorem derivative_self_div_tendsto_one
    (g : ℝ → ℝ) (F : Filter ℝ) (hg : ∀ᶠ x in F, deriv g x ≠ 0) :
    Tendsto (fun x => deriv g x / deriv g x) F (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  exact hg.mono fun x hx => (div_self hx).symm

theorem lhopital_zero_right (f g : ℝ → ℝ) (J : Set ℝ) (a : ℝ) (l : Filter ℝ)
    (hJ : IsOpen J) (_hinterval : OrdConnected J) (happroach : J ∈ (𝓝[>] a : Filter ℝ))
    (hf : DifferentiableOn ℝ f J) (hg : DifferentiableOn ℝ g J)
    (hn : ∀ x ∈ J, deriv g x ≠ 0)
    (hf0 : Tendsto f (𝓝[>] a) (𝓝 0)) (hg0 : Tendsto g (𝓝[>] a) (𝓝 0))
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) l) :
    (∀ᶠ x in (𝓝[>] a), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (𝓝[>] a) l := by
  have hdf : ∀ᶠ x in (𝓝[>] a), DifferentiableAt ℝ f x :=
    Filter.mem_of_superset happroach fun x hx => (hf x hx).differentiableAt (hJ.mem_nhds hx)
  have hdg : ∀ᶠ x in (𝓝[>] a), DifferentiableAt ℝ g x :=
    Filter.mem_of_superset happroach fun x hx => (hg x hx).differentiableAt (hJ.mem_nhds hx)
  have hdn : ∀ᶠ x in (𝓝[>] a), deriv g x ≠ 0 :=
    Filter.mem_of_superset happroach hn
  have hself : Tendsto (fun x => g x / g x) (𝓝[>] a) (𝓝 1) :=
    deriv.lhopital_zero_nhdsGT hdg hdn hg0 hg0
      (derivative_self_div_tendsto_one g _ hdn)
  exact ⟨eventually_ne_zero_of_self_div_tendsto_one g _ hself,
    deriv.lhopital_zero_nhdsGT hdf hdn hf0 hg0 hratio⟩

theorem lhopital_zero_left (f g : ℝ → ℝ) (J : Set ℝ) (a : ℝ) (l : Filter ℝ)
    (hJ : IsOpen J) (_hinterval : OrdConnected J) (happroach : J ∈ (𝓝[<] a : Filter ℝ))
    (hf : DifferentiableOn ℝ f J) (hg : DifferentiableOn ℝ g J)
    (hn : ∀ x ∈ J, deriv g x ≠ 0)
    (hf0 : Tendsto f (𝓝[<] a) (𝓝 0)) (hg0 : Tendsto g (𝓝[<] a) (𝓝 0))
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (𝓝[<] a) l) :
    (∀ᶠ x in (𝓝[<] a), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (𝓝[<] a) l := by
  have hdf : ∀ᶠ x in (𝓝[<] a), DifferentiableAt ℝ f x :=
    Filter.mem_of_superset happroach fun x hx => (hf x hx).differentiableAt (hJ.mem_nhds hx)
  have hdg : ∀ᶠ x in (𝓝[<] a), DifferentiableAt ℝ g x :=
    Filter.mem_of_superset happroach fun x hx => (hg x hx).differentiableAt (hJ.mem_nhds hx)
  have hdn : ∀ᶠ x in (𝓝[<] a), deriv g x ≠ 0 :=
    Filter.mem_of_superset happroach hn
  have hself : Tendsto (fun x => g x / g x) (𝓝[<] a) (𝓝 1) :=
    deriv.lhopital_zero_nhdsLT hdg hdn hg0 hg0
      (derivative_self_div_tendsto_one g _ hdn)
  exact ⟨eventually_ne_zero_of_self_div_tendsto_one g _ hself,
    deriv.lhopital_zero_nhdsLT hdf hdn hf0 hg0 hratio⟩

theorem lhopital_zero_atTop (f g : ℝ → ℝ) (J : Set ℝ) (l : Filter ℝ)
    (hJ : IsOpen J) (_hinterval : OrdConnected J) (happroach : J ∈ (atTop : Filter ℝ))
    (hf : DifferentiableOn ℝ f J) (hg : DifferentiableOn ℝ g J)
    (hn : ∀ x ∈ J, deriv g x ≠ 0)
    (hf0 : Tendsto f (atTop) (𝓝 0)) (hg0 : Tendsto g (atTop) (𝓝 0))
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (atTop) l) :
    (∀ᶠ x in (atTop), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (atTop) l := by
  have hdf : ∀ᶠ x in (atTop), DifferentiableAt ℝ f x :=
    Filter.mem_of_superset happroach fun x hx => (hf x hx).differentiableAt (hJ.mem_nhds hx)
  have hdg : ∀ᶠ x in (atTop), DifferentiableAt ℝ g x :=
    Filter.mem_of_superset happroach fun x hx => (hg x hx).differentiableAt (hJ.mem_nhds hx)
  have hdn : ∀ᶠ x in (atTop), deriv g x ≠ 0 :=
    Filter.mem_of_superset happroach hn
  have hself : Tendsto (fun x => g x / g x) (atTop) (𝓝 1) :=
    deriv.lhopital_zero_atTop hdg hdn hg0 hg0
      (derivative_self_div_tendsto_one g _ hdn)
  exact ⟨eventually_ne_zero_of_self_div_tendsto_one g _ hself,
    deriv.lhopital_zero_atTop hdf hdn hf0 hg0 hratio⟩

theorem lhopital_zero_atBot (f g : ℝ → ℝ) (J : Set ℝ) (l : Filter ℝ)
    (hJ : IsOpen J) (_hinterval : OrdConnected J) (happroach : J ∈ (atBot : Filter ℝ))
    (hf : DifferentiableOn ℝ f J) (hg : DifferentiableOn ℝ g J)
    (hn : ∀ x ∈ J, deriv g x ≠ 0)
    (hf0 : Tendsto f (atBot) (𝓝 0)) (hg0 : Tendsto g (atBot) (𝓝 0))
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (atBot) l) :
    (∀ᶠ x in (atBot), g x ≠ 0) ∧
      Tendsto (fun x => f x / g x) (atBot) l := by
  have hdf : ∀ᶠ x in (atBot), DifferentiableAt ℝ f x :=
    Filter.mem_of_superset happroach fun x hx => (hf x hx).differentiableAt (hJ.mem_nhds hx)
  have hdg : ∀ᶠ x in (atBot), DifferentiableAt ℝ g x :=
    Filter.mem_of_superset happroach fun x hx => (hg x hx).differentiableAt (hJ.mem_nhds hx)
  have hdn : ∀ᶠ x in (atBot), deriv g x ≠ 0 :=
    Filter.mem_of_superset happroach hn
  have hself : Tendsto (fun x => g x / g x) (atBot) (𝓝 1) :=
    deriv.lhopital_zero_atBot hdg hdn hg0 hg0
      (derivative_self_div_tendsto_one g _ hdn)
  exact ⟨eventually_ne_zero_of_self_div_tendsto_one g _ hself,
    deriv.lhopital_zero_atBot hdf hdn hf0 hg0 hratio⟩

end SingleVariableAnalysis
