import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.DerivativeUniformCauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Continuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Differentiation
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
Uniform convergence of derivatives, K03.12.differentiation.
The upstream mean inequality and scalar completeness give the uniform limit
on the closed interval from convergence at a single point. Its continuity
follows from the uniform-limit theorem. For differentiability we apply
Mathlib's hasDerivAt_of_tendstoUniformlyOn on the open interval: its hypotheses
are uniform convergence of derivatives, actual derivatives of the approximants,
and pointwise convergence of the functions. It uses the mean inequality and
the difference-quotient argument, without continuity of the derivatives.
The base field is ℝ for both target scalars. An arbitrary ambient extension
of the limit imposes no extra conditions outside the source interval.
-/

namespace SingleVariableAnalysis

open Set

theorem real_uniform_convergence_of_derivatives :
    Specs.SingleVariableAnalysis.Ch12.Differentiation.realUniformConvergenceOfDerivatives := by
  intro F g a b x₀ hab hx₀ hc hd hbase hg
  obtain ⟨f, hf⟩ := (real_derivative_uniform_cauchy
    F g a b x₀ hab hx₀ hc hd hbase hg).2
  obtain ⟨fext, hext⟩ := exists_ambientExtension (Icc a b) f
  have hu : RealUniformConverges (fun n (x : Icc a b) => F n x) (fun x => fext x) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun n hn x => ?_⟩
    simpa only [hext] using hN n hn x
  have hfc : Continuous f := realUniformLimit_continuous
    (fun n (x : Icc a b) => F n x) f
    (fun n => (continuousOn_iff_continuous_domRestrict.mp (hc n))) hf
  have hcont : ContinuousOn fext (Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr (by
      change Continuous (fun x : Icc a b => fext x)
      simpa only [hext] using hfc)
  have hfun : TendstoUniformlyOn F fext Filter.atTop (Icc a b) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      ((realUniformConverges_iff _ _).mp hu)
  have hderiv : TendstoUniformlyOn (fun n x => deriv (F n) x) g
      Filter.atTop (Ioo a b) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      ((realUniformConverges_iff _ _).mp hg)
  refine ⟨fext, hu, hcont, fun x hx => ?_⟩
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hderiv
    (Filter.Eventually.of_forall (fun n x hx => (hd n x hx).hasDerivAt))
    (fun y hy => hfun.tendsto_at (Ioo_subset_Icc_self hy)) hx

theorem complex_uniform_convergence_of_derivatives :
    Specs.SingleVariableAnalysis.Ch12.Differentiation.complexUniformConvergenceOfDerivatives := by
  intro F g a b x₀ hab hx₀ hc hd hbase hg
  obtain ⟨f, hf⟩ := (complex_derivative_uniform_cauchy
    F g a b x₀ hab hx₀ hc hd hbase hg).2
  obtain ⟨fext, hext⟩ := exists_ambientExtension (Icc a b) f
  have hu : ComplexUniformConverges (fun n (x : Icc a b) => F n x) (fun x => fext x) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    refine ⟨N, fun n hn x => ?_⟩
    simpa only [hext] using hN n hn x
  have hfc : Continuous f := complexUniformLimit_continuous
    (fun n (x : Icc a b) => F n x) f
    (fun n => (continuousOn_iff_continuous_domRestrict.mp (hc n))) hf
  have hcont : ContinuousOn fext (Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr (by
      change Continuous (fun x : Icc a b => fext x)
      simpa only [hext] using hfc)
  have hfun : TendstoUniformlyOn F fext Filter.atTop (Icc a b) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      ((complexUniformConverges_iff _ _).mp hu)
  have hderiv : TendstoUniformlyOn (fun n x => deriv (F n) x) g
      Filter.atTop (Ioo a b) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      ((complexUniformConverges_iff _ _).mp hg)
  refine ⟨fext, hu, hcont, fun x hx => ?_⟩
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hderiv
    (Filter.Eventually.of_forall (fun n x hx => (hd n x hx).hasDerivAt))
    (fun y hy => hfun.tendsto_at (Ioo_subset_Icc_self hy)) hx

end SingleVariableAnalysis
