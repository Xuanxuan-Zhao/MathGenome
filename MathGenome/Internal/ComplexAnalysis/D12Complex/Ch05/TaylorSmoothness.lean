import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.TaylorSmoothness
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.PowerSeriesCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open Filter Set Metric
open scoped Topology NNReal ENNReal

namespace D12Complex.TaylorSmoothness

abbrev coefficients := Taylor.coefficients
abbrev partialX := Taylor.partialX
abbrev partialY := Taylor.partialY
abbrev mixedPartial := Taylor.mixedPartial

open PowerSeriesCalculus

theorem taylor_hasSum :
    Specs.D12Complex.Ch05.TaylorSmoothness.taylor_hasSum_type := by
  intro a R f _ hf z hz
  have hd : DifferentiableOn ℂ f (eball a R) :=
    fun w hw => (hf.2 w hw).differentiableWithinAt
  convert Complex.hasSum_taylorSeries_on_eball hd hz using 1
  funext n
  simp only [Taylor.coefficients, smul_eq_mul, div_eq_mul_inv]
  ring

theorem taylor_radius_lowerBound :
    Specs.D12Complex.Ch05.TaylorSmoothness.taylor_radius_lowerBound_type := by
  intro a R f hR hf
  rw [PowerSeriesRadius.radius_eq_formal]
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hz : a + (r : ℂ) ∈ eball a R := by
    simpa [mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm] using hr
  have ht := (taylor_hasSum a R f hR hf _ hz).summable.tendsto_atTop_zero.norm
  apply FormalMultilinearSeries.le_radius_of_tendsto
  simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    Real.norm_of_nonneg r.2] using ht

private theorem series_eq (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ) (hR : 0 < R)
    (hf : HolomorphicOn (eball a R) f) :
    EqOn (seriesSum (coefficients f a) a) f (eball a R) := by
  intro z hz
  exact (taylor_hasSum a R f hR hf z hz).tsum_eq

theorem taylor_uniform_derivatives :
    Specs.D12Complex.Ch05.TaylorSmoothness.taylor_uniform_derivatives_type := by
  intro a R f hR hf k r hr hrR
  have hrad := taylor_radius_lowerBound a R f hR hf
  obtain ⟨hs, hu, ha⟩ := uniform_derivatives (coefficients f a) a k r hr
    (hrR.trans_le hrad)
  refine ⟨hs, hu.congr_right ?_, ha⟩
  intro z hz
  have hzR : z ∈ eball a R := by
    apply lt_of_le_of_lt _ hrR
    simpa [edist_dist] using ENNReal.ofReal_le_ofReal (mem_closedBall.mp hz)
  exact ((series_eq a R f hR hf).eventuallyEq_of_mem (hf.1.mem_nhds hzR)).iteratedDeriv_eq k

theorem holomorphic_real_smooth :
    Specs.D12Complex.Ch05.TaylorSmoothness.holomorphic_real_smooth_type := by
  intro U f hf
  have hd : DifferentiableOn ℂ f U := fun z hz => (hf.2 z hz).differentiableWithinAt
  exact (hd.contDiffOn hf.1).restrict_scalars ℝ

theorem holomorphic_coordinate_derivatives :
    Specs.D12Complex.Ch05.TaylorSmoothness.holomorphic_coordinate_derivatives_type := by
  intro U f hf z hz
  have hd := (hf.2 z hz).hasDerivAt.complexToReal_fderiv
  have hx : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
  have hy : HasDerivAt (fun t : ℝ => z + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
      Complex.I).const_add z
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hdX : HasFDerivAt f (deriv f z • (1 : ℂ →L[ℝ] ℂ)) (z + (0 : ℂ)) := by
      simpa using hd
    simpa [Function.comp_def] using hdX.comp_hasDerivAt 0 hx
  · have hdY : HasFDerivAt f (deriv f z • (1 : ℂ →L[ℝ] ℂ))
        (z + (0 : ℂ) * Complex.I) := by simpa using hd
    simpa [Function.comp_def, mul_comm] using hdY.comp_hasDerivAt 0 hy
  · simp [Taylor.partialX, hd.fderiv]
  · simp [Taylor.partialY, hd.fderiv, mul_comm]

/-- Iterating a real directional differential of a function locally equal to
c times a holomorphic derivative. The local equality is sufficient even if
the chosen total functions have arbitrary values outside U. -/
private theorem directional_iterate_eq (U : Set ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn U f) (g : ℂ → ℂ) (n : ℕ) (c v : ℂ)
    (hg : EqOn g (fun z => c * iteratedDeriv n f z) U) (k : ℕ) :
    EqOn (((fun (h : ℂ → ℂ) z => fderiv ℝ h z v)^[k]) g)
      (fun z => c * v^k * iteratedDeriv (n+k) f z) U := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    intro z hz
    rw [Function.iterate_succ_apply']
    have heq := ih.eventuallyEq_of_mem (hf.1.mem_nhds hz)
    have hd := ((DiskCauchyDerivatives.holomorphicOn_iteratedDeriv U f hf (n+k)).2
      z hz).const_mul (c * v^k)
    rw [heq.fderiv_eq (𝕜 := ℝ), hd.complexToReal_fderiv.fderiv]
    simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
    rw [show n + (k+1) = n+k+1 by omega, pow_succ]
    ring

theorem holomorphic_mixed_partials :
    Specs.D12Complex.Ch05.TaylorSmoothness.holomorphic_mixed_partials_type := by
  intro U f hf p q
  have hY : EqOn ((Taylor.partialY^[q]) f)
      (fun z => Complex.I^q * iteratedDeriv q f z) U := by
    change EqOn (((fun (h : ℂ → ℂ) z => fderiv ℝ h z Complex.I)^[q]) f) _ U
    simpa using directional_iterate_eq U f hf f 0 1 Complex.I
      (by simp [EqOn]) q
  have heq : EqOn (mixedPartial p q f)
      (fun z => Complex.I^q * iteratedDeriv (p+q) f z) U := by
    change EqOn (((fun (h : ℂ → ℂ) z => fderiv ℝ h z 1)^[p])
      ((Taylor.partialY^[q]) f)) _ U
    simpa [Nat.add_comm] using
      directional_iterate_eq U f hf ((Taylor.partialY^[q]) f) q (Complex.I^q) 1 hY p
  have hh : HolomorphicOn U (mixedPartial p q f) := by
    refine ⟨hf.1, fun z hz => ?_⟩
    have hd := ((DiskCauchyDerivatives.holomorphicOn_iteratedDeriv U f hf (p+q)).1.2
      z hz).const_mul (Complex.I^q)
    exact hd.congr_of_eventuallyEq (heq.eventuallyEq_of_mem (hf.1.mem_nhds hz))
  exact ⟨heq, fun z hz => (hh.2 z hz).continuousAt.continuousWithinAt, hh⟩

end D12Complex.TaylorSmoothness
