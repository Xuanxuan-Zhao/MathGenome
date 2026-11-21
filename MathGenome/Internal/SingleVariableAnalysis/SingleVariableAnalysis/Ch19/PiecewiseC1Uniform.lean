import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.C1Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Monotone
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

noncomputable section
namespace SingleVariableAnalysis
open Riemann Set Filter
open scoped BigOperators Topology
namespace PiecewiseFourier
open Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform

/-- Newton–Leibniz over a strict partition. Induction over prefixes cancels
each internal boundary value, without requiring differentiability at nodes. -/
lemma partition_ftc {a b : ℝ} (P : Partition a b) (F D : ℝ → ℂ)
    (hc : ContinuousOn F (Icc a b))
    (hd : ∀ i : Fin P.n, ∀ x ∈ Ioo (P.point i.castSucc) (P.point i.succ),
      HasDerivAt F (D x) x) (hi : ComplexIntegrable D a b) :
    complexIntegral D hi = F b - F a := by
  have hp (j : Fin (P.n+1)) : P.point j ∈ Icc a b :=
    ⟨by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le j),
     by simpa only [P.last] using P.strictMono.monotone (Fin.le_last j)⟩
  have prefixIntegral (j : Fin (P.n+1)) := hi.subinterval le_rfl (hp j).1 (hp j).2
  have hprefix : ∀ (k : ℕ) (hk : k < P.n+1),
      complexIntegral D (prefixIntegral ⟨k, hk⟩) = F (P.point ⟨k, hk⟩) - F a := by
    intro k
    induction k with
    | zero =>
      intro hk
      have he : P.point ⟨0, hk⟩ = a := P.first
      simp only [he, sub_self]
      have hzero : ComplexIntegrable D a a := by
        simpa only [he] using prefixIntegral ⟨0, hk⟩
      change complexIntegral D hzero = 0
      apply Complex.ext
      · exact (complexIntegral_components D hzero).1.trans (realIntegral_degenerate _ a hzero.1)
      · exact (complexIntegral_components D hzero).2.trans (realIntegral_degenerate _ a hzero.2)
    | succ k ih =>
      intro hk
      let i : Fin P.n := ⟨k, by omega⟩
      have hab := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
      have hcell := hi.subinterval (hp i.castSucc).1 hab (hp i.succ).2
      have he := complex_ftc_second F D (P.point i.castSucc) (P.point i.succ) hab
        (hc.mono (Icc_subset_Icc (hp i.castSucc).1 (hp i.succ).2)) (hd i) hcell
      have hs := (complex_split D (hp i.castSucc).1 hab (prefixIntegral i.succ).norm_bound).2
        (prefixIntegral i.succ) (prefixIntegral i.castSucc) hcell
      change complexIntegral D hcell = F (P.point i.succ) - F (P.point i.castSucc) at he
      change complexIntegral D (prefixIntegral i.succ) = F (P.point i.succ) - F a
      calc
        _ = complexIntegral D (prefixIntegral i.castSucc) + complexIntegral D hcell := hs
        _ = (F (P.point i.castSucc) - F a) +
            (F (P.point i.succ) - F (P.point i.castSucc)) :=
          congrArg₂ (fun z w : ℂ => z + w) (ih (by omega)) he
        _ = _ := by ring
  simpa only [show (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n+1)) = Fin.last P.n from rfl,
    P.last] using hprefix P.n (Nat.lt_succ_self _)

end PiecewiseFourier

/-- Piecewise integration by parts, retaining all internal node values. -/
theorem fourier_partition_parts :
    Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform.partitionParts := by
  intro u v du dv a b P hu hv hd hdu hdv
  have hab : a ≤ b := by
    simpa only [P.first, P.last] using P.strictMono.monotone (Fin.zero_le (Fin.last P.n))
  have hui := Fourier.complexIntegrable_of_continuousOn hab hu
  have hvi := Fourier.complexIntegrable_of_continuousOn hab hv
  have h₁ := complex_product hui hdv
  have h₂ := complex_product hdu hvi
  obtain ⟨hs, he⟩ := complex_add_value h₂ h₁
  have hf := PiecewiseFourier.partition_ftc P (fun x => u x * v x)
    (fun x => du x * v x + u x * dv x) (hu.mul hv)
    (fun i x hx => ((hd i x hx).1).mul ((hd i x hx).2)) hs
  exact ⟨h₁, h₂, eq_sub_of_add_eq (by
    simpa only [add_comm] using he.symm.trans hf)⟩

/-- Properly integrable piecewise derivative and the Fourier coefficient
identity; only f, rather than its derivative, has matching seam values. -/
theorem fourier_piecewise_c1_derivative :
    Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform.derivativeCoefficients := by
  intro f df P hc hd hend
  have hdi : ComplexIntegrable df (-Real.pi) Real.pi :=
    complex_piecewise_continuous_integrable df P (fun i => (hd i).2)
  have hfi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hc
  let H := fourierCoeff_integrable f hfi
  let Hd := fourierCoeff_integrable df hdi
  refine ⟨hdi, H, Hd, ?_⟩
  intro n
  let e := fourierMode (-n)
  let c : ℂ := -(Complex.I * (n : ℂ))
  have hed (x : ℝ) : HasDerivAt e (c * e x) x := by
    change HasDerivAt (fun t : ℝ => Complex.exp
      (Complex.I * (((-n : ℤ) : ℂ) * (t : ℂ)))) (c * e x) x
    simpa [e, c, fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue,
      mul_assoc] using oscillatory_phase_hasDerivAt (-(n : ℝ)) x
  have hec : ContinuousOn e (Icc (-Real.pi) Real.pi) :=
    (continuous_iff_continuousAt.mpr (fun x => (hed x).continuousAt)).continuousOn
  have hei := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hec
  obtain ⟨hce, _⟩ := complex_mul_value hei c
  obtain ⟨h₁, h₂, hp⟩ := fourier_partition_parts f e df (fun x => c * e x)
    P hc hec (fun i x hx => ⟨(hd i).1 x hx, hed x⟩) hdi hce
  have heend : e (-Real.pi) = e Real.pi := Fourier.mode_endpoints (-n)
  change complexIntegral _ h₁ = f Real.pi * e Real.pi -
    f (-Real.pi) * e (-Real.pi) - complexIntegral _ h₂ at hp
  rw [hend, heend, sub_self, zero_sub] at hp
  obtain ⟨hscale, hv⟩ := complex_mul_value (H n) c
  have hfun : (fun x => c * (f x * fourierMode (-n) x)) =
      (fun x => f x * (c * e x)) := by funext x; dsimp [e]; ring
  have hval : complexIntegral _ h₁ = c * complexIntegral _ (H n) := by
    simpa only [hfun] using hv
  have hdf : complexIntegral _ h₂ = complexIntegral _ (Hd n) := rfl
  rw [hval, hdf] at hp
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (Hd n) =
    (Complex.I * (n : ℂ)) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (H n))
  have heq : complexIntegral _ (Hd n) = -c * complexIntegral _ (H n) := by
    linear_combination hp
  rw [heq]
  dsimp [c]
  ring


namespace PiecewiseFourier
open Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform
open Specs.SingleVariableAnalysis.Ch19.Representation

/-- Bessel for an integrable piecewise derivative gives absolute summability.
The estimate 2ab ≤ a²+b² is the elementary square form of Cauchy–Schwarz. -/
lemma summable_of_derivative_identity {f df : ℝ → ℂ}
    (hdi : ComplexIntegrable df (-Real.pi) Real.pi)
    (H : ComplexWeights f) (Hd : ComplexWeights df)
    (he : ∀ n : ℤ, fourierCoeff df n (Hd n) =
      (Complex.I * (n : ℂ)) * fourierCoeff f n (H n)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n (H n)‖) := by
  have hsq := fourierBessel_summable df hdi Hd
  have hrecip : Summable (fun n : ℤ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_int_pow.mpr (by omega)
  apply (hsq.add hrecip).of_norm_bounded_eventually
  filter_upwards [show ∀ᶠ n : ℤ in cofinite, n ≠ 0 from
    (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have heq : ‖fourierCoeff df n (Hd n)‖ =
      |(n : ℝ)| * ‖fourierCoeff f n (H n)‖ := by
    rw [he, norm_mul]
    simp [Complex.norm_intCast, ← Int.cast_abs]
  have hdiv : ‖fourierCoeff f n (H n)‖ =
      ‖fourierCoeff df n (Hd n)‖ / |(n : ℝ)| := by
    rw [heq, mul_div_cancel_left₀ _ (abs_ne_zero.mpr hnr)]
  have hrecip2 : (1 / |(n : ℝ)|)^2 = 1 / (n : ℝ)^2 := by
    rw [div_pow, one_pow, sq_abs]
  have hbound := sq_nonneg (‖fourierCoeff df n (Hd n)‖ - 1 / |(n : ℝ)|)
  rw [norm_norm, hdiv, div_eq_mul_inv]
  rw [one_div] at hrecip2 hbound
  nlinarith [sq_nonneg ‖fourierCoeff df n (Hd n)‖,
    sq_nonneg (|(n : ℝ)|⁻¹)]

/-- Absolute synthesis for any continuous amplitude with summable coefficients.
Cesàro limits and uniform Fejér convergence identify the sum pointwise. This
step uses no regularity of a derivative. -/
lemma absoluteUniform_of_summable (f : ℝ → ℂ)
    (hc : ContinuousOn f (Icc (-Real.pi) Real.pi)) (hend : f (-Real.pi) = f Real.pi)
    (H : ComplexWeights f) (hs : Summable (fun n : ℤ => ‖fourierCoeff f n (H n)‖)) :
    AbsoluteUniform f := by
  obtain ⟨hec, hep, heq⟩ := fourier_periodic_extension f hc hend
  have hfi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hc
  have hei := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hec.continuousOn
  let He := fourierCoeff_integrable (Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f) hei
  have hcoeff (n : ℤ) : fourierCoeff f n (H n) =
      fourierCoeff (Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f) n (He n) :=
    (Fourier.coefficient_eq_of_eqOn hei hfi He H heq n).symm
  let terms (n : ℤ) (x : ℝ) := fourierCoeff f n (H n) * fourierMode n x
  have hnorm (n : ℤ) (x : ℝ) : ‖terms n x‖ = ‖fourierCoeff f n (H n)‖ := by
    dsimp [terms]
    rw [norm_mul, FourierAbsolute.mode_norm, mul_one]
  have hsum (x : ℝ) : Summable (terms · x) :=
    (hs.congr (fun n => (hnorm n x).symm)).of_norm
  have hu : TendstoUniformly (fourierPartialSum f H) (fun x => ∑' n, terms n x) atTop :=
    fun U hU => FourierAbsolute.symmetric_tendsto.eventually
      ((tendstoUniformly_tsum hs (fun n x => (hnorm n x).le)) U hU)
  have hvalue (x : ℝ) : (∑' n, terms n x) = Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f x := by
    have hcesaro := ((hu.tendsto_at x).cesaro_smul).comp (tendsto_add_atTop_nat 1)
    have hm : Tendsto (fun N => fejerMean f H N x) atTop
        (𝓝 (∑' n, terms n x)) := by
      simpa [fejerMean, Specs.SingleVariableAnalysis.Ch19.FejerKernel.meanValue,
        Function.comp_def, Nat.cast_add, Nat.cast_one, one_div, Complex.real_smul] using hcesaro
    have hfmean := ((complexUniformConverges_iff _ _).mp
      (fejer_uniform_convergence (Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f) hec hep He)).tendsto_at x
    have hequal : (fun N => fejerMean f H N x) =
        (fun N => fejerMean (Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f) He N x) := by
      funext N
      exact Fourier.fejerMean_eq_of_coeff_eq f (Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f) H He hcoeff N x
    rw [← hequal] at hfmean
    exact tendsto_nhds_unique hm hfmean
  have hfunc : (fun x => ∑' n, terms n x) = Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f := funext hvalue
  refine ⟨H, hs, hec, hep, heq, ?_, ?_, ?_⟩
  · rw [hfunc] at hu
    exact (complexUniformConverges_iff _ _).mpr hu
  · intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (hs.hasSum.comp FourierAbsolute.symmetric_tendsto) ε hε
    refine ⟨N, fun k hk x => ?_⟩
    change |(∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), ‖terms n x‖) - _| < ε
    simp_rw [hnorm]
    simpa only [Real.dist_eq, Function.comp_apply] using hN k hk
  · intro x
    simpa only [hvalue x] using (hsum x).hasSum

end PiecewiseFourier

/-- Absolute and uniform convergence under precisely the piecewise C¹
hypotheses, with equality to the specified continuous periodic extension. -/
theorem fourier_piecewise_c1_uniform_to_extension :
    Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform.absoluteUniformToExtension := by
  intro f P hf hend
  obtain ⟨df, hd⟩ := hf.2
  obtain ⟨hdi, H, Hd, he⟩ := fourier_piecewise_c1_derivative f df P hf.1 hd hend
  exact PiecewiseFourier.absoluteUniform_of_summable f hf.1 hend H
    (PiecewiseFourier.summable_of_derivative_identity hdi H Hd he)

/-- The globally periodic version agrees with f at every real argument. -/
theorem fourier_piecewise_c1_uniform_periodic :
    Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform.absoluteUniformPeriodic := by
  intro f P hc hp hd
  have hend : f (-Real.pi) = f Real.pi := by
    have hh := hp (-Real.pi)
    have hx : -Real.pi + 2 * Real.pi = Real.pi := by ring
    simpa only [hx] using hh.symm
  obtain ⟨H, hs, hec, hep, heq, hu, ha, hsum⟩ :=
    fourier_piecewise_c1_uniform_to_extension f P ⟨hc.continuousOn, hd⟩ hend
  have hfi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hc.continuousOn
  have hei := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hec.continuousOn
  let He := fourierCoeff_integrable (Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f) hei
  have he : Specs.SingleVariableAnalysis.Ch19.C1Uniform.periodicExtensionValue f = f :=
    fourierCoeff_unique _ _ hec hc hep hp He H
      (Fourier.coefficient_eq_of_eqOn hei hfi He H heq)
  rw [he] at hu hsum
  exact ⟨H, hs, hu, ha, hsum⟩

/-- Real scalar functions satisfy the same result under the canonical embedding. -/
theorem fourier_piecewise_c1_uniform_real :
    Specs.SingleVariableAnalysis.Ch19.PiecewiseC1Uniform.realAbsoluteUniformToExtension := by
  intro f P hf hend
  obtain ⟨df, hd⟩ := hf.2
  apply fourier_piecewise_c1_uniform_to_extension (fun x => (f x : ℂ)) P
  · refine ⟨Complex.continuous_ofReal.comp_continuousOn hf.1, fun x => (df x : ℂ), ?_⟩
    intro i
    obtain ⟨hder, hcont, L, R, hL, hR⟩ := hd i
    exact ⟨fun x hx => (hder x hx).ofReal_comp,
      Complex.continuous_ofReal.comp_continuousOn hcont,
      (L : ℂ), (R : ℂ), Complex.continuous_ofReal.continuousAt.tendsto.comp hL,
        Complex.continuous_ofReal.continuousAt.tendsto.comp hR⟩
  · exact congrArg Complex.ofReal hend

end SingleVariableAnalysis
