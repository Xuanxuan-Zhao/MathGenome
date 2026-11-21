import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.DominatedEulerLagrange
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace VariationalNotes.Sobolev.EulerLagrange

/-- Finite signed energy forces integrability, even without a lower bound. -/
theorem integrable_of_extendedIntegral_finite {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f : S → ℝ} (hm : AEMeasurable f μ)
    (hf : ∃ r : ℝ, extendedIntegral μ f = r) : Integrable f μ := by
  obtain ⟨r, hr⟩ := hf
  have hn : (∫⁻ x, ENNReal.ofReal (-f x) ∂μ) ≠ ⊤ := by
    intro h
    simp [extendedIntegral, h] at hr
  have hp : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ := by
    intro h
    have hn' : ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ) : EReal) ≠ ⊤ := by
      simpa using hn
    simp only [extendedIntegral, h, EReal.coe_ennreal_top, EReal.top_sub hn'] at hr
    exact EReal.coe_ne_top r hr.symm
  have hneg : Integrable (fun x => max (-f x) 0) μ :=
    (negativePartIntegrable_iff hm).mpr hn
  have hpos : Integrable (fun x => max (f x) 0) μ := by
    have := (negativePartIntegrable_iff hm.neg).mpr (by simpa using hp)
    simpa [NegativePartIntegrable] using this
  convert hpos.sub hneg using 1
  ext x
  dsimp
  by_cases h : 0 ≤ f x
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have h' : f x ≤ 0 := le_of_not_ge h
    simp [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]

/-- Measurability of the directional derivative follows from measurable
energy slices and differentiation; no componentwise flux bound is needed. -/
theorem aestronglyMeasurable_directional_derivative {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f : ℝ → S → ℝ} {g : S → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (f t) μ)
    (hd : ∀ᵐ x ∂μ, HasDerivAt (fun t => f t x) (g x) 0) :
    AEStronglyMeasurable g μ := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => by simp [t]; positivity
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n x => (t n)⁻¹ * (f (t n) x - f 0 x))
  · intro n
    exact ((hm (t n)).sub (hm 0)).const_mul _
  · filter_upwards [hd] with x hx
    simpa [slope, Function.comp_def, div_eq_inv_mul] using hx.tendsto_slope.comp ht


/-- Dominated stationarity for signed extended energies on a measure space.
Both nearby integrability and integrability of the first variation are conclusions. -/
theorem dominated_line_stationarity {S : Type*} [MeasurableSpace S]
    {μ : Measure S} {f g : ℝ → S → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (f t) μ)
    (hf : ∃ r : ℝ, extendedIntegral μ (f 0) = r)
    (hmin : IsLocalMin (fun t => extendedIntegral μ (f t)) 0)
    {ε : ℝ} (hε : 0 < ε) {b : S → ℝ} (hb : Integrable b μ)
    (hd : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε,
      HasDerivAt (fun t => f t x) (g t x) t)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖g t x‖ ≤ b x) :
    Integrable (g 0) μ ∧ (∫ x, g 0 x ∂μ) = 0 := by
  have h0 : (0 : ℝ) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hi : Integrable (f 0) μ := integrable_of_extendedIntegral_finite (hm 0).aemeasurable hf
  have hgm : AEStronglyMeasurable (g 0) μ :=
    aestronglyMeasurable_directional_derivative hm (hd.mono fun x hx => hx 0 h0)
  obtain ⟨hgi, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) hε) (Eventually.of_forall hm) hi hgm hbound hb hd
  have hlip : ∀ᵐ x ∂μ,
      LipschitzOnWith (Real.nnabs (b x)) (fun t => f t x) (Metric.ball 0 ε) := by
    filter_upwards [hd, hbound] with x hx hbx
    apply (convex_ball (0 : ℝ) ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hx t ht).hasDerivWithinAt)
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (hbx t ht).trans (le_abs_self _)
  have hnear : ∀ t ∈ Metric.ball (0 : ℝ) ε, Integrable (f t) μ := by
    intro t ht
    apply integrable_of_norm_sub_le (hm t) hi (hb.norm.const_mul ε)
    filter_upwards [hlip] with x hx
    have H := hx.norm_sub_le ht h0
    simp only [sub_zero, Real.norm_eq_abs] at H
    rw [norm_sub_rev]
    exact H.trans (by
      have ht' : |t| ≤ ε := (by simpa [Metric.mem_ball, Real.dist_eq] using ht : |t| < ε).le
      calc
        |b x| * |t| ≤ |b x| * ε := mul_le_mul_of_nonneg_left ht' (abs_nonneg _)
        _ = ε * |b x| := mul_comm _ _)
  have hmin' : IsLocalMin (fun t => ∫ x, f t x ∂μ) 0 := by
    filter_upwards [hmin, Metric.ball_mem_nhds (0 : ℝ) hε] with t ht htε
    rw [extendedIntegral_eq_integral hi, extendedIntegral_eq_integral (hnear t htε)] at ht
    exact EReal.coe_le_coe_iff.mp ht
  exact ⟨hgi, hder.deriv.symm.trans hmin'.deriv_eq_zero⟩


@[fun_prop]
theorem continuous_testGradient {d m : ℕ} {Ω : Opens (Domain d)}
    (φ : VectorTest Ω m) : Continuous (testGradient φ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin d => ℝ)).comp
  apply continuous_pi
  intro ij
  exact (PiLp.continuous_apply 2 _ ij.1).comp
    (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d ij.2) φ : VectorTest Ω m).continuous

/-- The chain rule along the affine line gives exactly the Frobenius pairing. -/
theorem hasDerivAt_variation {d m : ℕ} {Ω : Opens (Domain d)}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    {x : Domain d}
    (hF : ∀ y : Vector m × Gradient m d,
      HasFDerivAt (fun y => F x y.1 y.2)
        (fiberDerivative (Fs x y.1 y.2) (FZ x y.1 y.2)) y)
    (u : Domain d → Vector m) (U : Domain d → Gradient m d)
    (φ : VectorTest Ω m) (t : ℝ) :
    HasDerivAt (fun t => F x (u x + t • φ x) (U x + t • testGradient φ x))
      (variationDensity Fs FZ u U φ t x) t := by
  have h₁ := (hasDerivAt_const t (u x)).add ((hasDerivAt_id t).smul_const (φ x))
  have h₂ := (hasDerivAt_const t (U x)).add
    ((hasDerivAt_id t).smul_const (testGradient φ x))
  simpa [Function.comp_def, fiberDerivative, variationDensity, frobenius] using
    (hF (u x + t • φ x, U x + t • testGradient φ x)).comp_hasDerivAt t (h₁.prodMk h₂)

/-- The source theorem, on the canonical Sobolev classes and their measurable representatives. -/
theorem dominated_euler_lagrange_fields : Expected.FieldStationarity := by
  intro d m Ω p u F Fs FZ hF hder hfinite hmin hbound φ
  let v : Domain d → Vector m := value Ω m p u
  let V : Domain d → Gradient m d := gradient Ω m p u
  let f : ℝ → Domain d → ℝ := fun t x => F x (v x + t • φ x) (V x + t • testGradient φ x)
  let g : ℝ → Domain d → ℝ := variationDensity Fs FZ v V φ
  have hm : ∀ t, AEStronglyMeasurable (f t) (domainMeasure Ω) := by
    intro t
    apply AEMeasurable.aestronglyMeasurable
    change AEMeasurable (fun x => F x (v x + t • φ x) (V x + t • testGradient φ x)) _
    apply Caratheodory.aemeasurable_substitution
      (y := fun x => (v x + t • φ x, V x + t • testGradient φ x)) (show Caratheodory (domainMeasure Ω)
      (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) from hF)
    exact (((Lp.aestronglyMeasurable (value Ω m p u)).aemeasurable).add
      (φ.continuous.measurable.aemeasurable.const_smul t)).prodMk
        (((Lp.aestronglyMeasurable (gradient Ω m p u)).aemeasurable).add
          ((continuous_testGradient φ).measurable.aemeasurable.const_smul t))
  have hf : ∃ r : ℝ, extendedIntegral (domainMeasure Ω) (f 0) = r := by
    simpa [f, v, V, extendedIntegral, energy, energyOnFields] using hfinite
  have hmn : IsLocalMin (fun t => extendedIntegral (domainMeasure Ω) (f t)) 0 := by
    exact hmin φ
  obtain ⟨ε, b, hε, hb, hbd⟩ := hbound φ
  have hd : ∀ᵐ x ∂domainMeasure Ω, ∀ t ∈ Metric.ball (0 : ℝ) ε,
      HasDerivAt (fun t => f t x) (g t x) t := by
    filter_upwards [hder] with x hx
    intro t _
    exact hasDerivAt_variation hx.1 v V φ t
  have hbd' : ∀ᵐ x ∂domainMeasure Ω, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖g t x‖ ≤ b x := by
    filter_upwards [hbd] with x hx
    intro t ht
    exact hx t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
  have hh := dominated_line_stationarity hm hf hmn hε hb hd hbd'
  have he : g 0 = weakDensity
      (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
      (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ := by
    ext x
    simp [g, v, V, variationDensity, weakDensity]
  rw [he] at hh
  exact hh


/-- Differentiation commutes with a continuous linear change of target. -/
theorem test_lineDeriv_postcomp {E H K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    {Ω : Opens E} (L : H →L[ℝ] K) (φ : TestFunction Ω H ⊤) (v : E) :
    (TestFunction.lineDerivCLM ℝ v (TestFunction.postcompCLM L φ) : TestFunction Ω K ⊤) =
      TestFunction.postcompCLM L (TestFunction.lineDerivCLM ℝ v φ : TestFunction Ω H ⊤) := by
  ext x
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply, le_top, ↓reduceIte, TestFunction.postcompCLM_apply]
  change fderiv ℝ (L ∘ φ) x v = L (fderiv ℝ φ x v)
  rw [L.hasFDerivAt.comp x (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt |>.fderiv]
  rfl

/-- The scalar coordinate test of a Jacobian entry is its ordinary partial derivative. -/
theorem testGradient_coordinate {d m : ℕ} {Ω : Opens (Domain d)}
    (φ : VectorTest Ω m) (i : Fin m) (j : Fin d) (x : Domain d) :
    testGradient φ x (i,j) =
      (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d j)
        (vectorTestCoordinate Ω φ i) : P102.U4.TestSpace ℝ Ω) x := by
  rw [vectorTestCoordinate, test_lineDeriv_postcomp]
  rfl

private theorem regular_pairing_restrict {d : ℕ} {Ω : Opens (Domain d)}
    {a : Domain d → ℝ} (ha : LocallyIntegrableOn a Ω volume)
    (ψ : P102.U4.TestSpace ℝ Ω) :
    Distribution.ofFun Ω a volume ⊤ ψ = ∫ x, ψ x * a x ∂domainMeasure Ω := by
  rw [Distribution.ofFun_apply ha]
  change (∫ x, ψ x * a x) = _
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro x hx
  simp [ψ.zero_on_compl hx]

private theorem integrable_test_mul {d : ℕ} {Ω : Opens (Domain d)}
    {a : Domain d → ℝ} (ha : LocallyIntegrableOn a Ω volume)
    (ψ : P102.U4.TestSpace ℝ Ω) :
    Integrable (fun x => ψ x * a x) (domainMeasure Ω) := by
  exact (ψ.integrable_smul ha).restrict

/-- Testing the residual of one distributional row is the scalar weak pairing. -/
theorem row_residual_pairing {d m : ℕ} {Ω : Opens (Domain d)}
    {A : Domain d → Vector m} {B : Domain d → Gradient m d}
    (hA : ∀ i, LocallyIntegrableOn (fun x => A x i) Ω volume)
    (hB : ∀ i j, LocallyIntegrableOn (fun x => B x (i,j)) Ω volume)
    (i : Fin m) (ψ : P102.U4.TestSpace ℝ Ω) :
    (Distribution.ofFun Ω (fun x => A x i) volume ⊤ - rowDivergence Ω B i) ψ =
      ∫ x, (ψ x * A x i + ∑ j : Fin d,
        (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d j) ψ :
          P102.U4.TestSpace ℝ Ω) x * B x (i,j)) ∂domainMeasure Ω := by
  classical
  rw [integral_add (integrable_test_mul (hA i) ψ)
    (integrable_finsetSum _ (fun j _ => integrable_test_mul (hB i j) _))]
  rw [integral_finsetSum _ (fun j _ => integrable_test_mul (hB i j) _)]
  simp only [sub_apply, regular_pairing_restrict (hA i), rowDivergence, sum_apply,
    Distribution.lineDerivCLM_apply]
  simp only [regular_pairing_restrict (hB i _), Finset.sum_neg_distrib, sub_neg_eq_add]


/-- Resolve the Euclidean and Frobenius pairings into scalar test functions. -/
theorem weakDensity_eq_sum {d m : ℕ} {Ω : Opens (Domain d)}
    (A : Domain d → Vector m) (B : Domain d → Gradient m d)
    (φ : VectorTest Ω m) (x : Domain d) :
    weakDensity A B φ x = ∑ i : Fin m,
      ((vectorTestCoordinate Ω φ i) x * A x i + ∑ j : Fin d,
        (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d j)
          (vectorTestCoordinate Ω φ i) : P102.U4.TestSpace ℝ Ω) x * B x (i,j)) := by
  simp only [weakDensity, frobenius_eq_sum, PiLp.inner_apply, Real.inner_apply,
    ← testGradient_coordinate, ← Finset.sum_add_distrib]
  congr 1
  ext i
  congr 1
  · simp [vectorTestCoordinate, mul_comm]
  · apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

/-- The full weak pairing is the sum of the row residuals on the coordinate tests. -/
theorem weak_integral_eq_row_residuals {d m : ℕ} {Ω : Opens (Domain d)}
    {A : Domain d → Vector m} {B : Domain d → Gradient m d}
    (hA : ∀ i, LocallyIntegrableOn (fun x => A x i) Ω volume)
    (hB : ∀ i j, LocallyIntegrableOn (fun x => B x (i,j)) Ω volume)
    (φ : VectorTest Ω m) :
    (∫ x, weakDensity A B φ x ∂domainMeasure Ω) =
      ∑ i : Fin m, (Distribution.ofFun Ω (fun x => A x i) volume ⊤ - rowDivergence Ω B i)
        (vectorTestCoordinate Ω φ i) := by
  simp_rw [row_residual_pairing hA hB]
  simp_rw [weakDensity_eq_sum]
  apply integral_finsetSum
  intro i _
  exact (integrable_test_mul (hA i) _).add
    (integrable_finsetSum _ (fun j _ => integrable_test_mul (hB i j) _))

/-- Row by row distributional form, equivalent to the original vector test identity. -/
theorem distributional_euler_lagrange : Expected.DistributionalEquation := by
  intro d m Ω A B hA hB
  classical
  constructor
  · intro hw i
    ext ψ
    let φ : VectorTest Ω m := TestFunction.postcompCLM
      (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ))) ψ
    have hc : ∀ k : Fin m, vectorTestCoordinate Ω φ k = if k = i then ψ else 0 := by
      intro k
      ext x
      by_cases hk : k = i
      · subst k
        simp [vectorTestCoordinate, φ]
      · simp [vectorTestCoordinate, φ, hk]
    have H := hw φ
    rw [weak_integral_eq_row_residuals hA hB] at H
    rw [Finset.sum_eq_single i] at H
    · simpa [hc] using H
    · intro k _ hk
      simp [hc, hk]
    · simp
  · intro h φ
    rw [weak_integral_eq_row_residuals hA hB φ]
    simp [h]

/-- Continuous zero distributions vanish at every interior point. -/
theorem pointwise_euler_lagrange : Expected.PointwiseEquation := by
  intro d m Ω A B q hA hq hEL hdiv x hx
  apply PiLp.ext
  intro i
  have hAc : ContinuousOn (fun x => A x i) Ω :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp_continuousOn hA
  have hqc : ContinuousOn (fun x => q x i) Ω :=
    (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp_continuousOn hq
  have he : Distribution.ofFun Ω (fun x => A x i) volume ⊤ =
      Distribution.ofFun Ω (fun x => q x i) volume ⊤ := by
    rw [← hdiv i]
    exact sub_eq_zero.mp (hEL i)
  have hae := Distribution.ofFun_injective
    (hAc.locallyIntegrableOn Ω.isOpen.measurableSet)
    (hqc.locallyIntegrableOn Ω.isOpen.measurableSet) he
  exact (Measure.eqOn_open_of_ae_eq hae Ω.isOpen hAc hqc) hx


/-- The weak gradient of a smooth Sobolev class is its classical Jacobian. -/
theorem gradient_of_smooth_value {d m : ℕ} {Ω : Opens (Domain d)}
    (p : Exponent) (φ : VectorTest Ω m) (w : W1p Ω m p)
    (hw : value Ω m p w = testToValueLp Ω m p φ) :
    (gradient Ω m p w : Domain d → Gradient m d) =ᵐ[domainMeasure Ω] testGradient φ := by
  have hc (i : Fin m) (j : Fin d) :
      coordinateLp Ω p (i,j) (gradient Ω m p w) = P102.U4.testToDomainLp Ω p.ennreal
        (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d j)
          (vectorTestCoordinate Ω φ i) : P102.U4.TestSpace ℝ Ω) := by
    apply P102.U4.regularLp_injective Ω p.ennreal
    dsimp only
    rw [← distribution_derivative Ω p w i j, hw, coordinate_testToValueLp,
      P102.U4.regular_testToDomainLp, P102.U4.regular_testToDomainLp]
    rw [P102.U4.derivative_classicalCompatibility d ℝ Ω {j} (vectorTestCoordinate Ω φ i)
      ((vectorTestCoordinate Ω φ i).contDiff.of_le (by simp)).contDiffOn]
    congr 1
    ext x
    rw [TestFunction.lineDerivCLM_eq_fderivCLM]
    simp [P102.U4.multiPartial, P102.U4.partialWord]
  have hae (ij : Fin m × Fin d) :
      ∀ᵐ x ∂domainMeasure Ω, (gradient Ω m p w x) ij = testGradient φ x ij := by
    rcases ij with ⟨i,j⟩
    filter_upwards [coordinateLp_ae Ω p (i,j) (gradient Ω m p w),
      P102.U4.testToDomainLp_ae Ω p.ennreal
        (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d j)
          (vectorTestCoordinate Ω φ i) : P102.U4.TestSpace ℝ Ω)] with x hx hy
    rw [hc i j] at hx
    rw [← hx, hy, testGradient_coordinate]
  filter_upwards [Filter.eventually_all.mpr hae] with x hx
  exact PiLp.ext hx

/-- The line on representatives is exactly the line in the Sobolev space. -/
theorem lineEnergy_eq_sobolev_energy {d m : ℕ} {Ω : Opens (Domain d)}
    (p : Exponent) (F : Domain d → Vector m → Gradient m d → ℝ)
    (φ : VectorTest Ω m) (w : W1p Ω m p)
    (hw : value Ω m p w = testToValueLp Ω m p φ)
    (u : W1p Ω m p) (t : ℝ) :
    lineEnergy F (value Ω m p u) (gradient Ω m p u) φ t =
      energy Ω m p F (u + t • w) := by
  have hv : (value Ω m p w : Domain d → Vector m) =ᵐ[domainMeasure Ω] φ := by
    rw [hw]
    exact MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)
  have hg := gradient_of_smooth_value p φ w hw
  unfold lineEnergy energy
  symm
  apply energy_congr
  · simp only [map_add, map_smul]
    filter_upwards [Lp.coeFn_add (value Ω m p u) (t • value Ω m p w),
      Lp.coeFn_smul t (value Ω m p w), hv] with x hadd hsmul hval
    rw [hadd]
    change value Ω m p u x + (t • value Ω m p w) x = _
    rw [hsmul]
    change value Ω m p u x + t • value Ω m p w x = _
    rw [hval]
  · simp only [map_add, map_smul]
    filter_upwards [Lp.coeFn_add (gradient Ω m p u) (t • gradient Ω m p w),
      Lp.coeFn_smul t (gradient Ω m p w), hg] with x hadd hsmul hgrad
    rw [hadd]
    change gradient Ω m p u x + (t • gradient Ω m p w) x = _
    rw [hsmul]
    change gradient Ω m p u x + t • gradient Ω m p w x = _
    rw [hgrad]

/-- Dominated Euler--Lagrange with the local minimum stated on the actual
Sobolev energy `J(u + t • φ)`. Smooth tests have unique Sobolev classes. -/
theorem dominated_euler_lagrange : Expected.DominatedStationarity := by
  intro d m Ω p u F Fs FZ hF hder hfinite hmin hbound
  apply dominated_euler_lagrange_fields Ω p u F Fs FZ hF hder hfinite _ hbound
  intro φ
  obtain ⟨w, hw⟩ := smooth_vector_inclusion Ω p φ
  have he : lineEnergy F (value Ω m p u) (gradient Ω m p u) φ =
      fun t : ℝ => energy Ω m p F (u + t • w) := by
    funext t
    exact lineEnergy_eq_sobolev_energy p F φ w hw u t
  rw [he]
  exact hmin φ w hw

end VariationalNotes.Sobolev.EulerLagrange
