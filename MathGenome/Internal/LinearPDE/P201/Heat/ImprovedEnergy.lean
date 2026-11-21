import MathGenome.Internal.LinearPDE.P201Specs.Heat.ImprovedEnergy
import MathGenome.Internal.LinearPDE.P201.Heat.MildEnergyAgreement

/-! Abstract improved energy regularity (paper.tex, Theorem pde:heat-improved).

We test the finite Galerkin equations by their velocities on the cofinal
subspaces containing the initial datum. Weak compactness in L²(H) gives the
strong time derivative, and weak compactness in V gives a lift at every time.
The original weak equation then identifies the canonical operator value.
No compact embedding, separability, or spatial regularity is used. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
universe u v
namespace P201.Heat.ImprovedEnergy
open ExpandedFA.Evolution
open HilbertTripleSpec HilbertTripleTraceSpec
open MildEnergyAgreement

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Distributional differentiation commutes with a bounded linear map. -/
theorem derivative_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (T : ℝ) (b g : ℝ → E)
    (hb : derivativeValue T b g) :
    derivativeValue T (fun t => L (b t)) (fun t => L (g t)) := by
  exact hasTimeDerivative_map L T b g hb

/-- Any H-valued distributional derivative must be the given energy
solution's V'-valued derivative after the actual pivot injection. -/
theorem derivative_pivot_eq (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) (g : timeLpValue H 2 T)
    (hg : derivativeValue T (extendCurve z.curve) g) :
    z.derivative =ᵐ[timeMeasureValue T] fun t => pivotValue (triple d) (g t) := by
  have hd := derivative_comp (pivotValue (triple d)) T _ _ hg
  have hv : (fun t => pivotValue (triple d) (extendCurve z.curve t))
      =ᵐ[timeMeasureValue T] fun t => intoDualValue (triple d) (z.value t) := by
    filter_upwards [z.represents] with t ht
    rw [ht]
    rfl
  have hd' := (hasTimeDerivative_congr T _ _ _ _ hv Filter.EventuallyEq.rfl).mp hd
  exact hasTimeDerivative_unique T _ _ _ z.has_derivative hd'

/-- Once u' is in L²(H), the weak equation already supplies both the exact
operator domain and its action f-u'. No spatial regularity is involved. -/
theorem operator_graph_of_derivative (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) (g : timeLpValue H 2 T)
    (hg : derivativeValue T (extendCurve z.curve) g) :
    ∀ᵐ t ∂timeMeasureValue T,
      (extendCurve z.curve t, f t - g t) ∈ d.operator.graph := by
  filter_upwards [z.represents, z.equation, derivative_pivot_eq d T hT u₀ f z g hg]
    with t ht he hd
  rw [ht]
  apply (d.mem_graph_at (z.value t) (f t - g t)).mpr
  have ha : d.a (z.value t) = pivotValue (triple d) (f t - g t) := by
    rw [hd] at he
    rw [map_sub]
    exact eq_sub_of_add_eq (add_eq_of_eq_sub' he)
  intro w
  have hw := congrArg (fun ℓ : StrongDual ℝ V => ℓ w) ha
  change d.a (z.value t) w = pivotInjection (triple d) (f t - g t) w at hw
  simpa only [pivotInjection_apply, triple, real_inner_comm] using hw

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- L² norm bound for the operator value f-u'. -/
theorem sub_norm_sq_le (f g : timeLpValue H 2 T) :
    ‖f - g‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 2 * ‖g‖ ^ 2 := by
  have h := norm_sub_le f g
  have hs := sq_nonneg (‖f‖ - ‖g‖)
  nlinarith [norm_nonneg (f - g), norm_nonneg f, norm_nonneg g]

omit [CompleteSpace V] [CompleteSpace H] in
/-- Positive quadratic form bounds are preserved by arbitrary weakly
convergent nets. This needs no separability or spectral representation. -/
theorem form_energy_le_of_weak_limit {I : Type*} {l : Filter I} [l.NeBot]
    (d : CoerciveForm V H) (x : I → V) (y : V) (D : ℝ)
    (hweak : ∀ ℓ : StrongDual ℝ V,
      Filter.Tendsto (fun i => ℓ (x i)) l (nhds (ℓ y)))
    (hb : ∀ᶠ i in l, d.a (x i) (x i) ≤ D) : d.a y y ≤ D := by
  have hnonneg (v : V) : 0 ≤ d.a v v := by
    obtain ⟨c, hc, hcb⟩ := d.coercive
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hcb v)
  have ht : Filter.Tendsto (fun i => 2 * d.a y (x i) - d.a y y)
      l (nhds (d.a y y)) := by
    simpa only [two_mul, add_sub_cancel_left] using
      ((hweak (d.a y)).const_mul 2).sub_const (d.a y y)
  apply le_of_tendsto ht
  filter_upwards [hb] with i hi
  have hp := hnonneg (x i - y)
  simp only [map_sub, sub_apply] at hp
  rw [d.symmetric (x i) y] at hp
  linarith

omit [CompleteSpace H] in
/-- A pointwise weak H limit of an energy-bounded net has a V lift.
Weak compactness is used in V, without a compact embedding V → H. -/
theorem lift_of_weak_limit {I : Type*} {l : Filter I} [l.NeBot]
    (d : CoerciveForm V H) (x : I → V) (h : H) (D : ℝ) (hD : 0 ≤ D)
    (hweak : ∀ ℓ : StrongDual ℝ H,
      Filter.Tendsto (fun i => ℓ (d.j (x i))) l (nhds (ℓ h)))
    (hb : ∀ᶠ i in l, d.a (x i) (x i) ≤ D) :
    ∃ y : V, d.j y = h ∧ d.a y y ≤ D := by
  obtain ⟨c, hc, hcoerc⟩ := d.coercive
  have hn : ∀ᶠ i in l, ‖x i‖ ≤ Real.sqrt (D / c) := by
    filter_upwards [hb] with i hi
    apply (Real.le_sqrt (norm_nonneg _) (div_nonneg hD hc.le)).mpr
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hcoerc (x i)).trans hi
  obtain ⟨y, _, F, hF, hFl, hy⟩ :=
    ParabolicGalerkin.exists_weak_limit_of_eventually_norm_le x _ hn
  let : F.NeBot := hF
  refine ⟨y, ?_, form_energy_le_of_weak_limit d x y D hy (hb.filter_mono hFl)⟩
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  exact tendsto_nhds_unique (hy (ℓ.comp d.j)) ((hweak ℓ).mono_left hFl)

/-- A bounded V lift of the continuous curve bounds the original Bochner
representative in L∞(V), by injectivity of the original embedding. -/
theorem value_memLp_top_of_lift (d : CoerciveForm V H) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT (d.j u₀) f) (w : Icc 0 T → V)
    (hw : ∀ t, d.j (w t) = z.curve t) (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ t, ‖w t‖ ^ 2 ≤ R) :
    MemLp (fun t => z.value t) ∞ (timeMeasureValue T) := by
  apply memLp_top_of_bound (Lp.memLp z.value).aestronglyMeasurable (R + 1)
  filter_upwards [z.represents, ae_restrict_mem measurableSet_Ioo] with t ht hti
  let tt : Icc 0 T := ⟨t, hti.1.le, hti.2.le⟩
  have he : z.value t = w tt := by
    apply d.injective
    rw [hw]
    exact ht.symm.trans (extendCurve_apply z.curve tt)
  rw [he]
  have := hb tt
  nlinarith [norm_nonneg (w tt)]

/-- The analytic a priori estimate gives the full conclusion, including
strong measurability, domain membership, and the required uniform constant. -/
theorem conclusion_of_a_priori (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α)
    (d : CoerciveForm V H) (hbound : ‖d.a‖ ≤ M)
    (hcoerc : ∀ x, α * ‖x‖ ^ 2 ≤ d.a x x)
    (T : ℝ) (hT : 0 < T) (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT.le (d.j u₀) f)
    (hap : APriori d T hT.le u₀ f z) :
    Conclusion ((5 + α⁻¹) * (M + 1)) d T hT.le u₀ f z := by
  obtain ⟨w, g, hw, hg, hgn, henergy⟩ := hap
  let D : ℝ := d.a u₀ u₀ + ‖f‖ ^ 2
  have hau : 0 ≤ d.a u₀ u₀ :=
    (mul_nonneg hα.le (sq_nonneg _)).trans (hcoerc u₀)
  have hD : 0 ≤ D := add_nonneg hau (sq_nonneg _)
  have hfn : ‖f‖ ^ 2 ≤ D := by dsimp [D]; linarith
  have hwbound (t : Icc 0 T) : ‖w t‖ ^ 2 ≤ D / α := by
    apply (le_div_iff₀ hα).mpr
    simpa only [mul_comm] using (hcoerc (w t)).trans (henergy t)
  have hR : 0 ≤ D / α := div_nonneg hD hα.le
  have hBdd : BddAbove (Set.range (fun t => ‖w t‖ ^ 2)) :=
    ⟨D / α, by rintro _ ⟨t, rfl⟩; exact hwbound t⟩
  have hsup : supremumSquare w ≤ D / α := by
    apply csSup_le
    · exact ⟨‖w ⟨0, by simp [hT.le]⟩‖ ^ 2, ⟨0, by simp [hT.le]⟩, rfl⟩
    · rintro _ ⟨t, rfl⟩
      exact hwbound t
  let b := f - g
  have hbeq : (b : ℝ → H) =ᵐ[timeMeasureValue T] fun t => f t - g t :=
    Lp.coeFn_sub f g
  let r : Regularity d T hT.le u₀ f z :=
    { lift := w
      lift_eq := hw
      velocity := g
      operatorValue := b
      has_derivative := hg
      derivative_eq := derivative_pivot_eq d T hT.le u₀ f z g hg
      graph := by
        filter_upwards [operator_graph_of_derivative d T hT.le u₀ f z g hg, hbeq]
          with t ht hb
        simpa only [hb] using ht
      equation := by
        filter_upwards [hbeq] with t ht
        rw [ht]
        abel
      lift_bounded := hBdd
      value_linf := value_memLp_top_of_lift d T hT.le u₀ f z w hw _ hR hwbound }
  refine ⟨r, ?_⟩
  have hbn : ‖b‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 2 * ‖g‖ ^ 2 := sub_norm_sq_le f g
  have hfirst : ‖g‖ ^ 2 + ‖b‖ ^ 2 + supremumSquare w ≤ (5 + α⁻¹) * D := by
    have hR_eq : D / α = α⁻¹ * D := by rw [div_eq_mul_inv, mul_comm]
    rw [hR_eq] at hsup
    nlinarith
  have ha_bound : d.a u₀ u₀ ≤ M * ‖u₀‖ ^ 2 := by
    calc
      d.a u₀ u₀ ≤ ‖d.a u₀ u₀‖ := le_abs_self _
      _ ≤ ‖d.a‖ * ‖u₀‖ * ‖u₀‖ := d.a.le_opNorm₂ _ _
      _ ≤ M * ‖u₀‖ * ‖u₀‖ := by gcongr
      _ = M * ‖u₀‖ ^ 2 := by ring
  have hdata : D ≤ (M + 1) * (‖u₀‖ ^ 2 + ‖f‖ ^ 2) := by
    dsimp only [D]
    nlinarith [mul_nonneg hM (sq_nonneg ‖f‖), sq_nonneg ‖u₀‖]
  change ‖g‖ ^ 2 + ‖b‖ ^ 2 + supremumSquare w ≤ _
  exact hfirst.trans (by
    calc
      (5 + α⁻¹) * D ≤ (5 + α⁻¹) * ((M + 1) * (‖u₀‖ ^ 2 + ‖f‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hdata (by positivity)
      _ = _ := by ring)

/-- Assembly needs only the analytic a priori theorem. The remaining
quantitative constant and all operator conclusions are proved above. -/
theorem improved_energy_of_a_priori (h : APrioriTheorem.{u,v}) :
    ImprovedEnergyTheorem.{u,v} := by
  intro M α hM hα
  refine ⟨(5 + α⁻¹) * (M + 1), by positivity, ?_⟩
  intro V H _ _ _ _ _ _ d hb hc T hT u₀ f z
  exact conclusion_of_a_priori M α hM hα d hb hc T hT u₀ f z (h d T hT u₀ f z)

open ParabolicGalerkinSpec

omit [CompleteSpace H] in
/-- Product rule for a bounded symmetric form along a strong L² curve. -/
theorem form_energy_identity (d : CoerciveForm V H) (T : ℝ) (hT : 0 < T)
    (u g : timeLpValue V 2 T) (c : TraceCurve V T)
    (hr : extendCurve c =ᵐ[timeMeasureValue T] (u : ℝ → V))
    (hd : derivativeValue T (u : ℝ → V) g) (s t : Icc 0 T) :
    d.a (c t) (c t) - d.a (c s) (c s) =
      2 * ∫ r in s.val..t.val, d.a (u r) (g r) := by
  let j : HilbertTriple V V :=
    ⟨ContinuousLinearMap.id ℝ V, Function.injective_id, denseRange_id⟩
  let A : V →L[ℝ] V := InnerProductSpace.continuousLinearMapOfBilin d.a
  have hA (x y : V) : inner ℝ (A x) y = d.a x y :=
    InnerProductSpace.continuousLinearMapOfBilin_apply d.a x y
  let B := intoDualValue j
  let D := B.compLp g
  let Au := A.compLp u
  let AD := B.compLp (A.compLp g)
  have hD : tripleDerivativeValue j T u D := by
    apply (hasTimeDerivative_congr T _ _ _ _ Filter.EventuallyEq.rfl
      (Filter.EventuallyEq.symm (B.coeFn_compLp g))).mp
    exact hasTimeDerivative_map B T _ _ hd
  have hAD : tripleDerivativeValue j T Au AD := by
    apply (hasTimeDerivative_congr T _ _ _ _
      (Filter.EventuallyEq.rfl) (Filter.EventuallyEq.symm (B.coeFn_compLp (A.compLp g)))).mp
    apply hasTimeDerivative_map B T _ _
    exact (hasTimeDerivative_congr T _ _ _ _ (Filter.EventuallyEq.symm (A.coeFn_compLp u))
      (Filter.EventuallyEq.symm (A.coeFn_compLp g))).mp (hasTimeDerivative_map A T _ _ hd)
  let z : energySpaceValue j T := ⟨(u, D), hD⟩
  let w : energySpaceValue j T := ⟨(Au, AD), hAD⟩
  let Ac : TraceCurve V T := ⟨fun t => A (c t), A.continuous.comp c.continuous⟩
  obtain ⟨tr, hrep, huniq, _, _, _, hprod⟩ := P201.Common.TimeTrace.time_trace j T hT
  have hz : c = tr z := huniq z c hr
  have hw : Ac = tr w := by
    apply huniq w Ac
    filter_upwards [hr, A.coeFn_compLp u, ae_restrict_mem measurableSet_Ioo]
      with r hrr har hri
    change extendCurve Ac r = Au r
    rw [har]
    have hcc := Ioo_subset_Icc_self hri
    simpa only [extendCurve, dite_eq_left hcc, Ac, ContinuousMap.coe_mk] using congrArg A hrr
  have hid := (hprod w z).2.2.2 s t
  rw [← hz, ← hw] at hid
  simp only [P201Specs.Common.TimeTrace.productCurve, extendCurve_apply, Ac,
    ContinuousMap.coe_mk, hA] at hid
  rw [hid]
  have heq : (fun r => AD r (u r) + D r (Au r)) =ᵐ[timeMeasureValue T]
      fun r => (2 : ℝ) * d.a (u r) (g r) := by
    filter_upwards [B.coeFn_compLp (A.compLp g), B.coeFn_compLp g,
      A.coeFn_compLp u, A.coeFn_compLp g] with r h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    change (intoDual j (A (g r))) (u r) + (intoDual j (g r)) (A (u r)) = _
    simp only [intoDual_apply]
    change inner ℝ (A (g r)) (u r) + inner ℝ (g r) (A (u r)) = _
    rw [hA, show inner ℝ (g r) (A (u r)) = inner ℝ (A (u r)) (g r) from real_inner_comm _ _, hA, d.symmetric (g r)]
    ring
  rw [time_integral_congr_ae T heq s t, intervalIntegral.integral_const_mul]

/-- The improved energy inequality on each finite subspace containing the
initial datum. The constant is independent of that subspace and of T. -/
theorem galerkin_derivative_energy_bound (d : CoerciveForm V H)
    (T : ℝ) (hT : 0 < T) (u₀ : V) (f : timeLpValue H 2 T)
    (E : FiniteSubspace V) (hu₀ : u₀ ∈ E.val)
    (G : GalerkinSolution (triple d) T hT.le (fun _ => algebraicForm d)
      (pivotLp d T f) (d.j u₀) E) :
    ‖((d.j.comp E.val.subtypeL).compLp G.velocity)‖ ^ 2 ≤
        d.a u₀ u₀ + ‖f‖ ^ 2 ∧
      ∀ t, d.a (G.curve t) (G.curve t) ≤ d.a u₀ u₀ + ‖f‖ ^ 2 := by
  let zero : Icc 0 T := ⟨0, le_rfl, hT.le⟩
  let c : TraceCurve V T :=
    ⟨fun t => (G.curve t : V), continuous_subtype_val.comp G.curve.continuous⟩
  let v := E.val.subtypeL.compLp G.velocity
  let g := (d.j.comp E.val.subtypeL).compLp G.velocity
  have hv : (v : ℝ → V) =ᵐ[timeMeasureValue T] fun r => (G.velocity r : V) :=
    E.val.subtypeL.coeFn_compLp G.velocity
  have hg : (g : ℝ → H) =ᵐ[timeMeasureValue T] fun r => d.j (G.velocity r) :=
    (d.j.comp E.val.subtypeL).coeFn_compLp G.velocity
  have hc : extendCurve c =ᵐ[timeMeasureValue T] (G.value : ℝ → V) := by
    filter_upwards [G.represents, ae_restrict_mem measurableSet_Ioo] with r hr hri
    simpa only [c, extendCurve, extendSubspaceCurve, dite_eq_left (Ioo_subset_Icc_self hri),
      ContinuousMap.coe_mk] using hr.symm
  have hd : derivativeValue T (G.value : ℝ → V) v :=
    (hasTimeDerivative_congr T _ _ _ _ Filter.EventuallyEq.rfl hv.symm).mp
      (ParabolicGalerkin.galerkin_hasTimeDerivative _ _ _ _ _ _ _ G)
  have hinit : (G.curve zero : V) = u₀ := by
    apply d.injective
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hi := G.initial (G.curve zero - (⟨u₀, hu₀⟩ : E.val))
    simpa only [triple, Submodule.coe_sub, map_sub, Subtype.coe_mk] using hi
  let q : ℝ → ℝ := fun r => ‖g r‖ ^ 2
  let b : ℝ → ℝ := fun r => d.a (G.value r) (v r)
  let p : ℝ → ℝ := fun r => ‖f r‖ ^ 2
  have hqi : Integrable q (timeMeasureValue T) :=
    (Lp.memLp g).integrable_norm_pow (by norm_num)
  have hpi : Integrable p (timeMeasureValue T) :=
    (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hbi : Integrable b (timeMeasureValue T) :=
    memLp_one_iff_integrable.mp (d.a.memLp_of_bilin 1 (Lp.memLp G.value) (Lp.memLp v))
  have heq : ∀ᵐ r ∂timeMeasureValue T, q r + 2 * b r ≤ p r := by
    filter_upwards [G.equation, (pivotValue (triple d)).coeFn_compLp f, hv, hg]
      with r he hf hvr hgr
    have he' := he (G.velocity r)
    change inner ℝ (d.j (G.velocity r)) (d.j (G.velocity r)) +
      d.a (G.value r) (G.velocity r) = (pivotLp d T f) r (G.velocity r) at he'
    change (pivotLp d T f) r = pivotValue (triple d) (f r) at hf
    rw [hf] at he'
    change _ = pivotInjection (triple d) (f r) (G.velocity r) at he'
    rw [pivotInjection_apply] at he'
    change inner ℝ (d.j (G.velocity r)) (d.j (G.velocity r)) +
      d.a (G.value r) (G.velocity r) = inner ℝ (f r) (d.j (G.velocity r)) at he'
    rw [real_inner_self_eq_norm_sq] at he'
    have hn := norm_sub_sq_real (f r) (d.j (G.velocity r))
    dsimp only [q, b, p]
    rw [hvr, hgr]
    nlinarith [sq_nonneg ‖f r - d.j (G.velocity r)‖]
  have hpartial (t : Icc 0 T) :
      (∫ r in 0..t.val, q r) + d.a (G.curve t) (G.curve t) ≤
        d.a u₀ u₀ + ∫ r in 0..t.val, p r := by
    have hid := form_energy_identity d T hT G.value v c hc hd zero t
    change d.a (G.curve t) (G.curve t) - d.a (G.curve zero) (G.curve zero) =
      2 * ∫ r in 0..t.val, b r at hid
    rw [hinit] at hid
    have hm := ParabolicGalerkin.time_intervalIntegral_mono T t t.property
      (hqi.add (hbi.const_mul 2)) hpi heq
    simp only [Pi.add_apply] at hm
    rw [intervalIntegral.integral_add
      (P201.Heat.ParabolicForms.time_interval_integrable hqi zero t)
      (P201.Heat.ParabolicForms.time_interval_integrable (hbi.const_mul 2) zero t),
      intervalIntegral.integral_const_mul] at hm
    linarith
  have hpbound (t : Icc 0 T) : (∫ r in 0..t.val, p r) ≤ ‖f‖ ^ 2 := by
    rw [← timeLp_integral_norm_sq T f]
    rw [intervalIntegral.integral_of_le t.property.1, integral_Ioc_eq_integral_Ioo]
    exact integral_mono_measure (Measure.restrict_mono_set _
      (Ioo_subset_Ioo le_rfl t.property.2)) (by filter_upwards [] with r; exact sq_nonneg _) hpi
  have hqpos (t : Icc 0 T) : 0 ≤ ∫ r in 0..t.val, q r :=
    intervalIntegral.integral_nonneg t.property.1 (by intros; exact sq_nonneg _)
  have hapos (t : Icc 0 T) : 0 ≤ d.a (G.curve t) (G.curve t) := by
    obtain ⟨α, hα, ha⟩ := d.coercive
    exact (mul_nonneg hα.le (sq_nonneg _)).trans (ha _)
  constructor
  · have he := hpartial ⟨T, hT.le, le_rfl⟩
    have hq : (∫ r in 0..T, q r) = ‖g‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
      exact timeLp_integral_norm_sq T g
    rw [hq] at he
    exact (le_add_of_nonneg_right (hapos _)).trans
      (he.trans (add_le_add_right (hpbound _) _))
  · intro t
    exact (le_add_of_nonneg_left (hqpos t)).trans
      ((hpartial t).trans (add_le_add_right (hpbound t) _))

/-- Weak convergence of both Bochner classes preserves the distributional
strong derivative. No pointwise or strong convergence is assumed. -/
theorem derivative_of_weak_limits {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] {I : Type*} {F : Filter I} [F.NeBot]
    (T : ℝ) (u g : timeLpValue K 2 T) (us gs : I → timeLpValue K 2 T)
    (hu : ∀ e : StrongDual ℝ (timeLpValue K 2 T),
      Filter.Tendsto (fun i => e (us i)) F (nhds (e u)))
    (hg : ∀ e : StrongDual ℝ (timeLpValue K 2 T),
      Filter.Tendsto (fun i => e (gs i)) F (nhds (e g)))
    (hd : ∀ i, derivativeValue T (us i : ℝ → K) (gs i)) :
    derivativeValue T (u : ℝ → K) g := by
  let : IsLocallyFiniteMeasure (timeMeasureValue T) := by
    dsimp [timeMeasureValue]; infer_instance
  have hul := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hgl := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((Lp.memLp g).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  refine ⟨hul, hgl, ?_⟩
  intro φ hφ
  have hleft : Integrable (fun t => deriv φ t • u t) (timeMeasureValue T) :=
    ((Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable_smul_left_of_hasCompactSupport
      (hφ.1.continuous_deriv (by simp)) hφ.2.1.deriv
  have hright : Integrable (fun t => φ t • g t) (timeMeasureValue T) :=
    ((Lp.memLp g).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable_smul_left_of_hasCompactSupport
      hφ.1.continuous hφ.2.1
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro e
  obtain ⟨L, hL⟩ := ParabolicGalerkin.scalar_time_test_functional T (deriv φ)
    (hφ.1.continuous_deriv (by simp)) hφ.2.1.deriv e
  obtain ⟨R, hR⟩ := ParabolicGalerkin.scalar_time_test_functional T φ
    hφ.1.continuous hφ.2.1 e
  have heq (i : I) : L (us i) = -R (gs i) := by
    have h := congrArg e ((hd i).2.2 φ hφ)
    have hi := hasTimeDerivative_test_integrable T _ _ (hd i) φ hφ
    dsimp only [timeMeasure] at hi
    rw [map_neg, ← e.integral_comp_comm hi.1, ← e.integral_comp_comm hi.2] at h
    simpa only [hL, hR, map_smul, smul_eq_mul] using h
  have hlim := tendsto_nhds_unique ((hu L).congr' (Filter.Eventually.of_forall heq))
    (hg R).neg
  rw [map_neg, ← e.integral_comp_comm hleft, ← e.integral_comp_comm hright]
  simpa only [hL, hR, map_smul, smul_eq_mul] using hlim

/-- A continuous representative of a strong Sobolev curve has the expected
integral increments, including both endpoints. -/
theorem continuous_derivative_increment {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] (T : ℝ) (hT : 0 < T)
    (c : TraceCurve K T) (g : timeLpValue K 2 T)
    (hd : derivativeValue T (extendCurve c) g) (s t : Icc 0 T) :
    c t - c s = ∫ r in s.val..t.val, g r := by
  have hcint : Integrable (extendCurve c) (timeMeasureValue T) :=
    ((extendCurve_continuousOn c).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  obtain ⟨P, hPc, hrep, hinc⟩ := hasTimeDerivative_continuous_primitive T
    (extendCurve c) g hcint (timeLp_integrable T g) hd
  have hopen : EqOn (extendCurve c) P (Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq hrep isOpen_Ioo
      ((extendCurve_continuousOn c).mono Ioo_subset_Icc_self) hPc.continuousOn
  have hclosed : EqOn (extendCurve c) P (Icc 0 T) := by
    apply hopen.of_subset_closure (extendCurve_continuousOn c) hPc.continuousOn
      Ioo_subset_Icc_self
    rw [closure_Ioo (ne_of_lt hT)]
  simpa only [← hclosed t.property, ← hclosed s.property, extendCurve_apply] using hinc s t

/-- Integration on an initial subinterval is a bounded linear functional
on the actual L² class after testing by a continuous linear functional. -/
theorem interval_integral_functional {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [CompleteSpace K] (T : ℝ) (t : Icc 0 T)
    (e : StrongDual ℝ K) :
    ∃ L : StrongDual ℝ (timeLpValue K 2 T), ∀ q,
      L q = e (∫ r in 0..t.val, q r) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo 0 T)))
  let ψ : ℝ → ℝ := (Ioo 0 t.val).indicator (fun _ => 1)
  have hψ : MemLp ψ 2 (timeMeasureValue T) :=
    (memLp_const (1 : ℝ)).indicator measurableSet_Ioo.nullMeasurableSet
  obtain ⟨L, hL⟩ := ParabolicGalerkin.scalar_time_test_functional_of_memLp T ψ hψ e
  refine ⟨L, ?_⟩
  intro q
  rw [hL, ← e.intervalIntegral_comp_comm
    (timeLp_intervalIntegrable T q ⟨0, le_rfl, t.property.1.trans t.property.2⟩ t)]
  have hψq : (fun r => ψ r * e (q r)) = (Ioo 0 t.val).indicator (fun r => e (q r)) := by
    funext r
    by_cases hr : r ∈ Ioo 0 t.val <;> simp [ψ, hr]
  rw [hψq]
  rw [integral_indicator measurableSet_Ioo]
  change (∫ r, e (q r) ∂(volume.restrict (Ioo 0 T)).restrict (Ioo 0 t.val)) = _
  rw [Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (Ioo_subset_Ioo le_rfl t.property.2),
    intervalIntegral.integral_of_le t.property.1, integral_Ioc_eq_integral_Ioo]

/-- The central a priori estimate, obtained from the cofinal tail of finite
subspaces containing the initial vector and weak compactness in L²(H). -/
theorem a_priori (d : CoerciveForm V H) (T : ℝ) (hT : 0 < T)
    (u₀ : V) (f : timeLpValue H 2 T)
    (z : EnergySolution d T hT.le (d.j u₀) f) : APriori d T hT.le u₀ f z := by
  classical
  obtain ⟨α, hα, hcoerc⟩ := d.coercive
  have ha : FormHypotheses (triple d) T (fun _ => algebraicForm d) ‖d.a‖ α 0 := by
    refine ⟨hα, fun _ _ => aemeasurable_const, Filter.Eventually.of_forall ?_, ?_⟩
    · intro t
      refine ⟨d.a.le_opNorm₂, ?_⟩
      intro x
      simpa only [zero_mul, sub_zero, algebraicForm, LinearMap.mk₂_apply] using hcoerc x
    · intro x
      simpa only [autonomous_formOperator] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => d.a x)
          (timeMeasureValue T))
  obtain ⟨K, _, hex⟩ := ParabolicGalerkin.galerkin_existence_pos
    (triple d) T hT.le hT ‖d.a‖ α 0
  obtain ⟨G, zz, _, _, F, hF, hFat, hweak⟩ := hex _ ha (pivotLp d T f) (d.j u₀)
  let : F.NeBot := hF
  let zW : WeakSolution (triple d) T hT.le (fun _ => algebraicForm d) ‖d.a‖
      (pivotLp d T f) (d.j u₀) :=
    { value := z.value
      derivative := z.derivative
      curve := z.curve
      represents := z.represents
      has_derivative := z.has_derivative
      equation := by
        filter_upwards [z.equation, (pivotValue (triple d)).coeFn_compLp f]
          with t ht hf
        change (pivotLp d T f) t = pivotValue (triple d) (f t) at hf
        rw [hf, autonomous_formOperator]
        exact ht
      initial := z.initial }
  have hzz : zz = zW := ExpandedFA.Evolution.ParabolicForms.weakSolution_unique_pos
    (triple d) T hT.le hT _ ‖d.a‖ α 0 ha _ _ zz zW
  have hzvalue : zz.value = z.value := congrArg WeakSolution.value hzz
  rw [hzvalue] at hweak
  let D : ℝ := d.a u₀ u₀ + ‖f‖ ^ 2
  have hD : 0 ≤ D := add_nonneg
    ((mul_nonneg hα.le (sq_nonneg _)).trans (hcoerc u₀)) (sq_nonneg _)
  let us (E : FiniteSubspace V) := d.j.compLp (G E).value
  let gs (E : FiniteSubspace V) :=
    (d.j.comp E.val.subtypeL).compLp (G E).velocity
  have hbounds : ∀ᶠ E : FiniteSubspace V in F,
      ‖gs E‖ ^ 2 ≤ D ∧ ∀ t, d.a ((G E).curve t) ((G E).curve t) ≤ D := by
    filter_upwards [(ParabolicGalerkin.eventually_mem_finiteSubspace u₀).filter_mono hFat]
      with E hE
    exact galerkin_derivative_energy_bound d T hT u₀ f E hE (G E)
  have hgn : ∀ᶠ E in F, ‖gs E‖ ≤ Real.sqrt D := by
    filter_upwards [hbounds] with E hE
    nlinarith [Real.sq_sqrt hD, norm_nonneg (gs E), Real.sqrt_nonneg D]
  obtain ⟨g, hgnorm, L, hL, hLF, hweakg⟩ :=
    ParabolicGalerkin.exists_weak_limit_of_eventually_norm_le gs (Real.sqrt D) hgn
  let : L.NeBot := hL
  have hgu : ‖g‖ ^ 2 ≤ D := by
    nlinarith [Real.sq_sqrt hD, norm_nonneg g, Real.sqrt_nonneg D]
  have hweakus : ∀ e : StrongDual ℝ (timeLpValue H 2 T),
      Filter.Tendsto (fun E => e (us E)) L (nhds (e (d.j.compLp z.value))) := by
    intro e
    exact (hweak (e.comp (d.j.compLpL 2 (timeMeasureValue T)))).mono_left hLF
  have hdE (E : FiniteSubspace V) : derivativeValue T (us E : ℝ → H) (gs E) := by
    have hd := hasTimeDerivative_map d.j T _ _
      (ParabolicGalerkin.galerkin_hasTimeDerivative _ _ _ _ _ _ E (G E))
    exact (hasTimeDerivative_congr T _ _ _ _
      (Filter.EventuallyEq.symm (d.j.coeFn_compLp (G E).value))
      (Filter.EventuallyEq.symm ((d.j.comp E.val.subtypeL).coeFn_compLp (G E).velocity))).mp hd
  have hd := derivative_of_weak_limits T (d.j.compLp z.value) g us gs hweakus hweakg hdE
  have hrep : (d.j.compLp z.value : ℝ → H) =ᵐ[timeMeasureValue T] extendCurve z.curve :=
    Filter.EventuallyEq.trans (d.j.coeFn_compLp z.value) z.represents.symm
  have hder : derivativeValue T (extendCurve z.curve) g :=
    (hasTimeDerivative_congr T _ _ _ _ hrep Filter.EventuallyEq.rfl).mp hd
  let zero : Icc 0 T := ⟨0, le_rfl, hT.le⟩
  have hpoint (t : Icc 0 T) (e : StrongDual ℝ H) :
      Filter.Tendsto (fun E => e (d.j ((G E).curve t))) L (nhds (e (z.curve t))) := by
    obtain ⟨J, hJ⟩ := interval_integral_functional T t e
    have hlim := hweakg J
    simp only [hJ] at hlim
    have hc : d.j u₀ + (∫ r in 0..t.val, g r) = z.curve t := by
      have hi := continuous_derivative_increment T hT z.curve g hder zero t
      rw [z.initial] at hi
      change z.curve t - d.j u₀ = _ at hi
      rw [← hi]
      abel
    have hfinite : ∀ᶠ E in L,
        d.j u₀ + (∫ r in 0..t.val, gs E r) = d.j ((G E).curve t) := by
      filter_upwards [(ParabolicGalerkin.eventually_mem_finiteSubspace u₀).filter_mono
        (hLF.trans hFat)] with E hE
      have hinit : ((G E).curve zero : V) = u₀ := by
        apply d.injective
        apply sub_eq_zero.mp
        apply (inner_self_eq_zero (𝕜 := ℝ)).mp
        have hi := (G E).initial ((G E).curve zero - (⟨u₀, hE⟩ : E.val))
        simpa only [triple, Submodule.coe_sub, map_sub, Subtype.coe_mk] using hi
      let B := d.j.comp E.val.subtypeL
      have hi := congrArg B ((G E).integral_equation zero t)
      rw [map_sub, ← B.intervalIntegral_comp_comm
        (timeLp_intervalIntegrable T (G E).velocity zero t)] at hi
      change d.j ((G E).curve t) - d.j ((G E).curve zero) =
        ∫ r in 0..t.val, B ((G E).velocity r) at hi
      rw [← time_integral_congr_ae T (B.coeFn_compLp (G E).velocity) zero t, hinit] at hi
      change d.j ((G E).curve t) - d.j u₀ = ∫ r in 0..t.val, gs E r at hi
      rw [← hi]
      abel
    have hconv : Filter.Tendsto
        (fun E => e (d.j u₀) + e (∫ r in 0..t.val, gs E r)) L
        (nhds (e (d.j u₀) + e (∫ r in 0..t.val, g r))) :=
      tendsto_const_nhds.add hlim
    have hh : Filter.Tendsto (fun E => e (d.j ((G E).curve t))) L
        (nhds (e (d.j u₀) + e (∫ r in 0..t.val, g r))) :=
      hconv.congr' (hfinite.mono fun E hE => by rw [← map_add, hE])
    have hc' : e (d.j u₀) + e (∫ r in 0..t.val, g r) = e (z.curve t) := by
      rw [← map_add, hc]
    rw [hc'] at hh
    exact hh
  have hlift (t : Icc 0 T) : ∃ w : V, d.j w = z.curve t ∧ d.a w w ≤ D := by
    apply lift_of_weak_limit d (fun E => ((G E).curve t : V)) (z.curve t) D hD
      (hpoint t)
    exact (hbounds.filter_mono hLF).mono fun E hE => hE.2 t
  choose w hw hwb using hlift
  exact ⟨w, g, hw, hder, hgu, hwb⟩

/-- The full abstract improved regularity theorem, with no compactness or
spatial regularity hypothesis. -/
theorem improved_energy : ImprovedEnergyTheorem.{u,v} :=
  improved_energy_of_a_priori (fun d T hT u₀ f z => a_priori d T hT u₀ f z)

end P201.Heat.ImprovedEnergy
