import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.JacobiCoercivity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.PositiveJacobiSolution
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.VariationSpaces
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter TopologicalSpace
open scoped InnerProductSpace ENNReal
namespace VariationalNotes.Classical.JacobiCoercivity

/-- The velocity of the actual curve is C¹ when its state is C²,
including the one-sided derivatives at the endpoints. -/
theorem velocity_contDiffOn {I : Interval} {m : ℕ} (u : C1Curve I m)
    (hu : ContDiffOn ℝ 2 (stateField I m u) (Icc I.a I.b)) :
    ContDiffOn ℝ 1 (velocityField I m u) (Icc I.a I.b) := by
  apply (hu.derivWithin (uniqueDiffOn_Icc I.increasing) (by norm_num)).congr
  intro t ht
  simpa only [velocityField, extendState, dite_eq_left ht] using
    VariationSpaces.velocity_eq_derivWithin I m u ⟨t, ht⟩

/-- The Hessian along the curve has C¹ regularity under the source's
C³-near-the-graph hypothesis. This uses ambient derivatives only on the
open regularity neighborhood. -/
theorem hessian_contDiffOn {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m)
    (hu : ContDiffOn ℝ 2 (stateField I m u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3) :
    ContDiffOn ℝ 1 (fun t => fderiv ℝ (fderiv ℝ L.value)
      (t, stateField I m u t, velocityField I m u t)) (Icc I.a I.b) := by
  obtain ⟨U, hU, hgraph, _, hL⟩ := hreg
  have hfirst : ContDiffOn ℝ 2 (fderiv ℝ L.value) U :=
    hL.fderiv_of_isOpen hU (by norm_num)
  have hsecond : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ L.value)) U :=
    hfirst.fderiv_of_isOpen hU (by norm_num)
  apply hsecond.comp (contDiffOn_id.prodMk
    ((hu.of_le (by norm_num)).prodMk (velocity_contDiffOn u hu)))
  intro t ht
  simpa [graphPoint, stateField, velocityField, extendState, ht] using hgraph ⟨t, ht⟩

/-- All scalar Hessian coefficients are C¹, with their actual definitions. -/
theorem coefficients_contDiffOn {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3) :
    ContDiffOn ℝ 1 (coefficientP L u) (Icc I.a I.b) ∧
    ContDiffOn ℝ 1 (coefficientB L u) (Icc I.a I.b) ∧
    ContDiffOn ℝ 1 (coefficientC L u) (Icc I.a I.b) := by
  have hh := hessian_contDiffOn L u hu hreg
  exact ⟨(hh.clm_apply contDiffOn_const).clm_apply contDiffOn_const,
    (hh.clm_apply contDiffOn_const).clm_apply contDiffOn_const,
    (hh.clm_apply contDiffOn_const).clm_apply contDiffOn_const⟩

/-- In particular the reduced potential C−B′ is continuous on the entire
closed interval; no extra coefficient regularity is assumed. -/
theorem potential_continuousOn {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3) :
    ContinuousOn (coefficientV L u) (Icc I.a I.b) := by
  obtain ⟨_, hB, hC⟩ := coefficients_contDiffOn L u hu hreg
  exact hC.continuousOn.sub
    (hB.continuousOn_derivWithin (uniqueDiffOn_Icc I.increasing) le_rfl)

/-- The scalar fiber is the existing Euclidean fiber of dimension one. -/
lemma state_eq_scalarUnit (z : State 1) : z = z 0 • scalarUnit := by
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [scalarUnit]

/-- Exact scalarization of all three Hessian blocks, retaining the original
Lagrangian's Hessian and its state/velocity insertion conventions. -/
theorem secondVariation_scalarization (L : Lagrangian 1)
    (x : ℝ × State 1 × State 1) (z v : State 1) :
    secondVariationZZ L x z z = secondVariationZZ L x scalarUnit scalarUnit * (z 0) ^ 2 ∧
    secondVariationZV L x z v = secondVariationZV L x scalarUnit scalarUnit * z 0 * v 0 ∧
    secondVariationVV L x v v = secondVariationVV L x scalarUnit scalarUnit * (v 0) ^ 2 := by
  have hz : ((0 : ℝ), z, (0 : State 1)) =
      z 0 • ((0 : ℝ), scalarUnit, (0 : State 1)) := by
    rw [state_eq_scalarUnit z]
    simp [scalarUnit]
  have hv : ((0 : ℝ), (0 : State 1), v) =
      v 0 • ((0 : ℝ), (0 : State 1), scalarUnit) := by
    rw [state_eq_scalarUnit v]
    simp [scalarUnit]
  simp only [secondVariationZZ, secondVariationZV, secondVariationVV, hz, hv,
    map_smul, smul_apply, smul_eq_mul]
  constructor
  · ring
  constructor <;> ring

/-- The classical form is exactly the scalar coefficient expression before
integrating its mixed term by parts. No regularity or stationarity is needed
for this algebraic bridge. -/
theorem secondVariationForm_coefficients (I : Interval) (L : Lagrangian 1)
    (u η : C1Curve I 1) :
    secondVariationForm L u η = ∫ t in I.a..I.b,
      coefficientC L u t * (stateField I 1 η t 0) ^ 2 +
      2 * coefficientB L u t * stateField I 1 η t 0 * velocityField I 1 η t 0 +
      coefficientP L u t * (velocityField I 1 η t 0) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t _
  obtain ⟨hzz, hzv, hvv⟩ := secondVariation_scalarization L
    (t, stateField I 1 u t, velocityField I 1 u t)
    (stateField I 1 η t) (velocityField I 1 η t)
  dsimp [coefficientP, coefficientB, coefficientC]
  rw [hzz, hzv, hvv]
  ring

/-- A bounded measurable scalar weight gives a continuous quadratic
functional on L². The proof uses the actual Bochner integral. -/
theorem continuous_weighted_square {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : X → ℝ) (hw : MemLp w ∞ μ) (hp : p = 2) :
    Continuous (fun f : Lp E p μ => ∫ x, w x * ‖f x‖ ^ 2 ∂μ) := by
  subst p
  let B : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  let T : Lp E 2 μ →L[ℝ] Lp E 2 μ := B.holderL μ ∞ 2 2 (hw.toLp w)
  have he (f : Lp E 2 μ) :
      ⟪T f, f⟫_ℝ = ∫ x, w x * ‖f x‖ ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [B.coeFn_holder (r := 2) (hw.toLp w) f, hw.coeFn_toLp]
      with x hx hwx
    change ⟪B.holder 2 (hw.toLp w) f x, f x⟫_ℝ = _
    rw [hx, hwx]
    simp [B, real_inner_smul_left]
  simp_rw [← he]
  exact T.continuous.inner continuous_id

/-- Pulling a continuous interval coefficient back to the Euclidean interval
makes a bounded measurable coefficient for all Sobolev integrals. -/
theorem interval_weight_memLp (I : Interval) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc I.a I.b)) :
    MemLp (fun x : Sobolev.Domain 1 => w (x 0)) ∞
      (Sobolev.domainMeasure (intervalDomain I)) := by
  have hc : ContinuousOn (fun x : Sobolev.Domain 1 => w (x 0))
      (intervalDomain I : Set (Sobolev.Domain 1)) :=
    hw.comp (PiLp.continuous_apply 2 _ 0).continuousOn
      (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hw.norm
  refine memLp_top_of_bound (hc.aestronglyMeasurable (intervalDomain I).isOpen.measurableSet) M ?_
  filter_upwards [ae_restrict_mem (intervalDomain I).isOpen.measurableSet] with x hx
  exact hM (mem_image_of_mem _ ⟨hx.1.le, hx.2.le⟩)

/-- The same reduced integral on the full H¹ space is useful for passing
inequalities through the defining closure of smooth tests. -/
def ambientReducedForm (I : Interval) (P V : ℝ → ℝ)
    (η : Sobolev.H1 (intervalDomain I) 1) : ℝ :=
  ∫ x, P (x 0) * ‖Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η x‖ ^ 2 +
    V (x 0) * ‖Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η x‖ ^ 2
    ∂Sobolev.domainMeasure (intervalDomain I)

/-- Continuity of the reduced form on the full existing H¹ space follows
from the L² bilinear pairing, without any representative regularity assumption. -/
theorem continuous_ambientReducedForm (I : Interval) {P V : ℝ → ℝ}
    (hP : ContinuousOn P (Icc I.a I.b)) (hV : ContinuousOn V (Icc I.a I.b)) :
    Continuous (ambientReducedForm I P V) := by
  let μ := Sobolev.domainMeasure (intervalDomain I)
  have hp := interval_weight_memLp I hP
  have hv := interval_weight_memLp I hV
  have hp2 : Sobolev.Exponent.two.ennreal = 2 := by
    norm_num [Sobolev.Exponent.two, Sobolev.Exponent.ennreal]
  have hcP := continuous_weighted_square (E := Sobolev.Gradient 1 1) μ _ hp hp2
  have hcV := continuous_weighted_square (E := Sobolev.Vector 1) μ _ hv hp2
  have hg := (Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two).continuous
  have hu := (Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two).continuous
  have he (η : Sobolev.H1 (intervalDomain I) 1) : ambientReducedForm I P V η =
      (∫ x, P (x 0) * ‖Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η x‖ ^ 2 ∂μ) +
      ∫ x, V (x 0) * ‖Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η x‖ ^ 2 ∂μ := by
    apply integral_add
    · have hm : MemLp (Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η) 2 μ := by
        convert Lp.memLp (Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η) using 1
        exact hp2.symm
      exact (hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_of_top_right hp
    · have hm : MemLp (Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η) 2 μ := by
        convert Lp.memLp (Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η) using 1
        exact hp2.symm
      exact (hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_of_top_right hv

  change Continuous (fun η => ambientReducedForm I P V η)
  simp_rw [he]
  exact (hcP.comp hg).add (hcV.comp hu)

/-- Restrict the continuous integral to the existing closed zero-boundary
subspace with its inherited full H¹ norm. -/
theorem continuous_reducedForm (I : Interval) {P V : ℝ → ℝ}
    (hP : ContinuousOn P (Icc I.a I.b)) (hV : ContinuousOn V (Icc I.a I.b)) :
    Continuous (reducedForm I P V) :=
  (continuous_ambientReducedForm I hP hV).comp continuous_subtype_val

/-- The source's full H¹ norm is controlled by the weak derivative on the
actual interval space, with no change of norm instances. -/
theorem full_norm_le_derivative (I : Interval) (η : Variation I) :
    ‖η‖ ≤ (I.b - I.a + 1) *
      ‖Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η.val‖ := by
  exact (Sobolev.slab_norm_equivalence (intervalDomain I) Sobolev.Exponent.two
    0 I.a I.b I.increasing (fun _ hx => hx) η).2

/-- A continuous quadratic inequality proved on smooth tests passes to
H¹₀, which is defined as their closure. No Sobolev representative is
assumed to be smooth or pointwise differentiable. -/
theorem bound_on_zero_of_bound_on_smooth {d m : ℕ}
    (Ω : Opens (Sobolev.Domain d)) (Q : Sobolev.H1 Ω m → ℝ)
    (hQ : Continuous Q) (κ : ℝ)
    (h : ∀ η : Sobolev.H1 Ω m, η ∈ Sobolev.smoothSubmodule Ω m Sobolev.Exponent.two →
      κ * ‖η‖ ^ 2 ≤ Q η) :
    ∀ η : Sobolev.H1Zero Ω m, κ * ‖η‖ ^ 2 ≤ Q η.val := by
  let S : Set (Sobolev.H1 Ω m) := {η | κ * ‖η‖ ^ 2 ≤ Q η}
  have hc : IsClosed S :=
    isClosed_le (continuous_const.mul (continuous_norm.pow 2)) hQ
  intro η
  exact closure_minimal h hc η.property

/-- Compact coefficient bounds used after the ground-state factorization.
The velocity bound is for the actual derivative v'=q/P. -/
theorem exists_jacobi_bounds {a b : ℝ} {P V : ℝ → ℝ}
    {Y : ℝ → ℝ × ℝ} (hP : ContinuousOn P (Icc a b))
    (hp : ∀ t ∈ Icc a b, 0 < P t) (hY : Jacobi.IsSolution P V a b Y)
    (hv : ∀ t ∈ Icc a b, 0 < (Y t).1) :
    ∃ c M : ℝ, 0 < c ∧ 0 < M ∧ ∀ t ∈ Icc a b,
      c ≤ P t * (Y t).1 ^ 2 ∧ |(Y t).1| ≤ M ∧ |(Y t).2 / P t| ≤ M := by
  have hvel := hY.1.snd.div hP (fun t ht => (hp t ht).ne')
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_forall_le'
    (hP.mul (hY.1.fst.pow 2)) (fun t ht => mul_pos (hp t ht) (sq_pos_of_pos (hv t ht)))
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image (hY.1.fst.norm.add hvel.norm)
  refine ⟨c, max M 0 + 1, hc, by positivity, ?_⟩
  intro t ht
  have hm : ‖(Y t).1‖ + ‖(Y t).2 / P t‖ ≤ M := hM (mem_image_of_mem _ ht)
  refine ⟨hmin t ht, ?_, ?_⟩
  · change ‖(Y t).1‖ ≤ _
    have := le_max_left M 0
    linarith [norm_nonneg ((Y t).2 / P t)]
  · change ‖(Y t).2 / P t‖ ≤ _
    have := le_max_left M 0
    linarith [norm_nonneg ((Y t).1)]

/-- The numerical part of the full-norm coercivity estimate. Here E₀,E₁
are the value/derivative energies of η=vζ, and Z₀,Z₁ those of ζ.
The constant is explicit and strictly positive. -/
theorem quantitative_coercivity {c M D E₀ E₁ Z₀ Z₁ Q : ℝ}
    (hc : 0 < c) (hM : 0 < M)
    (hvalue : E₀ ≤ M ^ 2 * Z₀)
    (hderivative : E₁ ≤ 2 * M ^ 2 * (Z₀ + Z₁))
    (hpoincare : Z₀ ≤ D ^ 2 * Z₁) (henergy : c * Z₁ ≤ Q) :
    0 < c / (M ^ 2 * (3 * D ^ 2 + 2)) ∧
      c / (M ^ 2 * (3 * D ^ 2 + 2)) * (E₀ + E₁) ≤ Q := by
  have hden : 0 < M ^ 2 * (3 * D ^ 2 + 2) := by positivity
  have hsum : E₀ + E₁ ≤ M ^ 2 * (3 * D ^ 2 + 2) * Z₁ := by
    have h := mul_le_mul_of_nonneg_left hpoincare (by positivity : 0 ≤ 3 * M ^ 2)
    nlinarith only [hvalue, hderivative, h]
  refine ⟨div_pos hc hden, ?_⟩
  calc
    _ ≤ c / (M ^ 2 * (3 * D ^ 2 + 2)) *
        (M ^ 2 * (3 * D ^ 2 + 2) * Z₁) :=
      mul_le_mul_of_nonneg_left hsum (div_pos hc hden).le
    _ = c * Z₁ := by field_simp
    _ ≤ Q := henergy

/-- The cancellation in the positive-solution factorization uses the momentum
q=Pv' and therefore needs no derivative of P in the calculation itself. -/
theorem jacobi_factorization {a b : ℝ} {P V : ℝ → ℝ} {Y : ℝ → ℝ × ℝ}
    (hab : a < b) (hP : ContinuousOn P (Icc a b))
    (hV : ContinuousOn V (Icc a b)) (hp : ∀ t ∈ Icc a b, P t ≠ 0)
    (hY : Jacobi.IsSolution P V a b Y)
    {ζ ζ' : ℝ → ℝ} (hc : ContinuousOn ζ (Icc a b))
    (hc' : ContinuousOn ζ' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt ζ (ζ' t) (Icc a b) t)
    (ha : ζ a = 0) (hb : ζ b = 0) :
    (∫ t in a..b,
      P t * ((Y t).2 / P t * ζ t + (Y t).1 * ζ' t) ^ 2 +
        V t * ((Y t).1 * ζ t) ^ 2) =
      ∫ t in a..b, P t * (Y t).1 ^ 2 * ζ' t ^ 2 := by
  let f := fun t => (Y t).1 * (Y t).2 * (ζ t) ^ 2
  let g := fun t =>
    ((Y t).2 / P t * (Y t).2 + (Y t).1 * (V t * (Y t).1)) * ζ t ^ 2 +
      (Y t).1 * (Y t).2 * (2 * ζ t * ζ' t)
  have hg : ContinuousOn g (Icc a b) :=
    (((hY.1.snd.div hP hp).mul hY.1.snd).add
      (hY.1.fst.mul (hV.mul hY.1.fst))).mul (hc.pow 2) |>.add
      ((hY.1.fst.mul hY.1.snd).mul ((continuousOn_const.mul hc).mul hc'))
  have hfg : ∫ t in a..b, g t = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
      ((hY.1.fst.mul hY.1.snd).mul (hc.pow 2))
      (fun t ht => ?_) (hg.intervalIntegrable_of_Icc hab.le)
    · simpa [f, ha, hb] using h
    · convert (((hY.hasDerivWithinAt_fst (Ioo_subset_Icc_self ht)).mul
        (hY.hasDerivWithinAt_snd (Ioo_subset_Icc_self ht))).mul
        ((hd t (Ioo_subset_Icc_self ht)).pow 2)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2) using 1
      simp [g, pow_one, mul_assoc]
  have hw : ContinuousOn (fun t => P t * (Y t).1 ^ 2 * ζ' t ^ 2) (Icc a b) :=
    (hP.mul (hY.1.fst.pow 2)).mul (hc'.pow 2)
  calc
    _ = ∫ t in a..b, P t * (Y t).1 ^ 2 * ζ' t ^ 2 + g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hn := hp t (by simpa [uIcc_of_le hab.le] using ht)
      dsimp [g]
      field_simp
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hw.intervalIntegrable_of_Icc hab.le)
        (hg.intervalIntegrable_of_Icc hab.le), hfg, add_zero]

/-- Classical integration by parts in the mixed term, with the derivative
of B explicitly supplied and with one-sided endpoint derivatives. -/
theorem reduce_mixed_term {a b : ℝ} {P B B' C η η' : ℝ → ℝ}
    (hab : a < b) (hP : ContinuousOn P (Icc a b))
    (hB : ContinuousOn B (Icc a b)) (hB' : ContinuousOn B' (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hη : ContinuousOn η (Icc a b)) (hη' : ContinuousOn η' (Icc a b))
    (hdB : ∀ t ∈ Icc a b, HasDerivWithinAt B (B' t) (Icc a b) t)
    (hdη : ∀ t ∈ Icc a b, HasDerivWithinAt η (η' t) (Icc a b) t)
    (ha : η a = 0) (hb : η b = 0) :
    (∫ t in a..b, C t * η t ^ 2 + 2 * B t * η t * η' t + P t * η' t ^ 2) =
      ∫ t in a..b, P t * η' t ^ 2 + (C t - B' t) * η t ^ 2 := by
  let d := fun t => B' t * η t ^ 2 + B t * (2 * η t * η' t)
  have hc : ContinuousOn d (Icc a b) :=
    (hB'.mul (hη.pow 2)).add
      (hB.mul ((continuousOn_const.mul hη).mul hη'))
  have hz : ∫ t in a..b, d t = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
      (hB.mul (hη.pow 2)) (fun t ht => ?_)
      (hc.intervalIntegrable_of_Icc hab.le)
    · simpa [ha, hb] using h
    · convert ((hdB t (Ioo_subset_Icc_self ht)).mul
        ((hdη t (Ioo_subset_Icc_self ht)).pow 2)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2) using 1
      simp [d, pow_one, mul_assoc]
  have hr : ContinuousOn (fun t => P t * η' t ^ 2 + (C t - B' t) * η t ^ 2)
      (Icc a b) := (hP.mul (hη'.pow 2)).add ((hC.sub hB').mul (hη.pow 2))
  calc
    _ = ∫ t in a..b, (P t * η' t ^ 2 + (C t - B' t) * η t ^ 2) + d t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [d]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hr.intervalIntegrable_of_Icc hab.le)
        (hc.intervalIntegrable_of_Icc hab.le), hz, add_zero]

/-- Factorization for any classical endpoint-zero variation, dividing by an
actual nonvanishing Jacobi field. This is still a classical statement; its
extension to all weak-derivative classes is a separate obligation. -/
theorem jacobi_factorization_quotient {a b : ℝ} {P V : ℝ → ℝ}
    {Y : ℝ → ℝ × ℝ} (hab : a < b) (hP : ContinuousOn P (Icc a b))
    (hV : ContinuousOn V (Icc a b)) (hp : ∀ t ∈ Icc a b, P t ≠ 0)
    (hY : Jacobi.IsSolution P V a b Y)
    (hv : ∀ t ∈ Icc a b, (Y t).1 ≠ 0)
    {η η' : ℝ → ℝ} (hc : ContinuousOn η (Icc a b))
    (hc' : ContinuousOn η' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt η (η' t) (Icc a b) t)
    (ha : η a = 0) (hb : η b = 0) :
    (∫ t in a..b, P t * η' t ^ 2 + V t * η t ^ 2) =
      ∫ t in a..b, P t * (Y t).1 ^ 2 *
        ((η' t * (Y t).1 - η t * ((Y t).2 / P t)) / (Y t).1 ^ 2) ^ 2 := by
  let ζ := fun t => η t / (Y t).1
  let ζ' := fun t =>
    (η' t * (Y t).1 - η t * ((Y t).2 / P t)) / (Y t).1 ^ 2
  have hζ : ContinuousOn ζ (Icc a b) := hc.div hY.1.fst hv
  have hζ' : ContinuousOn ζ' (Icc a b) :=
    ((hc'.mul hY.1.fst).sub (hc.mul (hY.1.snd.div hP hp))).div
      (hY.1.fst.pow 2) (fun t ht => pow_ne_zero _ (hv t ht))
  have hζd : ∀ t ∈ Icc a b, HasDerivWithinAt ζ (ζ' t) (Icc a b) t := by
    intro t ht
    exact (hd t ht).div (hY.hasDerivWithinAt_fst ht) (hv t ht)
  have he := jacobi_factorization hab hP hV hp hY hζ hζ' hζd
    (by simp [ζ, ha]) (by simp [ζ, hb])
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab.le] using ht
  have hpt := hp t ht'
  have hvt := hv t ht'
  dsimp [ζ, ζ']
  field_simp
  ring

/-- Scalar state and velocity fields retain the original C¹ jet, including
its within derivatives at both endpoints. -/
theorem scalar_curve_regularity {I : Interval} (η : C1Curve I 1) :
    ContinuousOn (fun t => stateField I 1 η t 0) (Icc I.a I.b) ∧
    ContinuousOn (fun t => velocityField I 1 η t 0) (Icc I.a I.b) ∧
    ∀ t ∈ Icc I.a I.b, HasDerivWithinAt (fun t => stateField I 1 η t 0)
      (velocityField I 1 η t 0) (Icc I.a I.b) t := by
  have hs := (VariationSpaces.c1_contDiffOn I 1 η).continuousOn
  have hv : ContinuousOn (velocityField I 1 η) (Icc I.a I.b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert η.velocity.continuous using 1
    funext t
    change velocityField I 1 η t = η.velocity t
    simp only [velocityField, extendState, dite_eq_left t.property]
  refine ⟨(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).continuous.comp_continuousOn hs,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).continuous.comp_continuousOn hv, ?_⟩
  intro t ht
  convert (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).hasFDerivAt.comp_hasDerivWithinAt t
    (η.property ⟨t, ht⟩) using 1 <;>
    simp [Function.comp_def, stateField, velocityField, extendState, ht,
      C1Curve.state, C1Curve.velocity]

/-- Integration by parts reduces the actual classical Hessian form under
exactly the regularity hypotheses of the assigned theorem. -/
theorem secondVariationForm_reduced {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3) (η : C1Curve I 1)
    (hη : η ∈ endpointZero I 1) :
    secondVariationForm L u η = ∫ t in I.a..I.b,
      coefficientP L u t * (velocityField I 1 η t 0) ^ 2 +
      coefficientV L u t * (stateField I 1 η t 0) ^ 2 := by
  obtain ⟨hP, hB, hC⟩ := coefficients_contDiffOn L u hu hreg
  obtain ⟨hs, hv, hd⟩ := scalar_curve_regularity η
  rw [secondVariationForm_coefficients]
  apply reduce_mixed_term I.increasing hP.continuousOn hB.continuousOn
    (hB.continuousOn_derivWithin (uniqueDiffOn_Icc I.increasing) le_rfl)
    hC.continuousOn hs hv
  · intro t ht
    exact (hB.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  · exact hd
  · simp only [stateField, extendState,
      dite_eq_left (left_mem_Icc.mpr I.increasing.le)]
    change η.state I.left 0 = 0
    rw [hη.1]
    rfl
  · simp only [stateField, extendState,
      dite_eq_left (right_mem_Icc.mpr I.increasing.le)]
    change η.state I.right 0 = 0
    rw [hη.2]
    rfl

/-- Use uniqueness to transfer the source's nonconjugacy assumption from
its supplied normalized solution to the normalized field constructed upstream.
In particular existence of an everywhere positive solution is proved here,
not imposed as a new hypothesis. -/
theorem exists_positive_field {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3)
    (hp : ∀ t ∈ Icc I.a I.b, 0 < coefficientP L u t)
    (Y₀ : ℝ → ℝ × ℝ)
    (hY₀ : Jacobi.IsSolution (coefficientP L u) (coefficientV L u) I.a I.b Y₀)
    (hinit : Y₀ I.a = (0, coefficientP L u I.a))
    (hnz : ∀ t ∈ Ioc I.a I.b, (Y₀ t).1 ≠ 0) :
    ∃ Y : ℝ → ℝ × ℝ,
      Jacobi.IsSolution (coefficientP L u) (coefficientV L u) I.a I.b Y ∧
      ∀ t ∈ Icc I.a I.b, 0 < (Y t).1 := by
  obtain ⟨Z, _, _, _, huniq, hpos⟩ := Jacobi.positiveJacobiSolution
    I.a I.b (coefficientP L u) (coefficientV L u) I.increasing
    (coefficients_contDiffOn L u hu hreg).1 (potential_continuousOn L u hu hreg) hp
  apply (hpos ?_).2
  intro t ht
  rw [← huniq Y₀ hY₀ hinit (Ioc_subset_Icc_self ht)]
  exact hnz t ht

/-- Continuity of the extension now follows directly from the original
curve/Lagrangian hypotheses, rather than from assumed coefficient regularity. -/
theorem continuous_secondVariation_extension {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3) :
    Continuous (reducedForm I (coefficientP L u) (coefficientV L u)) :=
  continuous_reducedForm I (coefficients_contDiffOn L u hu hreg).1.continuousOn
    (potential_continuousOn L u hu hreg)

/-- Cauchy--Schwarz for a continuous scalar interval integrand, proved by
integrating a square. This version also covers a degenerate interval. -/
theorem interval_integral_cauchy {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let A := ∫ t in a..b, f t
  let D := b - a
  have hD : 0 < D := sub_pos.mpr hab
  have hi₁ : IntervalIntegrable (fun t => D ^ 2 * f t ^ 2) volume a b :=
    (continuousOn_const.mul (hf.pow 2)).intervalIntegrable_of_Icc hab.le
  have hi₂ : IntervalIntegrable (fun t => (2 * D * A) * f t) volume a b :=
    (continuousOn_const.mul hf).intervalIntegrable_of_Icc hab.le
  have hi₃ : IntervalIntegrable (fun _ : ℝ => A ^ 2) volume a b :=
    intervalIntegrable_const
  have he : (fun t => (D * f t - A) ^ 2) =
      (fun t => D ^ 2 * f t ^ 2 - (2 * D * A) * f t + A ^ 2) := by
    funext t
    ring
  have h : 0 ≤ ∫ t in a..b, (D * f t - A) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le
    (fun t (_ : t ∈ Icc a b) => sq_nonneg (D * f t - A))
  rw [he, intervalIntegral.integral_add (hi₁.sub hi₂) hi₃,
    intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h
  have h' : 0 ≤ D * (D * (∫ t in a..b, f t ^ 2) - A ^ 2) := by
    change 0 ≤ D ^ 2 * (∫ t in a..b, f t ^ 2) - (2 * D * A) * A + D * A ^ 2 at h
    nlinarith only [h]
  have hh := (mul_nonneg_iff_of_pos_left hD).mp h'
  change A ^ 2 ≤ D * _
  linarith

/-- Poincaré for a C¹ scalar jet vanishing at the left endpoint. It applies
to η/v, which need only be C¹ and is not assumed to be a smooth test. -/
theorem classical_poincare {a b : ℝ} (hab : a < b) {ζ ζ' : ℝ → ℝ}
    (hc : ContinuousOn ζ (Icc a b)) (hc' : ContinuousOn ζ' (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt ζ (ζ' t) (Icc a b) t)
    (ha : ζ a = 0) :
    (∫ t in a..b, ζ t ^ 2) ≤ (b - a) ^ 2 * ∫ t in a..b, ζ' t ^ 2 := by
  have hE : 0 ≤ ∫ t in a..b, ζ' t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun t => sq_nonneg _)
  have hpt (t : ℝ) (ht : t ∈ Icc a b) :
      ζ t ^ 2 ≤ (b - a) * ∫ r in a..b, ζ' r ^ 2 := by
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have hfund : ∫ r in a..t, ζ' r = ζ t := by
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
        (hc.mono hsub) (fun r hr =>
          (hd r (hsub (Ioo_subset_Icc_self hr))).hasDerivAt
            (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2)))
        ((hc'.mono hsub).intervalIntegrable_of_Icc ht.1)
      simpa only [ha, sub_zero] using he
    have hcs := interval_integral_cauchy ht.1 (hc'.mono hsub)
    rw [hfund] at hcs
    have hmono : (∫ r in a..t, ζ' r ^ 2) ≤ ∫ r in a..b, ζ' r ^ 2 :=
      intervalIntegral.integral_mono_interval (μ := volume) le_rfl ht.1 ht.2
        (Eventually.of_forall (fun r => sq_nonneg _))
        ((hc'.pow 2).intervalIntegrable_of_Icc hab.le)
    exact hcs.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr ht.1)).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_right ht.2 a) hE))
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    ((hc.pow 2).intervalIntegrable_of_Icc hab.le) intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul, Pi.pow_apply] at hi
  nlinarith only [hi]

/-- The positive-field factorization gives a uniform bound in the full
classical H¹ energy, for every endpoint-zero C¹ jet. -/
theorem positive_field_classical_coercivity {a b : ℝ} {P V : ℝ → ℝ}
    {Y : ℝ → ℝ × ℝ} (hab : a < b) (hP : ContinuousOn P (Icc a b))
    (hV : ContinuousOn V (Icc a b)) (hp : ∀ t ∈ Icc a b, 0 < P t)
    (hY : Jacobi.IsSolution P V a b Y) (hv : ∀ t ∈ Icc a b, 0 < (Y t).1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ η η' : ℝ → ℝ,
      ContinuousOn η (Icc a b) → ContinuousOn η' (Icc a b) →
      (∀ t ∈ Icc a b, HasDerivWithinAt η (η' t) (Icc a b) t) →
      η a = 0 → η b = 0 →
      κ * (∫ t in a..b, η t ^ 2 + η' t ^ 2) ≤
        ∫ t in a..b, P t * η' t ^ 2 + V t * η t ^ 2 := by
  obtain ⟨c, M, hc, hM, hbounds⟩ := exists_jacobi_bounds hP hp hY hv
  let κ := c / (M ^ 2 * (3 * (b - a) ^ 2 + 2))
  have hκ : 0 < κ := div_pos hc (by positivity)
  refine ⟨κ, hκ, ?_⟩
  intro η η' hη hη' hd ha hb
  have hpne : ∀ t ∈ Icc a b, P t ≠ 0 := fun t ht => (hp t ht).ne'
  have hvne : ∀ t ∈ Icc a b, (Y t).1 ≠ 0 := fun t ht => (hv t ht).ne'
  let ζ := fun t => η t / (Y t).1
  let ζ' := fun t =>
    (η' t * (Y t).1 - η t * ((Y t).2 / P t)) / (Y t).1 ^ 2
  have hζ : ContinuousOn ζ (Icc a b) := hη.div hY.1.fst hvne
  have hζ' : ContinuousOn ζ' (Icc a b) :=
    ((hη'.mul hY.1.fst).sub (hη.mul (hY.1.snd.div hP hpne))).div
      (hY.1.fst.pow 2) (fun t ht => pow_ne_zero _ (hvne t ht))
  have hζd : ∀ t ∈ Icc a b, HasDerivWithinAt ζ (ζ' t) (Icc a b) t :=
    fun t ht => (hd t ht).div (hY.hasDerivWithinAt_fst ht) (hvne t ht)
  have hζa : ζ a = 0 := by simp [ζ, ha]
  have hηeq (t : ℝ) (ht : t ∈ Icc a b) : η t = (Y t).1 * ζ t := by
    dsimp [ζ]
    field_simp [hvne t ht]
  have hη'eq (t : ℝ) (ht : t ∈ Icc a b) :
      η' t = (Y t).2 / P t * ζ t + (Y t).1 * ζ' t := by
    dsimp [ζ, ζ']
    field_simp [hvne t ht]
    ring
  have hvsq (t : ℝ) (ht : t ∈ Icc a b) : (Y t).1 ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (abs_le.mp (hbounds t ht).2.1).1 (abs_le.mp (hbounds t ht).2.1).2
  have hv'sq (t : ℝ) (ht : t ∈ Icc a b) : ((Y t).2 / P t) ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (abs_le.mp (hbounds t ht).2.2).1 (abs_le.mp (hbounds t ht).2.2).2
  have hiη : IntervalIntegrable (fun t => η t ^ 2) volume a b :=
    (hη.pow 2).intervalIntegrable_of_Icc hab.le
  have hiη' : IntervalIntegrable (fun t => η' t ^ 2) volume a b :=
    (hη'.pow 2).intervalIntegrable_of_Icc hab.le
  have hiζ : IntervalIntegrable (fun t => ζ t ^ 2) volume a b :=
    (hζ.pow 2).intervalIntegrable_of_Icc hab.le
  have hiζ' : IntervalIntegrable (fun t => ζ' t ^ 2) volume a b :=
    (hζ'.pow 2).intervalIntegrable_of_Icc hab.le
  have hvalue : (∫ t in a..b, η t ^ 2) ≤ M ^ 2 * ∫ t in a..b, ζ t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le hiη (hiζ.const_mul _)
    intro t ht
    rw [hηeq t ht, mul_pow]
    exact mul_le_mul_of_nonneg_right (hvsq t ht) (sq_nonneg _)
  have hderivative : (∫ t in a..b, η' t ^ 2) ≤
      2 * M ^ 2 * ((∫ t in a..b, ζ t ^ 2) + ∫ t in a..b, ζ' t ^ 2) := by
    rw [← intervalIntegral.integral_add hiζ hiζ', ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le hiη' ((hiζ.add hiζ').const_mul _)
    intro t ht
    rw [hη'eq t ht]
    have h₁ := mul_le_mul_of_nonneg_right (hv'sq t ht) (sq_nonneg (ζ t))
    have h₂ := mul_le_mul_of_nonneg_right (hvsq t ht) (sq_nonneg (ζ' t))
    calc
      _ ≤ 2 * (((Y t).2 / P t * ζ t) ^ 2 + ((Y t).1 * ζ' t) ^ 2) := add_sq_le
      _ ≤ _ := by nlinarith only [h₁, h₂]
  have henergy : c * (∫ t in a..b, ζ' t ^ 2) ≤
      ∫ t in a..b, P t * η' t ^ 2 + V t * η t ^ 2 := by
    rw [jacobi_factorization_quotient hab hP hV hpne hY hvne hη hη' hd ha hb,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le (hiζ'.const_mul _)
      (((hP.mul (hY.1.fst.pow 2)).mul (hζ'.pow 2)).intervalIntegrable_of_Icc hab.le)
    intro t ht
    exact mul_le_mul_of_nonneg_right (hbounds t ht).1 (sq_nonneg _)
  have hfinal := (quantitative_coercivity hc hM hvalue hderivative
    (classical_poincare hab hζ hζ' hζd hζa) henergy).2
  rw [intervalIntegral.integral_add hiη hiη']
  exact hfinal

/-- Uniform classical coercivity with the original Hessian form and original
no-conjugate-point hypothesis. The scalar integral is the full H¹ energy. -/
theorem classical_secondVariation_coercive {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3)
    (hp : ∀ t ∈ Icc I.a I.b, 0 < coefficientP L u t)
    (Y₀ : ℝ → ℝ × ℝ)
    (hY₀ : Jacobi.IsSolution (coefficientP L u) (coefficientV L u) I.a I.b Y₀)
    (hinit : Y₀ I.a = (0, coefficientP L u I.a))
    (hnz : ∀ t ∈ Ioc I.a I.b, (Y₀ t).1 ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ η : C1Curve I 1, η ∈ endpointZero I 1 →
      κ * (∫ t in I.a..I.b,
        (stateField I 1 η t 0) ^ 2 + (velocityField I 1 η t 0) ^ 2) ≤
      secondVariationForm L u η := by
  obtain ⟨Y, hY, hv⟩ := exists_positive_field L u hu hreg hp Y₀ hY₀ hinit hnz
  obtain ⟨κ, hκ, hbound⟩ := positive_field_classical_coercivity I.increasing
    (coefficients_contDiffOn L u hu hreg).1.continuousOn
    (potential_continuousOn L u hu hreg) hp hY hv
  refine ⟨κ, hκ, ?_⟩
  intro η hη
  obtain ⟨hs, hvη, hd⟩ := scalar_curve_regularity η
  rw [secondVariationForm_reduced L u hu hreg η hη]
  apply hbound _ _ hs hvη hd
  · simp only [stateField, extendState,
      dite_eq_left (left_mem_Icc.mpr I.increasing.le)]
    change η.state I.left 0 = 0
    rw [hη.1]
    rfl
  · simp only [stateField, extendState,
      dite_eq_left (right_mem_Icc.mpr I.increasing.le)]
    change η.state I.right 0 = 0
    rw [hη.2]
    rfl

/-- Physical one-dimensional Euclidean coordinates, preserving length and
Lebesgue measure. -/
def scalarLine : ℝ ≃ₗᵢ[ℝ] Sobolev.Domain 1 where
  toFun t := WithLp.toLp 2 (fun _ => t)
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by
    apply PiLp.ext
    intro i
    exact congrArg x (Subsingleton.elim _ _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' t := by
    simp [PiLp.norm_eq_of_L2, Real.sqrt_sq_eq_abs]

/-- Exact change of variables between the Euclidean interval domain and
ordinary real interval integrals, without a dimension-dependent factor. -/
theorem integral_intervalDomain (I : Interval) (f : Sobolev.Domain 1 → ℝ) :
    (∫ x, f x ∂Sobolev.domainMeasure (intervalDomain I)) =
      ∫ t in I.a..I.b, f (scalarLine t) := by
  have h := scalarLine.measurePreserving.setIntegral_preimage_emb
    scalarLine.toHomeomorph.measurableEmbedding f (intervalDomain I : Set (Sobolev.Domain 1))
  change (∫ t in Ioo I.a I.b, f (scalarLine t)) = _ at h
  rw [← h, intervalIntegral.integral_of_le I.increasing.le, integral_Ioc_eq_integral_Ioo]

/-- The squared L² norm is its actual integral, allowing the source's
exponent representation to be equated with the literal exponent 2. -/
theorem lp_norm_sq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p = 2) (f : Lp E p μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  subst p
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- Squared product norm, with an explicit equality for the source exponent. -/
theorem product_norm_sq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p = 2) (x : WithLp p (E × F)) :
    ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
  subst p
  exact WithLp.prod_norm_sq_eq_of_L2 x

/-- The full existing H¹ norm equals the sum of the weak value and gradient
energies. No equivalent replacement norm is introduced. -/
theorem full_norm_sq_integral (I : Interval) (η : Sobolev.H1 (intervalDomain I) 1) :
    ‖η‖ ^ 2 = ∫ x,
      ‖Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η x‖ ^ 2 +
      ‖Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η x‖ ^ 2
      ∂Sobolev.domainMeasure (intervalDomain I) := by
  have hp2 : Sobolev.Exponent.two.ennreal = 2 := by
    norm_num [Sobolev.Exponent.two, Sobolev.Exponent.ennreal]
  have h := product_norm_sq hp2 η.val
  change ‖η‖ ^ 2 =
    ‖Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η‖ ^ 2 +
    ‖Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η‖ ^ 2 at h
  rw [h, lp_norm_sq_integral _ hp2, lp_norm_sq_integral _ hp2]
  symm
  apply integral_add
  · have hm : MemLp (Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η) 2
        (Sobolev.domainMeasure (intervalDomain I)) := by
      convert Lp.memLp (Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η) using 1
      exact hp2.symm
    exact hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  · have hm : MemLp (Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η) 2
        (Sobolev.domainMeasure (intervalDomain I)) := by
      convert Lp.memLp (Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η) using 1
      exact hp2.symm
    exact hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

/-- Exact squared norm in the one-coordinate value fiber. -/
theorem scalar_norm_sq (z : Sobolev.Vector 1) : ‖z‖ ^ 2 = (z 0) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp

/-- Exact squared norm in the one-coordinate weak gradient fiber. -/
theorem scalar_gradient_norm_sq (z : Sobolev.Gradient 1 1) :
    ‖z‖ ^ 2 = (z (0, 0)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  simp

/-- Real scalar restriction of a genuine smooth vector test. -/
def scalarTest {I : Interval} (φ : Sobolev.VectorTest (intervalDomain I) 1) : ℝ → ℝ :=
  fun t => φ (scalarLine t) 0

theorem scalarTest_contDiff {I : Interval} (φ : Sobolev.VectorTest (intervalDomain I) 1) :
    ContDiff ℝ 1 (scalarTest φ) := by
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff.comp
    (φ.contDiff.of_le (by simp) |>.comp scalarLine.toContinuousLinearEquiv.contDiff)

/-- The derivative of the scalar restriction is the one actual directional
derivative of the original test in the Euclidean coordinate direction. -/
theorem scalarTest_deriv {I : Interval} (φ : Sobolev.VectorTest (intervalDomain I) 1)
    (t : ℝ) :
    deriv (scalarTest φ) t =
      (fderiv ℝ φ (scalarLine t) (P102.U4.coordinateVector 1 0)) 0 := by
  have hs := scalarLine.toContinuousLinearEquiv.toContinuousLinearMap.hasDerivAt (x := t)
  have hφ := ((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t hs
  have hh := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).hasFDerivAt.comp_hasDerivAt t hφ
  have he : scalarLine 1 = P102.U4.coordinateVector 1 0 := by
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [scalarLine, P102.U4.coordinateVector]
  convert hh.deriv using 1
  · rfl
  · rw [← he]
    rfl

/-- Smooth tests vanish at each endpoint because their support is contained
in the open interval, even when their ambient values are evaluated there. -/
theorem scalarTest_endpoints {I : Interval} (φ : Sobolev.VectorTest (intervalDomain I) 1) :
    scalarTest φ I.a = 0 ∧ scalarTest φ I.b = 0 := by
  have ha : scalarLine I.a ∉ (intervalDomain I : Set (Sobolev.Domain 1)) := by
    change ¬ (I.a < I.a ∧ I.a < I.b)
    simp
  have hb : scalarLine I.b ∉ (intervalDomain I : Set (Sobolev.Domain 1)) := by
    change ¬ (I.a < I.b ∧ I.b < I.b)
    simp
  exact ⟨by simp [scalarTest, φ.zero_on_compl ha],
    by simp [scalarTest, φ.zero_on_compl hb]⟩

/-- Values and gradients of a smooth Sobolev class agree a.e. with the
scalar restriction and its classical derivative. -/
theorem smooth_scalar_fields {I : Interval} (η : Sobolev.H1 (intervalDomain I) 1)
    (φ : Sobolev.VectorTest (intervalDomain I) 1)
    (hφ : Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η =
      Sobolev.testToValueLp (intervalDomain I) 1 Sobolev.Exponent.two φ) :
    (fun x => Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η x 0) =ᵐ[
      Sobolev.domainMeasure (intervalDomain I)] (fun x => scalarTest φ (x 0)) ∧
    (fun x => Sobolev.gradient (intervalDomain I) 1 Sobolev.Exponent.two η x (0, 0)) =ᵐ[
      Sobolev.domainMeasure (intervalDomain I)] (fun x => deriv (scalarTest φ) (x 0)) := by
  have hval : (Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η :
      Sobolev.Domain 1 → Sobolev.Vector 1) =ᵐ[Sobolev.domainMeasure (intervalDomain I)] φ := by
    rw [hφ]
    exact (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).coeFn_toLp
  have hgrad := Sobolev.smooth_partialVector_ae (intervalDomain I) Sobolev.Exponent.two 0 η φ hφ
  have hcol := Sobolev.partialVector_ae (intervalDomain I) Sobolev.Exponent.two 0 η
  have hx (x : Sobolev.Domain 1) : scalarLine (x 0) = x := scalarLine.apply_symm_apply x
  constructor
  · filter_upwards [hval] with x hxv
    simp only [scalarTest, hx]
    exact congrArg (fun z : Sobolev.Vector 1 => z 0) hxv
  · filter_upwards [hgrad, hcol] with x hxg hxc
    rw [scalarTest_deriv, hx]
    have he := congrArg (fun z : Sobolev.Vector 1 => z 0) (hxc.symm.trans hxg)
    exact he



/-- The full H¹ norm of a smooth Sobolev class is exactly its classical scalar energy. -/
theorem smooth_full_norm_sq {I : Interval} (η : Sobolev.H1 (intervalDomain I) 1)
    (φ : Sobolev.VectorTest (intervalDomain I) 1)
    (hφ : Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η =
      Sobolev.testToValueLp (intervalDomain I) 1 Sobolev.Exponent.two φ) :
    ‖η‖ ^ 2 = ∫ t in I.a..I.b, scalarTest φ t ^ 2 + deriv (scalarTest φ) t ^ 2 := by
  obtain ⟨hval, hgrad⟩ := smooth_scalar_fields η φ hφ
  rw [full_norm_sq_integral]
  calc
    _ = ∫ x, scalarTest φ (x 0) ^ 2 + deriv (scalarTest φ) (x 0) ^ 2
        ∂Sobolev.domainMeasure (intervalDomain I) := by
      apply integral_congr_ae
      filter_upwards [hval, hgrad] with x hxv hxg
      rw [scalar_norm_sq, scalar_gradient_norm_sq, hxv, hxg]
    _ = _ := integral_intervalDomain I _

/-- The reduced form of a smooth Sobolev class agrees with the classical scalar integral. -/
theorem smooth_ambientReducedForm {I : Interval} (P V : ℝ → ℝ)
    (η : Sobolev.H1 (intervalDomain I) 1)
    (φ : Sobolev.VectorTest (intervalDomain I) 1)
    (hφ : Sobolev.value (intervalDomain I) 1 Sobolev.Exponent.two η =
      Sobolev.testToValueLp (intervalDomain I) 1 Sobolev.Exponent.two φ) :
    ambientReducedForm I P V η = ∫ t in I.a..I.b,
      P t * deriv (scalarTest φ) t ^ 2 + V t * scalarTest φ t ^ 2 := by
  obtain ⟨hval, hgrad⟩ := smooth_scalar_fields η φ hφ
  calc
    _ = ∫ x, P (x 0) * deriv (scalarTest φ) (x 0) ^ 2 +
        V (x 0) * scalarTest φ (x 0) ^ 2
        ∂Sobolev.domainMeasure (intervalDomain I) := by
      apply integral_congr_ae
      filter_upwards [hval, hgrad] with x hxv hxg
      rw [scalar_norm_sq, scalar_gradient_norm_sq, hxv, hxg]
    _ = _ := integral_intervalDomain I _

/-- A positive Jacobi field gives a uniform lower bound in the actual full
H¹₀ norm, by the defining closure of smooth tests. -/
theorem positive_field_sobolev_coercivity (I : Interval) {P V : ℝ → ℝ}
    {Y : ℝ → ℝ × ℝ} (hP : ContinuousOn P (Icc I.a I.b))
    (hV : ContinuousOn V (Icc I.a I.b)) (hp : ∀ t ∈ Icc I.a I.b, 0 < P t)
    (hY : Jacobi.IsSolution P V I.a I.b Y)
    (hv : ∀ t ∈ Icc I.a I.b, 0 < (Y t).1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ η : Variation I, κ * ‖η‖ ^ 2 ≤ reducedForm I P V η := by
  obtain ⟨κ, hκ, hclassical⟩ := positive_field_classical_coercivity I.increasing hP hV hp hY hv
  refine ⟨κ, hκ, ?_⟩
  apply bound_on_zero_of_bound_on_smooth (intervalDomain I) (ambientReducedForm I P V)
    (continuous_ambientReducedForm I hP hV) κ
  intro η hη
  change η ∈ (Sobolev.smoothSubmodule (intervalDomain I) 1 Sobolev.Exponent.two : Set _) at hη
  rw [Sobolev.smoothSubmodule_eq_vector_tests] at hη
  obtain ⟨φ, hφ⟩ := hη
  rw [smooth_full_norm_sq η φ hφ, smooth_ambientReducedForm P V η φ hφ]
  have hc := scalarTest_contDiff φ
  obtain ⟨ha, hb⟩ := scalarTest_endpoints φ
  apply hclassical _ _ hc.continuous.continuousOn
    (hc.continuous_deriv le_rfl).continuousOn
  · intro t ht
    exact ((hc.differentiable one_ne_zero).differentiableAt.hasDerivAt).hasDerivWithinAt
  · exact ha
  · exact hb

/-- The original nonconjugacy hypothesis gives the coercive H¹₀ estimate. -/
theorem secondVariation_sobolev_coercive {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3)
    (hp : ∀ t ∈ Icc I.a I.b, 0 < coefficientP L u t)
    (Y₀ : ℝ → ℝ × ℝ)
    (hY₀ : Jacobi.IsSolution (coefficientP L u) (coefficientV L u) I.a I.b Y₀)
    (hinit : Y₀ I.a = (0, coefficientP L u I.a))
    (hnz : ∀ t ∈ Ioc I.a I.b, (Y₀ t).1 ≠ 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ η : Variation I,
      κ * ‖η‖ ^ 2 ≤ reducedForm I (coefficientP L u) (coefficientV L u) η := by
  obtain ⟨Y, hY, hv⟩ := exists_positive_field L u hu hreg hp Y₀ hY₀ hinit hnz
  exact positive_field_sobolev_coercivity I
    (coefficients_contDiffOn L u hu hreg).1.continuousOn
    (potential_continuousOn L u hu hreg) hp hY hv


/-- A represented classical jet has precisely the original reduced integral. -/
theorem reducedForm_of_represents {I : Interval} (P V : ℝ → ℝ)
    (η : C1Curve I 1) (h : Variation I) (hrep : Represents η h) :
    reducedForm I P V h = ∫ t in I.a..I.b,
      P t * (velocityField I 1 η t 0) ^ 2 +
      V t * (stateField I 1 η t 0) ^ 2 := by
  unfold reducedForm
  calc
    _ = ∫ x, P (x 0) * (velocityField I 1 η (x 0) 0) ^ 2 +
        V (x 0) * (stateField I 1 η (x 0) 0) ^ 2
          ∂Sobolev.domainMeasure (intervalDomain I) := by
      apply integral_congr_ae
      filter_upwards [hrep.1, hrep.2] with x hv hg
      rw [hv, hg, scalar_norm_sq, scalar_gradient_norm_sq]
    _ = _ := integral_intervalDomain I _

/-- The source's full H¹ norm of a represented jet is exactly its classical
value and derivative energy. -/
theorem full_norm_sq_of_represents {I : Interval} (η : C1Curve I 1)
    (h : Variation I) (hrep : Represents η h) :
    ‖h‖ ^ 2 = ∫ t in I.a..I.b,
      (stateField I 1 η t 0) ^ 2 + (velocityField I 1 η t 0) ^ 2 := by
  rw [show ‖h‖ ^ 2 = ‖h.val‖ ^ 2 by rfl, full_norm_sq_integral]
  calc
    _ = ∫ x, (stateField I 1 η (x 0) 0) ^ 2 +
        (velocityField I 1 η (x 0) 0) ^ 2
          ∂Sobolev.domainMeasure (intervalDomain I) := by
      apply integral_congr_ae
      filter_upwards [hrep.1, hrep.2] with x hv hg
      rw [hv, hg, scalar_norm_sq, scalar_gradient_norm_sq]
    _ = _ := integral_intervalDomain I _

/-- Whenever a classical endpoint-zero jet is represented by a Sobolev class,
the reduced extension agrees with its original second variation. -/
theorem reducedForm_eq_secondVariation_of_represents {I : Interval}
    (L : Lagrangian 1) (u : C1Curve I 1)
    (hu : ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b))
    (hreg : regularNearGraph L u 3) (η : C1Curve I 1)
    (hη : η ∈ endpointZero I 1) (h : Variation I) (hrep : Represents η h) :
    reducedForm I (coefficientP L u) (coefficientV L u) h =
      secondVariationForm L u η := by
  rw [reducedForm_of_represents _ _ _ _ hrep,
    secondVariationForm_reduced L u hu hreg η hη]




/-- Continuous interval fields belong to the actual restricted Lᵖ space. -/
theorem scalar_interval_memLp (I : Interval) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc I.a I.b)) (p : ℝ≥0∞) :
    MemLp (fun x : Sobolev.Domain 1 => f (x 0)) p
      (Sobolev.domainMeasure (intervalDomain I)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.norm
  have hm : MemLp f p (volume.restrict (Ioo I.a I.b)) := by
    apply MemLp.of_bound ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) M
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hM (mem_image_of_mem _ ⟨hx.1.le, hx.2.le⟩)
  have hmp := scalarLine.symm.measurePreserving.restrict_preimage (s := Ioo I.a I.b) measurableSet_Ioo
  exact hm.comp_measurePreserving hmp

/-- Construct a scalar weak-derivative class from an absolutely continuous jet. -/
theorem scalar_sobolev_of_jet (I : Interval) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc I.a I.b)) (hg : ContinuousOn g (Icc I.a I.b))
    (hac : AbsolutelyContinuousOnInterval f I.a I.b)
    (hd : ∀ t ∈ Ioo I.a I.b, HasDerivAt f (g t) t) :
    ∃ u : P102.U4.Sobolev ℝ (intervalDomain I) 1 Sobolev.Exponent.two.ennreal,
      (P102.U4.sobolevUnderlying u : Sobolev.Domain 1 → ℝ) =ᵐ[
        Sobolev.domainMeasure (intervalDomain I)] (fun x => f (x 0)) ∧
      (P102.U4.firstWeakDerivative u 0 : Sobolev.Domain 1 → ℝ) =ᵐ[
        Sobolev.domainMeasure (intervalDomain I)] (fun x => g (x 0)) := by
  let Ω := intervalDomain I
  let p := Sobolev.Exponent.two.ennreal
  let hfm := scalar_interval_memLp I hf p
  let hgm := scalar_interval_memLp I hg p
  let U := hfm.toLp (fun x : Sobolev.Domain 1 => f (x 0))
  let G := hgm.toLp (fun x : Sobolev.Domain 1 => g (x 0))
  have hUa : (U : Sobolev.Domain 1 → ℝ) =ᵐ[Sobolev.domainMeasure Ω] (fun x => f (x 0)) :=
    hfm.coeFn_toLp
  have hGa : (G : Sobolev.Domain 1 → ℝ) =ᵐ[Sobolev.domainMeasure Ω] (fun x => g (x 0)) :=
    hgm.coeFn_toLp
  have hweak : P102.U4.distributionPartial {(0 : Fin 1)}
      (P102.U4.regularDistribution Ω U) = P102.U4.regularDistribution Ω G := by
    apply (P102.U4.acl_dimensionOne ℝ Ω U G
      (P102.U4.domainLp_locallyIntegrable Ω p U)
      (P102.U4.domainLp_locallyIntegrable Ω p G)).mpr
    refine ⟨fun x => f (x 0), hUa, ?_, ?_⟩
    · intro s t hst
      change AbsolutelyContinuousOnInterval f s t
      apply hac.mono
      rw [uIcc_of_le I.increasing.le]
      intro r hr
      exact ⟨(hst hr).1.le, (hst hr).2.le⟩
    · have hmp := scalarLine.measurePreserving.restrict_preimage Ω.isOpen.measurableSet
      have hGline := hmp.quasiMeasurePreserving.ae hGa
      filter_upwards [hGline, ae_restrict_mem measurableSet_Ioo] with t ht hti
      simp only [P102.Trace.Ordinary.acl_line_one_eq]
      change HasDerivAt f (G (scalarLine t)) t
      rw [ht]
      exact hd t hti
  have hderivs : P102.U4.HasSobolevDerivatives Ω 1 p U := by
    intro α hα
    by_cases hz : α = 0
    · subst α
      exact ⟨U, P102.U4.derivative_zero 1 ℝ Ω _⟩
    · have hc : α.card = 1 := by
        have hn := Multiset.card_eq_zero.not.mpr hz
        omega
      obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp hc
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact ⟨G, hweak⟩
  obtain ⟨u, hu⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range Ω 1 p) U).mpr hderivs
  refine ⟨u, ?_, ?_⟩
  · rwa [hu]
  · have hG : G = P102.U4.firstWeakDerivative u 0 := by
      apply P102.U4.sobolev_derivative_unique Ω 1 p u ⟨{0}, by simp⟩ G
      rwa [hu]
    rw [← hG]
    exact hGa


section ScalarBridge
open P102.U4 P102.Trace.Ordinary

/-- On this single interval, zero endpoint values imply the smooth-test closure. -/
theorem mem_zero_of_endpoint_representative {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (I : Interval)
    (u : Sobolev ℝ (intervalDomain I) 1 p) (f : ℝ → ℝ)
    (hf : IsEndpointRepresentative (fun _ : Fin 1 => I.a) (fun _ : Fin 1 => I.b) u f)
    (ha : f I.a = 0) (hb : f I.b = 0) :
    u ∈ sobolevZeroSubmodule ℝ (intervalDomain I) 1 p := by
  have hI : (intervalDomain I : Set (Space 1)) =
      ⋃ _ : Fin 1, linePoint '' Ioo I.a I.b := by
    ext x
    simp only [mem_iUnion, mem_image, mem_Ioo]
    constructor
    · intro hx
      refine ⟨0, x 0, hx, ?_⟩
      exact scalarLine.apply_symm_apply x
    · rintro ⟨i, t, ht, rfl⟩
      exact ht
  have hab : ∀ _ : Fin 1, I.a < I.b := fun _ => I.increasing
  have hinj : Function.Injective
      (Sum.elim (fun _ : Fin 1 => I.a) (fun _ : Fin 1 => I.b)) := by
    rintro (i | i) (j | j) h
    · congr 1; exact Subsingleton.elim _ _
    · exact False.elim (I.increasing.ne h)
    · exact False.elim (I.increasing.ne h.symm)
    · congr 1; exact Subsingleton.elim _ _
  have hdis : Pairwise (fun i j : Fin 1 => Disjoint (Ioo I.a I.b) (Ioo I.a I.b)) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  have he := zeroExtension_of_zero_endpoint_values hab hdis hI u f hf (fun _ => ⟨ha, hb⟩)
  exact mem_sobolevZero_of_zeroExtension_finite_intervals hp hab hinj hdis hI u he

/-- The scalar coordinate class of an endpoint-zero curve has zero boundary values. -/
theorem coordinate_mem_zero_of_represents {I : Interval}
    (η : C1Curve I 1)
    (u : Sobolev ℝ (intervalDomain I) 1 VariationalNotes.Sobolev.Exponent.two.ennreal)
    (hval : (sobolevUnderlying u : Space 1 → ℝ) =ᵐ[
        VariationalNotes.Sobolev.domainMeasure (intervalDomain I)]
      fun x => stateField I 1 η (x 0) 0)
    (hgrad : (firstWeakDerivative u 0 : Space 1 → ℝ) =ᵐ[
        VariationalNotes.Sobolev.domainMeasure (intervalDomain I)]
      fun x => velocityField I 1 η (x 0) 0)
    (hzero : η ∈ endpointZero I 1) :
    u ∈ sobolevZeroSubmodule ℝ (intervalDomain I) 1
      VariationalNotes.Sobolev.Exponent.two.ennreal := by
  let f := fun t => stateField I 1 η t 0
  have hmp : MeasurePreserving linePoint volume volume := linePoint_measurePreserving
  have hmpR := hmp.restrict_preimage (intervalDomain I).isOpen.measurableSet
  have hv := hmpR.quasiMeasurePreserving.ae hval
  have hg := hmpR.quasiMeasurePreserving.ae hgrad
  have hr := scalar_curve_regularity η
  have hdiff : ContDiffOn ℝ 1 f (Icc I.a I.b) := by
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff.comp_contDiffOn
      (VariationSpaces.c1_contDiffOn I 1 η)
  have hac : AbsolutelyContinuousOnInterval f I.a I.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le I.increasing.le] using hdiff
  have hrepr : IsEndpointRepresentative (fun _ : Fin 1 => I.a)
      (fun _ : Fin 1 => I.b) u f := by
    refine ⟨hv, fun _ => hac, ?_⟩
    filter_upwards [hg, ae_restrict_mem (measurableSet_preimage hmp.measurable
      (intervalDomain I).isOpen.measurableSet)] with t ht hti
    change I.a < t ∧ t < I.b at hti
    rw [ht]
    exact (hr.2.2 t ⟨hti.1.le, hti.2.le⟩).hasDerivAt (Icc_mem_nhds hti.1 hti.2)
  apply mem_zero_of_endpoint_representative (p := VariationalNotes.Sobolev.Exponent.two.ennreal)
    (by norm_num [VariationalNotes.Sobolev.Exponent.two, VariationalNotes.Sobolev.Exponent.ennreal])
    I u f hrepr
  · change stateField I 1 η I.a 0 = 0
    have hz := hzero.1
    simpa [stateField, extendState, I.increasing.le, Interval.left] using congrArg (fun z => z 0) hz
  · change stateField I 1 η I.b 0 = 0
    have hz := hzero.2
    simpa [stateField, extendState, I.increasing.le, Interval.right] using congrArg (fun z => z 0) hz

/-- Assemble the scalar coordinate class into the canonical Euclidean H¹₀ space. -/
theorem variation_of_scalar_sobolev {I : Interval}
    (η : C1Curve I 1)
    (u : Sobolev ℝ (intervalDomain I) 1 VariationalNotes.Sobolev.Exponent.two.ennreal)
    (hval : (sobolevUnderlying u : Space 1 → ℝ) =ᵐ[
        VariationalNotes.Sobolev.domainMeasure (intervalDomain I)]
      fun x => stateField I 1 η (x 0) 0)
    (hgrad : (firstWeakDerivative u 0 : Space 1 → ℝ) =ᵐ[
        VariationalNotes.Sobolev.domainMeasure (intervalDomain I)]
      fun x => velocityField I 1 η (x 0) 0)
    (hzero : η ∈ endpointZero I 1) :
    ∃ h : Variation I, Represents η h := by
  let Ω := intervalDomain I
  let p := VariationalNotes.Sobolev.Exponent.two
  let w : VariationalNotes.Sobolev.H1 Ω 1 :=
    (VariationalNotes.Sobolev.coordinateEquiv Ω p).symm (fun _ : Fin 1 => u)
  have hw (i : Fin 1) : VariationalNotes.Sobolev.toCoordinates Ω p w i = u := by
    change VariationalNotes.Sobolev.coordinateEquiv Ω p w i = u
    exact congrFun ((VariationalNotes.Sobolev.coordinateEquiv Ω p).apply_symm_apply _) i
  have hwzero : w ∈ VariationalNotes.Sobolev.zeroSubmodule Ω 1 p := by
    apply (VariationalNotes.Sobolev.zero_mem_iff_coordinates Ω p w).mpr
    intro i
    change VariationalNotes.Sobolev.toCoordinates Ω p w i ∈ _
    rw [hw]
    exact coordinate_mem_zero_of_represents η u hval hgrad hzero
  let h : Variation I := ⟨w, hwzero⟩
  have hv : VariationalNotes.Sobolev.coordinateLp Ω p 0
      (VariationalNotes.Sobolev.value Ω 1 p w) = sobolevUnderlying u := by
    rw [← VariationalNotes.Sobolev.toCoordinates_value, hw]
  have hg : VariationalNotes.Sobolev.coordinateLp Ω p (0, 0)
      (VariationalNotes.Sobolev.gradient Ω 1 p w) = firstWeakDerivative u 0 := by
    rw [← VariationalNotes.Sobolev.toCoordinates_derivative, hw]
    rfl
  have hva := VariationalNotes.Sobolev.coordinateLp_ae Ω p 0
    (VariationalNotes.Sobolev.value Ω 1 p w)
  have hga := VariationalNotes.Sobolev.coordinateLp_ae Ω p (0, 0)
    (VariationalNotes.Sobolev.gradient Ω 1 p w)
  rw [hv] at hva
  rw [hg] at hga
  refine ⟨h, ?_, ?_⟩
  · filter_upwards [hva, hval] with x hx hxv
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hx.symm.trans hxv
  · filter_upwards [hga, hgrad] with x hx hxg
    apply PiLp.ext
    intro i
    have hi : i = (0, 0) := Subsingleton.elim _ _
    subst i
    exact hx.symm.trans hxg

end ScalarBridge

/-- Every classical endpoint-zero C¹ direction represents an actual H¹₀ class. -/
theorem exists_representing_variation {I : Interval} (η : C1Curve I 1)
    (hzero : η ∈ endpointZero I 1) : ∃ h : Variation I, Represents η h := by
  obtain ⟨hf, hg, hd⟩ := scalar_curve_regularity η
  have hac : AbsolutelyContinuousOnInterval (fun t => stateField I 1 η t 0) I.a I.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le I.increasing.le]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) 0).contDiff.comp_contDiffOn
      (VariationSpaces.c1_contDiffOn I 1 η)
  obtain ⟨u, hval, hgrad⟩ := scalar_sobolev_of_jet I hf hg hac (fun t ht =>
    (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  exact variation_of_scalar_sobolev η u hval hgrad hzero



/-- The coercivity clause of the strengthened Legendre–Jacobi theorem,
with the original classical form and the full source H¹₀ norm. -/
theorem coercive_secondVariation :
    Specs.VariationalNotes.Classical.JacobiCoercivity.CoerciveSecondVariation := by
  intro I L u hu _hstationary hreg hp Y₀ hY₀ hinit hnz
  refine ⟨continuous_secondVariation_extension L u hu hreg, ?_,
    secondVariation_sobolev_coercive L u hu hreg hp Y₀ hY₀ hinit hnz⟩
  intro η hη
  obtain ⟨h, hrep⟩ := exists_representing_variation η hη
  exact ⟨h, hrep, reducedForm_eq_secondVariation_of_represents L u hu hreg η hη h hrep⟩

end VariationalNotes.Classical.JacobiCoercivity
