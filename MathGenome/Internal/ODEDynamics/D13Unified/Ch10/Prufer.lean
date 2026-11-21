import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Prufer
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Separation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.LinearVolterra
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix
namespace D13Unified.Ch10.Prufer
open Specs.D13Unified.Ch10.RegularProblem Specs.D13Unified.Ch10.Separation
open Specs.D13Unified.Ch10.Prufer

lemma left_mem (P : Problem) : P.a ∈ intervalValue P := ⟨le_rfl, P.a_lt_b.le⟩
lemma right_mem (P : Problem) : P.b ∈ intervalValue P := ⟨P.a_lt_b.le, le_rfl⟩

/-- Reconstruct a scalar C² solution from the first-order flux system.
Only p is differentiated; q and w remain merely continuous. -/
lemma scalar_of_system (P : Problem) (lam : ℝ) (Y : ℝ → Fin 2 → ℝ)
    (hc : ContinuousOn Y (intervalValue P))
    (hd : ∀ x ∈ intervalValue P,
      HasDerivWithinAt Y (Separation.systemMatrix P lam x *ᵥ Y x) (intervalValue P) x) :
    IsRealSolution P lam (fun x => Y x 0) ∧
    EqOn (flux P (fun x => Y x 0)) (fun x => Y x 1) (intervalValue P) := by
  have h0 (x : ℝ) (hx : x ∈ intervalValue P) :
      HasDerivWithinAt (fun x => Y x 0) ((P.p x)⁻¹ * Y x 1) (intervalValue P) x := by
    simpa [Separation.systemMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      using (hasDerivWithinAt_pi.mp (hd x hx) 0)
  have h1 (x : ℝ) (hx : x ∈ intervalValue P) :
      HasDerivWithinAt (fun x => Y x 1) ((P.q x - lam * P.w x) * Y x 0)
        (intervalValue P) x := by
    simpa [Separation.systemMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      using (hasDerivWithinAt_pi.mp (hd x hx) 1)
  have hc0 : ContinuousOn (fun x => Y x 0) (intervalValue P) :=
    (continuousOn_pi.mp hc) 0
  have hc1 : ContinuousOn (fun x => Y x 1) (intervalValue P) :=
    (continuousOn_pi.mp hc) 1
  have hreg1 : ContDiffOn ℝ 1 (fun x => Y x 1) (intervalValue P) :=
    Ch07.LinearSystemExistence.regularity
      ((P.q_continuous.sub (continuousOn_const.mul P.w_continuous)).mul hc0) h1
  have heq : EqOn (derivative P (fun x => Y x 0))
      (fun x => (P.p x)⁻¹ * Y x 1) (intervalValue P) := by
    intro x hx
    exact (h0 x hx).derivWithin ((Separation.uniqueDiff P) x hx)
  have hf : EqOn (flux P (fun x => Y x 0)) (fun x => Y x 1) (intervalValue P) := by
    intro x hx
    simp [flux, heq hx, ne_of_gt (P.p_positive x hx)]
  have hp : ContDiffOn ℝ 1 (fun x => (P.p x)⁻¹ * Y x 1) (intervalValue P) :=
    (P.p_regular.inv (fun x hx => ne_of_gt (P.p_positive x hx))).mul hreg1
  refine ⟨⟨?_, ?_⟩, hf⟩
  · apply (contDiffOn_succ_iff_derivWithin (n := 1) (Separation.uniqueDiff P)).mpr
    refine ⟨fun x hx => (h0 x hx).differentiableWithinAt, ?_, hp.congr heq⟩
    simp
  · intro x hx
    have hflux := (h1 x hx).congr_of_mem hf hx
    have hderiv := hflux.derivWithin ((Separation.uniqueDiff P) x hx)
    dsimp [expression]
    rw [hderiv]
    ring

lemma exists_normalized (P : Problem) (lam : ℝ) : ∃ u : ℝ → ℝ, Normalized P lam u := by
  let I : TimeInterval := ⟨intervalValue P, ⟨P.a, left_mem P⟩, ordConnected_Icc⟩
  obtain ⟨Y, hc, hi, hd, _⟩ := Ch07.LinearSystemExistence.vector_existence ℝ 2 I
    (Separation.systemMatrix P lam) P.a ![0,1] (left_mem P)
    (Separation.systemMatrix_continuous P lam)
  obtain ⟨hu, hf⟩ := scalar_of_system P lam Y hc hd
  refine ⟨fun x => Y x 0, hu, ?_, ?_⟩
  · exact congrFun hi 0
  · rw [hf (left_mem P)]
    exact congrFun hi 1

lemma normalized (P : Problem) (lam : ℝ) : Normalized P lam (solution P lam) :=
  Classical.epsilon_spec (exists_normalized P lam)

lemma normalized_unique {P : Problem} {lam : ℝ} {u v : ℝ → ℝ}
    (hu : Normalized P lam u) (hv : Normalized P lam v) :
    EqOn u v (intervalValue P) := by
  let I : TimeInterval := ⟨intervalValue P, ⟨P.a, left_mem P⟩, ordConnected_Icc⟩
  obtain ⟨Y, _, _, _, _, huniq⟩ := Ch07.LinearSystemExistence.vector_existence ℝ 2 I
    (Separation.systemMatrix P lam) P.a ![0,1] (left_mem P)
    (Separation.systemMatrix_continuous P lam)
  have hi (u : ℝ → ℝ) (hu : Normalized P lam u) : Separation.state P u P.a = ![0,1] := by
    simp [Separation.state, hu.2.1, hu.2.2]
  have hU := huniq (Separation.state P u) (Separation.state_continuous hu.1) (hi u hu)
    (fun x hx => Separation.state_derivative hu.1 hx)
  have hV := huniq (Separation.state P v) (Separation.state_continuous hv.1) (hi v hv)
    (fun x hx => Separation.state_derivative hv.1 hx)
  intro x hx
  exact congrFun ((hU hx).trans (hV hx).symm) 0

theorem normalized_solution : Specs.D13Unified.Ch10.Prufer.NormalizedSolution := by
  intro P lam
  exact ⟨normalized P lam, fun u hu => normalized_unique hu (normalized P lam)⟩

lemma solution_nonzero (P : Problem) (lam : ℝ) : Nonzero P (solution P lam) := by
  by_contra hn
  have hz : EqOn (solution P lam) (fun _ => 0) (intervalValue P) := by
    intro x hx
    exact not_ne_iff.mp (fun h => hn ⟨x, hx, h⟩)
  have hderiv : derivative P (solution P lam) P.a = 0 := by
    have h := (hasDerivWithinAt_const P.a (intervalValue P) (0 : ℝ)).congr_of_mem hz (left_mem P)
    exact h.derivWithin ((Separation.uniqueDiff P) P.a (left_mem P))
  have hi := (normalized P lam).2.2
  simp [flux, hderiv] at hi

lemma radius_pos (P : Problem) (lam : ℝ) {x : ℝ} (hx : x ∈ intervalValue P) :
    0 < radius P lam x := by
  apply Real.sqrt_pos.2
  have hn := Separation.no_simultaneous_zero (normalized P lam).1 (solution_nonzero P lam) hx
  have hsum := add_nonneg (sq_nonneg (solution P lam x))
    (sq_nonneg (flux P (solution P lam) x))
  by_contra h
  have hz : solution P lam x ^ 2 + flux P (solution P lam) x ^ 2 = 0 := by linarith
  exact hn ⟨by nlinarith [sq_nonneg (flux P (solution P lam) x)],
    by nlinarith [sq_nonneg (solution P lam x)]⟩

lemma radius_sq (P : Problem) (lam x : ℝ) :
    radius P lam x ^ 2 = solution P lam x ^ 2 + flux P (solution P lam) x ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma radius_continuous (P : Problem) (lam : ℝ) :
    ContinuousOn (radius P lam) (intervalValue P) :=
  (((normalized P lam).1.1.continuousOn.pow 2).add
    ((Separation.flux_continuous (normalized P lam).1).pow 2)).sqrt

lemma radius_left (P : Problem) (lam : ℝ) : radius P lam P.a = 1 := by
  simp [radius, (normalized P lam).2.1, (normalized P lam).2.2]

lemma angle_left (P : Problem) (lam : ℝ) : angle P lam P.a = 0 := by
  simp [angle]

lemma angularVelocity_continuous (P : Problem) (lam : ℝ) :
    ContinuousOn (angularVelocity P lam) (intervalValue P) := by
  apply ContinuousOn.div
  · exact ((P.p_regular.continuousOn.inv₀ (fun x hx => ne_of_gt (P.p_positive x hx))).mul
      ((Separation.flux_continuous (normalized P lam).1).pow 2)).add
      ((continuousOn_const.mul P.w_continuous |>.sub P.q_continuous).mul
        ((normalized P lam).1.1.continuousOn.pow 2))
  · exact (radius_continuous P lam).pow 2
  · intro x hx
    exact pow_ne_zero 2 (ne_of_gt (radius_pos P lam hx))

lemma angle_hasDerivWithinAt (P : Problem) (lam : ℝ) {x : ℝ} (hx : x ∈ intervalValue P) :
    HasDerivWithinAt (angle P lam) (angularVelocity P lam x) (intervalValue P) x :=
  D13Unified.hasDerivWithinAt_integral_on_interval ordConnected_Icc
    (angularVelocity_continuous P lam) (left_mem P) hx

lemma angle_continuous (P : Problem) (lam : ℝ) :
    ContinuousOn (angle P lam) (intervalValue P) := by
  intro x hx
  exact (angle_hasDerivWithinAt P lam hx).continuousWithinAt

/-- The radius has the derivative forced by the first-order system. -/
lemma radius_hasDerivWithinAt (P : Problem) (lam : ℝ) {x : ℝ}
    (hx : x ∈ intervalValue P) :
    HasDerivWithinAt (radius P lam)
      (((P.p x)⁻¹ + (P.q x - lam * P.w x)) *
        solution P lam x * flux P (solution P lam) x / radius P lam x)
      (intervalValue P) x := by
  have hy := Separation.solution_derivative (normalized P lam).1 hx
  have hz := Separation.solution_flux_derivative (normalized P lam).1 hx
  have hdy : derivative P (solution P lam) x =
      (P.p x)⁻¹ * flux P (solution P lam) x := by
    simp [flux, ne_of_gt (P.p_positive x hx)]
  rw [hdy] at hy
  have hpos : 0 < solution P lam x ^ 2 + flux P (solution P lam) x ^ 2 := by
    rw [← radius_sq]
    exact sq_pos_of_pos (radius_pos P lam hx)
  convert ((hy.pow 2).add (hz.pow 2)).sqrt (ne_of_gt hpos) using 1
  · rfl
  · dsimp [radius]
    ring

/-- Dividing by the radius reduces the state to a linear rotation equation.
This supplies a direct argument-lift construction rather than presupposing one. -/
lemma normalized_state_derivative (P : Problem) (lam : ℝ) {x : ℝ}
    (hx : x ∈ intervalValue P) :
    HasDerivWithinAt
      (fun t => ![solution P lam t / radius P lam t,
        flux P (solution P lam) t / radius P lam t])
      ![angularVelocity P lam x * (flux P (solution P lam) x / radius P lam x),
        -angularVelocity P lam x * (solution P lam x / radius P lam x)]
      (intervalValue P) x := by
  have hy := Separation.solution_derivative (normalized P lam).1 hx
  have hz := Separation.solution_flux_derivative (normalized P lam).1 hx
  have hdy : derivative P (solution P lam) x =
      (P.p x)⁻¹ * flux P (solution P lam) x := by
    simp [flux, ne_of_gt (P.p_positive x hx)]
  rw [hdy] at hy
  have hr := radius_hasDerivWithinAt P lam hx
  have hn := ne_of_gt (radius_pos P lam hx)
  have hs := radius_sq P lam x
  apply hasDerivWithinAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivWithinAt (fun t => solution P lam t / radius P lam t)
      (angularVelocity P lam x * (flux P (solution P lam) x / radius P lam x)) _ _
    convert hy.div hr hn using 1
    dsimp only [angularVelocity]
    field_simp [hn]
    rw [hs]
    ring
  · change HasDerivWithinAt (fun t => flux P (solution P lam) t / radius P lam t)
      (-angularVelocity P lam x * (solution P lam x / radius P lam x)) _ _
    convert hz.div hr hn using 1
    dsimp only [angularVelocity]
    field_simp [hn]
    rw [hs]
    ring

lemma sin_cos_derivative (P : Problem) (lam : ℝ) {x : ℝ}
    (hx : x ∈ intervalValue P) :
    HasDerivWithinAt
      (fun t => ![Real.sin (angle P lam t), Real.cos (angle P lam t)])
      ![angularVelocity P lam x * Real.cos (angle P lam x),
        -angularVelocity P lam x * Real.sin (angle P lam x)]
      (intervalValue P) x := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  fin_cases i
  · simpa [mul_comm] using (angle_hasDerivWithinAt P lam hx).sin
  · simpa [mul_comm, neg_mul] using (angle_hasDerivWithinAt P lam hx).cos

lemma normalized_state_eq (P : Problem) (lam : ℝ) :
    EqOn (fun t => ![solution P lam t / radius P lam t,
      flux P (solution P lam) t / radius P lam t])
      (fun t => ![Real.sin (angle P lam t), Real.cos (angle P lam t)])
      (intervalValue P) := by
  let I : TimeInterval := ⟨intervalValue P, ⟨P.a, left_mem P⟩, ordConnected_Icc⟩
  let A : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun t => !![0, angularVelocity P lam t; -angularVelocity P lam t, 0]
  have hA : ContinuousOn A (intervalValue P) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact continuousOn_const
    · exact angularVelocity_continuous P lam
    · exact (angularVelocity_continuous P lam).neg
    · exact continuousOn_const
  obtain ⟨Z, _, _, _, _, huniq⟩ :=
    Ch07.LinearSystemExistence.vector_existence ℝ 2 I A P.a ![0,1] (left_mem P) hA
  have hnc : ContinuousOn
      (fun t => ![solution P lam t / radius P lam t,
        flux P (solution P lam) t / radius P lam t]) (intervalValue P) := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact (normalized P lam).1.1.continuousOn.div (radius_continuous P lam)
        (fun x hx => ne_of_gt (radius_pos P lam hx))
    · exact (Separation.flux_continuous (normalized P lam).1).div (radius_continuous P lam)
        (fun x hx => ne_of_gt (radius_pos P lam hx))
  have htc : ContinuousOn
      (fun t => ![Real.sin (angle P lam t), Real.cos (angle P lam t)]) (intervalValue P) := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact Real.continuous_sin.comp_continuousOn (angle_continuous P lam)
    · exact Real.continuous_cos.comp_continuousOn (angle_continuous P lam)
  have hN := huniq _ hnc (by simp [radius_left, (normalized P lam).2.1, (normalized P lam).2.2])
    (fun x hx => by
      convert normalized_state_derivative P lam hx using 1
      ext i
      fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  have hT := huniq _ htc (by simp [angle_left])
    (fun x hx => by
      convert sin_cos_derivative P lam hx using 1
      ext i
      fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
  intro x hx
  exact (hN hx).trans (hT hx).symm

theorem angle_lift : Specs.D13Unified.Ch10.Prufer.AngleLift := by
  intro P lam
  refine ⟨radius_continuous P lam, angle_continuous P lam, angle_left P lam, ?_⟩
  intro x hx
  have hn := ne_of_gt (radius_pos P lam hx)
  have h0 := congrFun (normalized_state_eq P lam hx) 0
  have h1 := congrFun (normalized_state_eq P lam hx) 1
  refine ⟨radius_pos P lam hx, ?_, ?_⟩
  · exact (div_eq_iff hn).mp h0 |>.trans (mul_comm _ _)
  · exact (div_eq_iff hn).mp h1 |>.trans (mul_comm _ _)

theorem angle_derivative : Specs.D13Unified.Ch10.Prufer.AngleDerivative := by
  intro P lam x hx
  convert angle_hasDerivWithinAt P lam hx using 1
  have h := (angle_lift P lam).2.2.2 x hx
  dsimp [angularVelocity]
  rw [h.2.1, h.2.2]
  field_simp [ne_of_gt h.1]

theorem upward_crossings : Specs.D13Unified.Ch10.Prufer.UpwardCrossings := by
  intro P lam x hx hy
  have h := (angle_lift P lam).2.2.2 x hx
  have hs : Real.sin (angle P lam x) = 0 :=
    (mul_eq_zero.mp (h.2.1.symm.trans hy)).resolve_left (ne_of_gt h.1)
  have hc : Real.cos (angle P lam x) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (angle P lam x)]
  refine ⟨?_, inv_pos.mpr (P.p_positive x hx)⟩
  simpa [hs, hc] using angle_derivative P lam x hx

/-- Differentiating a continuously time-dependent linear family with affine
parameter dependence. The proof uses difference quotients and uniform Volterra
dependence; it requires no time derivative of the coefficients. -/
lemma affine_parameter_derivative
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → ℝ → E →L[ℝ] E) (D : ℝ → E →L[ℝ] E)
    (Y : ℝ → ℝ → E) (ξ : E) (lam : ℝ)
    (hAc : Continuous (fun q : ℝ × Icc a b => A q.1 q.2))
    (hDc : ContinuousOn D (Icc a b))
    (hYa : ∀ mu, Y mu a = ξ)
    (hYc : ∀ mu, ContinuousOn (Y mu) (Icc a b))
    (hYd : ∀ mu x, x ∈ Icc a b →
      HasDerivWithinAt (Y mu) (A mu x (Y mu x)) (Icc a b) x)
    (haff : ∀ mu x, x ∈ Icc a b → A mu x - A lam x = (mu-lam) • D x) :
    ∃ V : ℝ → E, ContinuousOn V (Icc a b) ∧ V a = 0 ∧
      (∀ x ∈ Icc a b, HasDerivWithinAt V
        (A lam x (V x) + D x (Y lam x)) (Icc a b) x) ∧
      ∀ x ∈ Icc a b, HasDerivAt (fun mu => Y mu x) (V x) lam := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hA (mu : ℝ) : ContinuousOn (A mu) (Icc a b) := by
    exact continuousOn_iff_continuous_domRestrict.mpr
      (hAc.comp (continuous_const.prodMk continuous_id))
  let B : ℝ → E := fun x => D x (Y lam x)
  have hB : ContinuousOn B (Icc a b) := hDc.clm_apply (hYc lam)
  obtain ⟨V, hV, _⟩ := Ch06.LinearVolterra.existence a b a (A lam) B 0 ha (hA lam) hB
  have hVd := (Ch06.LinearVolterra.differential_equivalence a b a (A lam) B 0 V ha
    (hA lam) hB).mp hV
  let Q : ℝ → ℝ → E := fun mu x =>
    if mu = lam then V x else (mu-lam)⁻¹ • (Y mu x - Y lam x)
  have hQ (mu : ℝ) : Ch06.LinearVolterra.IsIntegralSolution a b a (A mu) B 0 (Q mu) := by
    by_cases hm : mu = lam
    · subst mu
      simpa [Q] using hV
    have hm0 : mu - lam ≠ 0 := sub_ne_zero.mpr hm
    apply (Ch06.LinearVolterra.differential_equivalence a b a (A mu) B 0 (Q mu) ha
      (hA mu) hB).mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Q, ite_eq_right hm, Pi.smul_def, Pi.sub_def] using ((hYc mu).sub (hYc lam)).const_smul ((mu-lam)⁻¹)
    · simp [Q, hm, hYa]
    · intro x hx
      have hD : A mu x (Y lam x) - A lam x (Y lam x) =
          (mu-lam) • D x (Y lam x) := by
        exact congrArg (fun T : E →L[ℝ] E => T (Y lam x)) (haff mu x hx)
      have hsplit : A mu x (Y mu x) - A lam x (Y lam x) =
          A mu x (Y mu x - Y lam x) + (mu-lam) • D x (Y lam x) := by
        rw [map_sub, ← hD]
        abel
      have heq : (mu-lam)⁻¹ • (A mu x (Y mu x) - A lam x (Y lam x)) =
          A mu x (Q mu x) + B x := by
        rw [hsplit, smul_add, smul_smul, inv_mul_cancel₀ hm0, one_smul]
        simp [Q, hm, B]
      simpa only [Q, ite_eq_right hm, heq, Pi.smul_def, Pi.sub_def] using
        ((hYd mu x hx).sub (hYd lam x hx)).const_smul ((mu-lam)⁻¹)
  let AA (mu : ℝ) : C(Icc a b, E →L[ℝ] E) :=
    ⟨fun x => A mu x, (hA mu).domRestrict⟩
  have hAA : Continuous AA := ContinuousMap.continuous_of_continuous_uncurry AA hAc
  have hAlim : TendstoUniformlyOn A (A lam) (𝓝 lam) (Icc a b) :=
    tendstoUniformlyOn_iff_restrict.mpr
      (ContinuousMap.tendsto_iff_tendstoUniformly.mp hAA.continuousAt)
  have hQlim := Ch06.LinearVolterra.tendstoUniformlyOn_solutions ha hA
    (fun _ => hB) (hA lam) hB hQ hV hAlim (by
      rw [Metric.tendstoUniformlyOn_iff]
      exact fun ε hε => Eventually.of_forall (fun _ _ _ => by simpa using hε)) tendsto_const_nhds
  refine ⟨V, hVd.1, hVd.2.1, hVd.2.2, ?_⟩
  intro x hx
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hp : Tendsto (fun mu => Q mu x) (𝓝[≠] lam) (𝓝 (V x)) :=
    (hQlim.tendsto_at hx).mono_left nhdsWithin_le_nhds
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with mu hmu
  have hm : mu ≠ lam := hmu
  simp [Q, hm, slope, vsub_eq_sub]

/-- The coefficient family is continuous jointly in λ and x on the fixed
interval, although no x derivative of q or w need exist. -/
lemma systemMatrix_joint (P : Problem) :
    Continuous (fun q : ℝ × intervalValue P => Separation.systemMatrix P q.1 q.2) := by
  have hp : Continuous (fun q : ℝ × intervalValue P => P.p q.2) :=
    P.p_regular.continuousOn.domRestrict.comp continuous_snd
  have hq : Continuous (fun q : ℝ × intervalValue P => P.q q.2) :=
    P.q_continuous.domRestrict.comp continuous_snd
  have hw : Continuous (fun q : ℝ × intervalValue P => P.w q.2) :=
    P.w_continuous.domRestrict.comp continuous_snd
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact hp.inv₀ (fun q => ne_of_gt (P.p_positive q.2 q.2.property))
  · exact hq.sub (continuous_fst.mul hw)
  · exact continuous_const

lemma state_parameter_derivative (P : Problem) (lam : ℝ) :
    ∃ V : ℝ → Fin 2 → ℝ,
      ContinuousOn V (intervalValue P) ∧ V P.a = 0 ∧
      (∀ x ∈ intervalValue P, HasDerivWithinAt V
        (Separation.systemMatrix P lam x *ᵥ V x + ![0, -P.w x * solution P lam x])
        (intervalValue P) x) ∧
      ∀ x ∈ intervalValue P,
        HasDerivAt (fun mu => Separation.state P (solution P mu) x) (V x) lam := by
  let A (mu x : ℝ) := Ch07.LinearSystemExistence.vectorAction (Separation.systemMatrix P mu x)
  let D (x : ℝ) := Ch07.LinearSystemExistence.vectorAction (!![0,0; -P.w x,0])
  have hDc : ContinuousOn D (intervalValue P) := by
    apply Ch07.LinearSystemExistence.continuous_vectorAction.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact continuousOn_const
    · exact continuousOn_const
    · exact P.w_continuous.neg
    · exact continuousOn_const
  have haff (mu x : ℝ) (_hx : x ∈ intervalValue P) :
      A mu x - A lam x = (mu-lam) • D x := by
    ext v i
    fin_cases i <;>
      simp [A, D, Ch07.LinearSystemExistence.vectorAction_apply,
        Separation.systemMatrix, dotProduct, Fin.sum_univ_two]
    all_goals ring
  obtain ⟨V, hc, hi, hd, hp⟩ := affine_parameter_derivative P.a_lt_b.le A D
    (fun mu => Separation.state P (solution P mu)) ![0,1] lam
    (Ch07.LinearSystemExistence.continuous_vectorAction.comp (systemMatrix_joint P)) hDc
    (fun mu => by simp [Separation.state, (normalized P mu).2.1, (normalized P mu).2.2])
    (fun mu => Separation.state_continuous (normalized P mu).1)
    (fun mu x hx => Separation.state_derivative (normalized P mu).1 hx) haff
  refine ⟨V, hc, hi, ?_, hp⟩
  intro x hx
  convert hd x hx using 1 <;> try rfl
  ext i
  fin_cases i <;>
    simp [A, D, Ch07.LinearSystemExistence.vectorAction_apply, Separation.state,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem parameter_variation : Specs.D13Unified.Ch10.Prufer.ParameterVariation := by
  intro P lam
  obtain ⟨V, hc, hi, hd, hp⟩ := state_parameter_derivative P lam
  have hv (x : ℝ) (hx : x ∈ intervalValue P) : variation P lam x = V x 0 :=
    (hasDerivAt_pi.mp (hp x hx) 0).deriv
  have hf (x : ℝ) (hx : x ∈ intervalValue P) : fluxVariation P lam x = V x 1 :=
    (hasDerivAt_pi.mp (hp x hx) 1).deriv
  refine ⟨((continuousOn_pi.mp hc) 0).congr hv,
    ((continuousOn_pi.mp hc) 1).congr hf, ?_, ?_, ?_⟩
  · rw [hv P.a (left_mem P), hi]; rfl
  · rw [hf P.a (left_mem P), hi]; rfl
  · intro x hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hv x hx]
      exact hasDerivAt_pi.mp (hp x hx) 0
    · rw [hf x hx]
      exact hasDerivAt_pi.mp (hp x hx) 1
    · rw [hf x hx]
      have h := hasDerivWithinAt_pi.mp (hd x hx) 0
      simp [Separation.systemMatrix, dotProduct, Fin.sum_univ_two] at h
      exact h.congr_of_mem (fun t ht => hv t ht) hx
    · rw [hv x hx]
      have h := hasDerivWithinAt_pi.mp (hd x hx) 1
      simp [Separation.systemMatrix, dotProduct, Fin.sum_univ_two] at h
      exact h.congr_of_mem (fun t ht => hf t ht) hx

/-- Positivity uses an actual nonzero value and continuity on a nondegenerate
interval; it holds for every real parameter without any spectral hypothesis. -/
theorem terminal_strictness : Specs.D13Unified.Ch10.Prufer.TerminalStrictness := by
  intro P lam
  apply div_pos _ (sq_pos_of_pos (radius_pos P lam (right_mem P)))
  apply intervalIntegral.integral_pos P.a_lt_b
  · exact P.w_continuous.mul ((normalized P lam).1.1.continuousOn.pow 2)
  · intro x hx
    exact mul_nonneg (P.w_positive x ⟨hx.1.le, hx.2⟩).le (sq_nonneg _)
  · obtain ⟨x, hx, hn⟩ := solution_nonzero P lam
    exact ⟨x, hx, mul_pos (P.w_positive x hx) (sq_pos_of_ne_zero hn)⟩

lemma state_joint_continuous (P : Problem) :
    Continuous (fun q : ℝ × intervalValue P => Separation.state P (solution P q.1) q.2) := by
  let A (mu x : ℝ) := Ch07.LinearSystemExistence.vectorAction (Separation.systemMatrix P mu x)
  have hA := Ch07.LinearSystemExistence.continuous_vectorAction.comp (systemMatrix_joint P)
  have hc (mu : ℝ) : ContinuousOn (A mu) (intervalValue P) :=
    Ch07.LinearSystemExistence.continuous_vectorAction.comp_continuousOn
      (Separation.systemMatrix_continuous P mu)
  obtain ⟨Z, hZ, hZj⟩ := Ch06.LinearVolterra.joint_dependence P.a P.b P.a A
    (fun _ _ => 0) (fun _ : ℝ => (![0,1] : Fin 2 → ℝ)) (left_mem P)
    hA continuous_const continuous_const
  apply hZj.congr
  rintro ⟨mu, x, hx⟩
  have hy : Ch06.LinearVolterra.IsIntegralSolution P.a P.b P.a (A mu) (fun _ => 0)
      ![0,1] (Separation.state P (solution P mu)) := by
    apply (Ch06.LinearVolterra.differential_equivalence P.a P.b P.a (A mu) (fun _ => 0)
      ![0,1] _ (left_mem P) (hc mu) continuousOn_const).mpr
    refine ⟨Separation.state_continuous (normalized P mu).1, ?_, ?_⟩
    · simp [Separation.state, (normalized P mu).2.1, (normalized P mu).2.2]
    · intro x hx
      simpa [A, intervalValue] using Separation.state_derivative (normalized P mu).1 hx
  exact (Ch06.LinearVolterra.unique (left_mem P) (hc mu) continuousOn_const hy (hZ mu) hx).symm

lemma angularVelocity_joint (P : Problem) :
    Continuous (fun q : ℝ × intervalValue P => angularVelocity P q.1 q.2) := by
  have hy : Continuous (fun q : ℝ × intervalValue P => solution P q.1 q.2) :=
    (continuous_apply 0).comp (state_joint_continuous P)
  have hz : Continuous (fun q : ℝ × intervalValue P => flux P (solution P q.1) q.2) :=
    (continuous_apply 1).comp (state_joint_continuous P)
  have hp := P.p_regular.continuousOn.domRestrict.comp (continuous_snd (X := ℝ))
  have hq := P.q_continuous.domRestrict.comp (continuous_snd (X := ℝ))
  have hw := P.w_continuous.domRestrict.comp (continuous_snd (X := ℝ))
  apply Continuous.div
  · exact ((hp.inv₀ (fun q => ne_of_gt (P.p_positive q.2 q.2.property))).mul (hz.pow 2)).add
      ((continuous_fst.mul hw |>.sub hq).mul (hy.pow 2))
  · exact ((hy.pow 2).add (hz.pow 2)).sqrt.pow 2
  · intro q
    exact pow_ne_zero 2 (ne_of_gt (radius_pos P q.1 q.2.property))

lemma angle_parameter_continuous (P : Problem) {x : ℝ} (hx : x ∈ intervalValue P) :
    Continuous (fun mu => angle P mu x) := by
  let f : ℝ → ℝ → ℝ := fun mu t =>
    angularVelocity P mu (projIcc P.a P.b P.a_lt_b.le t)
  have hfc : Continuous f.uncurry :=
    (angularVelocity_joint P).comp (continuous_fst.prodMk ((continuous_projIcc (h := P.a_lt_b.le)).comp continuous_snd))
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hfc (isCompact_Icc (a := P.a) (b := x))
  apply hi.congr
  intro mu
  rw [angle, intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp [f]
  congr 1
  exact congrArg Subtype.val (projIcc_of_mem P.a_lt_b.le ⟨ht.1, ht.2.trans hx.2⟩)

lemma parameter_wronskian (P : Problem) (lam : ℝ) {x : ℝ} (hx : x ∈ intervalValue P) :
    flux P (solution P lam) x * variation P lam x -
      solution P lam x * fluxVariation P lam x =
      ∫ t in P.a..x, P.w t * solution P lam t ^ 2 := by
  have hv := parameter_variation P lam
  let W : ℝ → ℝ := fun t => flux P (solution P lam) t * variation P lam t -
    solution P lam t * fluxVariation P lam t
  have hc : ContinuousOn W (intervalValue P) :=
    ((Separation.flux_continuous (normalized P lam).1).mul hv.1).sub
      ((normalized P lam).1.1.continuousOn.mul hv.2.1)
  have hd (t : ℝ) (ht : t ∈ intervalValue P) :
      HasDerivWithinAt W (P.w t * solution P lam t ^ 2) (intervalValue P) t := by
    have hy := Separation.solution_derivative (normalized P lam).1 ht
    have hz := Separation.solution_flux_derivative (normalized P lam).1 ht
    have hdy : derivative P (solution P lam) t = (P.p t)⁻¹ * flux P (solution P lam) t := by
      simp [flux, ne_of_gt (P.p_positive t ht)]
    rw [hdy] at hy
    have hvar := hv.2.2.2.2 t ht
    convert (hz.mul hvar.2.2.1).sub (hy.mul hvar.2.2.2) using 1
    all_goals ring
  have heq := integral_eq_sub_on_interval ordConnected_Icc hc
    (P.w_continuous.mul ((normalized P lam).1.1.continuousOn.pow 2)) hd (left_mem P) hx
  have hWa : W P.a = 0 := by
    simp [W, hv.2.2.1, hv.2.2.2.1, (normalized P lam).2.1]
  simpa [hWa] using heq.symm

/-- A local arctangent chart differentiates the continuous lift in λ. The
chart is applied only to the angle difference, which stays in (-π/2,π/2)
near the chosen parameter; no global principal-argument continuity is used. -/
lemma angle_parameter_hasDerivAt (P : Problem) (lam : ℝ) {x : ℝ}
    (hx : x ∈ intervalValue P) :
    HasDerivAt (fun mu => angle P mu x)
      ((flux P (solution P lam) x * variation P lam x -
        solution P lam x * fluxVariation P lam x) / radius P lam x ^ 2) lam := by
  let y (mu : ℝ) := solution P mu x
  let z (mu : ℝ) := flux P (solution P mu) x
  let F (mu : ℝ) := (y mu * z lam - z mu * y lam) / (z mu * z lam + y mu * y lam)
  have hv := (parameter_variation P lam).2.2.2.2 x hx
  have hy : HasDerivAt y (variation P lam x) lam := hv.1
  have hz : HasDerivAt z (fluxVariation P lam x) lam := hv.2.1
  have hden : z lam * z lam + y lam * y lam = radius P lam x ^ 2 := by
    rw [radius_sq]
    dsimp [y, z]
    ring
  have hn : z lam * z lam + y lam * y lam ≠ 0 := by
    rw [hden]
    exact pow_ne_zero 2 (ne_of_gt (radius_pos P lam hx))
  have hnum := (hy.mul_const (z lam)).sub (hz.mul_const (y lam))
  have hdenD := (hz.mul_const (z lam)).add (hy.mul_const (y lam))
  have hF : HasDerivAt (fun mu => Real.arctan (F mu))
      ((z lam * variation P lam x - y lam * fluxVariation P lam x) / radius P lam x ^ 2) lam := by
    convert (hnum.div hdenD hn).arctan using 1
    dsimp [F]
    have hzero : y lam * z lam - z lam * y lam = 0 := by ring
    rw [hzero, zero_div]
    simp only [zero_pow (by decide : 2 ≠ 0), add_zero, div_one, one_mul,
      zero_mul, sub_zero]
    rw [← hden]
    field_simp
  have hnear : ∀ᶠ mu in 𝓝 lam,
      angle P mu x - angle P lam x ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    apply ((angle_parameter_continuous P hx).continuousAt.sub_const (angle P lam x)).eventually
    apply Ioo_mem_nhds <;> simp only [sub_self]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have heq : (fun mu => angle P mu x) =ᶠ[𝓝 lam]
      (fun mu => angle P lam x + Real.arctan (F mu)) := by
    filter_upwards [hnear] with mu hmu
    have h0 := (angle_lift P lam).2.2.2 x hx
    have h1 := (angle_lift P mu).2.2.2 x hx
    have htan : F mu = Real.tan (angle P mu x - angle P lam x) := by
      calc
        F mu = (radius P mu x * radius P lam x * Real.sin (angle P mu x - angle P lam x)) /
            (radius P mu x * radius P lam x * Real.cos (angle P mu x - angle P lam x)) := by
          dsimp [F, y, z]
          rw [h0.2.1, h0.2.2, h1.2.1, h1.2.2, Real.sin_sub, Real.cos_sub]
          congr 1 <;> ring
        _ = Real.tan (angle P mu x - angle P lam x) := by
          rw [mul_div_mul_left _ _ (mul_ne_zero (ne_of_gt h1.1) (ne_of_gt h0.1))]
          exact (Real.tan_eq_sin_div_cos _).symm
    rw [htan, Real.arctan_tan hmu.1 hmu.2]
    ring
  exact (hF.const_add (angle P lam x)).congr_of_eventuallyEq heq

theorem angle_parameter_derivative : Specs.D13Unified.Ch10.Prufer.AngleParameterDerivative := by
  intro P lam x hx
  have hw := parameter_wronskian P lam hx
  exact ⟨hw ▸ angle_parameter_hasDerivAt P lam hx, hw⟩

theorem flux_variation_identity : Specs.D13Unified.Ch10.Prufer.FluxVariationIdentity := by
  intro P lam x hx
  have hv := ((parameter_variation P lam).2.2.2.2 x hx).2.2.1
  have heq := hv.derivWithin ((Separation.uniqueDiff P) x hx)
  simp [flux, heq, ne_of_gt (P.p_positive x hx)]

theorem radius_parameter_derivative : Specs.D13Unified.Ch10.Prufer.RadiusParameterDerivative := by
  intro P lam x hx
  have h := (parameter_variation P lam).2.2.2.2 x hx
  have hpos : solution P lam x ^ 2 + flux P (solution P lam) x ^ 2 ≠ 0 := by
    rw [← radius_sq]
    exact pow_ne_zero 2 (ne_of_gt (radius_pos P lam hx))
  convert ((h.1.pow 2).add (h.2.1.pow 2)).sqrt hpos using 1
  · rfl
  · dsimp [radius]
    ring

theorem terminal_parameter_derivative : Specs.D13Unified.Ch10.Prufer.TerminalParameterDerivative := by
  intro P lam
  exact ⟨(angle_parameter_derivative P lam P.b (right_mem P)).1, terminal_strictness P lam⟩

end D13Unified.Ch10.Prufer
