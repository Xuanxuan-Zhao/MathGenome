import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.IndexProperties
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.CircleLift
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexProperties

namespace D13Unified.Ch21.IndexProperties
open unitInterval Set
open scoped Topology
noncomputable section

abbrev Loop := Specs.D13Unified.Ch21.IndexProperties.Loop
abbrev Avoids := Specs.D13Unified.Ch21.IndexProperties.Avoids
abbrev IsLogLift := Specs.D13Unified.Ch21.IndexProperties.IsLogLift
abbrev IsArgument := Specs.D13Unified.Ch21.IndexProperties.IsArgument
abbrev HasIndex := Specs.D13Unified.Ch21.IndexProperties.HasIndex
abbrev index := Specs.D13Unified.Ch21.IndexProperties.index
abbrev period := Specs.D13Unified.Ch21.IndexProperties.period
abbrev planeDet := Specs.D13Unified.Ch21.IndexProperties.planeDet
abbrev circleLoop := Specs.D13Unified.Ch21.IndexProperties.circleLoop

private abbrev expProjection (z : ℂ) : {z : ℂ // z ≠ 0} := ⟨z.exp, z.exp_ne_zero⟩

lemma period_ne_zero : period ≠ 0 := by
  simp [period, Specs.D13Unified.Ch21.IndexProperties.period, Real.pi_ne_zero]

theorem log_lift_exists (α : Loop) (p : ℂ) (ha : Avoids α p) :
    ∃ L : C(I, ℂ), IsLogLift α p L := by
  let f : C(I, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨α t - p, sub_ne_zero.mpr (ha t)⟩,
      (α.map.continuous.sub continuous_const).subtype_mk _⟩
  obtain ⟨L, hL, _⟩ := Complex.isCoveringMap_exp.exists_path_lifts f
    (Complex.log (α 0 - p)) (Subtype.ext (Complex.exp_log (sub_ne_zero.mpr (ha 0))).symm)
  exact ⟨L, fun t => congrArg Subtype.val (congrFun hL t)⟩

theorem log_lifts_differ_by_integer (α : Loop) (p : ℂ) (L M : C(I, ℂ))
    (hL : IsLogLift α p L) (hM : IsLogLift α p M) :
    ∃ k : ℤ, ∀ t, L t = M t + (k : ℂ) * period := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp ((hL 0).trans (hM 0).symm)
  refine ⟨k, ?_⟩
  have he : (L : I → ℂ) = fun t => M t + (k : ℂ) * period := by
    apply Complex.isCoveringMap_exp.eq_of_comp_eq L.continuous
      (M.continuous.add continuous_const) ?_ 0 hk
    funext t
    apply Subtype.ext
    change Complex.exp (L t) = Complex.exp (M t + (k : ℂ) * period)
    have hp : Complex.exp ((k : ℂ) * period) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩
    rw [Complex.exp_add, hp, mul_one, hL t, hM t]
  exact congrFun he

lemma index_unique {α : Loop} {p : ℂ} {k l : ℤ}
    (hk : HasIndex α p k) (hl : HasIndex α p l) : k = l := by
  obtain ⟨L, hL, hLend⟩ := hk
  obtain ⟨M, hM, hMend⟩ := hl
  obtain ⟨j, hj⟩ := log_lifts_differ_by_integer α p L M hL hM
  have he : (k : ℂ) * period = (l : ℂ) * period := by
    rw [← hLend, ← hMend, hj 1, hj 0]
    ring
  exact_mod_cast mul_right_cancel₀ period_ne_zero he

theorem index_exists_unique (α : Loop) (p : ℂ) (ha : Avoids α p) :
    ∃! k : ℤ, HasIndex α p k := by
  obtain ⟨L, hL⟩ := log_lift_exists α p ha
  have h := (hL 1).trans ((congrArg (fun z : ℂ => z - p) α.closed).symm.trans (hL 0).symm)
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨k, ⟨L, hL, ?_⟩, fun l hl => index_unique hl ⟨L, hL, ?_⟩⟩ <;>
    exact sub_eq_iff_eq_add.mpr (by simpa [Specs.D13Unified.Ch21.IndexProperties.period, add_comm] using hk)

theorem index_characterization (α : Loop) (p : ℂ) (ha : Avoids α p) (k : ℤ) :
    HasIndex α p k ↔ k = index α p := by
  have hex := (index_exists_unique α p ha).exists
  have hc : HasIndex α p (index α p) := by
    simpa only [index, Specs.D13Unified.Ch21.IndexProperties.index, dite_eq_left hex] using
      Classical.choose_spec hex
  exact ⟨fun hk => index_unique hk hc, fun hk => hk ▸ hc⟩

theorem argument_lift_exists (α : Loop) (p : ℂ) (ha : Avoids α p) :
    ∃ θ : C(I, ℝ), IsArgument α p θ ∧
      θ 1 - θ 0 = 2 * Real.pi * (index α p : ℝ) := by
  obtain ⟨L, hL, hend⟩ := (index_characterization α p ha (index α p)).mpr rfl
  refine ⟨⟨fun t => (L t).im, Complex.continuous_im.comp L.continuous⟩, ?_, ?_⟩
  · intro t
    change α t - p = (‖α t - p‖ : ℂ) * Complex.exp ((L t).im * Complex.I)
    rw [← hL t, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
  · have h := congrArg Complex.im hend
    simpa [period, Specs.D13Unified.Ch21.IndexProperties.period, mul_comm, mul_left_comm] using h


theorem argument_lift_independent (α : Loop) (p : ℂ) (ha : Avoids α p)
    (θ : C(I, ℝ)) (hθ : IsArgument α p θ) :
    θ 1 - θ 0 = 2 * Real.pi * (index α p : ℝ) := by
  let L : C(I, ℂ) := ⟨fun t => (Real.log ‖α t - p‖ : ℂ) + (θ t : ℂ) * Complex.I, by
    have hc := ((α.map.continuous.sub continuous_const).norm.log
      (fun t => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ha t))))
    exact (Complex.continuous_ofReal.comp hc).add
      ((Complex.continuous_ofReal.comp θ.continuous).mul continuous_const)⟩
  have hL : IsLogLift α p L := by
    intro t
    change Complex.exp ((Real.log ‖α t - p‖ : ℂ) + (θ t : ℂ) * Complex.I) = α t - p
    rw [Complex.exp_add, ← Complex.ofReal_exp,
      Real.exp_log (norm_pos_iff.mpr (sub_ne_zero.mpr (ha t)))]
    exact (hθ t).symm
  obtain ⟨M, hM, hend⟩ := (index_characterization α p ha (index α p)).mpr rfl
  obtain ⟨j, hj⟩ := log_lifts_differ_by_integer α p L M hL hM
  have he : L 1 - L 0 = (index α p : ℂ) * period := by
    rw [hj 1, hj 0, ← hend]; ring
  have him := congrArg Complex.im he
  simpa [L, period, Specs.D13Unified.Ch21.IndexProperties.period, mul_comm, mul_left_comm] using him

/-- A free loop homotopy has a logarithmic lift on the whole parameter square.
Its endpoint difference is continuous in the homotopy parameter and maps
under exp to 1, so the covering-map uniqueness principle makes it constant. -/
theorem homotopy_invariant (α β : Loop) (p : ℂ) (H : C(I × I, ℂ))
    (h0 : ∀ t, H (0, t) = α t) (h1 : ∀ t, H (1, t) = β t)
    (hc : ∀ s, H (s, 0) = H (s, 1)) (ha : ∀ s t, H (s, t) ≠ p) :
    index α p = index β p := by
  let f : C(I × I, {z : ℂ // z ≠ 0}) :=
    ⟨fun st => ⟨H st - p, sub_ne_zero.mpr (ha st.1 st.2)⟩,
      (H.continuous.sub continuous_const).subtype_mk _⟩
  have hα : Avoids α p := fun t => by simpa [h0] using ha 0 t
  have hβ : Avoids β p := fun t => by simpa [h1] using ha 1 t
  obtain ⟨L, hL, hend⟩ := (index_characterization α p hα (index α p)).mpr rfl
  have hf0 : ∀ t, f (0, t) = expProjection (L t) := by
    intro t
    apply Subtype.ext
    exact ((hL t).trans (congrArg (· - p) (h0 t).symm)).symm
  let F := Complex.isCoveringMap_exp.liftHomotopy f L hf0
  have hF := Complex.isCoveringMap_exp.liftHomotopy_lifts f L hf0
  have hF' (s t : I) : Complex.exp (F (s, t)) = H (s, t) - p :=
    congrArg Subtype.val (congrFun hF (s, t))
  have hconst : ∀ s t : I, F (s, 1) - F (s, 0) = F (t, 1) - F (t, 0) := by
    apply Complex.isCoveringMap_exp.const_of_comp
      ((F.continuous.comp (continuous_id.prodMk continuous_const)).sub
        (F.continuous.comp (continuous_id.prodMk continuous_const)))
    intro s t
    apply Subtype.ext
    change Complex.exp (F (s, 1) - F (s, 0)) = Complex.exp (F (t, 1) - F (t, 0))
    simp only [Complex.exp_sub, hF', ← hc,
      div_self (sub_ne_zero.mpr (ha _ _))]
  let F0 : C(I, ℂ) := ⟨fun t => F (0, t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let F1 : C(I, ℂ) := ⟨fun t => F (1, t), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hF0 : IsLogLift α p F0 := fun t => (hF' 0 t).trans (congrArg (· - p) (h0 t))
  have hF1 : IsLogLift β p F1 := fun t => (hF' 1 t).trans (congrArg (· - p) (h1 t))
  obtain ⟨j, hj⟩ := log_lifts_differ_by_integer α p F0 L hF0 hL
  apply (index_characterization β p hβ (index α p)).mp
  refine ⟨F1, hF1, ?_⟩
  calc
    F1 1 - F1 0 = F0 1 - F0 0 := hconst 1 0
    _ = L 1 - L 0 := by rw [hj 1, hj 0]; ring
    _ = _ := hend

/-- Index depends only on the path of displacement vectors. -/
lemma index_eq_of_displacement_eq (α β : Loop) (p q : ℂ)
    (he : ∀ t, α t - p = β t - q) : index α p = index β q := by
  have hh (k : ℤ) : HasIndex α p k ↔ HasIndex β q k := by
    simp only [HasIndex, Specs.D13Unified.Ch21.IndexProperties.HasIndex,
      Specs.D13Unified.Ch21.IndexProperties.IsLogLift, he]
  classical
  unfold index Specs.D13Unified.Ch21.IndexProperties.index
  split_ifs with hα hβ hβ
  · exact index_unique (Classical.choose_spec hα)
      ((hh _).mpr (Classical.choose_spec hβ))
  · exact False.elim (hβ ⟨_, (hh _).mp (Classical.choose_spec hα)⟩)
  · exact False.elim (hα ⟨_, (hh _).mpr (Classical.choose_spec hβ)⟩)
  · rfl


lemma constant_loop_index (z p : ℂ) (hz : z ≠ p) :
    index ⟨ContinuousMap.const I z, rfl⟩ p = 0 := by
  symm
  apply (index_characterization _ p (fun _ => hz) 0).mp
  refine ⟨ContinuousMap.const I (Complex.log (z - p)), ?_, by simp⟩
  intro t
  exact Complex.exp_log (sub_ne_zero.mpr hz)

theorem index_locally_constant (α : Loop) (p : ℂ) (ha : Avoids α p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℂ, dist q p < ε →
      Avoids α q ∧ index α q = index α p := by
  have hcompact : IsCompact (range α) := isCompact_range α.map.continuous
  have hp : p ∈ (range α)ᶜ := by rintro ⟨t, ht⟩; exact ha t ht
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl p hp
  refine ⟨ε, hε, fun q hq => ?_⟩
  have haq : Avoids α q := by
    intro t ht
    exact hball hq ⟨t, ht⟩
  let β : Loop := ⟨⟨fun t => α t - (q - p),
      α.map.continuous.sub continuous_const⟩, congrArg (· - (q - p)) α.closed⟩
  let H : C(I × I, ℂ) :=
    ⟨fun st => α st.2 - (st.1 : ℝ) • (q - p), by fun_prop⟩
  have hH : ∀ s t : I, H (s, t) ≠ p := by
    intro s t he
    have hev : α t - p = (s : ℝ) • (q - p) := by
      change α t - (s : ℝ) • (q - p) = p at he
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
    have hd : dist (α t) p < ε := by
      rw [dist_eq_norm, hev, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) s.property.2).trans_lt
        (by simpa [dist_eq_norm] using hq)
    exact hball hd ⟨t, rfl⟩
  have hi := homotopy_invariant α β p H (fun t => by simp [H])
    (fun t => by simp [H, β]) (fun s => by simp [H, α.closed]) hH
  refine ⟨haq, ?_⟩
  calc
    index α q = index β p := index_eq_of_displacement_eq α β q p (fun t => by dsimp [β]; ring)
    _ = index α p := hi.symm

theorem index_zero_outside_ball (α : Loop) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : ℂ, R < ‖p‖ → Avoids α p ∧ index α p = 0 := by
  obtain ⟨R, hR, hbound⟩ := (isCompact_range α.map.continuous).isBounded.exists_pos_norm_lt
  refine ⟨R, hR, fun p hp => ?_⟩
  have ha : Avoids α p := fun t he => by
    have := hbound (α t) ⟨t, rfl⟩
    rw [he] at this
    linarith
  let β : Loop := ⟨ContinuousMap.const I 0, rfl⟩
  let H : C(I × I, ℂ) := ⟨fun st => (1 - (st.1 : ℝ)) • α st.2, by fun_prop⟩
  have hH : ∀ s t : I, H (s, t) ≠ p := by
    intro s t he
    have hs : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.property.2
    have hn : ‖H (s, t)‖ < R := by
      change ‖(1 - (s : ℝ)) • α t‖ < R
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [s.property.1])).trans_lt
        (hbound (α t) ⟨t, rfl⟩)
    rw [he] at hn
    linarith
  have hi := homotopy_invariant α β p H (fun t => by simp [H])
    (fun t => by simp [H, β]) (fun s => by simp [H, α.closed]) hH
  exact ⟨ha, hi.trans (constant_loop_index 0 p (by intro he; rw [← he, norm_zero] at hp; linarith))⟩

theorem circle_periodic_lift
    (γ : C(Ch15.CircleLift.Circle, ℂ)) (x : ℝ) (k : ℤ) :
    γ (Ch15.CircleLift.quotientMap (x + (k : ℝ))) = γ (Ch15.CircleLift.quotientMap x) := by
  exact congrArg γ ((Ch15.CircleLift.quotientMap_eq_iff _ _).mpr ⟨k, rfl⟩)

theorem circle_parameter_eq (x y : ℝ) :
    Ch15.CircleLift.quotientMap x = Ch15.CircleLift.quotientMap y ↔
      ∃ k : ℤ, x = y + (k : ℝ) := Ch15.CircleLift.quotientMap_eq_iff x y

theorem circle_trace (γ : C(Ch15.CircleLift.Circle, ℂ)) :
    range (circleLoop γ) = range γ := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Ch15.CircleLift.quotientMap t, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy, hxy⟩ := AddCircle.eq_coe_Ico x
    exact ⟨⟨y, hy.1, hy.2.le⟩, congrArg γ hxy⟩

theorem circle_avoids (γ : C(Ch15.CircleLift.Circle, ℂ)) (p : ℂ) :
    Avoids (circleLoop γ) p ↔ ∀ x, γ x ≠ p := by
  change (∀ t, circleLoop γ t ≠ p) ↔ ∀ x, γ x ≠ p
  simp only [← not_exists, ← mem_range, circle_trace]


/-- The imaginary logarithmic derivative is the standard positively oriented
area determinant divided by squared Euclidean norm. -/
lemma imaginary_log_derivative (z v : ℂ) :
    (z⁻¹ * v).im = planeDet z v / ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [planeDet, Specs.D13Unified.Ch21.IndexProperties.planeDet,
    Complex.mul_im, Complex.inv_re, Complex.inv_im]
  ring

/-- Construct a logarithmic lift by integrating the continuous logarithmic
 derivative. The exponential endpoint identity from the complex-analysis
 foundation is used on each actual subinterval [0,t]. -/
lemma integral_log_lift (α : Loop) (p : ℂ) (ha : Avoids α p)
    (f f' : ℝ → ℂ) (hfα : ∀ t : I, f t = α t)
    (hf : ContinuousOn f (Icc 0 1)) (hf' : ContinuousOn f' (Icc 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc 0 1) t) :
    ∃ L : C(I, ℂ), IsLogLift α p L ∧
      L 1 - L 0 = ∫ t in (0 : ℝ)..1, (f t - p)⁻¹ * f' t := by
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, f t - p ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr (by rw [hfα ⟨t, ht⟩]; exact ha ⟨t, ht⟩)
  let g : ℝ → ℂ := fun t => (f t - p)⁻¹ * f' t
  have hg : ContinuousOn g (Icc 0 1) := ((hf.sub continuousOn_const).inv₀ hne).mul hf'
  have hgi := hg.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hprim : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Icc 0 1) := by
    simpa using intervalIntegral.continuousOn_primitive_interval' hgi (by simp)
  let L : C(I, ℂ) := ⟨fun t => Complex.log (f 0 - p) + ∫ s in (0 : ℝ)..t, g s,
    continuous_const.add hprim.domRestrict⟩
  refine ⟨L, ?_, by simp [L, g]⟩
  intro t
  change Complex.exp (Complex.log (f 0 - p) + ∫ s in (0 : ℝ)..(t : ℝ), g s) = α t - p
  rw [Complex.exp_add, Complex.exp_log (hne 0 (by norm_num))]
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = 0 := Subtype.ext ht
    subst t
    change (f 0 - p) * Complex.exp (∫ s in (0 : ℝ)..0, g s) = α 0 - p
    simpa using congrArg (· - p) (hfα 0)
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl t.property.2
    have hder (x : ℝ) (hx : x ∈ Icc (0 : ℝ) t) :
        HasDerivWithinAt (fun x => f x - p) (f' x) (Icc 0 t) x :=
      ((hd x (hsub hx)).sub_const p).mono hsub
    have hdval (x : ℝ) (hx : x ∈ Icc (0 : ℝ) t) :
        derivWithin (fun x => f x - p) (Icc 0 t) x = f' x :=
      (hder x hx).derivWithin (uniqueDiffOn_Icc htpos x hx)
    have hC1 : ContDiffOn ℝ 1 (fun x => f x - p) (Icc (0 : ℝ) t) := by
      apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc htpos)).mpr
      exact ⟨fun x hx => (hder x hx).differentiableWithinAt,
        (hf'.mono hsub).congr (fun x hx => hdval x hx)⟩
    have he := D12Complex.IndexProperties.exp_integral_log_derivative htpos hC1
      (fun x hx => hne x (hsub hx))
    have hi : (∫ s in (0 : ℝ)..(t : ℝ), g s) =
        ∫ s in (0 : ℝ)..(t : ℝ), (f s - p)⁻¹ *
          derivWithin (fun x => f x - p) (Icc 0 t) s := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le htpos.le] at hx
      change (f x - p)⁻¹ * f' x = (f x - p)⁻¹ * derivWithin (fun x => f x - p) (Icc 0 t) x
      rw [hdval x hx]
    rw [hi, he, ← hfα t]
    field_simp [hne 0 (by norm_num)]

/-- The full C¹ winding formula, including one-sided endpoint derivatives. -/
theorem integral_formula (α : Loop) (p : ℂ) (ha : Avoids α p)
    (f f' : ℝ → ℂ) (hfα : ∀ t : I, f t = α t)
    (hf : ContinuousOn f (Icc 0 1)) (hf' : ContinuousOn f' (Icc 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Icc 0 1) t) :
    (index α p : ℝ) = (2 * Real.pi)⁻¹ *
      ∫ t in (0 : ℝ)..1, planeDet (f t - p) (f' t) / ‖f t - p‖ ^ 2 := by
  obtain ⟨L, hL, hend⟩ := integral_log_lift α p ha f f' hfα hf hf' hd
  obtain ⟨M, hM, hMend⟩ := (index_characterization α p ha (index α p)).mpr rfl
  obtain ⟨j, hj⟩ := log_lifts_differ_by_integer α p L M hL hM
  have he : (∫ t in (0 : ℝ)..1, (f t - p)⁻¹ * f' t) = (index α p : ℂ) * period := by
    rw [← hend, hj 1, hj 0, ← hMend]; ring
  have hg : ContinuousOn (fun t => (f t - p)⁻¹ * f' t) (Icc (0 : ℝ) 1) := by
    refine ((hf.sub continuousOn_const).inv₀ ?_).mul hf'
    intro t ht
    exact sub_ne_zero.mpr (by rw [hfα ⟨t, ht⟩]; exact ha ⟨t, ht⟩)
  have him := congrArg Complex.im he
  have hi := Complex.imCLM.intervalIntegral_comp_comm
    (hg.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ) ≤ 1))
  change (∫ t in (0 : ℝ)..1, ((f t - p)⁻¹ * f' t).im) =
    (∫ t in (0 : ℝ)..1, (f t - p)⁻¹ * f' t).im at hi
  rw [← hi] at him
  simp only [imaginary_log_derivative] at him
  have hh : (∫ t in (0 : ℝ)..1, planeDet (f t - p) (f' t) / ‖f t - p‖ ^ 2) =
      2 * Real.pi * (index α p : ℝ) := by
    simpa [period, Specs.D13Unified.Ch21.IndexProperties.period, mul_comm, mul_left_comm] using him
  rw [hh]
  field_simp


theorem index_characterization_by_argument (α : Loop) (p : ℂ) (ha : Avoids α p) (k : ℤ) :
    (∃ θ : C(I, ℝ), IsArgument α p θ ∧ θ 1 - θ 0 = 2 * Real.pi * (k : ℝ)) ↔
      k = index α p := by
  constructor
  · rintro ⟨θ, hθ, hend⟩
    have hi := argument_lift_independent α p ha θ hθ
    have he : (k : ℝ) = (index α p : ℝ) :=
      mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) (hend.symm.trans hi)
    exact_mod_cast he
  · rintro rfl
    exact argument_lift_exists α p ha

/-- The complex representation has the specified Euclidean norm and the
standard left rotation, so it preserves both the metric and the orientation. -/
theorem plane_coordinates (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 ∧
      (Complex.I * z).re = -z.im ∧ (Complex.I * z).im = z.re := by
  constructor
  · rw [Complex.sq_norm, Complex.normSq_apply]; ring
  · simp

/-- Specialization to the periodic real lift of a circle-parametrized loop. -/
theorem circle_integral_formula (γ : C(Ch15.CircleLift.Circle, ℂ)) (p : ℂ)
    (ha : ∀ x, γ x ≠ p) (f' : ℝ → ℂ) (hf' : ContinuousOn f' (Icc 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t => γ (Ch15.CircleLift.quotientMap t)) (f' t) (Icc 0 1) t) :
    (index (circleLoop γ) p : ℝ) = (2 * Real.pi)⁻¹ *
      ∫ t in (0 : ℝ)..1,
        planeDet (γ (Ch15.CircleLift.quotientMap t) - p) (f' t) /
          ‖γ (Ch15.CircleLift.quotientMap t) - p‖ ^ 2 := by
  exact integral_formula (circleLoop γ) p ((circle_avoids γ p).mpr ha)
    (fun t => γ (Ch15.CircleLift.quotientMap t)) f' (fun _ => rfl)
    (γ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).continuousOn hf' hd

end
end D13Unified.Ch21.IndexProperties
