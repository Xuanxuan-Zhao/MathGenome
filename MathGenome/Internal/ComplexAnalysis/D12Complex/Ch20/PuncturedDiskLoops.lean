import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.PuncturedDiskLoops
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.ModelCoverings
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.CoveringHomotopies
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.Surfaces
import Mathlib.GroupTheory.Perm.Cycle.Basic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexOperationsHomotopy
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open unitInterval
namespace D12Complex.Ch20.PuncturedDiskLoops

/-- Inclusion of a punctured disk into the canonical punctured plane. -/
def puncturedInclusion {r : ℝ} (z : Disk r) : ModelCoverings.PuncturedPlane :=
  ⟨z, norm_pos_iff.mp z.property.1⟩

lemma continuous_puncturedInclusion {r : ℝ} :
    Continuous (puncturedInclusion (r := r)) := by
  exact continuous_subtype_val.subtype_mk _

/-- Every loop has a logarithmic lift starting at the principal logarithm of
its basepoint. Existence is supplied by the proved exponential covering. -/
theorem exists_log_lift {r : ℝ} (b : Disk r) (γ : Path b b) :
    ∃ L : C(I, ℂ), L 0 = Complex.log (b : ℂ) ∧
      ∀ t, Complex.exp (L t) = (γ t : ℂ) := by
  let q : C(I, ModelCoverings.PuncturedPlane) :=
    ⟨puncturedInclusion ∘ γ, continuous_puncturedInclusion.comp γ.continuous⟩
  have h₀ : ModelCoverings.expProjection (Complex.log (b : ℂ)) = q 0 := by
    apply Subtype.ext
    simpa [q, puncturedInclusion, ModelCoverings.expProjection] using
      Complex.exp_log (norm_pos_iff.mp b.property.1)
  obtain ⟨L, hL, _⟩ := CoveringPaths.path_lifting ModelCoverings.expProjection
    ModelCoverings.exponential_covering.2.1 q q.continuous (Complex.log (b : ℂ)) h₀
  refine ⟨⟨L, hL.1⟩, hL.2.1, fun t => ?_⟩
  exact congrArg Subtype.val (congrFun hL.2.2 t)

lemma log_lift_unique {r : ℝ} {b : Disk r} {γ : Path b b}
    {L M : C(I, ℂ)} (hL₀ : L 0 = Complex.log (b : ℂ))
    (hM₀ : M 0 = Complex.log (b : ℂ))
    (hL : ∀ t, Complex.exp (L t) = (γ t : ℂ))
    (hM : ∀ t, Complex.exp (M t) = (γ t : ℂ)) : L = M := by
  apply ContinuousMap.coe_injective
  apply (CoveringPaths.covering_bridge ModelCoverings.expProjection ModelCoverings.exponential_covering.2.1).eq_of_comp_eq
    L.continuous M.continuous _ 0 (hL₀.trans hM₀.symm)
  apply funext
  intro t
  exact Subtype.ext ((hL t).trans (hM t).symm)

lemma period_ne_zero : ModelCoverings.period ≠ 0 := by
  simp [ModelCoverings.period, Real.pi_ne_zero]

lemma winding_unique {r : ℝ} {b : Disk r} {γ : Path b b} {k l : ℤ}
    (hk : HasWinding γ k) (hl : HasWinding γ l) : k = l := by
  obtain ⟨L, hL₀, hL, hL₁⟩ := hk
  obtain ⟨M, hM₀, hM, hM₁⟩ := hl
  have heq := log_lift_unique hL₀ hM₀ hL hM
  have hc : (k : ℂ) * ModelCoverings.period = (l : ℂ) * ModelCoverings.period := by
    have := congrArg (fun f : C(I, ℂ) => f 1) heq
    rw [hL₁, hM₁] at this
    exact add_left_cancel this
  exact_mod_cast mul_right_cancel₀ period_ne_zero hc

theorem logarithmic_lift : Specs.D12Complex.Ch20.PuncturedDiskLoops.logarithmic_lift := by
  intro r _hr b γ
  obtain ⟨L, hL₀, hL⟩ := exists_log_lift b γ
  have hE : Complex.exp (L 1) = Complex.exp (Complex.log (b : ℂ)) := by
    rw [hL, γ.target, Complex.exp_log (norm_pos_iff.mp b.property.1)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE
  refine ⟨k, ⟨L, hL₀, hL, hk⟩, ?_⟩
  intro l hl
  exact winding_unique hl ⟨L, hL₀, hL, hk⟩

theorem argument_lift : Specs.D12Complex.Ch20.PuncturedDiskLoops.argument_lift := by
  intro r _hr b γ k hk
  obtain ⟨L, hL₀, hL, hL₁⟩ := hk
  refine ⟨⟨fun t => (L t).im, Complex.continuous_im.comp L.continuous⟩, ?_, ?_, ?_⟩
  · change (L 0).im = _
    rw [hL₀, Complex.log_im]
  · intro t
    change (γ t : ℂ) = (‖(γ t : ℂ)‖ : ℂ) * Complex.exp ((L t).im * Complex.I)
    rw [← hL t, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add,
      Complex.re_add_im]
  · change (L 1).im - (L 0).im = _
    rw [hL₀, hL₁]
    simp [ModelCoverings.period, mul_comm, mul_left_comm]

lemma exp_period (k : ℤ) : Complex.exp ((k : ℂ) * ModelCoverings.period) = 1 := by
  exact Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩

lemma circleValue_norm {r : ℝ} (b : Disk r) (k : ℤ) (t : I) :
    ‖circleValue b k t‖ = ‖(b : ℂ)‖ := by
  simp [circleValue, Complex.norm_exp, ModelCoverings.period]

/-- The explicit constant-modulus loop representing the integer `k`. -/
def circleLoop {r : ℝ} (b : Disk r) (k : ℤ) : Path b b where
  toFun t := ⟨circleValue b k t, by rw [circleValue_norm]; exact b.property⟩
  continuous_toFun := by dsimp [circleValue]; fun_prop
  source' := by apply Subtype.ext; simp [circleValue]
  target' := by apply Subtype.ext; simp [circleValue, exp_period]

/-- Straight line in the logarithmic plane above the standard loop. -/
def lineLog {r : ℝ} (b : Disk r) (k : ℤ) : C(I, ℂ) :=
  ⟨fun t => Complex.log (b : ℂ) + (t : ℝ) * (k : ℂ) * ModelCoverings.period,
    by fun_prop⟩

lemma exp_lineLog {r : ℝ} (b : Disk r) (k : ℤ) (t : I) :
    Complex.exp (lineLog b k t) = circleValue b k t := by
  simp [lineLog, circleValue, Complex.exp_add,
    Complex.exp_log (norm_pos_iff.mp b.property.1)]

lemma circleLoop_winding {r : ℝ} (b : Disk r) (k : ℤ) :
    HasWinding (circleLoop b k) k := by
  refine ⟨lineLog b k, ?_, exp_lineLog b k, ?_⟩ <;> simp [lineLog]

lemma re_lt_log_radius {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖Complex.exp z‖ < r) :
    z.re < Real.log r := by
  apply Real.exp_lt_exp.mp
  simpa only [← Complex.norm_exp, Real.exp_log hr] using hz

lemma affine_exp_mem {r : ℝ} (hr : 0 < r) (z w : ℂ)
    (hz : ‖Complex.exp z‖ < r) (hw : ‖Complex.exp w‖ < r) (s : I) :
    0 < ‖Complex.exp ((1 - (s : ℝ) : ℂ) * z + (s : ℝ) * w)‖ ∧
      ‖Complex.exp ((1 - (s : ℝ) : ℂ) * z + (s : ℝ) * w)‖ < r := by
  refine ⟨norm_pos_iff.mpr (Complex.exp_ne_zero _), ?_⟩
  have hz' := re_lt_log_radius hr hz
  have hw' := re_lt_log_radius hr hw
  rw [Complex.norm_exp, ← Real.exp_log hr, Real.exp_lt_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  have hs₀ := s.property.1
  have hs₁ := s.property.2
  have hm : max z.re w.re < Real.log r := max_lt hz' hw'
  have h₁ := mul_nonneg (sub_nonneg.mpr hs₁) (sub_nonneg.mpr (le_max_left z.re w.re))
  have h₂ := mul_nonneg hs₀ (sub_nonneg.mpr (le_max_right z.re w.re))
  nlinarith

/-- Interpolating logarithmic lifts stays in the half-plane lying above the
disk. Exponentiation therefore gives a homotopy with both endpoints fixed. -/
theorem normal_form : Specs.D12Complex.Ch20.PuncturedDiskLoops.normal_form := by
  intro r hr b γ k hk
  obtain ⟨L, hL₀, hL, hL₁⟩ := hk
  refine ⟨circleLoop b k, fun _ => rfl, ⟨?_⟩⟩
  refine {
    toFun := fun p => ⟨Complex.exp
      ((1 - (p.1 : ℝ) : ℂ) * L p.2 + (p.1 : ℝ) * lineLog b k p.2), ?_⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · apply affine_exp_mem hr
    · rw [hL]; exact (γ _).property.2
    · rw [exp_lineLog, circleValue_norm]; exact b.property.2
  · fun_prop
  · intro t
    apply Subtype.ext
    simpa using hL t
  · intro t
    apply Subtype.ext
    simpa [circleLoop] using exp_lineLog b k t
  · intro s t ht
    rcases ht with ht | ht
    · subst t
      apply Subtype.ext
      change Complex.exp _ = (γ 0 : ℂ)
      rw [hL₀]
      simp [lineLog, ← add_mul, Complex.exp_log (norm_pos_iff.mp b.property.1)]
    · have ht' : t = 1 := ht
      subst t
      apply Subtype.ext
      change Complex.exp _ = (γ 1 : ℂ)
      rw [hL₁]
      simp [lineLog, ← add_mul, Complex.exp_add, exp_period,
        Complex.exp_log (norm_pos_iff.mp b.property.1)]

/-- A based homotopy preserves the endpoint of the normalized exponential lift. -/
lemma winding_eq_of_homotopic {r : ℝ} {b : Disk r} {γ δ : Path b b}
    {k l : ℤ} (hk : HasWinding γ k) (hl : HasWinding δ l)
    (h : γ.Homotopic δ) : k = l := by
  obtain ⟨L, hL₀, hL, hL₁⟩ := hk
  obtain ⟨M, hM₀, hM, hM₁⟩ := hl
  let cov := CoveringPaths.covering_bridge ModelCoverings.expProjection
    ModelCoverings.exponential_covering.2.1
  have hmap := h.map ⟨puncturedInclusion, continuous_puncturedInclusion⟩
  have hpL : (ContinuousMap.comp ⟨ModelCoverings.expProjection, cov.continuous⟩ L) =
      (γ.map continuous_puncturedInclusion).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact Subtype.ext (hL t)
  have hpM : (ContinuousMap.comp ⟨ModelCoverings.expProjection, cov.continuous⟩ M) =
      (δ.map continuous_puncturedInclusion).toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact Subtype.ext (hM t)
  have hLM : L.HomotopicRel M {0, 1} := by
    apply (cov.homotopicRel_iff_comp (A := I) (f₀ := L) (f₁ := M) (S := {0, 1})
      ⟨0, Or.inl rfl, hL₀.trans hM₀.symm⟩).mpr
    rw [hpL, hpM]
    exact hmap
  obtain ⟨H⟩ := hLM
  have hend : L 1 = M 1 :=
    (H.eq_fst 0 (Or.inr rfl)).symm.trans (H.eq_snd 0 (Or.inr rfl))
  rw [hL₁, hM₁] at hend
  have hc := mul_right_cancel₀ period_ne_zero (add_left_cancel hend)
  exact_mod_cast hc

theorem classification : Specs.D12Complex.Ch20.PuncturedDiskLoops.classification := by
  intro r hr b γ δ k l hk hl
  refine ⟨winding_eq_of_homotopic hk hl, ?_⟩
  intro hkl
  subst l
  obtain ⟨η, hη, hγη⟩ := normal_form hr b γ k hk
  obtain ⟨ξ, hξ, hδξ⟩ := normal_form hr b δ k hl
  have heq : η = ξ := by
    apply Path.ext
    apply funext
    intro t
    exact Subtype.ext ((hη t).trans (hξ t).symm)
  exact hγη.trans (heq ▸ hδξ.symm)

/-- Smooth real-parameter representative of the canonical loop. -/
def circleReal {r : ℝ} (b : Disk r) (k : ℤ) (t : ℝ) : ℂ :=
  (b : ℂ) * Complex.exp ((t : ℂ) * k * ModelCoverings.period)

lemma circleReal_ne_zero {r : ℝ} (b : Disk r) (k : ℤ) (t : ℝ) :
    circleReal b k t ≠ 0 :=
  mul_ne_zero (norm_pos_iff.mp b.property.1) (Complex.exp_ne_zero _)

lemma circleReal_hasDerivAt {r : ℝ} (b : Disk r) (k : ℤ) (t : ℝ) :
    HasDerivAt (circleReal b k)
      (circleReal b k t * ((k : ℂ) * ModelCoverings.period)) t := by
  change HasDerivAt (fun u : ℝ => (b : ℂ) * Complex.exp ((u : ℂ) * k * ModelCoverings.period))
    (((b : ℂ) * Complex.exp ((t : ℂ) * k * ModelCoverings.period)) *
      ((k : ℂ) * ModelCoverings.period)) t
  have h := (((Complex.hasDerivAt_exp ((t : ℂ) * k * ModelCoverings.period)).comp
    (t : ℂ) (((hasDerivAt_id (t : ℂ)).mul_const (k : ℂ)).mul_const
      ModelCoverings.period)).const_mul (b : ℂ)).comp_ofReal
  simpa only [circleReal, Function.comp_def, id_eq, one_mul, mul_assoc] using h

lemma circleReal_smooth {r : ℝ} (b : Disk r) (k : ℤ) :
    ContDiff ℝ 1 (circleReal b k) := by
  change ContDiff ℝ 1 (fun t : ℝ => (b : ℂ) * Complex.exp ((t : ℂ) * k * ModelCoverings.period))
  have hcoe : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((hcoe.mul contDiff_const).mul contDiff_const).cexp

def circleContour {r : ℝ} (b : Disk r) (k : ℤ) : PiecewiseC1Path :=
  ⟨⟨0, 1, zero_le_one, circleReal b k, (circleReal_smooth b k).continuous.continuousOn⟩,
    isPiecewiseC1_of_contDiffOn _ (circleReal_smooth b k).contDiffOn⟩

lemma circleContour_avoids {r : ℝ} (b : Disk r) (k : ℤ) :
    0 ∉ (circleContour b k).trace := by
  rintro ⟨t, _ht, heq⟩
  exact circleReal_ne_zero b k t heq

lemma circleContour_closed {r : ℝ} (b : Disk r) (k : ℤ) :
    (circleContour b k).IsClosed := by
  change circleReal b k 1 = circleReal b k 0
  simp [circleReal, exp_period]

lemma circleContour_index {r : ℝ} (b : Disk r) (k : ℤ) :
    (circleContour b k).index 0 = (k : ℂ) := by
  have hf : ContinuousOn (fun z : ℂ => 1 / (z - 0)) (circleContour b k).trace := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro z hz
    exact sub_ne_zero.mpr (fun heq : z = 0 => circleContour_avoids b k (heq ▸ hz))
  rw [IndexOperationsHomotopy.path_index_eq_integral _ _ (circleContour_avoids b k)]
  change ModelCoverings.period⁻¹ * (circleContour b k).partition.integral _ = _
  rw [C1Partition.integral_eq_intervalIntegral _ _ _ hf]
  change ModelCoverings.period⁻¹ *
    (∫ t in (0 : ℝ)..1, (1 / (circleReal b k t - 0)) * deriv (circleReal b k) t) = _
  have hint : (∫ t in (0 : ℝ)..1,
      (1 / (circleReal b k t - 0)) * deriv (circleReal b k) t) =
        (k : ℂ) * ModelCoverings.period := by
    have heq : (fun t : ℝ => (1 / (circleReal b k t - 0)) * deriv (circleReal b k) t) =
        fun _ => (k : ℂ) * ModelCoverings.period := by
      funext t
      rw [(circleReal_hasDerivAt b k t).deriv, sub_zero]
      field_simp [circleReal_ne_zero b k t]
    rw [heq]
    simp
  rw [hint]
  field_simp [period_ne_zero]

lemma interval_normalization_surjective {a d : ℝ} (had : a ≤ d) {u : ℝ}
    (hu : u ∈ Set.Icc a d) : ∃ t : I, a + (d - a) * (t : ℝ) = u := by
  by_cases heq : a = d
  · refine ⟨0, ?_⟩
    simpa using le_antisymm hu.1 (heq ▸ hu.2)
  · have hd : 0 < d - a := sub_pos.mpr (lt_of_le_of_ne had heq)
    refine ⟨⟨(u - a) / (d - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hu.1) hd.le
    · rw [div_le_one hd]
      linarith [hu.2]
    · dsimp
      field_simp
      ring

/-- The integral-based index equals the integer of the continuous exponential
lift. The comparison uses a continuous homotopy; intermediate paths need not
be rectifiable. -/
theorem integral_index : Specs.D12Complex.Ch20.PuncturedDiskLoops.integral_index := by
  intro r hr b γ c k hc hk
  have hc₀ : c c.path.a = (b : ℂ) := by
    have := hc 0
    simpa using this.symm
  have hc₁ : c c.path.b = (b : ℂ) := by
    have := hc 1
    simpa using this.symm
  have hclosed : c.IsClosed := hc₁.trans hc₀.symm
  have hzero : 0 ∉ c.trace := by
    rintro ⟨u, hu, heq⟩
    obtain ⟨t, ht⟩ := interval_normalization_surjective c.path.ordered hu
    have hn := norm_pos_iff.mp (γ t).property.1
    apply hn
    rw [hc, ht, heq]
  obtain ⟨η, hη, ⟨H⟩⟩ := normal_form hr b γ k hk
  let Hc : C(I × I, ℂ) := ⟨fun p => (H p : ℂ), continuous_subtype_val.comp H.continuous⟩
  have heq : c.index 0 = (circleContour b k).index 0 := by
    apply IndexOperationsHomotopy.free_loop_index c (circleContour b k) 0 hzero
      (circleContour_avoids b k) hclosed (circleContour_closed b k) Hc
    · intro p
      exact norm_pos_iff.mp (H p).property.1
    · intro t
      change (H (0, t) : ℂ) = _
      rw [H.apply_zero]
      exact hc t
    · intro t
      change (H (1, t) : ℂ) = circleReal b k (0 + (1 - 0) * (t : ℝ))
      rw [H.apply_one]
      change (η t : ℂ) = _
      rw [hη]
      simp [circleValue, circleReal]
    · intro s
      change (H (s, 0) : ℂ) = (H (s, 1) : ℂ)
      rw [H.source, H.target]
  exact heq.trans (circleContour_index b k)

lemma winding_refl {r : ℝ} (b : Disk r) : HasWinding (Path.refl b) 0 := by
  refine ⟨ContinuousMap.const I (Complex.log (b : ℂ)), rfl, ?_, ?_⟩
  · intro t
    exact Complex.exp_log (norm_pos_iff.mp b.property.1)
  · simp

/-- Winding is additive for concatenation, with the first path traversed first. -/
lemma winding_trans {r : ℝ} {b : Disk r} {γ δ : Path b b} {k l : ℤ}
    (hk : HasWinding γ k) (hl : HasWinding δ l) :
    HasWinding (γ.trans δ) (k + l) := by
  obtain ⟨L, hL₀, hL, hL₁⟩ := hk
  obtain ⟨M, hM₀, hM, hM₁⟩ := hl
  let a := Complex.log (b : ℂ)
  let A : Path a (a + k * ModelCoverings.period) :=
    ⟨L, hL₀, hL₁⟩
  let B : Path (a + k * ModelCoverings.period) (a + (k + l : ℤ) * ModelCoverings.period) := {
    toFun := fun t => M t + k * ModelCoverings.period
    continuous_toFun := by fun_prop
    source' := by rw [hM₀]
    target' := by rw [hM₁]; push_cast; ring }
  refine ⟨(A.trans B).toContinuousMap, (A.trans B).source, ?_, (A.trans B).target⟩
  intro t
  change Complex.exp ((A.trans B) t) = ((γ.trans δ) t : ℂ)
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hL _
  · change Complex.exp (M _ + k * ModelCoverings.period) = _
    rw [Complex.exp_add, exp_period, mul_one, hM]

/-- The class of the standard loop. -/
def circleClass {r : ℝ} (b : Disk r) (k : ℤ) : FundamentalGroup (Disk r) b :=
  .of (.mk (circleLoop b k))

lemma circleClass_zero {r : ℝ} (hr : 0 < r) (b : Disk r) : circleClass b 0 = 1 := by
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk (circleLoop b 0) = .mk (Path.refl b)
  exact Quotient.sound ((classification hr b _ _ 0 0 (circleLoop_winding b 0)
    (winding_refl b)).mpr rfl)

lemma circleClass_add {r : ℝ} (hr : 0 < r) (b : Disk r) (k l : ℤ) :
    circleClass b (k + l) = circleClass b k * circleClass b l := by
  rw [FundamentalGroup.mul_def]
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk (circleLoop b (k + l)) =
    (Path.Homotopic.Quotient.mk (circleLoop b l)).trans (Path.Homotopic.Quotient.mk (circleLoop b k))
  rw [← Path.Homotopic.Quotient.mk_trans]
  exact Quotient.sound ((classification hr b _ _ (k + l) (l + k)
    (circleLoop_winding b (k + l))
    (winding_trans (circleLoop_winding b l) (circleLoop_winding b k))).mpr (add_comm k l))

def circleClassHom {r : ℝ} (hr : 0 < r) (b : Disk r) :
    Multiplicative ℤ →* FundamentalGroup (Disk r) b where
  toFun k := circleClass b k.toAdd
  map_one' := circleClass_zero hr b
  map_mul' k l := circleClass_add hr b k.toAdd l.toAdd

lemma circleClass_eq_zpow {r : ℝ} (hr : 0 < r) (b : Disk r) (k : ℤ) :
    circleClass b k = circleClass b 1 ^ k := by
  have h := (circleClassHom hr b).map_zpow (Multiplicative.ofAdd (1 : ℤ)) k
  simpa [circleClassHom, ← ofAdd_zsmul] using h

/-- Every fundamental-group element is an integral power of the positive loop. -/
lemma fundamentalGroup_generator {r : ℝ} (hr : 0 < r) (b : Disk r)
    (q : FundamentalGroup (Disk r) b) : ∃ k : ℤ, q = circleClass b 1 ^ k := by
  rcases q with ⟨q⟩
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  obtain ⟨k, hk, _⟩ := logarithmic_lift hr b γ
  refine ⟨k, ?_⟩
  rw [← circleClass_eq_zpow hr b k]
  apply CategoryTheory.End.ext
  change Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk (circleLoop b k)
  exact Quotient.sound ((classification hr b _ _ k k hk (circleLoop_winding b k)).mpr rfl)

/-- Actual endpoint lifting agrees with the standard monodromy permutation. -/
lemma monodromy_endpoint_iff {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) {b : B} (η : Path b b)
    (x y : p ⁻¹' {b}) :
    cov.monodromyPerm b (.of (.mk η)) x = y ↔ LiftEndpoint p η x y := by
  constructor
  · intro hxy
    let L := cov.liftPath η x (η.source.trans x.property.symm)
    have h₀ : L 0 = (x : E) := cov.liftPath_zero _ _ _
    have h₁ : L 1 = (y : E) := congrArg Subtype.val hxy
    refine ⟨⟨L, h₀, h₁⟩, fun t => ?_⟩
    exact congrFun (cov.liftPath_lifts η x (η.source.trans x.property.symm)) t
  · rintro ⟨Γ, hΓ⟩
    apply Subtype.ext
    exact (cov.monodromy_eq_apply_one (funext hΓ) Γ.source).trans Γ.target

/-- Connectedness of the surface makes the covering monodromy transitive.
Loop classification reduces this full action to powers of one permutation. -/
lemma generator_transitive {r : ℝ} (hr : 0 < r) {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] {p : E → Disk r} (cov : IsCoveringMap p) (b : Disk r) :
    ∀ x y : p ⁻¹' {b}, ∃ k : ℤ,
      (cov.monodromyPerm b (circleClass b 1) ^ k) x = y := by
  intro x y
  let Γ : Path (x : E) (y : E) := PathConnectedSpace.somePath (x : E) (y : E)
  let η : Path b b := (Γ.map cov.continuous).cast x.property.symm y.property.symm
  have hη : LiftEndpoint p η x y := ⟨Γ, fun _ => rfl⟩
  have hxy := (monodromy_endpoint_iff cov η x y).mpr hη
  obtain ⟨k, hk⟩ := fundamentalGroup_generator hr b (.of (.mk η))
  refine ⟨k, ?_⟩
  rw [← map_zpow, ← hk]
  exact hxy

/-- A transitive permutation of a finite set is one full cycle. This version
includes a singleton, where the cycle is the identity. -/
lemma full_cycle_of_transitive {A : Type*} [Fintype A] (τ : Equiv.Perm A)
    (hτ : ∀ x y, ∃ k : ℤ, (τ ^ k) x = y) :
    τ ^ Fintype.card A = 1 ∧
      ∀ x, Function.Bijective (fun i : Fin (Fintype.card A) => (τ ^ i.val) x) := by
  classical
  have hcycle : τ.IsCycleOn (Finset.univ : Finset A) :=
    ⟨by simp, fun x _hx y _hy => hτ x y⟩
  constructor
  · apply Equiv.ext
    intro x
    simpa using hcycle.pow_card_apply (Finset.mem_univ x)
  · intro x
    constructor
    · intro i j hij
      apply Fin.ext
      exact hcycle.injOn_pow_apply (Finset.mem_univ x) (by simp)
        (by simp) hij
    · intro y
      obtain ⟨n, hn, hny⟩ := hcycle.exists_pow_eq (Finset.mem_univ x) (Finset.mem_univ y)
      exact ⟨⟨n, by simpa using hn⟩, hny⟩

theorem cyclic_monodromy : Specs.D12Complex.Ch20.PuncturedDiskLoops.cyclic_monodromy := by
  intro r hr E _ S p hp m hm hcard b η hη
  let : PathConnectedSpace E := Surfaces.surface_pathConnected S
  let cov := CoveringPaths.covering_bridge p hp
  have hfin : Finite (p ⁻¹' {b}) :=
    Nat.finite_of_card_ne_zero (by rw [hcard b]; exact hm.ne')
  let := hfin
  let := Fintype.ofFinite (p ⁻¹' {b})
  have hc : Fintype.card (p ⁻¹' {b}) = m := by
    simpa only [Nat.card_eq_fintype_card] using hcard b
  have hηclass : (CategoryTheory.End.of (Path.Homotopic.Quotient.mk η) :
      FundamentalGroup (Disk r) b) = circleClass b 1 := by
    apply CategoryTheory.End.ext
    exact Quotient.sound ((classification hr b η (circleLoop b 1) 1 1 hη
      (circleLoop_winding b 1)).mpr rfl)
  let τ := cov.monodromyPerm b (circleClass b 1)
  refine ⟨τ, ?_, ?_⟩
  · intro x y
    change cov.monodromyPerm b (circleClass b 1) x = y ↔ _
    rw [← hηclass]
    exact monodromy_endpoint_iff cov η x y
  · have hfull := full_cycle_of_transitive τ (generator_transitive hr cov b)
    exact hc ▸ hfull

/-- No loop-representation hypothesis is required of a piecewise C1 contour:
its affine unit-interval traversal always supplies one, even when a=b. -/
theorem contour_winding : Specs.D12Complex.Ch20.PuncturedDiskLoops.contour_winding := by
  intro r hr c hclosed htrace
  let b : Disk r := ⟨c c.path.a, htrace _ ⟨c.path.a, ⟨le_rfl, c.path.ordered⟩, rfl⟩⟩
  have htime (t : I) : c.path.a + (c.path.b - c.path.a) * (t : ℝ) ∈
      Set.Icc c.path.a c.path.b := by
    have hd : 0 ≤ c.path.b - c.path.a := sub_nonneg.mpr c.path.ordered
    have ht₀ := t.property.1
    have ht₁ := t.property.2
    constructor <;> nlinarith [mul_nonneg hd ht₀, mul_nonneg hd (sub_nonneg.mpr ht₁)]
  let γ : Path b b := {
    toFun := fun t => ⟨c (c.path.a + (c.path.b - c.path.a) * (t : ℝ)),
      htrace _ ⟨_, htime t, rfl⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact c.path.continuousOn.comp_continuous (by fun_prop) htime
    source' := by apply Subtype.ext; simp [b]
    target' := by
      apply Subtype.ext
      change c (c.path.a + (c.path.b - c.path.a) * ((1 : I) : ℝ)) = c c.path.a
      simpa using (show c c.path.b = c c.path.a from hclosed) }
  obtain ⟨k, hk, _⟩ := logarithmic_lift hr b γ
  exact ⟨b, γ, k, fun _ => rfl, hk, integral_index hr b γ c k (fun _ => rfl) hk⟩

end D12Complex.Ch20.PuncturedDiskLoops
