import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDivisibility
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyInnerOuter
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.Beurling

noncomputable section
open MeasureTheory Filter
open scoped Topology Real
namespace ExpandedFA.PartIV.HardyDivisibility
open BeurlingSpec BeurlingWanderingSpec
open HardyDiskSpec
open HardyDisk hiding H2 Circle BoundaryL2 disk Disk infinityNorm HInfinity eval boundary shift IsInner IsOuter nonnegativeFourier poissonExtension
open HardyLogModulus

lemma boundedVector_eval (b : HInfinity) (z : Disk) :
    eval (boundedVector b) z = b.val z := by
  have h := multiplierVector_eval b (lp.single 2 0 1) z.property
  have hone : eval (lp.single 2 0 (1 : ℂ)) z = 1 := by
    simpa only [pow_zero, mul_one] using monomial_evaluation 0 1 (z : ℂ)
  exact h.trans ((congrArg₂ (· * ·) (zeroExtend_apply b.val z) hone).trans (mul_one _))

lemma boundedVector_eval_on (b : HInfinity) (z : ℂ) (hz : z ∈ disk) :
    eval (boundedVector b) z = b.val ⟨z, hz⟩ := boundedVector_eval b ⟨z, hz⟩

/-- The exact exported multiplier acts by analytic multiplication. -/
theorem multiplier_eval : Spec.MultiplierEvaluation := by
  intro b f z
  exact (multiplierVector_eval b f z.property).trans (by rw [zeroExtend_apply])

lemma boundedVector_ne_zero {b : HInfinity} (hb : ¬IsZero b) : boundedVector b ≠ 0 := by
  intro h
  apply hb
  intro z
  rw [← boundedVector_eval, h]
  simp [HardyDiskSpec.eval]

lemma outer_ne_zero {f : H2} (hf : IsOuter f) : f ≠ 0 := by
  intro h
  have he : Submodule.span ℂ (Set.range (fun n : ℕ => (shift^[n]) (0 : H2))) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    have hz : (shift^[n]) (0 : H2) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]
    simp [hz]
  rw [h] at hf
  change (Submodule.span ℂ _).topologicalClosure = ⊤ at hf
  rw [he, (isClosed_singleton : IsClosed ({0} : Set H2)).submodule_topologicalClosure_eq] at hf
  have hmem : lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ) ∈ (⊥ : Submodule ℂ H2) := by
    rw [hf]
    trivial
  change lp.single 2 0 (1 : ℂ) = (0 : H2) at hmem
  have hz := congrArg (fun f : H2 => f 0) hmem
  simp [lp.single_apply] at hz

/-- Regard a bounded H² evaluation as a bounded holomorphic symbol. -/
def symbolOfVector (f : H2) (hb : ∃ C : ℝ, ∀ z ∈ disk, ‖eval f z‖ ≤ C) : HInfinity :=
  ⟨fun z => eval f z,
    (analytic_evaluation f).differentiableOn.congr (fun z hz => by
      simp [zeroExtend, hz]), by
        obtain ⟨C, hC⟩ := hb
        exact ⟨C, fun z => hC z z.property⟩⟩

lemma innerRange_closed (θ : H2) (hθ : IsInner θ) :
    IsClosed (ProductRange θ) := by
  rw [← Beurling.innerMul_range θ hθ]
  exact (Beurling.innerMul θ hθ).isometry.isUniformInducing.isComplete_range.isClosed

lemma innerRange_self (θ : H2) : θ ∈ ProductRange θ := by
  refine ⟨lp.single 2 0 1, ?_⟩
  intro z hz
  rw [monomial_evaluation]
  simp

lemma inner_ne_zero {θ : H2} (hθ : IsInner θ) : θ ≠ 0 := by
  intro h
  have hn := Beurling.inner_norm hθ
  simp [h] at hn

/-- Disk bounds pass to the genuine radial boundary values. -/
lemma boundary_bound_of_disk_bound {f : H2} {C : ℝ}
    (hf : ∀ z ∈ disk, ‖eval f z‖ ≤ C) :
    ∀ᵐ t ∂circleMeasure, ‖boundary f t‖ ≤ C := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hr0 (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    have := (div_le_one (by positivity : 0 < (n : ℝ) + 2)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 2)
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa [r] using tendsto_const_nhds.sub hinv
  obtain ⟨k, _, hk⟩ := exists_subseq_radial_ae f hr0 hr1 hrlim
  filter_upwards [hk] with t ht
  apply le_of_tendsto ht.norm
  exact Eventually.of_forall fun n => hf _ (radial_point_mem_disk (hr0 _) (hr1 _) t)

lemma boundedVector_boundary_bound (b : HInfinity) :
    ∀ᵐ t ∂circleMeasure, ‖boundary (boundedVector b) t‖ ≤ infinityNorm b := by
  apply boundary_bound_of_disk_bound
  intro z hz
  rw [boundedVector_eval b ⟨z, hz⟩]
  exact norm_le_infinityNorm b ⟨z, hz⟩

theorem commutant : Spec.Commutant := HardyCommutant.shift_commutant

theorem inner_criterion : Spec.InnerCriterion := by
  intro θ hθ b
  constructor
  · rintro ⟨q, hq⟩ h ⟨f, rfl⟩
    refine ⟨multiplier q f, ?_⟩
    intro z hz
    calc
      _ = b.val ⟨z, hz⟩ * eval f z := multiplier_eval b f ⟨z, hz⟩
      _ = eval θ z * (q.val ⟨z, hz⟩ * eval f z) := by rw [hq]; ring
      _ = _ := congrArg (eval θ z * ·) (multiplier_eval q f ⟨z, hz⟩).symm

  · intro h
    obtain ⟨f, hf⟩ := h (show boundedVector b ∈ multiplierRange b from
      ⟨lp.single 2 0 1, rfl⟩)
    have hprod : ∀ z ∈ disk, eval (boundedVector b) z = eval θ z * eval f z := hf
    have hbound : ∀ᵐ t ∂circleMeasure, ‖boundary f t‖ ≤ infinityNorm b := by
      have hb := boundedVector_boundary_bound b
      filter_upwards [boundary_mul_of_eval_mul hprod, hθ.2, hb] with t ht hθt hbt
      rw [ht, norm_mul, hθt, one_mul] at hbt
      exact hbt
    let q := symbolOfVector f ⟨infinityNorm b, fun z hz =>
      evaluation_norm_le_of_boundary_norm_le hbound hz⟩
    exact ⟨q, fun z => (boundedVector_eval b z).symm.trans (hf z z.property)⟩


lemma outer_formula_self {o : H2} (ho : IsOuter o) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn (eval o) (exponentialFactor (boundaryLog o) a) disk := by
  apply HardyInnerOuter.outer_formula o (lp.single 2 0 1) o (outer_ne_zero ho)
    HardyInnerOuter.inner_one ho
  intro z hz
  rw [monomial_evaluation]
  simp

lemma outer_eval_ne_zero {o : H2} (ho : IsOuter o) {z : ℂ} (hz : z ∈ disk) :
    eval o z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := outer_formula_self ho
  rw [he hz]
  apply exponential_nonzero _ a (by intro h; simp [h] at ha)

/-- Poisson majorization compared with the exact outer logarithmic modulus. -/
lemma outer_quotient_bound {f o : H2} (ho : IsOuter o) {C : ℝ} (hC : 0 < C)
    (hb : ∀ᵐ t ∂circleMeasure, ‖boundary f t / boundary o t‖ ≤ C) :
    ∀ z ∈ disk, ‖eval f z / eval o z‖ ≤ C := by
  have hon := outer_ne_zero ho
  obtain ⟨a, ha, hea⟩ := outer_formula_self ho
  have hlogO := (boundary_log_integrable o hon).1
  by_cases hfn : f = 0
  · intro z hz
    simp [hfn, HardyDiskSpec.eval, hC.le]
  have hlogF := (boundary_log_integrable f hfn).1
  have hlog : ∀ᵐ t ∂circleMeasure,
      boundaryLog f t ≤ Real.log C + boundaryLog o t := by
    filter_upwards [hb, (boundary_log_integrable f hfn).2,
      (boundary_log_integrable o hon).2] with t ht hft hot
    have hft' : 0 < ‖boundary f t‖ := norm_pos_iff.mpr hft
    have hot' : 0 < ‖boundary o t‖ := norm_pos_iff.mpr hot
    rw [norm_div] at ht
    have ht' := (div_le_iff₀ hot').mp ht
    have hl := Real.log_le_log hft' ht'
    rw [Real.log_mul hC.ne' hot'.ne'] at hl
    exact hl
  intro z hz
  have hP : Integrable (poissonWeight z) circleMeasure :=
    (continuous_poissonWeight hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmono : poissonLog (boundaryLog f) z ≤ Real.log C + poissonLog (boundaryLog o) z := by
    calc
      _ ≤ ∫ t, poissonWeight z t * (Real.log C + boundaryLog o t) ∂circleMeasure := by
        apply integral_mono_ae (integrable_poissonWeight_mul hlogF hz)
          (integrable_poissonWeight_mul ((integrable_const _).add hlogO) hz)
        filter_upwards [hlog] with t ht
        exact mul_le_mul_of_nonneg_left ht (poissonWeight_nonneg hz t)
      _ = _ := by
        simp_rw [mul_add]
        rw [integral_add (hP.mul_const _) (integrable_poissonWeight_mul hlogO hz),
          integral_mul_const, integral_poissonWeight hz, one_mul]
        rfl
  rw [norm_div, hea hz, exponential_norm _ hlogO a ha z hz]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  calc
    ‖eval f z‖ ≤ Real.exp (poissonLog (boundaryLog f) z) := exponential_majorization f hfn z hz
    _ ≤ Real.exp (Real.log C + poissonLog (boundaryLog o) z) := Real.exp_le_exp.mpr hmono
    _ = C * Real.exp (poissonLog (boundaryLog o) z) := by rw [Real.exp_add, Real.exp_log hC]

theorem outer_criterion : Spec.OuterCriterion := by
  intro O ho b
  constructor
  · rintro ⟨q, hq⟩
    have hprod : ∀ z ∈ disk, eval (boundedVector b) z =
        eval (boundedVector O) z * eval (boundedVector q) z := by
      intro z hz
      rw [boundedVector_eval_on b z hz, boundedVector_eval_on O z hz, boundedVector_eval_on q z hz]
      exact hq ⟨z, hz⟩
    refine ⟨infinityNorm q, ?_⟩
    filter_upwards [boundary_mul_of_eval_mul hprod,
      (boundary_log_integrable _ (outer_ne_zero ho)).2,
      boundedVector_boundary_bound q] with t ht hot hqt
    rw [ht, mul_div_cancel_left₀ _ hot]
    exact hqt
  · rintro ⟨C, hC⟩
    let D := max C 1
    have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_right C 1)
    have hbound := outer_quotient_bound ho hD
      (hC.mono fun t ht => ht.trans (le_max_left _ _))
    let F : ℂ → ℂ := fun z => eval (boundedVector b) z / eval (boundedVector O) z
    let q : HInfinity := ⟨fun z => F z,
      (((analytic_evaluation (boundedVector b)).differentiableOn.div (analytic_evaluation (boundedVector O)).differentiableOn
        (fun z hz => outer_eval_ne_zero ho hz)).congr (fun z hz => by simp [zeroExtend, hz, F])),
      ⟨D, fun z => hbound z z.property⟩⟩
    refine ⟨q, fun z => ?_⟩
    change b.val z = O.val z * (eval (boundedVector b) z / eval (boundedVector O) z)
    rw [boundedVector_eval, boundedVector_eval, mul_div_cancel₀]
    exact (boundedVector_eval O z).symm ▸ outer_eval_ne_zero ho z.property


lemma mem_multiplierRange (b : HInfinity) (h : H2) :
    h ∈ multiplierRange b ↔ ∃ f : H2, ∀ z : Disk, eval h z = b.val z * eval f z := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, multiplier_eval b f⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, evaluation_injective _ _ ?_⟩
    intro z hz
    exact (multiplier_eval b f ⟨z, hz⟩).trans (hf ⟨z, hz⟩).symm

lemma innerSymbol_range (θ : H2) (hθ : IsInner θ) :
    (multiplierRange (symbolOfVector θ hθ.1) : Set H2) = ProductRange θ := by
  ext h
  change h ∈ multiplierRange (symbolOfVector θ hθ.1) ↔ h ∈ ProductRange θ
  constructor
  · intro hh
    obtain ⟨f, hf⟩ := (mem_multiplierRange _ h).mp hh
    exact ⟨f, fun z hz => hf ⟨z, hz⟩⟩
  · rintro ⟨f, hf⟩
    exact (mem_multiplierRange _ h).mpr ⟨f, fun z => hf z z.property⟩

lemma inner_divides_inner_iff (θ η : H2) (hθ : IsInner θ) (hη : IsInner η) :
    InnerDividesInner θ η ↔ ProductRange η ⊆ ProductRange θ := by
  have h := inner_criterion θ hθ (symbolOfVector η hη.1)
  rw [innerSymbol_range η hη] at h
  exact h

lemma multiplierRange_invariant (b : HInfinity) : ShiftInvariant (multiplierRange b) := by
  rintro _ ⟨f, rfl⟩
  exact ⟨shift f, HardyCommutant.multiplier_commutes (multiplier b) b (multiplier_eval b) f⟩

lemma closedSum_invariant (b c : HInfinity) : ShiftInvariant (closedSum b c) := by
  let S := multiplierRange b ⊔ multiplierRange c
  have hS : S.map shift.toLinearMap ≤ S := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
    change shift (x + y) ∈ S
    rw [map_add]
    exact Submodule.add_mem_sup (multiplierRange_invariant b x hx)
      (multiplierRange_invariant c y hy)
  have hm := (S.topologicalClosure_map shift.toContinuousLinearMap).trans
    (Submodule.topologicalClosure_mono hS)
  intro g hg
  exact hm ⟨g, hg, rfl⟩

lemma closedSum_nonzero (b c : HInfinity) (h : ¬IsZero b ∨ ¬IsZero c) :
    closedSum b c ≠ ⊥ := by
  intro he
  have hzero : ∀ d : HInfinity, multiplierRange d ≤ closedSum b c → IsZero d := by
    intro d hd
    have hm : boundedVector d ∈ closedSum b c := hd ⟨lp.single 2 0 1, rfl⟩
    rw [he] at hm
    change boundedVector d = 0 at hm
    intro z
    rw [← boundedVector_eval d z, hm]
    simp [HardyDiskSpec.eval]
  cases h with
  | inl hb => exact hb (hzero b ((show multiplierRange b ≤ multiplierRange b ⊔ multiplierRange c from le_sup_left).trans (Submodule.le_topologicalClosure _)))
  | inr hc => exact hc (hzero c ((show multiplierRange c ≤ multiplierRange b ⊔ multiplierRange c from le_sup_right).trans (Submodule.le_topologicalClosure _)))

lemma common_divisor_closedSum_le (b c : HInfinity) (θ : H2) (hθ : IsInner θ)
    (hb : InnerDivides θ b) (hc : InnerDivides θ c) :
    (closedSum b c : Set H2) ⊆ ProductRange θ := by
  let R := LinearMap.range (Beurling.innerMul θ hθ).toLinearMap
  have hR : (R : Set H2) = ProductRange θ := Beurling.innerMul_range θ hθ
  have hb' : multiplierRange b ≤ R := by
    intro f hf
    change f ∈ (R : Set H2)
    rw [hR]
    exact (inner_criterion θ hθ b).mp hb hf
  have hc' : multiplierRange c ≤ R := by
    intro f hf
    change f ∈ (R : Set H2)
    rw [hR]
    exact (inner_criterion θ hθ c).mp hc hf
  have hle : closedSum b c ≤ R := Submodule.topologicalClosure_minimal _
    (sup_le hb' hc') ((hR ▸ innerRange_closed θ hθ) : IsClosed (R : Set H2))
  intro f hf
  rw [← hR]
  exact hle hf

theorem greatest_common_divisor : Spec.GreatestCommonDivisor := by
  intro b c hbc
  obtain ⟨θ, hθ, hM⟩ := Beurling.classification (closedSum b c)
    (Submodule.isClosed_topologicalClosure _) (closedSum_nonzero b c hbc)
    (closedSum_invariant b c)
  have hb : InnerDivides θ b := (inner_criterion θ hθ b).mpr (by
    intro f hf
    rw [← hM]
    exact (Submodule.le_topologicalClosure _) (Submodule.mem_sup_left hf))
  have hc : InnerDivides θ c := (inner_criterion θ hθ c).mpr (by
    intro f hf
    rw [← hM]
    exact (Submodule.le_topologicalClosure _) (Submodule.mem_sup_right hf))
  refine ⟨θ, ⟨hθ, hb, hc, ?_⟩, hM⟩
  intro η hη hbη hcη
  apply (inner_divides_inner_iff η θ hη hθ).mpr
  rw [← hM]
  exact common_divisor_closedSum_le b c η hη hbη hcη

/-- Shifting an inner function gives another inner function. -/
lemma shift_inner {θ : H2} (hθ : IsInner θ) : IsInner (shift θ) := by
  refine ⟨⟨1, ?_⟩, ?_⟩
  · intro z hz
    rw [shift_evaluation θ z hz, norm_mul]
    calc
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left (HardyInnerOuter.inner_bound hθ hz) (norm_nonneg _)
      _ ≤ 1 := by simpa using (show ‖z‖ < 1 from by simpa [disk] using hz).le
  · have hb := BeurlingWandering.modulation_coe 1 (boundary θ)
    rw [← BeurlingWandering.boundary_shift] at hb
    filter_upwards [hb, hθ.2] with t ht hθt
    rw [ht, norm_mul, norm_fourier_point, hθt, mul_one]

/-- The generator is orthogonal to its shifted product subspace. -/
lemma shift_not_divides {θ : H2} (hθ : IsInner θ) :
    ¬InnerDividesInner (shift θ) θ := by
  rintro ⟨q, hq⟩
  let R := LinearMap.range (Beurling.innerMul θ hθ).toLinearMap
  let g := Beurling.innerMul θ hθ (boundedVector q)
  have hg : g ∈ R := ⟨boundedVector q, rfl⟩
  have he : shift g = θ := by
    apply evaluation_injective
    intro z hz
    rw [shift_evaluation g z hz]
    change z * eval (Beurling.innerMul θ hθ (boundedVector q)) z = eval θ z
    have hgval := Beurling.innerMul_evaluation θ hθ (boundedVector q) z hz
    change eval (Beurling.innerMul θ hθ (boundedVector q)) z = eval θ z * eval (boundedVector q) z at hgval
    rw [hgval, boundedVector_eval_on q z hz]
    have h := hq ⟨z, hz⟩
    rw [shift_evaluation θ z hz] at h
    exact (mul_assoc _ _ _).symm.trans h.symm
  have hw := Beurling.generator_wandering θ hθ
  have horth : inner ℂ θ θ = 0 := hw.2 θ ⟨g, hg, he⟩
  exact inner_ne_zero hθ (inner_self_eq_zero.mp horth)

def zeroSymbol : HInfinity := symbolOfVector 0 ⟨0, by simp [HardyDiskSpec.eval]⟩

lemma inner_divides_zero (θ : H2) (b : HInfinity) (hb : IsZero b) : InnerDivides θ b := by
  refine ⟨zeroSymbol, fun z => ?_⟩
  rw [hb z]
  simp [zeroSymbol, symbolOfVector, HardyDiskSpec.eval]

lemma no_gcd_zero_pair (b c : HInfinity) (hb : IsZero b) (hc : IsZero c) :
    ¬∃ θ : H2, IsGreatestCommonInnerDivisor b c θ := by
  rintro ⟨θ, hθ, _, _, hgreat⟩
  exact shift_not_divides hθ (hgreat (shift θ) (shift_inner hθ)
    (inner_divides_zero _ b hb) (inner_divides_zero _ c hc))

lemma multiplierRange_zero (b : HInfinity) (hb : IsZero b) : multiplierRange b = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨f, rfl⟩
  change multiplier b f = 0
  apply evaluation_injective
  intro z hz
  rw [multiplier_eval b f ⟨z, hz⟩, hb]
  simp [HardyDiskSpec.eval]

theorem zero_pair : Spec.ZeroPair := by
  intro b c hb hc
  have hs : closedSum b c = ⊥ := by
    unfold closedSum
    rw [multiplierRange_zero b hb, multiplierRange_zero c hc, sup_idem,
      (isClosed_singleton : IsClosed ({0} : Set H2)).submodule_topologicalClosure_eq]
  refine ⟨hs, ?_, no_gcd_zero_pair b c hb hc⟩
  rintro ⟨θ, hθ, hgen⟩
  have hm := innerRange_self θ
  rw [← hgen, hs] at hm
  exact inner_ne_zero hθ hm

theorem generator_characterization : Spec.GeneratorCharacterization := by
  intro b c θ hθ
  have hbc : ¬IsZero b ∨ ¬IsZero c := by
    by_contra h
    have hh : IsZero b ∧ IsZero c := by simpa only [not_or, not_not] using h
    exact no_gcd_zero_pair b c hh.1 hh.2 ⟨θ, hθ⟩
  obtain ⟨η, hη, hgen⟩ := greatest_common_divisor b c hbc
  apply Set.Subset.antisymm
  · exact common_divisor_closedSum_le b c θ hθ.1 hθ.2.1 hθ.2.2.1
  · rw [hgen]
    exact (inner_divides_inner_iff η θ hη.1 hθ.1).mp
      (hθ.2.2.2 η hη.1 hη.2.1 hη.2.2.1)

theorem uniqueness : Spec.Uniqueness := by
  intro b c θ η hθ hη
  exact Beurling.uniqueness θ η hθ.1 hη.1
    ((generator_characterization b c θ hθ).symm.trans
      (generator_characterization b c η hη))

end ExpandedFA.PartIV.HardyDivisibility
