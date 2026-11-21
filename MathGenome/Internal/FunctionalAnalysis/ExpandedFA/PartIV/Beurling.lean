import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.Beurling
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.BeurlingWandering

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal NNReal Topology ComplexConjugate
namespace ExpandedFA.PartIV.Beurling
open HardyDisk BeurlingWanderingSpec BeurlingWandering BeurlingSpec

/-- Boundary modulus one makes all shifted copies orthonormal. -/
theorem inner_shifts_orthonormal {θ : H2} (hθ : IsInner θ) :
    Orthonormal ℂ (fun n : ℕ => (shift^[n]) θ) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi := (orthonormal_iff_ite.mp HardyDiskSpec.modes_orthonormal) i j
  change inner ℂ (fourierLp (T := 2 * π) 2 (i : ℤ))
    (fourierLp (T := 2 * π) 2 (j : ℤ)) = _ at hi
  rw [← boundary.inner_map_map, L2.inner_def, ← hi, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundary_iterate_coe i θ, boundary_iterate_coe j θ,
    coeFn_fourierLp (T := 2 * π) 2 (i : ℤ),
    coeFn_fourierLp (T := 2 * π) 2 (j : ℤ), hθ.2] with t hi hj hmi hmj ht
  rw [hi, hj, hmi, hmj]
  simp only [RCLike.inner_apply', map_mul]
  have hu : conj (boundary θ t) * boundary θ t = 1 := by
    simp [RCLike.conj_mul, ht]
  calc
    _ = (conj (fourier (T := 2 * π) (i : ℤ) t) *
      fourier (T := 2 * π) (j : ℤ) t) * (conj (boundary θ t) * boundary θ t) := by ring
    _ = _ := by rw [hu, mul_one]

/-- Fourier synthesis in the orthonormal family of shifted inner vectors. -/
def innerMul (θ : H2) (hθ : IsInner θ) : H2 →ₗᵢ[ℂ] H2 :=
  (inner_shifts_orthonormal hθ).orthogonalFamily.linearIsometry

theorem innerMul_single (θ : H2) (hθ : IsInner θ) (n : ℕ) (c : ℂ) :
    innerMul θ hθ (lp.single 2 n c) = c • (shift^[n]) θ := by
  exact (inner_shifts_orthonormal hθ).orthogonalFamily.linearIsometry_apply_single c

theorem innerMul_series (θ : H2) (hθ : IsInner θ) (f : H2) :
    HasSum (fun n : ℕ => f n • (shift^[n]) θ) (innerMul θ hθ f) :=
  (inner_shifts_orthonormal hθ).orthogonalFamily.hasSum_linearIsometry f

theorem iterate_evaluation (n : ℕ) (f : H2) (z : ℂ) (hz : z ∈ disk) :
    eval ((shift^[n]) f) z = z ^ n * eval f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change HardyDiskSpec.eval (HardyDiskSpec.shift _) z = _
    rw [shift_evaluation _ _ hz]
    change z * eval ((shift^[n]) f) z = _
    rw [ih, pow_succ]
    ring

theorem innerMul_evaluation (θ : H2) (hθ : IsInner θ) (f : H2)
    (z : ℂ) (hz : z ∈ disk) :
    eval (innerMul θ hθ f) z = eval θ z * eval f z := by
  have hs := (evaluationMap ⟨z, hz⟩).hasSum (innerMul_series θ hθ f)
  have ht := (evaluation_hasSum f z hz).mul_left (eval θ z)
  apply hs.unique
  convert ht using 1
  ext n
  change eval (f n • (shift^[n]) θ) z = _
  rw [evaluation_smul, iterate_evaluation _ _ _ hz]
  ring

theorem innerMul_range (θ : H2) (hθ : IsInner θ) :
    Set.range (innerMul θ hθ) = ProductRange θ := by
  ext h
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, innerMul_evaluation θ hθ f⟩
  · rintro ⟨f, hf⟩
    refine ⟨f, evaluation_injective _ _ ?_⟩
    intro z hz
    exact (innerMul_evaluation θ hθ f z hz).trans (hf z hz).symm

theorem inner_isometry : InnerIsometry := by
  intro θ hθ
  exact ⟨innerMul θ hθ, innerMul_evaluation θ hθ, innerMul_range θ hθ,
    (innerMul θ hθ).isometry.isUniformInducing.isComplete_range.isClosed⟩

/-- Orthogonality to the product range can be tested on shifted generators. -/
theorem innerMul_orthogonal_iff (θ : H2) (hθ : IsInner θ) (f : H2) :
    f ∈ (LinearMap.range (innerMul θ hθ).toLinearMap)ᗮ ↔
      ∀ n : ℕ, inner ℂ ((shift^[n]) θ) f = 0 := by
  constructor
  · intro hf n
    apply hf _
    refine ⟨lp.single 2 n 1, ?_⟩
    simp only [LinearIsometry.coe_toLinearMap, innerMul_single, one_smul]
  · intro hf g hg
    obtain ⟨a, rfl⟩ := hg
    apply inner_eq_zero_symm.mpr
    have hs := (innerSL ℂ f).hasSum (innerMul_series θ hθ a)
    have hz : ∀ n : ℕ, inner ℂ f (a n • (shift^[n]) θ) = 0 := by
      intro n
      rw [inner_smul_right, inner_eq_zero_symm.mpr (hf n), mul_zero]
    exact hs.unique (by simpa only [innerSL_apply_apply, hz] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0))

/-- A closed invariant subspace contains every convergent shifted-generator series. -/
theorem innerMul_range_le {M : Submodule ℂ H2} (hclosed : IsClosed (M : Set H2))
    (hM : ShiftInvariant M) {θ : H2} (hθ : IsInner θ) (hθM : θ ∈ M) :
    LinearMap.range (innerMul θ hθ).toLinearMap ≤ M := by
  rintro _ ⟨f, rfl⟩
  apply hclosed.mem_of_tendsto (innerMul_series θ hθ f)
  exact Eventually.of_forall fun s => M.sum_mem (fun n _ => M.smul_mem _ (iterate_mem hM hθM n))

/-- The residual space has a surjective shift. The coefficient shift has no
nonzero subspace with this property. This is the pure-isometry part of Wold's argument. -/
theorem residual_eq_bot {M : Submodule ℂ H2} (hclosed : IsClosed (M : Set H2))
    (hne : M ≠ ⊥) (hM : ShiftInvariant M) {θ : H2}
    (hθW : θ ∈ wandering M) (hnorm : ‖θ‖ = 1) :
    M ⊓ (LinearMap.range (innerMul θ (wandering_inner M hclosed hne hM θ hθW hnorm)).toLinearMap)ᗮ = ⊥ := by
  let hθ := wandering_inner M hclosed hne hM θ hθW hnorm
  let R := LinearMap.range (innerMul θ hθ).toLinearMap
  let N := M ⊓ Rᗮ
  have memN (f : H2) : f ∈ N ↔ f ∈ M ∧ ∀ n : ℕ, inner ℂ ((shift^[n]) θ) f = 0 := by
    exact and_congr_right (fun _ => innerMul_orthogonal_iff θ hθ f)
  have hforward : ShiftInvariant N := by
    intro f hf
    obtain ⟨hfM, hfθ⟩ := (memN f).mp hf
    apply (memN (shift f)).mpr
    refine ⟨hM f hfM, ?_⟩
    intro n
    cases n with
    | zero =>
      simp only [Function.iterate_zero_apply]
      exact inner_eq_zero_symm.mp (hθW.2 _ ⟨f, hfM, rfl⟩)
    | succ n =>
      rw [Function.iterate_succ_apply', shift.inner_map_map]
      exact hfθ n
  have hbackward : N ≤ shiftRange N := by
    intro f hf
    obtain ⟨hfM, hfθ⟩ := (memN f).mp hf
    let : CompleteSpace (shiftRange M) := (shift_closed M hclosed).completeSpace_coe
    have hdecomp := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (shiftRange_le hM)
    obtain ⟨v, hv, w, hw, he⟩ := (Submodule.mem_sup.mp (show f ∈
        shiftRange M ⊔ (shiftRange M)ᗮ ⊓ M by rwa [hdecomp]))
    have hwW : w ∈ wandering M := ⟨hw.2, hw.1⟩
    have hwzero : w = 0 := by
      have hwc := wandering_eq_smul hclosed hne hM hθW hnorm hwW
      have hvθ : inner ℂ θ v = 0 := inner_eq_zero_symm.mp (hθW.2 _ hv)
      have hfw : inner ℂ θ w = 0 := by
        have hh := hfθ 0
        simp only [Function.iterate_zero_apply] at hh
        rw [← he, inner_add_right, hvθ, zero_add] at hh
        exact hh
      rw [hfw, zero_smul] at hwc
      exact hwc
    have hvf : v = f := by simpa only [hwzero, add_zero] using he
    obtain ⟨g, hg, hgv⟩ := hv
    have hgf : shift g = f := hgv.trans hvf
    refine ⟨g, (memN g).mpr ⟨hg, ?_⟩, hgf⟩
    intro n
    have hh := hfθ (n + 1)
    rw [← hgf, Function.iterate_succ_apply', shift.inner_map_map] at hh
    exact hh
  exact eq_bot_of_shiftRange_eq (le_antisymm (shiftRange_le hforward) hbackward)

/-- The wandering generator exhausts the whole invariant subspace. -/
theorem wandering_range {M : Submodule ℂ H2} (hclosed : IsClosed (M : Set H2))
    (hne : M ≠ ⊥) (hM : ShiftInvariant M) {θ : H2}
    (hθW : θ ∈ wandering M) (hnorm : ‖θ‖ = 1) :
    LinearMap.range (innerMul θ (wandering_inner M hclosed hne hM θ hθW hnorm)).toLinearMap = M := by
  let hθ := wandering_inner M hclosed hne hM θ hθW hnorm
  let R := LinearMap.range (innerMul θ hθ).toLinearMap
  have hle : R ≤ M := innerMul_range_le hclosed hM hθ hθW.1
  let : CompleteSpace R := (innerMul θ hθ).isometry.isUniformInducing.isComplete_range.completeSpace_coe
  have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  have hz : Rᗮ ⊓ M = ⊥ := by
    rw [inf_comm]
    exact residual_eq_bot hclosed hne hM hθW hnorm
  rw [hz, sup_bot_eq] at h
  exact h

theorem classification : Classification := by
  intro M hclosed hne hM
  obtain ⟨θ, hθW, hnorm⟩ := wandering_unit M hclosed hne hM
  let hθ := wandering_inner M hclosed hne hM θ hθW hnorm
  refine ⟨θ, hθ, ?_⟩
  rw [← innerMul_range θ hθ]
  exact congrArg (fun S : Submodule ℂ H2 => (S : Set H2))
    (wandering_range hclosed hne hM hθW hnorm).symm

/-- Analytic multiplication commutes with the actual coefficient shift. -/
theorem innerMul_shift (θ : H2) (hθ : IsInner θ) (f : H2) :
    innerMul θ hθ (shift f) = shift (innerMul θ hθ f) := by
  apply evaluation_injective
  intro z hz
  calc
    eval (innerMul θ hθ (shift f)) z = eval θ z * eval (shift f) z :=
      innerMul_evaluation θ hθ (shift f) z hz
    _ = eval θ z * (z * eval f z) := congrArg (fun w => eval θ z * w) (shift_evaluation f z hz)
    _ = z * (eval θ z * eval f z) := by ring
    _ = z * eval (innerMul θ hθ f) z :=
      congrArg (fun w => z * w) (innerMul_evaluation θ hθ f z hz).symm
    _ = eval (shift (innerMul θ hθ f)) z := (shift_evaluation _ _ hz).symm

theorem inner_range_invariant (θ : H2) (hθ : IsInner θ) :
    ShiftInvariant (LinearMap.range (innerMul θ hθ).toLinearMap) := by
  rintro _ ⟨f, rfl⟩
  exact ⟨shift f, innerMul_shift θ hθ f⟩

theorem inner_norm {θ : H2} (hθ : IsInner θ) : ‖θ‖ = 1 := by
  simpa only [Function.iterate_zero_apply] using (inner_shifts_orthonormal hθ).1 0

theorem generator_wandering (θ : H2) (hθ : IsInner θ) :
    θ ∈ wandering (LinearMap.range (innerMul θ hθ).toLinearMap) := by
  have he : innerMul θ hθ (lp.single 2 0 1) = θ := by
    simp only [innerMul_single, Function.iterate_zero_apply, one_smul]
  refine ⟨⟨lp.single 2 0 1, he⟩, ?_⟩
  rintro _ ⟨f, ⟨a, rfl⟩, rfl⟩
  change inner ℂ (shift (innerMul θ hθ a)) θ = 0
  rw [← innerMul_shift]
  calc
    inner ℂ (innerMul θ hθ (shift a)) θ =
        inner ℂ (innerMul θ hθ (shift a)) (innerMul θ hθ (lp.single 2 0 1)) :=
      congrArg (fun w => inner ℂ (innerMul θ hθ (shift a)) w) he.symm
    _ = inner ℂ (shift a) (lp.single 2 0 (1 : ℂ)) := (innerMul θ hθ).inner_map_map _ _
    _ = 0 := by
      rw [lp.inner_single_right]
      change inner ℂ (HardyDiskSpec.shift a 0) (1 : ℂ) = 0
      rw [shift_zero, inner_zero_left]

theorem uniqueness : Uniqueness := by
  intro θ η hθ hη heq
  let M := LinearMap.range (innerMul θ hθ).toLinearMap
  have hclosed : IsClosed (M : Set H2) :=
    (innerMul θ hθ).isometry.isUniformInducing.isComplete_range.isClosed
  have hθW : θ ∈ wandering M := generator_wandering θ hθ
  have hne : M ≠ ⊥ := by
    intro he
    have hz : θ = 0 := by simpa only [he, wandering, bot_inf_eq, Submodule.mem_bot] using hθW
    have hh := inner_norm hθ
    rw [hz, norm_zero] at hh
    exact zero_ne_one hh
  have hr : M = LinearMap.range (innerMul η hη).toLinearMap := by
    apply SetLike.coe_injective
    change Set.range (innerMul θ hθ) = Set.range (innerMul η hη)
    rw [innerMul_range θ hθ, innerMul_range η hη, heq]
  have hηW : η ∈ wandering M := by rw [hr]; exact generator_wandering η hη
  have hs := wandering_eq_smul hclosed hne (inner_range_invariant θ hθ)
    hθW (inner_norm hθ) hηW
  refine ⟨inner ℂ θ η, ?_, hs⟩
  have hh := congrArg norm hs
  simpa only [norm_smul, inner_norm hθ, inner_norm hη, mul_one] using hh.symm

/-- The bounded analytic coordinate function is one of the quantified multipliers. -/
def coordinateSymbol : HInfinity :=
  ⟨fun z => z.val, (differentiableOn_id.congr (fun z hz =>
      zeroExtend_apply (fun w : Disk => w.val) ⟨z, hz⟩)),
    ⟨1, fun z => le_of_lt (by
      simpa only [HardyDiskSpec.disk, Metric.mem_ball, dist_zero_right] using z.property)⟩⟩

/-- Every product range is invariant under all bounded analytic multipliers. -/
theorem productRange_multiplier (θ : H2) (b : HInfinity)
    (f : H2) (hf : f ∈ ProductRange θ) (g : H2)
    (hg : ∀ z : Disk, eval g z = b.val z * eval f z) : g ∈ ProductRange θ := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨multiplier b a, ?_⟩
  intro z hz
  have hm : eval (multiplier b a) z = b.val ⟨z, hz⟩ * eval a z := by
    change eval (multiplierVector b a) z = _
    rw [multiplierVector_eval b a hz, zeroExtend_apply b.val ⟨z, hz⟩]
  calc
    eval g z = b.val ⟨z, hz⟩ * eval f z := hg ⟨z, hz⟩
    _ = b.val ⟨z, hz⟩ * (eval θ z * eval a z) := congrArg (fun w => b.val ⟨z, hz⟩ * w) (ha z hz)
    _ = eval θ z * (b.val ⟨z, hz⟩ * eval a z) := by ring
    _ = eval θ z * eval (multiplier b a) z := congrArg (fun w => eval θ z * w) hm.symm

theorem multiplier_equivalence : MultiplierEquivalence := by
  intro M hclosed
  constructor
  · intro hM b f hf g hg
    by_cases hne : M = ⊥
    · have hfzero : f = 0 := by simpa only [hne, Submodule.mem_bot] using hf
      have hgzero : g = 0 := by
        apply evaluation_injective
        intro z hz
        have hh := hg ⟨z, hz⟩
        simpa [hfzero, HardyDiskSpec.eval] using hh
      rw [hgzero]
      exact M.zero_mem
    · obtain ⟨θ, hθ, he⟩ := classification M hclosed hne hM
      have hf' : f ∈ ProductRange θ := by rwa [← he]
      have hg' := productRange_multiplier θ b f hf' g hg
      rwa [← he] at hg'
  · intro hM f hf
    apply hM coordinateSymbol f hf (shift f)
    intro z
    exact shift_evaluation f z.val z.property

end ExpandedFA.PartIV.Beurling
