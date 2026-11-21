import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LinearMaximalMonotone
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LumerPhillips
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Monotone.Definitions
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open Filter Topology Set
namespace ExpandedFA.Semigroups.LinearMaximalMonotone
open LinearMaximalMonotoneSpec
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem monotonicity_bridge : MonotonicityBridge := by
  intro 𝕜 H _ _ _ L
  letI := NormedSpace.restrictScalars ℝ 𝕜 H
  letI := InnerProductSpace.rclikeToReal 𝕜 H
  rw [ExpandedFA.Monotone.monotone_hilbertGraph_iff]
  constructor
  · intro h x y a b ha hb
    obtain ⟨u, hu, hua⟩ := (LinearPMap.mem_graph_iff _).mp ha
    obtain ⟨v, hv, hvb⟩ := (LinearPMap.mem_graph_iff _).mp hb
    cases hu
    cases hv
    cases hua
    cases hvb
    exact h u v
  · intro h x y
    exact h ((realOperator L).mem_graph x) ((realOperator L).mem_graph y)

theorem positive_iff (L : Unbounded.Operator 𝕜 H H) :
    Monotone L ↔ ∀ x : L.domain, 0 ≤ RCLike.re (inner 𝕜 (x : H) (L x)) := by
  constructor
  · intro h x
    have hp := h x 0
    simpa only [L.map_zero, Submodule.coe_zero, sub_zero, inner_re_symm] using hp
  · intro h x y
    have hp := h (x - y)
    simpa only [L.map_sub, Submodule.coe_sub, inner_re_symm] using hp

theorem dissipative_neg (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L) :
    LumerPhillipsSpec.Dissipative (-L) := by
  apply (LumerPhillips.hilbert_dissipative_iff (-L)).mpr
  intro x
  simpa only [LinearPMap.neg_apply, inner_neg_right, map_neg, neg_nonpos]
    using (positive_iff L).mp hm x

@[simp] theorem plusMap_apply (L : Unbounded.Operator 𝕜 H H) (r : ℝ) (x : L.domain) :
    plusMap L r x = (x : H) + algebraMap ℝ 𝕜 r • L x := rfl

theorem fullRange_one (L : Unbounded.Operator 𝕜 H H)
    (hs : Function.Surjective (plusMap L 1)) : LumerPhillipsSpec.FullRange (-L) 1 := by
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨x, ?_⟩
  simpa [LumerPhillipsSpec.shiftMap, plusMap, LinearPMap.neg_apply] using hx

variable [CompleteSpace H]

theorem dense_domain (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) : Dense (L.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨u, hu⟩ := hs f
  have hz : inner 𝕜 (u : H) f = 0 := hf u u.2
  have he : (u : H) + L u = f := by simpa using hu
  have hz := congrArg RCLike.re hz
  rw [← he, inner_add_right, map_add, inner_self_eq_norm_sq, map_zero] at hz
  have hp := (positive_iff L).mp hm u
  have hun : ‖(u : H)‖ = 0 := by nlinarith [norm_nonneg (u : H)]
  have huz : u = 0 := Subtype.ext (norm_eq_zero.mp hun)
  simpa [huz, L.map_zero] using he.symm


/-- All positive shifted ranges for -L, from the source's one range condition. -/
theorem range_neg_all (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (r : ℝ) (hr : 0 < r) :
    LumerPhillipsSpec.FullRange (-L) r :=
  LumerPhillips.fullRange_all (-L) (dissipative_neg L hm)
    ⟨1, zero_lt_one, fullRange_one L hs⟩ r hr

/-- The source range condition at an arbitrary positive scale. -/
theorem plusMap_surjective (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (r : ℝ) (hr : 0 < r) :
    Function.Surjective (plusMap L r) := by
  intro y
  obtain ⟨x, hx⟩ := range_neg_all L hm hs r⁻¹ (inv_pos.mpr hr)
    (algebraMap ℝ 𝕜 r⁻¹ • y)
  refine ⟨x, ?_⟩
  have he := congrArg (fun z : H => algebraMap ℝ 𝕜 r • z) hx
  simpa [LumerPhillipsSpec.shiftMap, LinearPMap.neg_apply, smul_add,
    smul_smul, ← map_mul, hr.ne'] using he

/-- The ambient norm lower bound for I+rL. -/
theorem plusMap_lower (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (r : ℝ) (hr : 0 < r) (x : L.domain) : ‖(x : H)‖ ≤ ‖plusMap L r x‖ := by
  have hd := dissipative_neg L hm r⁻¹ (inv_pos.mpr hr) x
  have he : plusMap L r x = algebraMap ℝ 𝕜 r • LumerPhillipsSpec.shiftMap (-L) r⁻¹ x := by
    simp [plusMap, LumerPhillipsSpec.shiftMap, LinearPMap.neg_apply,
      smul_add, smul_smul, ← map_mul, hr.ne']
  rw [he, norm_smul, norm_algebraMap', Real.norm_eq_abs, abs_of_pos hr]
  calc
    ‖(x : H)‖ = r * (r⁻¹ * ‖(x : H)‖) := by field_simp
    _ ≤ r * ‖LumerPhillipsSpec.shiftMap (-L) r⁻¹ x‖ :=
      mul_le_mul_of_nonneg_left hd hr.le

/-- Inverse data for the plus convention. No domain completeness is assumed. -/
structure PlusInverse (L : Unbounded.Operator 𝕜 H H) (r : ℝ) where
  J : H →L[𝕜] H
  mem : ∀ x, J x ∈ L.domain
  right : ∀ x, plusMap L r ⟨J x, mem x⟩ = x
  left : ∀ x : L.domain, J (plusMap L r x) = (x : H)
  bound : ‖J‖ ≤ 1

def plusInverse (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (r : ℝ) (hr : 0 < r) : PlusInverse L r := by
  have hinj : Function.Injective (plusMap L r) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hh := plusMap_lower L hm r hr x
    rw [hx, norm_zero] at hh
    exact Subtype.ext (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  let e := LinearEquiv.ofBijective (plusMap L r) ⟨hinj, plusMap_surjective L hm hs r hr⟩
  let f : H →ₗ[𝕜] H := L.domain.subtype.comp e.symm.toLinearMap
  have hb (y : H) : ‖f y‖ ≤ 1 * ‖y‖ := by
    have hh := plusMap_lower L hm r hr (e.symm y)
    change ‖(e.symm y : H)‖ ≤ 1 * ‖y‖
    rw [one_mul]
    exact hh.trans_eq (congrArg norm (e.apply_symm_apply y))
  let J := f.mkContinuous 1 hb
  refine ⟨J, fun y => (e.symm y).2, fun y => e.apply_symm_apply y, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (e.symm_apply_apply x)
  · exact J.opNorm_le_bound zero_le_one hb


namespace PlusInverse
variable {L : Unbounded.Operator 𝕜 H H} {r : ℝ}

theorem apply_norm_le (R : PlusInverse L r) (x : H) : ‖R.J x‖ ≤ ‖x‖ :=
  (R.J.le_opNorm x).trans ((mul_le_mul_of_nonneg_right R.bound (norm_nonneg x)).trans_eq (one_mul _))

/-- Resolvent commutation holds on the exact original domain. -/
theorem commute (R : PlusInverse L r) (hr : 0 < r) (x : L.domain) :
    L ⟨R.J x, R.mem x⟩ = R.J (L x) := by
  have hleft := R.left x
  rw [plusMap_apply, map_add, map_smul] at hleft
  have hright := R.right (x : H)
  rw [plusMap_apply] at hright
  have he : algebraMap ℝ 𝕜 r • L ⟨R.J x, R.mem x⟩ =
      algebraMap ℝ 𝕜 r • R.J (L x) := add_left_cancel (hright.trans hleft.symm)
  have hne : algebraMap ℝ 𝕜 r ≠ 0 := by simpa using hr.ne'
  exact (smul_right_injective H hne) he

def K (R : PlusInverse L r) : H →L[𝕜] H :=
  (algebraMap ℝ 𝕜 r)⁻¹ • (ContinuousLinearMap.id 𝕜 H - R.J)

theorem K_apply (R : PlusInverse L r) (hr : 0 < r) (x : H) :
    R.K x = L ⟨R.J x, R.mem x⟩ := by
  have h := R.right x
  rw [plusMap_apply] at h
  have he : x - R.J x = algebraMap ℝ 𝕜 r • L ⟨R.J x, R.mem x⟩ :=
    (sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _)))
  have hne : algebraMap ℝ 𝕜 r ≠ 0 := by simpa using hr.ne'
  change (algebraMap ℝ 𝕜 r)⁻¹ • (x - R.J x) = _
  rw [he, inv_smul_smul₀ hne]

theorem K_domain (R : PlusInverse L r) (hr : 0 < r) (x : L.domain) :
    R.K x = R.J (L x) := (R.K_apply hr x).trans (R.commute hr x)

theorem sub_identity (R : PlusInverse L r) (x : L.domain) :
    R.J x - (x : H) = -(algebraMap ℝ 𝕜 r • R.J (L x)) := by
  have h := R.left x
  rw [plusMap_apply, map_add, map_smul] at h
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_zero]
  exact h

theorem sub_norm_le (R : PlusInverse L r) (hr : 0 < r) (x : L.domain) :
    ‖R.J x - (x : H)‖ ≤ r * ‖L x‖ := by
  rw [R.sub_identity, norm_neg, norm_smul, norm_algebraMap', Real.norm_eq_abs, abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left (R.apply_norm_le _) hr.le

end PlusInverse

/-- Chosen resolvents are totalized only outside the positive parameters. -/
def resolventFamily (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (r : ℝ) : H →L[𝕜] H :=
  if hr : 0 < r then (plusInverse L hm hs r hr).J else 0

def yosidaFamily (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (r : ℝ) : H →L[𝕜] H :=
  if hr : 0 < r then (plusInverse L hm hs r hr).K else 0


/-- Closed graph follows from the bounded inverse, without assuming the domain closed. -/
theorem closed_of_plusInverse (L : Unbounded.Operator 𝕜 H H) (R : PlusInverse L 1) :
    L.IsClosed := by
  have heq : (L.graph : Set (H × H)) = {p | R.J (p.1 + p.2) = p.1} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hx, hv⟩ := (Unbounded.mem_graph_iff L p).mp hp
      change R.J (p.1 + p.2) = p.1
      rw [← hv]
      simpa using R.left ⟨p.1, hx⟩
    · intro hp
      change R.J (p.1 + p.2) = p.1 at hp
      have hm : p.1 ∈ L.domain := hp ▸ R.mem _
      apply (Unbounded.mem_graph_iff L p).mpr
      refine ⟨hm, ?_⟩
      have h := R.right (p.1 + p.2)
      have hd : (⟨R.J (p.1 + p.2), R.mem _⟩ : L.domain) = ⟨p.1, hm⟩ := Subtype.ext hp
      rw [plusMap_apply, hd] at h
      simpa using h
  change IsClosed (L.graph : Set (H × H))
  rw [heq]
  exact isClosed_eq (R.J.continuous.comp (continuous_fst.add continuous_snd)) continuous_fst

theorem resolvent_limit_domain (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (x : L.domain) :
    Tendsto (fun r => resolventFamily L hm hs r x) (𝓝[>] (0 : ℝ)) (𝓝 (x : H)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero_norm' (a := fun r : ℝ => r * ‖L x‖)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    simpa only [resolventFamily, dite_eq_left hr, norm_norm] using
      (plusInverse L hm hs r hr).sub_norm_le hr x
  · simpa using (tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_id.mul_const ‖L x‖) :
      Tendsto (fun r : ℝ => r * ‖L x‖) (𝓝[>] 0) (𝓝 (0 * ‖L x‖)))

/-- Contractivity extends strong resolvent approximation from the dense domain. -/
theorem resolvent_limit (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (x : H) :
    Tendsto (fun r => resolventFamily L hm hs r x) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := (dense_domain L hm hs).exists_dist_lt x (by positivity : 0 < ε / 8)
  have hd : ‖x - y‖ < ε / 8 := by simpa only [dist_eq_norm] using hxy
  have hh := Metric.tendsto_nhds.mp (resolvent_limit_domain L hm hs ⟨y, hy⟩)
    (ε / 2) (half_pos hε)
  filter_upwards [hh, self_mem_nhdsWithin] with r hr hrpos
  have hrpos : 0 < r := hrpos
  rw [dist_eq_norm] at hr ⊢
  have hb : ‖resolventFamily L hm hs r (x - y)‖ ≤ ‖x - y‖ := by
    simpa only [resolventFamily, dite_eq_left hrpos] using
      (plusInverse L hm hs r hrpos).apply_norm_le (x - y)
  have he : resolventFamily L hm hs r x - x =
      resolventFamily L hm hs r (x - y) + (resolventFamily L hm hs r y - y) - (x - y) := by
    rw [map_sub]; abel
  calc
    ‖resolventFamily L hm hs r x - x‖ ≤
        ‖resolventFamily L hm hs r (x - y)‖ +
        ‖resolventFamily L hm hs r y - y‖ + ‖x - y‖ := by
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖x - y‖ + ‖resolventFamily L hm hs r y - y‖ + ‖x - y‖ := by gcongr
    _ < ε := by linarith

theorem yosida_limit (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (x : L.domain) :
    Tendsto (fun r => yosidaFamily L hm hs r x) (𝓝[>] (0 : ℝ)) (𝓝 (L x)) := by
  apply (resolvent_limit L hm hs (L x)).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  simpa only [yosidaFamily, resolventFamily, dite_eq_left hr] using
    ((plusInverse L hm hs r hr).K_domain hr x).symm

/-- Resolvent smoothing approximates both graph coordinates simultaneously. -/
theorem square_domain_graph_dense (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) (x : L.domain) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : L.domain, L y ∈ L.domain ∧ ‖(y : H) - x‖ + ‖L y - L x‖ < ε := by
  have hJ := Metric.tendsto_nhds.mp (resolvent_limit L hm hs x) (ε / 2) (half_pos hε)
  have hK := Metric.tendsto_nhds.mp (yosida_limit L hm hs x) (ε / 2) (half_pos hε)
  obtain ⟨r, hrJ, hrK, hr⟩ := (hJ.and (hK.and self_mem_nhdsWithin)).exists
  let R := plusInverse L hm hs r hr
  refine ⟨⟨R.J x, R.mem x⟩, ?_, ?_⟩
  · rw [R.commute hr x]
    exact R.mem (L x)
  · rw [dist_eq_norm] at hrJ hrK
    have heJ : resolventFamily L hm hs r x = R.J x := by
      simp only [resolventFamily, dite_eq_left hr]; rfl
    have heK : yosidaFamily L hm hs r x = L ⟨R.J x, R.mem x⟩ := by
      simp only [yosidaFamily, dite_eq_left hr]
      exact R.K_apply hr x
    rw [heJ] at hrJ
    rw [heK] at hrK
    exact (add_lt_add hrJ hrK).trans_eq (add_halves ε)

/-- Linear maximal monotonicity yields a contraction semigroup with generator -L. -/
theorem contraction_generation (L : Unbounded.Operator 𝕜 H H) (hm : Monotone L)
    (hs : Function.Surjective (plusMap L 1)) :
    ∃ T : C0Semigroup 𝕜 H, C0SemigroupSpec.generatorValue T = -L ∧
      LumerPhillipsSpec.Contractive T := by
  apply (LumerPhillips.characterization (-L) (dense_domain L hm hs)).mpr
  exact ⟨dissipative_neg L hm, 1, zero_lt_one, fullRange_one L hs⟩

/-- The entire source proposition, over real or complex Hilbert spaces. -/
theorem linear_maximal_monotone : LinearMaximalMonotoneSpec.LinearMaximalMonotone := by
  intro 𝕜 H _ _ _ _ L hm hs
  refine ⟨closed_of_plusInverse L (plusInverse L hm hs 1 zero_lt_one),
    dense_domain L hm hs, plusMap_surjective L hm hs, ?_,
    square_domain_graph_dense L hm hs, contraction_generation L hm hs⟩
  refine ⟨resolventFamily L hm hs, yosidaFamily L hm hs, ?_,
    resolvent_limit L hm hs, yosida_limit L hm hs⟩
  intro r hr
  let R := plusInverse L hm hs r hr
  simp only [resolventFamily, yosidaFamily, dite_eq_left hr]
  refine ⟨R.mem, R.right, R.left, R.bound, R.K_apply hr, ?_⟩
  intro x
  rw [R.K_domain hr x]
  exact R.apply_norm_le (L x)

end ExpandedFA.Semigroups.LinearMaximalMonotone



