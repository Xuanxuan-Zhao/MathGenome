import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.ChernoffProductFormula
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.TrotterKatoApproximation
import Mathlib.Analysis.SpecificLimits.Normed

/-! Chernoff products on a real or complex Banach space.

We construct Q_h = (I-(F(h)-I)/h)⁻¹ by a geometric series. Core consistency
and graph density give Q_h → R(1,A) strongly, hence uniformly on compact
orbits. On vectors R(1,A)²y, a one-step comparison has defect bounded by
h times the resolvent error plus the generator difference-quotient error.
The discrete contraction estimate accumulates at most n such defects.
Density of the squared resolvent range gives the result on all of X.

The strong-resolvent formulation is also discussed in V. Zagrebnov,
“Notes on the Chernoff Product Formula”, arXiv:1911.09480, Proposition 1.2.
The discrete comparison here uses no measurability assumption on F.
-/

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace ExpandedFA.Semigroups.ChernoffProductFormula
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
open ChernoffSpec

/-- Resolvent at 1 of the bounded difference operator (F(h)-I)/h.
The formula is used only for positive h. -/
def stepResolvent (F : ℝ≥0 → X →L[𝕜] X) (h : ℝ) : X →L[𝕜] X :=
  (h / (1 + h)) • ∑' k : ℕ, (((1 + h)⁻¹ : ℝ) • F h.toNNReal) ^ k

omit [CompleteSpace X] in
/-- A contraction decreases the norm of every vector. -/
theorem contraction_apply (L : X →L[𝕜] X) (hL : ‖L‖ ≤ 1) (x : X) :
    ‖L x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (L.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg x))

omit [CompleteSpace X] in
/-- All powers of a contraction remain contractions, including the zeroth power
on the zero space. -/
theorem contraction_pow (L : X →L[𝕜] X) (hL : ‖L‖ ≤ 1) (n : ℕ) :
    ‖L ^ n‖ ≤ 1 := by
  induction n with
  | zero =>
    change ‖(1 : X →L[𝕜] X)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (L ^ n)])

omit [CompleteSpace X] in
/-- The Neumann-series parameter lies strictly inside the unit ball. -/
theorem step_parameter_lt (F : ℝ≥0 → X →L[𝕜] X)
    (hF : ∀ h, ‖F h‖ ≤ 1) {h : ℝ} (hh : 0 < h) :
    ‖((1 + h)⁻¹ : ℝ) • F h.toNNReal‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (1 + h)⁻¹ * 1 := mul_le_mul_of_nonneg_left (hF _) (by positivity)
    _ < 1 := by rw [mul_one]; exact (inv_lt_one₀ (by positivity)).mpr (by linarith)

omit [CompleteSpace X] in
/-- The discrete resolvents have the same contraction bound as R(1,A). -/
theorem norm_stepResolvent_le (F : ℝ≥0 → X →L[𝕜] X)
    (hF : ∀ h, ‖F h‖ ≤ 1) {h : ℝ} (hh : 0 < h) :
    ‖stepResolvent F h‖ ≤ 1 := by
  let L := ((1 + h)⁻¹ : ℝ) • F h.toNNReal
  have hL := step_parameter_lt F hF hh
  have hden : 0 < 1 + h := by linarith
  have hLn : ‖L‖ ≤ (1 + h)⁻¹ := by
    dsimp [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hF h.toNNReal) (show 0 ≤ (1 + h)⁻¹ by positivity)
  have hgeom := tsum_geometric_le_of_norm_lt_one L hL
  have hone : ‖(1 : X →L[𝕜] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hp : 0 < 1 - (1 + h)⁻¹ := by
    have := (inv_lt_one₀ hden).mpr (show 1 < 1 + h by linarith)
    linarith
  have hinv : (1 - ‖L‖)⁻¹ ≤ (1 - (1 + h)⁻¹)⁻¹ := by
    exact inv_anti₀ hp (sub_le_sub_left hLn 1)
  have heq : h / (1 + h) * (1 - (1 + h)⁻¹)⁻¹ = 1 := by
    field_simp [ne_of_gt hh]
    ring
  change ‖(h / (1 + h)) • ∑' k : ℕ, L ^ k‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hh hden)]
  calc
    _ ≤ h / (1 + h) * (1 - (1 + h)⁻¹)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (div_pos hh hden).le
      exact hgeom.trans (by linarith)
    _ = 1 := heq

/-- The two algebraic resolvent identities, before division by h. -/
theorem stepResolvent_identities (F : ℝ≥0 → X →L[𝕜] X)
    (hF : ∀ h, ‖F h‖ ≤ 1) {h : ℝ} (hh : 0 < h) :
    (((1 + h) • (1 : X →L[𝕜] X) - F h.toNNReal) * stepResolvent F h = h • 1) ∧
    (stepResolvent F h * ((1 + h) • (1 : X →L[𝕜] X) - F h.toNNReal) = h • 1) := by
  let L := ((1 + h)⁻¹ : ℝ) • F h.toNNReal
  have hL := step_parameter_lt F hF hh
  have hn : 1 + h ≠ 0 := ne_of_gt (show 0 < 1 + h by linarith)
  have hf : (1 + h) • (1 : X →L[𝕜] X) - F h.toNNReal =
      (1 + h) • (1 - L) := by
    simp [L, smul_sub, smul_smul, hn]
  have hc : (1 + h) * (h / (1 + h)) = h := by field_simp
  have hc' : (h / (1 + h)) * (1 + h) = h := by field_simp
  dsimp only [stepResolvent]
  change (_ * ((h / (1 + h)) • ∑' k : ℕ, L ^ k) = _) ∧
    (((h / (1 + h)) • ∑' k : ℕ, L ^ k) * _ = _)
  rw [hf]
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, mul_neg_geom_series L hL, smul_smul, hc]
  · rw [smul_mul_assoc, mul_smul_comm, geom_series_mul_neg L hL, smul_smul, hc']

/-- The discrete resolvent inverts I-(F(h)-I)/h on every vector. -/
theorem stepResolvent_left (F : ℝ≥0 → X →L[𝕜] X)
    (hF : ∀ h, ‖F h‖ ≤ 1) {h : ℝ} (hh : 0 < h) (x : X) :
    stepResolvent F h (x - h⁻¹ • (F h.toNNReal x - x)) = x := by
  have hid := congrArg (fun L : X →L[𝕜] X => L x)
    (stepResolvent_identities F hF hh).2
  simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at hid
  have he : x - h⁻¹ • (F h.toNNReal x - x) =
      h⁻¹ • ((1 + h) • x - F h.toNNReal x) := by
    simp only [smul_sub, add_smul, one_smul, smul_add,
      inv_smul_smul₀ (ne_of_gt hh)]
    module
  rw [he, (stepResolvent F h).map_smul_of_tower, hid,
    inv_smul_smul₀ (ne_of_gt hh)]

/-- A form of the right resolvent identity used in the discrete comparison. -/
theorem stepResolvent_right (F : ℝ≥0 → X →L[𝕜] X)
    (hF : ∀ h, ‖F h‖ ≤ 1) {h : ℝ} (hh : 0 < h) (x : X) :
    F h.toNNReal (stepResolvent F h x) =
      (1 + h) • stepResolvent F h x - h • x := by
  have hid := congrArg (fun L : X →L[𝕜] X => L x)
    (stepResolvent_identities F hF hh).1
  simp only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] at hid
  exact (eq_sub_iff_add_eq.mpr (by
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hid).symm))

omit [CompleteSpace X] in
/-- The image of a graph core under I-A is dense whenever 1 is a resolvent
point. This uses the graph core, rather than ambient density alone. -/
theorem core_resolvent_range_dense (A : Unbounded.Operator 𝕜 X X)
    (D : Submodule 𝕜 X) (hcore : Unbounded.OperatorDomainsSpec.coreValue A D)
    (R : Unbounded.ResolventInverse A 1) :
    DenseRange (fun x : D => (x : X) - A ⟨x, hcore.1 x.2⟩) := by
  intro y
  let x : A.domain := ⟨R.inverse y, R.mem_domain y⟩
  have hx : ((x : X), A x) ∈ closure ((A.domRestrict D).graph : Set (X × X)) := by
    change ((x : X), A x) ∈ (A.domRestrict D).graph.topologicalClosure
    rw [hcore.2]
    exact subset_closure (A.mem_graph x)
  have hc : Continuous (fun p : X × X => p.1 - p.2) := continuous_fst.sub continuous_snd
  have hy := mem_closure_image hc.continuousAt hx
  have he : (x : X) - A x = y := by simpa only [one_smul] using R.right_inverse y
  rw [he] at hy
  apply closure_mono _ hy
  rintro z ⟨p, hp, rfl⟩
  obtain ⟨v, hv⟩ := (A.domRestrict D).mem_graph_iff'.mp hp
  refine ⟨⟨v, v.2.1⟩, ?_⟩
  rw [← hv]
  congr 1

omit [CompleteSpace X] in
/-- Uniformly contractive operators extend strong convergence from a dense set,
for an arbitrary index filter. -/
theorem strong_of_dense {ι : Type*} {l : Filter ι}
    (P : ι → X →L[𝕜] X) (R : X →L[𝕜] X)
    (hP : ∀ᶠ i in l, ‖P i‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    {D : Set X} (hD : Dense D)
    (h : ∀ y ∈ D, Tendsto (fun i => P i y) l (𝓝 (R y))) :
    ∀ x, Tendsto (fun i => P i x) l (𝓝 (R x)) := by
  intro x
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x (show 0 < ε / 4 by positivity)
  filter_upwards [hP, Metric.tendsto_nhds.mp (h y hy) (ε / 4) (by positivity)] with i hi hiy
  have hl (L : X →L[𝕜] X) (hL : ‖L‖ ≤ 1) : dist (L x) (L y) < ε / 4 := by
    rw [dist_eq_norm, ← map_sub]
    exact (contraction_apply L hL (x - y)).trans_lt (by simpa [dist_eq_norm] using hxy)
  calc
    dist (P i x) (R x) ≤ dist (P i x) (P i y) + dist (P i y) (R y) +
        dist (R y) (R x) := dist_triangle4 _ _ _ _
    _ < ε / 4 + ε / 4 + ε / 4 := by
      apply add_lt_add (add_lt_add (hl _ hi) hiy)
      rw [dist_comm]
      exact hl _ hR
    _ < ε := by linarith

omit [CompleteSpace X] in
/-- Strong convergence of contractions is uniform on each compact set, with an
arbitrary filter of indices. -/
theorem uniform_on_compact {ι : Type*} {l : Filter ι}
    (P : ι → X →L[𝕜] X) (R : X →L[𝕜] X)
    (hP : ∀ᶠ i in l, ‖P i‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (h : ∀ x, Tendsto (fun i => P i x) l (𝓝 (R x)))
    {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i x => P i x) R l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨D, _, hD, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 4 by positivity)
  have hev : ∀ᶠ i in l, ∀ y ∈ D, dist (R y) (P i y) < ε / 4 :=
    hD.eventually_all.mpr (fun y _ => by
      simpa only [dist_comm] using Metric.tendsto_nhds.mp (h y) (ε / 4) (by positivity))
  filter_upwards [hP, hev] with i hi hn x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hl (L : X →L[𝕜] X) (hL : ‖L‖ ≤ 1) : dist (L x) (L y) < ε / 4 := by
    rw [dist_eq_norm, ← map_sub]
    exact (contraction_apply L hL (x - y)).trans_lt (by simpa [dist_eq_norm] using hxy)
  calc
    dist (R x) (P i x) ≤ dist (R x) (R y) + dist (R y) (P i y) +
        dist (P i y) (P i x) := dist_triangle4 _ _ _ _
    _ < ε / 4 + ε / 4 + ε / 4 := by
      apply add_lt_add (add_lt_add (hl _ hR) (hn y hy))
      rw [dist_comm]
      exact hl _ hi
    _ < ε := by linarith

/-- Consistency on a graph core implies strong convergence of the discrete
resolvents at 1. No consistency on the whole generator domain is assumed. -/
theorem stepResolvent_tendsto (T : C0Semigroup 𝕜 X)
    (F : ℝ≥0 → X →L[𝕜] X) (hF : ∀ h, ‖F h‖ ≤ 1)
    (D : Submodule 𝕜 X)
    (hcore : Unbounded.OperatorDomainsSpec.coreValue (C0SemigroupSpec.generatorValue T) D)
    (hc : CoreConsistency T F D hcore.1)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) 1)
    (hR : ‖R.inverse‖ ≤ 1) :
    ∀ x, Tendsto (fun h : ℝ => stepResolvent F h x) (𝓝[>] 0) (𝓝 (R.inverse x)) := by
  have hP : ∀ᶠ h : ℝ in 𝓝[>] 0, ‖stepResolvent F h‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact norm_stepResolvent_le F hF hh
  apply strong_of_dense (stepResolvent F) R.inverse hP hR
    (core_resolvent_range_dense _ D hcore R)
  rintro y ⟨x, rfl⟩
  let a := C0SemigroupSpec.generatorValue T ⟨x, hcore.1 x.2⟩
  let q : ℝ → X := fun h => h⁻¹ • (F h.toNNReal (x : X) - (x : X))
  have hq : Tendsto q (𝓝[>] 0) (𝓝 a) := by
    convert hc x using 1
    funext h
    rw [← map_inv₀]
    rfl
  have hz : Tendsto (fun h : ℝ => stepResolvent F h (q h - a)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hP] with h hh
      exact contraction_apply _ hh _
    · simpa only [sub_self, norm_zero] using (hq.sub_const a).norm
  have heR : R.inverse ((x : X) - a) = x := by
    simpa only [one_smul] using R.left_inverse ⟨x, hcore.1 x.2⟩
  apply (tendsto_sub_nhds_zero_iff.mp ?_)
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change stepResolvent F h (q h - a) =
    stepResolvent F h ((x : X) - a) - R.inverse ((x : X) - a)
  rw [heR]
  calc
    _ = stepResolvent F h (((x : X) - a) - ((x : X) - q h)) := by
      congr 1
      abel
    _ = _ := by
      rw [map_sub, stepResolvent_left F hF hh]

omit [CompleteSpace X] in
/-- The elementary telescoping estimate for a discrete contraction orbit. -/
theorem discrete_comparison (L : X →L[𝕜] X) (hL : ‖L‖ ≤ 1)
    (v : ℕ → X) (n : ℕ) {c : ℝ}
    (hc : ∀ j < n, ‖L (v j) - v (j + 1)‖ ≤ c) :
    ‖(L ^ n) (v 0) - v n‖ ≤ (n : ℝ) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun j hj => hc j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    have he : (L ^ (n + 1)) (v 0) - v (n + 1) =
        L ((L ^ n) (v 0) - v n) + (L (v n) - v (n + 1)) := by
      rw [pow_succ', mul_apply_eq_comp, map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖L ((L ^ n) (v 0) - v n)‖ + ‖L (v n) - v (n + 1)‖ := norm_add_le _ _
      _ ≤ (n : ℝ) * c + c := add_le_add ((contraction_apply L hL _).trans hi)
        (hc n (Nat.lt_succ_self n))
      _ = ((n + 1 : ℕ) : ℝ) * c := by push_cast; ring

/-- The one-step defect after resolvent smoothing. -/
theorem smoothed_step_bound (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1)
    (F : ℝ≥0 → X →L[𝕜] X) (hF : ∀ h, ‖F h‖ ≤ 1)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) 1)
    (y : X) {h : ℝ} (hh : 0 < h) (s : ℝ≥0) :
    ‖F h.toNNReal (stepResolvent F h (T.operators s (R.inverse y))) -
      stepResolvent F h (T.operators (s + h.toNNReal) (R.inverse y))‖ ≤
    h * (‖stepResolvent F h (T.operators s y) - R.inverse (T.operators s y)‖ +
      ‖h⁻¹ • (T.operators h.toNNReal (R.inverse y) - R.inverse y) - (R.inverse y - y)‖) := by
  let Q := stepResolvent F h
  let e := h⁻¹ • (T.operators h.toNNReal (R.inverse y) - R.inverse y) - (R.inverse y - y)
  have he : T.operators h.toNNReal (R.inverse y) =
      R.inverse y + h • (R.inverse y - y + e) := by
    dsimp [e]
    have hcancel (a b : X) : a + (b - a) = b := by abel
    rw [hcancel, smul_inv_smul₀ (ne_of_gt hh)]
    abel
  have hcomm := TrotterKatoApproximation.resolvent_semigroup_commute T 1 R s y
  have hid : F h.toNNReal (Q (T.operators s (R.inverse y))) -
      Q (T.operators (s + h.toNNReal) (R.inverse y)) =
      h • (Q (T.operators s y) - R.inverse (T.operators s y) - Q (T.operators s e)) := by
    rw [stepResolvent_right F hF hh, T.add_apply, he]
    simp only [map_add, map_sub, ContinuousLinearMap.map_smul_of_tower]
    rw [hcomm]
    module
  change ‖_ - _‖ ≤ h * (‖_ - _‖ + ‖e‖)
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  apply mul_le_mul_of_nonneg_left _ hh.le
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    ((contraction_apply Q (norm_stepResolvent_le F hF hh) _).trans
      (contraction_apply _ (hT s) e)))

/-- A finite-time product estimate on the dense range of R(1,A)². -/
theorem smoothed_product_bound (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1)
    (F : ℝ≥0 → X →L[𝕜] X) (hF : ∀ h, ‖F h‖ ≤ 1)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) 1)
    (y : X) {h b η : ℝ} (hh : 0 < h) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (n : ℕ) (hnb : (n : ℝ) * h ≤ b)
    (hc : ∀ s ∈ Icc (0 : ℝ) b,
      ‖stepResolvent F h (T.operators s.toNNReal y) - R.inverse (T.operators s.toNNReal y)‖ ≤ η ∧
      ‖stepResolvent F h (T.operators s.toNNReal (R.inverse y)) -
        R.inverse (T.operators s.toNNReal (R.inverse y))‖ ≤ η)
    (he : ‖h⁻¹ • (T.operators h.toNNReal (R.inverse y) - R.inverse y) - (R.inverse y - y)‖ ≤ η) :
    ‖(F h.toNNReal ^ n) (R.inverse (R.inverse y)) -
      T.operators ((n : ℝ) * h).toNNReal (R.inverse (R.inverse y))‖ ≤ (2 + 2 * b) * η := by
  let Q := stepResolvent F h
  let v : ℕ → X := fun j => Q (T.operators ((j : ℝ≥0) * h.toNNReal) (R.inverse y))
  have htime (j : ℕ) : (((j : ℝ≥0) * h.toNNReal : ℝ≥0) : ℝ) = (j : ℝ) * h := by
    simp [Real.coe_toNNReal _ hh.le]
  have htime' (j : ℕ) : ((j : ℝ≥0) * h.toNNReal) = ((j : ℝ) * h).toNNReal := by
    apply NNReal.coe_injective
    rw [htime, Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg j) hh.le)]
  have hd : ∀ j < n, ‖F h.toNNReal (v j) - v (j + 1)‖ ≤ h * (η + η) := by
    intro j hj
    have hjs : (((j : ℝ≥0) * h.toNNReal : ℝ≥0) : ℝ) ≤ b := by
      rw [htime]
      exact (mul_le_mul_of_nonneg_right (show (j : ℝ) ≤ n by exact_mod_cast hj.le) hh.le).trans hnb
    have hcj := (hc (((j : ℝ≥0) * h.toNNReal : ℝ≥0) : ℝ)
      ⟨NNReal.coe_nonneg _, hjs⟩).1
    rw [Real.toNNReal_coe] at hcj
    have hhj := smoothed_step_bound T hT F hF R y hh ((j : ℝ≥0) * h.toNNReal)
    apply le_trans (by simpa only [v, Q, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hhj)
    exact mul_le_mul_of_nonneg_left (add_le_add hcj he) hh.le
  have hmid := discrete_comparison (F h.toNNReal) (hF _) v n hd
  have hv0 : v 0 = Q (R.inverse y) := by simp [v, T.zero_apply]
  have hvn : v n = Q (T.operators ((n : ℝ) * h).toNNReal (R.inverse y)) := by dsimp only [v]; rw [htime']
  rw [hv0, hvn] at hmid
  have h0 := (hc 0 ⟨le_rfl, hb⟩).2
  simp only [Real.toNNReal_zero, T.zero_apply] at h0
  have hfirst : ‖(F h.toNNReal ^ n) (R.inverse (R.inverse y)) -
      (F h.toNNReal ^ n) (Q (R.inverse y))‖ ≤ η := by
    rw [← map_sub]
    exact (contraction_apply _ (contraction_pow _ (hF _) n) _).trans (by
      simpa only [norm_sub_rev] using h0)
  have hlast := (hc ((n : ℝ) * h) ⟨mul_nonneg (Nat.cast_nonneg n) hh.le, hnb⟩).2
  rw [TrotterKatoApproximation.resolvent_semigroup_commute T 1 R] at hlast
  calc
    _ ≤ ‖(F h.toNNReal ^ n) (R.inverse (R.inverse y)) -
          (F h.toNNReal ^ n) (Q (R.inverse y))‖ +
        ‖(F h.toNNReal ^ n) (Q (R.inverse y)) -
          Q (T.operators ((n : ℝ) * h).toNNReal (R.inverse y))‖ +
        ‖Q (T.operators ((n : ℝ) * h).toNNReal (R.inverse y)) -
          T.operators ((n : ℝ) * h).toNNReal (R.inverse (R.inverse y))‖ := by
      simpa only [dist_eq_norm] using dist_triangle4
        ((F h.toNNReal ^ n) (R.inverse (R.inverse y)))
        ((F h.toNNReal ^ n) (Q (R.inverse y)))
        (Q (T.operators ((n : ℝ) * h).toNNReal (R.inverse y)))
        (T.operators ((n : ℝ) * h).toNNReal (R.inverse (R.inverse y)))
    _ ≤ η + (n : ℝ) * (h * (η + η)) + η := add_le_add (add_le_add hfirst hmid) hlast
    _ ≤ (2 + 2 * b) * η := by nlinarith [mul_le_mul_of_nonneg_right hnb hη]

/-- Resolvent convergence yields uniform product convergence on the range of
R(1,A)². The small-step estimates are uniform down to time zero. -/
theorem product_convergence_resolvent_range (T : C0Semigroup 𝕜 X)
    (hT : ∀ t, ‖T.operators t‖ ≤ 1)
    (F : ℝ≥0 → X →L[𝕜] X) (hF : ∀ h, ‖F h‖ ≤ 1)
    (h0 : F 0 = ContinuousLinearMap.id 𝕜 X)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) 1)
    (hR : ‖R.inverse‖ ≤ 1)
    (hlim : ∀ x, Tendsto (fun h : ℝ => stepResolvent F h x) (𝓝[>] 0) (𝓝 (R.inverse x)))
    (y : X) (b : ℝ) (hb : 0 ≤ b) :
    TendstoUniformlyOn
      (fun n : ℕ => fun t : ℝ => (F (t / n).toNNReal ^ n) (R.inverse (R.inverse y)))
      (fun t : ℝ => T.operators t.toNNReal (R.inverse (R.inverse y))) atTop (Icc 0 b) := by
  have hP : ∀ᶠ h : ℝ in 𝓝[>] 0, ‖stepResolvent F h‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact norm_stepResolvent_le F hF hh
  let e : ℝ → X := fun h =>
    h⁻¹ • (T.operators h.toNNReal (R.inverse y) - R.inverse y) - (R.inverse y - y)
  have he : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    have hg := generator_has_limit T ⟨R.inverse y, R.mem_domain y⟩
    change Tendsto (fun h => differenceQuotient T h (R.inverse y)) _
      (𝓝 (C0SemigroupSpec.generatorValue T ⟨R.inverse y, R.mem_domain y⟩)) at hg
    simp_rw [T.differenceQuotient_real,
      TrotterKatoApproximation.generator_resolvent T 1 R, one_smul] at hg
    simpa only [sub_self] using hg.sub_const (R.inverse y - y)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let η := ε / (4 * (b + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hcompact (v : X) : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ s ∈ Icc (0 : ℝ) b,
      ‖stepResolvent F h (T.operators s.toNNReal v) -
        R.inverse (T.operators s.toNNReal v)‖ ≤ η := by
    have hu := uniform_on_compact (stepResolvent F) R.inverse hP hR hlim
      ((isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).image (T.continuous_real_orbit v))
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu η hη] with h hh s hs
    have hh' := (hh _ ⟨s, hs, rfl⟩).le
    simpa only [dist_eq_norm, norm_sub_rev] using hh'
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∀ s ∈ Icc (0 : ℝ) b,
        ‖stepResolvent F h (T.operators s.toNNReal y) - R.inverse (T.operators s.toNNReal y)‖ ≤ η ∧
        ‖stepResolvent F h (T.operators s.toNNReal (R.inverse y)) -
          R.inverse (T.operators s.toNNReal (R.inverse y))‖ ≤ η) ∧ ‖e h‖ ≤ η := by
    filter_upwards [hcompact y, hcompact (R.inverse y),
      Metric.tendsto_nhds.mp he η hη] with h h1 h2 h3
    exact ⟨fun s hs => ⟨h1 s hs, h2 s hs⟩, by simpa only [dist_zero_right] using h3.le⟩
  obtain ⟨δ, hδ, hδsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  have hdiv : Tendsto (fun n : ℕ => b / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), hdiv.eventually (gt_mem_nhds hδ)] with n hn hbn t ht
  by_cases ht0 : t = 0
  · subst t
    simpa only [zero_div, Real.toNNReal_zero, h0, ← ContinuousLinearMap.one_def,
      one_pow, one_apply_eq_self, T.zero_apply, dist_self] using hε
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 < t / (n : ℝ) := div_pos htp hnp
  have hhδ : t / (n : ℝ) < δ :=
    (div_le_div_of_nonneg_right ht.2 hnp.le).trans_lt hbn
  have hs := hδsmall ⟨hh, hhδ⟩
  have hnt : (n : ℝ) * (t / (n : ℝ)) = t := by field_simp
  have hhbound := smoothed_product_bound T hT F hF R y hh hb hη.le n
    (by simpa only [hnt] using ht.2) hs.1 hs.2
  rw [hnt] at hhbound
  rw [dist_eq_norm, norm_sub_rev]
  apply hhbound.trans_lt
  dsimp [η]
  have hden : b + 1 ≠ 0 := ne_of_gt (by positivity)
  calc
    (2 + 2 * b) * (ε / (4 * (b + 1))) = ε / 2 := by field_simp; ring
    _ < ε := by linarith

omit [CompleteSpace X] in
/-- Extend uniform convergence from a dense range using common contraction
bounds. The operators indexed by n need not themselves form semigroups. -/
theorem uniform_of_dense_range
    (P : ℕ → ℝ → X →L[𝕜] X) (U : ℝ → X →L[𝕜] X)
    (D : X → X) (hD : DenseRange D) (b : ℝ)
    (hP : ∀ n t, t ∈ Icc 0 b → ‖P n t‖ ≤ 1)
    (hU : ∀ t, t ∈ Icc 0 b → ‖U t‖ ≤ 1)
    (h : ∀ y, TendstoUniformlyOn (fun n t => P n t (D y))
      (fun t => U t (D y)) atTop (Icc 0 b)) :
    ∀ x, TendstoUniformlyOn (fun n t => P n t x) (fun t => U t x) atTop (Icc 0 b) := by
  intro x
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := hD.exists_dist_lt x (show 0 < ε / 4 by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h y) (ε / 4) (by positivity)] with n hn t ht
  have hl (L : X →L[𝕜] X) (hL : ‖L‖ ≤ 1) : dist (L x) (L (D y)) < ε / 4 := by
    rw [dist_eq_norm, ← map_sub]
    exact (contraction_apply L hL _).trans_lt (by simpa [dist_eq_norm] using hy)
  calc
    _ ≤ dist (U t x) (U t (D y)) + dist (U t (D y)) (P n t (D y)) +
        dist (P n t (D y)) (P n t x) := dist_triangle4 _ _ _ _
    _ < ε / 4 + ε / 4 + ε / 4 := by
      apply add_lt_add (add_lt_add (hl _ (hU t ht)) (hn t ht))
      rw [dist_comm]
      exact hl _ (hP n t ht)
    _ < ε := by linarith

/-- Chernoff's product formula for contractions, with consistency imposed only
on a graph core of the exact generator. -/
theorem chernoff_product_formula : ChernoffFormula (𝕜 := 𝕜) (X := X) := by
  intro T F D hT hF h0 hcore hc
  have hbT : C0SemigroupSpec.exponentialBoundValue T 1 0 :=
    ⟨le_rfl, by simpa only [zero_mul, Real.exp_zero, mul_one] using hT⟩
  let R := LaplaceResolvent.inverse T 1 0 1 hbT (by simp)
  have hR : ‖R.inverse‖ ≤ 1 := by
    simpa using (LaplaceResolvent.resolvent_powers T 1 0 1 hbT (by simp) R 0).2
  have hlim := stepResolvent_tendsto T F hF D hcore hc R hR
  have hdR := TrotterKatoApproximation.resolvent_denseRange T 1 R
  have hdRR := hdR.comp hdR R.inverse.continuous
  intro x b hb
  apply uniform_of_dense_range (fun n t => F (t / n).toNNReal ^ n)
    (fun t => T.operators t.toNNReal) (R.inverse ∘ R.inverse) hdRR b
    (fun n _ _ => contraction_pow _ (hF _) n) (fun t _ => hT t.toNNReal) _ x
  intro y
  exact product_convergence_resolvent_range T hT F hF h0 R hR hlim y b hb

end ExpandedFA.Semigroups.ChernoffProductFormula
