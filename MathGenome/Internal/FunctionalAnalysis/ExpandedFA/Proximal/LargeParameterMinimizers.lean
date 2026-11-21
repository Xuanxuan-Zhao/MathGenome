import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.LargeParameterMinimizers
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.VariationalFirmness
import Mathlib.Topology.MetricSpace.Cauchy

/-! Large positive parameters select the nearest global minimizer.
We prove a Cauchy estimate for the entire real-parameter path. This gives
strong convergence directly, without an inference from weak convergence. -/
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
universe u

def argmin : LargeParameterSpec.ArgminType.{u} := LargeParameterSpec.ArgminValue

section MinimizerSet
variable {H : Type u}

lemma argmin_finite (φ : ExtendedFunction H) (hp : Proper H φ)
    {p : H} (hpM : p ∈ argmin H φ) : φ p ≠ ⊤ := by
  obtain ⟨v, hv⟩ := hp
  exact ne_top_of_le_ne_top hv (hpM v)

lemma argmin_eq_sublevel (φ : ExtendedFunction H) {p : H} (hpM : p ∈ argmin H φ) :
    argmin H φ = {x | φ x ≤ φ p} := by
  ext x
  exact ⟨fun hx => hx p, fun hx y => hx.trans (hpM y)⟩

end MinimizerSet

theorem minimizer_set_geometry : LargeParameterSpec.MinimizerSetGeometry.{u} := by
  intro H _ _ _ φ hp hc hl hne
  obtain ⟨p, hpM⟩ := hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (argmin_finite φ hp hpM)
  have heq := argmin_eq_sublevel φ hpM
  refine ⟨⟨p, hpM⟩, ?_, ?_⟩
  · change IsClosed (argmin H φ)
    rw [heq, ← hm]
    exact hl m
  · intro x hx y hy a b ha hb hab
    have hxval : φ x = (m : WithTop ℝ) := (le_antisymm (hx p) (hpM x)).trans hm.symm
    have hyval : φ y = (m : WithTop ℝ) := (le_antisymm (hy p) (hpM y)).trans hm.symm
    change a • x + b • y ∈ argmin H φ
    rw [heq]
    change φ (a • x + b • y) ≤ φ p
    have hh := hc x y m m a b hxval hyval ha hb hab
    have habm : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
    simpa [habm, hm] using hh

section Path
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (φ : ExtendedFunction H) (hp : Proper H φ) (hc : ExtendedConvex H φ)
  (hl : LowerSemicontinuous H φ) (f : H)
include hp hc hl

private lemma path_vi (μ : ℝ) (hμ : 0 < μ) :
    VariationalInequality H φ μ f (proximalMap H φ μ f) :=
  ((proximalMap_characterization H φ hp hc hl μ hμ f _).1).mp rfl

/-- For ordered positive parameters, the function values decrease, and the
squared displacement between proximal points is bounded by the increase in
squared distance to f. -/
lemma proximalPath_order_estimate (μ ν : ℝ) (hμ : 0 < μ) (hμν : μ ≤ ν) :
    φ (proximalMap H φ ν f) ≤ φ (proximalMap H φ μ f) ∧
    ‖proximalMap H φ μ f - proximalMap H φ ν f‖ ^ 2 ≤
      ‖f - proximalMap H φ ν f‖ ^ 2 - ‖f - proximalMap H φ μ f‖ ^ 2 := by
  let u := proximalMap H φ μ f
  let v := proximalMap H φ ν f
  have hu := path_vi φ hp hc hl f μ hμ
  have hv := path_vi φ hp hc hl f ν (hμ.trans_le hμν)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hv.1
  have h1 := hu.2 v r s hr.symm hs.symm
  have h2 := hv.2 u s r hs.symm hr.symm
  have hid : ⟪f - u, v - u⟫_ℝ + ⟪f - v, u - v⟫_ℝ = ‖u - v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm v u]
    ring
  have hsr : s ≤ r := by
    rcases eq_or_lt_of_le hμν with heq | hlt
    · subst ν
      exact WithTop.coe_le_coe.mp (hs.trans hr.symm).le
    · nlinarith [sq_nonneg ‖u - v‖]
  have hnonpos : ⟪f - u, v - u⟫_ℝ ≤ 0 := by
    nlinarith [mul_nonneg hμ.le (sub_nonneg.mpr hsr)]
  refine ⟨?_, ?_⟩
  · change φ v ≤ φ u
    rw [← hs, ← hr]
    exact WithTop.coe_le_coe.mpr hsr
  · have heq : f - v = (f - u) - (v - u) := by abel
    change ‖u - v‖ ^ 2 ≤ ‖f - v‖ ^ 2 - ‖f - u‖ ^ 2
    rw [heq, norm_sub_sq_real (f - u) (v - u), norm_sub_rev v u]
    linarith

/-- Every minimizer bounds the proximal path's distance to the datum. -/
lemma proximalPath_minimizer_bound (p : H) (hpM : p ∈ argmin H φ)
    (μ : ℝ) (hμ : 0 < μ) :
    ‖f - proximalMap H φ μ f‖ ^ 2 ≤ ‖f - p‖ ^ 2 := by
  let u := proximalMap H φ μ f
  have hu := path_vi φ hp hc hl f μ hμ
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (argmin_finite φ hp hpM)
  change (r : WithTop ℝ) = φ u at hr
  have hmr : m ≤ r := WithTop.coe_le_coe.mp (by simpa only [← hm, ← hr] using hpM u)
  have hvi := hu.2 p r m hr.symm hm.symm
  have hnonpos : ⟪f - u, p - u⟫_ℝ ≤ 0 := by
    nlinarith [mul_nonneg hμ.le (sub_nonneg.mpr hmr)]
  have heq : f - p = (f - u) - (p - u) := by abel
  change ‖f - u‖ ^ 2 ≤ ‖f - p‖ ^ 2
  rw [heq, norm_sub_sq_real (f - u) (p - u)]
  nlinarith [sq_nonneg ‖p - u‖]

/-- A bounded monotone squared radius controls the full parameter path. -/
lemma proximalPath_cauchy (hne : (argmin H φ).Nonempty) :
    CauchySeq (fun μ : ℝ => proximalMap H φ μ f) := by
  obtain ⟨p, hpM⟩ := hne
  let q : ℝ → ℝ := fun μ => ‖f - proximalMap H φ μ f‖ ^ 2
  let T : Set ℝ := q '' Ioi 0
  have hT : T.Nonempty := ⟨q 1, 1, by norm_num, rfl⟩
  have hb : BddAbove T := by
    refine ⟨‖f - p‖ ^ 2, ?_⟩
    rintro r ⟨μ, hμ, rfl⟩
    exact proximalPath_minimizer_bound φ hp hc hl f p hpM μ hμ
  have hq (μ : ℝ) (hμ : 0 < μ) : q μ ≤ sSup T :=
    le_csSup hb ⟨μ, hμ, rfl⟩
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨r, ⟨μ, hμ, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hT
    (show sSup T - ε ^ 2 < sSup T by nlinarith [sq_pos_of_pos hε])
  refine ⟨μ, ?_⟩
  intro ν hμν
  have hh := (proximalPath_order_estimate φ hp hc hl f μ ν hμ hμν).2
  have hν := hq ν (hμ.trans_le hμν)
  change q μ > sSup T - ε ^ 2 at hr
  change ‖proximalMap H φ μ f - proximalMap H φ ν f‖ ^ 2 ≤ q ν - q μ at hh
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (proximalMap H φ μ f - proximalMap H φ ν f)]

/-- Energy comparison with any finite competitor bounds the original function
value above by a real level approaching the competitor value. -/
lemma proximalPath_value_bound (p : H) (m : ℝ)
    (hm : φ p = (m : WithTop ℝ)) (μ : ℝ) (hμ : 0 < μ) :
    φ (proximalMap H φ μ f) ≤
      ((m + ‖f - p‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ) := by
  have hu := proximalMap_minimizes H φ hp hc hl μ hμ f
  change IsProximalMinimizer H φ μ f (proximalMap H φ μ f) at hu
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu.1
  have hh := hu.2 p
  change φ (proximalMap H φ μ f) + _ ≤ φ p + _ at hh
  rw [← hr, hm, ← WithTop.coe_add, ← WithTop.coe_add] at hh
  have hh' := WithTop.coe_le_coe.mp hh
  rw [← hr]
  apply WithTop.coe_le_coe.mpr
  have hnonneg : 0 ≤ ‖f - proximalMap H φ μ f‖ ^ 2 / (2 * μ) := by positivity
  linarith

/-- The strong limit is a global minimizer, by norm lower semicontinuity. -/
lemma proximalPath_limit_mem (hne : (argmin H φ).Nonempty) (z : H)
    (hz : Tendsto (fun μ : ℝ => proximalMap H φ μ f) atTop (𝓝 z)) :
    z ∈ argmin H φ := by
  obtain ⟨p, hpM⟩ := hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (argmin_finite φ hp hpM)
  have ht : Tendsto (fun μ : ℝ => m + ‖f - p‖ ^ 2 / (2 * μ)) atTop (𝓝 m) := by
    have hh : Tendsto (fun μ : ℝ => (‖f - p‖ ^ 2 / 2) / μ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have heq (μ : ℝ) : ‖f - p‖ ^ 2 / (2 * μ) = (‖f - p‖ ^ 2 / 2) / μ := by ring
    simpa only [heq, add_zero] using tendsto_const_nhds.add hh
  have hepi := (lowerSemicontinuous_iff_closed_epigraph H φ).mp hl
  have hzval : φ z ≤ (m : WithTop ℝ) :=
    hepi.mem_of_tendsto (hz.prodMk_nhds ht) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
      exact proximalPath_value_bound φ hp hc hl f p m hm.symm μ hμ)
  intro v
  exact hzval.trans (hm.le.trans (hpM v))

/-- The limit is the nearest minimizer, using the uniform distance bound. -/
lemma proximalPath_limit_nearest (z : H)
    (hz : Tendsto (fun μ : ℝ => proximalMap H φ μ f) atTop (𝓝 z))
    (p : H) (hpM : p ∈ argmin H φ) : ‖f - z‖ ≤ ‖f - p‖ := by
  have hh : ‖f - z‖ ^ 2 ≤ ‖f - p‖ ^ 2 :=
    le_of_tendsto ((tendsto_const_nhds.sub hz).norm.pow 2) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
      exact proximalPath_minimizer_bound φ hp hc hl f p hpM μ hμ)
  nlinarith [norm_nonneg (f - z), norm_nonneg (f - p)]

end Path

/-- Large positive parameters converge in norm to the shared metric projector
onto the nonempty minimizer set. -/
theorem proximalMap_largeParameter_limit : LargeParameterSpec.LargeParameterLimit.{u} := by
  intro H _ _ _ φ hp hc hl hne
  obtain ⟨_, hclosed, hcM⟩ := minimizer_set_geometry H φ hp hc hl hne
  refine ⟨hclosed, hcM, ?_⟩
  intro f
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (proximalPath_cauchy φ hp hc hl f hne)
  have hzM := proximalPath_limit_mem φ hp hc hl f hne z hz
  have hzmin := proximalPath_limit_nearest φ hp hc hl f z hz
  have huniq := Hilbert.Projection.existsUnique_nearestPoint ℝ H
    (argmin H φ) hne hclosed hcM f
  have hproj := Hilbert.Projection.convexProjection_spec ℝ H
    (argmin H φ) hne hclosed hcM f
  have heq := huniq.unique (show z ∈ argmin H φ ∧
    ∀ p ∈ argmin H φ, ‖f - z‖ ≤ ‖f - p‖ from ⟨hzM, hzmin⟩) hproj
  rw [heq] at hz
  exact hz

end ExpandedFA.Proximal
