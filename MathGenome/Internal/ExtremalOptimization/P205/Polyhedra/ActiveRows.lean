import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.ActiveRows
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
namespace P205.Polyhedra

theorem convex_polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Convex ℝ (polyhedron A b) := by
  intro x hx y hy a c ha hc hac i
  change rowCovector A i (a • x + c • y) ≤ b i
  rw [map_add, map_smul, map_smul]
  change a * rowCovector A i x + c * rowCovector A i y ≤ b i
  calc
    _ ≤ a * b i + c * b i := add_le_add
      (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

/-- Active covectors span precisely when their common kernel is trivial. -/
theorem activeSpan_eq_top_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Coordinate n) :
    activeSpan A b x = ⊤ ↔
      ∀ d : Coordinate n, (∀ i ∈ activeRows A b x, rowCovector A i d = 0) → d = 0 := by
  have mem_iff (d : Coordinate n) : d ∈ (activeSpan A b x).dualCoannihilator ↔
      ∀ i ∈ activeRows A b x, rowCovector A i d = 0 := by
    change d ∈ (Submodule.span ℝ _).dualCoannihilator ↔ _
    rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
    simp
  constructor
  · intro h d hd
    have hm := (mem_iff d).mpr hd
    rw [h, Submodule.dualCoannihilator_top] at hm
    exact hm
  · intro h
    have hb : (activeSpan A b x).dualCoannihilator = ⊥ := by
      apply eq_bot_iff.mpr
      intro d hd
      exact h d ((mem_iff d).mp hd)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := activeSpan A b x), hb,
      Submodule.dualAnnihilator_bot]

/-- A direction annihilating the active rows permits small steps of either sign. -/
theorem feasible_small_steps {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x d : Coordinate n) (hx : x ∈ polyhedron A b)
    (hd : ∀ i ∈ activeRows A b x, rowCovector A i d = 0) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε → x + t • d ∈ polyhedron A b := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ polyhedron A b := by
    change ∀ᶠ t : ℝ in 𝓝 0, ∀ i, rowCovector A i (x + t • d) ≤ b i
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ activeRows A b x
    · filter_upwards [] with t
      simpa [map_add, map_smul, hd i hi] using hx i
    · have hlt : rowCovector A i x < b i :=
        lt_of_le_of_ne (hx i) hi
      have hc : Continuous (fun t : ℝ => rowCovector A i x + t * rowCovector A i d) := by
        fun_prop
      have hc0 : ContinuousAt (fun t : ℝ => rowCovector A i x + t * rowCovector A i d) 0 :=
        hc.continuousAt
      have he := hc0.tendsto.eventually_lt_const (by simpa using hlt)
      filter_upwards [he] with t ht
      simpa [map_add, map_smul] using ht.le
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun t ht => he ?_⟩
  simpa [Real.dist_eq] using ht

/-- The midpoint test forces the active common kernel to be zero. -/
theorem MidpointExtreme.kernel_trivial {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} {x : Coordinate n} (h : MidpointExtreme (polyhedron A b) x) :
    ∀ d : Coordinate n, (∀ i ∈ activeRows A b x, rowCovector A i d = 0) → d = 0 := by
  intro d hd
  obtain ⟨ε, hε, he⟩ := feasible_small_steps A b x d h.1 hd
  have hp := he (ε / 2) (by rw [abs_of_pos (by positivity)]; linarith)
  have hn := he (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  have hm : (1 / 2 : ℝ) • ((x + (ε / 2) • d) + (x + (-(ε / 2)) • d)) = x := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have heq := h.2 _ hp _ hn hm
  have hz : (ε / 2) • d = 0 := by
    have h2 : (ε / 2) • d = -(ε / 2) • d := add_left_cancel heq
    ext j
    have hj := congrFun h2 j
    simp only [Pi.smul_apply, smul_eq_mul] at hj ⊢
    change ε / 2 * d j = 0
    nlinarith
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt (by positivity))

/-- A trivial active common kernel rules out all strict convex decompositions. -/
theorem vertex_of_kernel_trivial {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Coordinate n) (hx : x ∈ polyhedron A b)
    (hk : ∀ d : Coordinate n, (∀ i ∈ activeRows A b x, rowCovector A i d = 0) → d = 0) :
    IsVertex A b x := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a, c, ha, hc, hac, heq⟩ := hseg
  have hd : y - x = 0 := hk (y - x) (by
    intro i hi
    have hactive : rowCovector A i x = b i := hi
    have he := congrArg (rowCovector A i) heq
    simp only [map_add, map_smul, smul_eq_mul] at he
    rw [map_sub]
    have hyy := hy i
    have hzz := hz i
    have hbound := mul_le_mul_of_nonneg_left hzz hc.le
    have hab : a * b i + c * b i = b i := by rw [← add_mul, hac, one_mul]
    have hp : a * (b i - rowCovector A i y) ≤ 0 := by nlinarith
    have hzero : a * (b i - rowCovector A i y) = 0 :=
      le_antisymm hp (mul_nonneg ha.le (sub_nonneg.mpr hyy))
    have hrow := (mul_eq_zero.mp hzero).resolve_left ha.ne'
    linarith)
  exact sub_eq_zero.mp hd

/-- Standard extremality implies the paper's midpoint test. -/
theorem midpointExtreme_of_vertex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Coordinate n) (h : IsVertex A b x) :
    MidpointExtreme (polyhedron A b) x := by
  refine ⟨h.1, ?_⟩
  intro y hy z hz heq
  have hs : x ∈ openSegment ℝ y z := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    simpa only [← smul_add] using heq
  have hyx := h.2 hy hz hs
  have hzx := h.2 hz hy (by rwa [openSegment_symm])
  exact hyx.trans hzx.symm

theorem midpoint_iff_vertex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Coordinate n) :
    MidpointExtreme (polyhedron A b) x ↔ IsVertex A b x := by
  exact ⟨fun h => vertex_of_kernel_trivial A b x h.1 h.kernel_trivial,
    midpointExtreme_of_vertex A b x⟩

theorem vertex_iff_activeSpan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Coordinate n) (hx : x ∈ polyhedron A b) :
    IsVertex A b x ↔ activeSpan A b x = ⊤ := by
  rw [activeSpan_eq_top_iff]
  exact ⟨fun h => (midpointExtreme_of_vertex A b x h).kernel_trivial,
    vertex_of_kernel_trivial A b x hx⟩

end P205.Polyhedra
