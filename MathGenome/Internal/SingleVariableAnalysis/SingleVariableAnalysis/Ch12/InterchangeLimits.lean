import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Cauchy
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.InterchangeLimits
import Batteries.Tactic.OpenPrivate

/-!
# Interchanging a sequence limit and a domain limit

K03.12.interchange_limits, paper.tex:1236–1244. Transfer the uniform Cauchy
estimate to the domain limits, using closedness of a distance bound. Scalar
completeness is the proved upstream sequence Cauchy criterion. Then a three-term
triangle inequality proves the domain limit. A nontrivial approach ensures
uniqueness of both outer limits. The local version uses one fixed approach
region; functions and their limits need no bounds or continuity.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology
open private approach_isBasis from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Cauchy

private theorem interchange_on_filter {X K : Type*} [MetricSpace K]
    (scalar_complete : ∀ a : ℕ → K,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (a n) (a m) < ε) →
        ∃ B, Tendsto a atTop (𝓝 B))
    (l : Filter X) [l.NeBot] (F : ℕ → X → K) (f : X → K) (b : ℕ → K)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ᶠ x in l, dist (F n x) (f x) < ε)
    (hB : ∀ n, Tendsto (F n) l (𝓝 (b n))) :
    ∃ B, Tendsto b atTop (𝓝 B) ∧ Tendsto f l (𝓝 B) ∧
      ∀ B₁ B₂, Tendsto f l (𝓝 B₁) → Tendsto b atTop (𝓝 B₂) → B₁ = B₂ := by
  have hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, dist (b n) (b m) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hU (ε / 4) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hd : dist (b n) (b m) ≤ ε / 2 := by
      apply le_of_tendsto ((hB n).dist (hB m))
      filter_upwards [hN n hn, hN m hm] with x hx hy
      have ht := dist_triangle_right (F n x) (F m x) (f x)
      linarith
    exact hd.trans_lt (half_lt_self hε)
  obtain ⟨B, hb⟩ := scalar_complete b hc
  have hf : Tendsto f l (𝓝 B) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hthird : 0 < ε / 3 := by linarith
    obtain ⟨N, hN⟩ := hU (ε / 3) hthird
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hb (ε / 3) hthird
    let n := max N M
    have hn : dist (b n) B < ε / 3 := hM n (le_max_right _ _)
    have hnb : ∀ᶠ x in l, dist (F n x) (b n) < ε / 3 :=
      Metric.tendsto_nhds.mp (hB n) _ hthird
    filter_upwards [hN n (le_max_left _ _), hnb] with x hx hy
    have ht₁ := dist_triangle (f x) (F n x) B
    have ht₂ := dist_triangle (F n x) (b n) B
    rw [dist_comm (f x) (F n x)] at ht₁
    linarith
  refine ⟨B, hb, hf, ?_⟩
  intro B₁ B₂ h₁ h₂
  exact (tendsto_nhds_unique h₁ hf).trans (tendsto_nhds_unique hb h₂)

private theorem interchange_on_approach {K : Type*} [MetricSpace K]
    (scalar_complete : ∀ a : ℕ → K,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (a n) (a m) < ε) →
        ∃ B, Tendsto a atTop (𝓝 B))
    (E : Set ℝ) (q : RealApproach) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (F : ℕ → ℝ → K) (f : ℝ → K) (b : ℕ → K)
    (ha : ApproachNontrivial E q)
    (hU : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ E ∩ ApproachRegion q r₀, dist (F n x) (f x) < ε)
    (hB : ∀ n, FiniteApproachLimit (F n) E q (b n)) :
    ∃ B, Tendsto b atTop (𝓝 B) ∧ FiniteApproachLimit f E q B ∧
      ∀ B₁ B₂, FiniteApproachLimit f E q B₁ →
        Tendsto b atTop (𝓝 B₂) → B₁ = B₂ := by
  let basis := approach_isBasis E q
  have : basis.filter.NeBot := basis.hasBasis.neBot_iff.mpr (fun {r} hr => by
    obtain ⟨x, hx, hxr⟩ := ha r hr
    exact ⟨x, hx, hxr⟩)
  have hlim (g : ℝ → K) (B : K) :
      FiniteApproachLimit g E q B ↔ Tendsto g basis.filter (𝓝 B) := by
    rw [basis.hasBasis.tendsto_iff Metric.nhds_basis_ball]
    simp only [FiniteApproachLimit, ha, true_and, ApproachEventually,
      Set.mem_inter_iff, Metric.mem_ball, and_imp]
  have hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ᶠ x in basis.filter, dist (F n x) (f x) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hU ε hε
    refine ⟨N, fun n hn => ?_⟩
    exact basis.hasBasis.mem_iff.mpr ⟨r₀, hr₀, hN n hn⟩
  obtain ⟨B, hb, hf, heq⟩ := interchange_on_filter scalar_complete basis.filter F f b
    hu (fun n => (hlim (F n) (b n)).mp (hB n))
  exact ⟨B, hb, (hlim f B).mpr hf,
    fun B₁ B₂ h₁ h₂ => heq B₁ B₂ ((hlim f B₁).mp h₁) h₂⟩

private theorem real_scalar_complete (a : ℕ → ℝ)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (a n) (a m) < ε) :
    ∃ B, Tendsto a atTop (𝓝 B) := by
  obtain ⟨B, hB⟩ := (real_cauchy_criterion a).mpr (by simpa only [Real.dist_eq] using hc)
  exact ⟨B, (realSequenceConverges_iff a B).mp hB⟩

private theorem complex_scalar_complete (a : ℕ → ℂ)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (a n) (a m) < ε) :
    ∃ B, Tendsto a atTop (𝓝 B) := by
  obtain ⟨B, hB⟩ := (complex_cauchy_criterion a).mpr (by simpa only [dist_eq_norm] using hc)
  exact ⟨B, (complexSequenceConverges_iff a B).mp hB⟩

theorem real_interchange_limits_on_approach_neighborhood :
  ∀ (E : Set ℝ) (q : RealApproach) (r₀ : ℝ), 0 < r₀ →
    ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (b : ℕ → ℝ),
      ApproachNontrivial E q →
      RealUniformConverges
        (fun n (x : ↥(E ∩ ApproachRegion q r₀)) => F n x) (fun x => f x) →
      (∀ n, FiniteApproachLimit (F n) E q (b n)) →
      ∃ B : ℝ, RealSequenceConverges b B ∧
        FiniteApproachLimit f E q B ∧
        ∀ B₁ B₂ : ℝ, FiniteApproachLimit f E q B₁ →
          RealSequenceConverges b B₂ → B₁ = B₂ := by
  intro E q r₀ hr₀ F f b ha hU hB
  have hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ E ∩ ApproachRegion q r₀, dist (F n x) (f x) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hU ε hε
    refine ⟨N, fun n hn x hx => ?_⟩
    simpa only [Real.dist_eq] using hN n hn ⟨x, hx⟩
  obtain ⟨B, hb, hf, heq⟩ := interchange_on_approach real_scalar_complete
    E q r₀ hr₀ F f b ha hu hB
  exact ⟨B, (realSequenceConverges_iff b B).mpr hb, hf,
    fun B₁ B₂ h₁ h₂ => heq B₁ B₂ h₁ ((realSequenceConverges_iff b B₂).mp h₂)⟩

theorem real_interchange_limits :
  ∀ (E : Set ℝ) (q : RealApproach),
    ∀ (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (b : ℕ → ℝ),
      ApproachNontrivial E q →
      RealUniformConverges
        (fun n (x : E) => F n x) (fun x => f x) →
      (∀ n, FiniteApproachLimit (F n) E q (b n)) →
      ∃ B : ℝ, RealSequenceConverges b B ∧
        FiniteApproachLimit f E q B ∧
        ∀ B₁ B₂ : ℝ, FiniteApproachLimit f E q B₁ →
          RealSequenceConverges b B₂ → B₁ = B₂ := by
  intro E q F f b ha hU hB
  apply real_interchange_limits_on_approach_neighborhood
    E q 1 zero_lt_one F f b ha ?_ hB
  intro ε hε
  obtain ⟨N, hN⟩ := hU ε hε
  exact ⟨N, fun n hn x => hN n hn ⟨x.val, x.property.1⟩⟩

theorem complex_interchange_limits_on_approach_neighborhood :
  ∀ (E : Set ℝ) (q : RealApproach) (r₀ : ℝ), 0 < r₀ →
    ∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (b : ℕ → ℂ),
      ApproachNontrivial E q →
      ComplexUniformConverges
        (fun n (x : ↥(E ∩ ApproachRegion q r₀)) => F n x) (fun x => f x) →
      (∀ n, FiniteApproachLimit (F n) E q (b n)) →
      ∃ B : ℂ, ComplexSequenceConverges b B ∧
        FiniteApproachLimit f E q B ∧
        ∀ B₁ B₂ : ℂ, FiniteApproachLimit f E q B₁ →
          ComplexSequenceConverges b B₂ → B₁ = B₂ := by
  intro E q r₀ hr₀ F f b ha hU hB
  have hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      ∀ x ∈ E ∩ ApproachRegion q r₀, dist (F n x) (f x) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hU ε hε
    refine ⟨N, fun n hn x hx => ?_⟩
    simpa only [dist_eq_norm] using hN n hn ⟨x, hx⟩
  obtain ⟨B, hb, hf, heq⟩ := interchange_on_approach complex_scalar_complete
    E q r₀ hr₀ F f b ha hu hB
  exact ⟨B, (complexSequenceConverges_iff b B).mpr hb, hf,
    fun B₁ B₂ h₁ h₂ => heq B₁ B₂ h₁ ((complexSequenceConverges_iff b B₂).mp h₂)⟩

theorem complex_interchange_limits :
  ∀ (E : Set ℝ) (q : RealApproach),
    ∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (b : ℕ → ℂ),
      ApproachNontrivial E q →
      ComplexUniformConverges
        (fun n (x : E) => F n x) (fun x => f x) →
      (∀ n, FiniteApproachLimit (F n) E q (b n)) →
      ∃ B : ℂ, ComplexSequenceConverges b B ∧
        FiniteApproachLimit f E q B ∧
        ∀ B₁ B₂ : ℂ, FiniteApproachLimit f E q B₁ →
          ComplexSequenceConverges b B₂ → B₁ = B₂ := by
  intro E q F f b ha hU hB
  apply complex_interchange_limits_on_approach_neighborhood
    E q 1 zero_lt_one F f b ha ?_ hB
  intro ε hε
  obtain ⟨N, hN⟩ := hU ε hε
  exact ⟨N, fun n hn x => hN n hn ⟨x.val, x.property.1⟩⟩

end SingleVariableAnalysis
