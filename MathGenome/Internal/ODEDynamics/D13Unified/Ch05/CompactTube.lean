import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalLipschitz
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.CompactTube
import Mathlib.Tactic.Linarith

/-! Compact tubes from local product control, using compactness of the
reference time interval. No continuation or solution-dependence theorem is
used in this construction. -/

noncomputable section
open Set Metric Filter Topology

namespace D13Unified

/-- A locally available estimate, monotone under decreasing its radius and
increasing its bound, admits a uniform radius and bound on a compact set. -/
theorem IsCompact.exists_uniform_radius_bound {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (R : ℝ → ℝ → X → Prop)
    (hmono : ∀ {r r' L L' : ℝ} {t : X},
      0 < r' → r' ≤ r → L ≤ L' → R r L t → R r' L' t)
    (hloc : ∀ t ∈ K, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ᶠ s in 𝓝[K] t, R r L s) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ t ∈ K, R r L t := by
  let Q : Set X → Prop := fun S =>
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ t ∈ S, R r L t
  apply hK.induction_on (p := Q)
  · exact ⟨1, 0, zero_lt_one, le_rfl, by simp⟩
  · intro S T hST hT
    obtain ⟨r, L, hr, hL, h⟩ := hT
    exact ⟨r, L, hr, hL, fun t ht => h t (hST ht)⟩
  · intro S T hS hT
    obtain ⟨r, L, hr, hL, hs⟩ := hS
    obtain ⟨r', L', hr', hL', ht⟩ := hT
    refine ⟨min r r', max L L', lt_min hr hr', hL.trans (le_max_left _ _), ?_⟩
    intro t hmem
    rcases hmem with hmem | hmem
    · exact hmono (lt_min hr hr') (min_le_left _ _) (le_max_left _ _) (hs t hmem)
    · exact hmono (lt_min hr hr') (min_le_right _ _) (le_max_right _ _) (ht t hmem)
  · intro t ht
    obtain ⟨r, L, hr, hL, h⟩ := hloc t ht
    exact ⟨{s | R r L s}, h, r, L, hr, hL, fun _ hs => hs⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation of the compact product by the continuous reference graph
proves compactness of the closed tube, even for degenerate time intervals. -/
theorem isCompact_closedTube [FiniteDimensional ℝ E] {x : ℝ → E} {a b ρ : ℝ}
    (hx : ContinuousOn x (Icc a b)) : IsCompact (closedTube x a b ρ) := by
  have heq : closedTube x a b ρ =
      (fun q : ℝ × E => (q.1, x q.1 + q.2)) '' (Icc a b ×ˢ closedBall (0 : E) ρ) := by
    ext q
    constructor
    · rintro ⟨ht, hz⟩
      refine ⟨(q.1, q.2 - x q.1), ⟨ht, ?_⟩, ?_⟩
      · simpa [mem_closedBall, dist_eq_norm] using hz
      · simp
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      exact ⟨ht, by simpa [mem_closedBall, dist_eq_norm] using hv⟩
  rw [heq]
  apply (isCompact_Icc.prod (isCompact_closedBall (0 : E) ρ)).image_of_continuousOn
  exact continuousOn_fst.prodMk
    ((hx.comp continuousOn_fst (fun _ h => h.1)).add continuousOn_snd)

/-- Local state Lipschitz control gives uniform control around any continuous
compact reference graph; the curve need not itself solve the equation. -/
theorem ODE.compact_graph_tube [FiniteDimensional ℝ E] (F : ODE E)
    (hF : F.LocallyLipschitzInState) {K : Set ℝ} (hK : IsCompact K)
    {x : ℝ → E} (hx : ContinuousOn x K)
    (hgraph : ∀ t ∈ K, (t, x t) ∈ F.domain) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧
      (∀ t ∈ K, ∀ z ∈ closedBall (x t) ρ, (t, z) ∈ F.domain) ∧
      ∀ t ∈ K, ∀ z ∈ closedBall (x t) ρ, ∀ w ∈ closedBall (x t) ρ,
        ‖F.eval t z - F.eval t w‖ ≤ L * ‖z - w‖ := by
  let R : ℝ → ℝ → ℝ → Prop := fun r L t =>
    (∀ z ∈ closedBall (x t) r, (t, z) ∈ F.domain) ∧
    ∀ z ∈ closedBall (x t) r, ∀ w ∈ closedBall (x t) r,
      ‖F.eval t z - F.eval t w‖ ≤ L * ‖z - w‖
  obtain ⟨ρ, L, hρ, hL, h⟩ := IsCompact.exists_uniform_radius_bound hK R
    (by
      intro r r' L L' t _ hr hLL h
      exact ⟨fun z hz => h.1 z (closedBall_subset_closedBall hr hz),
        fun z hz w hw => (h.2 z (closedBall_subset_closedBall hr hz)
          w (closedBall_subset_closedBall hr hw)).trans
            (mul_le_mul_of_nonneg_right hLL (norm_nonneg _))⟩)
    (by
      intro s hs
      obtain ⟨α, β, L, hα, hβ, hL, hdom, hbound⟩ := hF s (x s) (hgraph s hs)
      have htnear : ∀ᶠ t in 𝓝[K] s, t ∈ ball s α :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hα)
      have hxnear : ∀ᶠ t in 𝓝[K] s, x t ∈ ball (x s) (β / 2) :=
        (hx s hs).eventually (ball_mem_nhds (x s) (half_pos hβ))
      refine ⟨β / 2, L, half_pos hβ, hL, ?_⟩
      filter_upwards [htnear, hxnear] with t ht hxt
      have hsub : closedBall (x t) (β / 2) ⊆ ball (x s) β :=
        closedBall_subset_ball' (by have := mem_ball.mp hxt; linarith)
      exact ⟨fun z hz => hdom ⟨ht, hsub hz⟩,
        fun z hz w hw => hbound t ht z (hsub hz) w (hsub hw)⟩)
  exact ⟨ρ, L, hρ, hL, fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩

/-- The compact tube assertion of d13:05:common-interval, with the actual
reference solution and its open interval retained. -/
theorem compact_solution_tube :
    Specs.D13Unified.Ch05.CompactTube.compactSolutionTubeExpected := by
  intro E _ _ _ F hF I x hx a b _hab hI
  obtain ⟨ρ, L, hρ, hL, hdom, hbound⟩ :=
    F.compact_graph_tube hF isCompact_Icc (hx.1.continuousOn.mono hI)
      (fun t ht => hx.2.1 t (hI ht))
  refine ⟨ρ, L, hρ, hL, isCompact_closedTube (hx.1.continuousOn.mono hI), ?_, hbound⟩
  intro q hq
  exact hdom q.1 hq.1 q.2 (by simpa [mem_closedBall, dist_eq_norm] using hq.2)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Uniform parameter-local state control along a compact reference graph.
The same radius can be used for the state and parameter; no control of
parameter differences is assumed. -/
theorem ParameterODE.compact_graph_tube (F : ParameterODE E P)
    (hF : F.LocallyLipschitzInState) {K : Set ℝ} (hK : IsCompact K)
    {x : ℝ → E} {p₀ : P} (hx : ContinuousOn x K)
    (hgraph : ∀ t ∈ K, ((t, x t), p₀) ∈ F.domain) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧
      (∀ t ∈ K, ∀ z ∈ closedBall (x t) ρ, ∀ p ∈ closedBall p₀ ρ,
        ((t, z), p) ∈ F.domain) ∧
      ∀ t ∈ K, ∀ z ∈ closedBall (x t) ρ, ∀ w ∈ closedBall (x t) ρ,
      ∀ p ∈ closedBall p₀ ρ,
        ‖F.eval t z p - F.eval t w p‖ ≤ L * ‖z - w‖ := by
  let R : ℝ → ℝ → ℝ → Prop := fun r L t =>
    (∀ z ∈ closedBall (x t) r, ∀ p ∈ closedBall p₀ r, ((t, z), p) ∈ F.domain) ∧
    ∀ z ∈ closedBall (x t) r, ∀ w ∈ closedBall (x t) r, ∀ p ∈ closedBall p₀ r,
      ‖F.eval t z p - F.eval t w p‖ ≤ L * ‖z - w‖
  obtain ⟨ρ, L, hρ, hL, h⟩ := IsCompact.exists_uniform_radius_bound hK R
    (by
      intro r r' L L' t _ hr hLL h
      exact ⟨fun z hz p hp => h.1 z (closedBall_subset_closedBall hr hz)
          p (closedBall_subset_closedBall hr hp),
        fun z hz w hw p hp =>
          (h.2 z (closedBall_subset_closedBall hr hz)
            w (closedBall_subset_closedBall hr hw) p (closedBall_subset_closedBall hr hp)).trans
            (mul_le_mul_of_nonneg_right hLL (norm_nonneg _))⟩)
    (by
      intro s hs
      obtain ⟨α, β, γ, L, hα, hβ, hγ, hL, hdom, hbound⟩ :=
        hF s (x s) p₀ (hgraph s hs)
      have htnear : ∀ᶠ t in 𝓝[K] s, t ∈ ball s α :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hα)
      have hxnear : ∀ᶠ t in 𝓝[K] s, x t ∈ ball (x s) (β / 2) :=
        (hx s hs).eventually (ball_mem_nhds (x s) (half_pos hβ))
      refine ⟨min (β / 2) (γ / 2), L, lt_min (half_pos hβ) (half_pos hγ), hL, ?_⟩
      filter_upwards [htnear, hxnear] with t ht hxt
      have hsub : closedBall (x t) (min (β / 2) (γ / 2)) ⊆ ball (x s) β := by
        apply closedBall_subset_ball'
        have := mem_ball.mp hxt
        have := min_le_left (β / 2) (γ / 2)
        linarith
      have hpar : closedBall p₀ (min (β / 2) (γ / 2)) ⊆ ball p₀ γ := by
        apply closedBall_subset_ball
        have := min_le_right (β / 2) (γ / 2)
        linarith
      exact ⟨fun z hz p hp => hdom ⟨⟨ht, hsub hz⟩, hpar hp⟩,
        fun z hz w hw p hp => hbound p (hpar hp) t ht z (hsub hz) w (hsub hw)⟩)
  exact ⟨ρ, L, hρ, hL, fun t ht => (h t ht).1, fun t ht => (h t ht).2⟩

/-- The compact product tube used in d13:05:openness, including compactness,
containment in the joint domain, and state Lipschitz control at every nearby
parameter on every closed tube slice. -/
theorem compact_parameter_solution_tube :
    Specs.D13Unified.Ch05.CompactTube.compactParameterSolutionTubeExpected := by
  intro E _ _ _ P _ _ _ F hF p₀ I x hx a b _hab hI
  obtain ⟨ρ, L, hρ, hL, hdom, hbound⟩ :=
    F.compact_graph_tube hF isCompact_Icc (hx.1.continuousOn.mono hI)
      (fun t ht => hx.2.1 t (hI ht))
  refine ⟨ρ, ρ, L, hρ, hρ, hL,
    (isCompact_closedTube (hx.1.continuousOn.mono hI)).prod (isCompact_closedBall p₀ ρ),
    ?_, hbound⟩
  intro q hq
  exact hdom q.1.1 hq.1.1 q.1.2
    (by simpa [mem_closedBall, dist_eq_norm] using hq.1.2) q.2 hq.2

end D13Unified
