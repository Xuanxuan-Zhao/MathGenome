import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.NonlinearYosidaEvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.MonotoneGraphResolvents
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! Global regularized flows and the nonlinear Yosida evolution on real Hilbert
spaces. Weak compactness and graph closedness are applied in Bochner L², and
strong derivatives follow from the Bochner Lebesgue differentiation theorem. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal
namespace ExpandedFA.Evolution.NonlinearYosidaEvolution
universe u v
open MonotoneGraphResolvents

/-- Picard existence on an interval whose length depends only on the global
Lipschitz constant, not on the initial point. This is the local ingredient for
the global continuation construction below. -/
theorem local_solution_of_lipschitz {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → E) (L : ℝ≥0)
    (hf : LipschitzWith L f) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc (-((L : ℝ) + 1)⁻¹) ((L : ℝ) + 1)⁻¹,
        HasDerivWithinAt u (f (u t))
          (Icc (-((L : ℝ) + 1)⁻¹) ((L : ℝ) + 1)⁻¹) t := by
  let a : ℝ≥0 := ‖f x‖₊ + 1
  let B : ℝ≥0 := (L + 1) * a
  let δ : ℝ := ((L : ℝ) + 1)⁻¹
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hδ : 0 < δ := inv_pos.mpr hL
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hpic : IsPicardLindelof (fun (_ : ℝ) => f) ⟨0, hzero⟩ x a 0 B L := by
    constructor
    · intro t ht
      exact hf.lipschitzOnWith
    · intro y hy
      exact continuousOn_const
    · intro t ht y hy
      have hy' : ‖y - x‖ ≤ (a : ℝ) := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
      have hb := (norm_add_le (f y - f x) (f x))
      rw [sub_add_cancel] at hb
      have hlip := hf.norm_sub_le y x
      have hmul := mul_le_mul_of_nonneg_left hy' L.coe_nonneg
      change ‖f y‖ ≤ ((L : ℝ) + 1) * (‖f x‖ + 1)
      dsimp [a] at hmul
      nlinarith
    · change (B : ℝ) * max (δ - 0) (0 - -δ) ≤ (a : ℝ) - 0
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      change (((L : ℝ) + 1) * (a : ℝ)) * ((L : ℝ) + 1)⁻¹ ≤ (a : ℝ)
      rw [mul_right_comm, mul_inv_cancel₀ hL.ne', one_mul]
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Classical trajectories on overlapping open intervals can be glued. Uniqueness
on the intersection makes the piecewise function locally equal to either
trajectory, including at the endpoints of the first interval. -/
theorem glue_classical_solutions {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) {L : ℝ≥0} (hf : LipschitzWith L f)
    {u v : ℝ → E} {a b c d t₀ : ℝ}
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ Ioo c d, HasDerivAt v (f (v t)) t)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (heq : u t₀ = v t₀) :
    ∀ t ∈ Ioo a b ∪ Ioo c d,
      HasDerivAt ((Ioo a b).piecewise u v)
        (f ((Ioo a b).piecewise u v t)) t := by
  classical
  have hequiv : EqOn u v (Ioo a b ∩ Ioo c d) := by
    rw [Ioo_inter_Ioo]
    exact ODE_solution_unique_of_mem_Ioo
      (s := fun _ => univ) (fun _ _ => hf.lipschitzOnWith)
      ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩
      (fun t ht => ⟨hu t ⟨(le_max_left _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_left _ _)⟩, mem_univ _⟩)
      (fun t ht => ⟨hv t ⟨(le_max_right _ _).trans_lt ht.1,
        ht.2.trans_le (min_le_right _ _)⟩, mem_univ _⟩) heq
  intro t ht
  by_cases h : t ∈ Ioo a b
  · have he : ((Ioo a b).piecewise u v) =ᶠ[𝓝 t] u := by
      filter_upwards [Ioo_mem_nhds h.1 h.2] with r hr
      exact piecewise_eq_of_mem _ _ _ hr
    rw [he.eq_of_nhds]
    exact (hu t h).congr_of_eventuallyEq he
  · have ht' : t ∈ Ioo c d := ht.resolve_left h
    have he : ((Ioo a b).piecewise u v) =ᶠ[𝓝 t] v := by
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with r hr
      by_cases hr' : r ∈ Ioo a b
      · rw [piecewise_eq_of_mem _ _ _ hr']
        exact hequiv ⟨hr', hr⟩
      · exact piecewise_eq_of_notMem _ _ _ hr'
    rw [he.eq_of_nhds]
    exact (hv t ht').congr_of_eventuallyEq he

/-- A local existence time independent of the initial point implies global
existence for an autonomous Lipschitz equation. Only interval uniqueness,
not differentiability of the vector field, is needed in the patching step. -/
theorem global_solution_of_uniform_local {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) {L : ℝ≥0} (hf : LipschitzWith L f)
    {ε : ℝ} (hε : 0 < ε)
    (hloc : ∀ x : E, ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt u (f (u t)) t) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f (u t)) t := by
  classical
  have hext {r : ℝ} (hr : ε / 2 ≤ r) {u : ℝ → E}
      (hu₀ : u 0 = x)
      (hu : ∀ t ∈ Ioo (-r) r, HasDerivAt u (f (u t)) t) :
      ∃ w : ℝ → E, w 0 = x ∧
        ∀ t ∈ Ioo (-(r + ε / 2)) (r + ε / 2),
          HasDerivAt w (f (w t)) t := by
    let q := r - ε / 4
    have hq : 0 < q := by dsimp [q]; linarith
    have hqr : q < r := by dsimp [q]; linarith
    obtain ⟨v₁, hv₁₀, hv₁⟩ := hloc (u (-q))
    obtain ⟨v₂, hv₂₀, hv₂⟩ := hloc (u q)
    let w₁ : ℝ → E := fun t => v₁ (t + q)
    let w₂ : ℝ → E := fun t => v₂ (t - q)
    have hw₁ : ∀ t ∈ Ioo (-q - ε) (-q + ε), HasDerivAt w₁ (f (w₁ t)) t := by
      intro t ht
      simpa only [w₁, Function.comp_def, id_eq, one_smul] using
        (hv₁ (t + q) ⟨by linarith [ht.1], by linarith [ht.2]⟩).scomp t
          ((hasDerivAt_id t).add_const q)
    have hw₂ : ∀ t ∈ Ioo (q - ε) (q + ε), HasDerivAt w₂ (f (w₂ t)) t := by
      intro t ht
      simpa only [w₂, Function.comp_def, id_eq, one_smul] using
        (hv₂ (t - q) ⟨by linarith [ht.1], by linarith [ht.2]⟩).scomp t
          ((hasDerivAt_id t).sub_const q)
    let z := (Ioo (-r) r).piecewise u w₁
    have hz : ∀ t ∈ Ioo (-(r + ε / 2)) r, HasDerivAt z (f (z t)) t := by
      apply fun t ht => glue_classical_solutions f hf hu hw₁
        (t₀ := -q) ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
        (by simpa [w₁] using hv₁₀.symm) t ?_
      by_cases ht' : -r < t
      · exact Or.inl ⟨ht', ht.2⟩
      · exact Or.inr ⟨by dsimp [q] at *; linarith [ht.1], by linarith⟩
    let w := (Ioo (-(r + ε / 2)) r).piecewise z w₂
    refine ⟨w, ?_, ?_⟩
    · dsimp [w, z]
      rw [piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Ioo (-(r + ε / 2)) r from
        ⟨by linarith, by linarith⟩),
        piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Ioo (-r) r from
          ⟨by linarith, by linarith⟩), hu₀]
    · intro t ht
      apply glue_classical_solutions f hf hz hw₂ (t₀ := q)
        ⟨⟨by linarith, hqr⟩, ⟨by linarith, by linarith⟩⟩ ?_ t ?_
      · dsimp [z]
        rw [piecewise_eq_of_mem _ _ _ (show q ∈ Ioo (-r) r from ⟨by linarith, hqr⟩)]
        simpa [w₂] using hv₂₀.symm
      · by_cases ht' : t < r
        · exact Or.inl ⟨ht.1, ht'⟩
        · exact Or.inr ⟨by dsimp [q] at *; linarith, by dsimp [q] at *; linarith [ht.2]⟩
  have hn (n : ℕ) : ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Ioo (-((n + 1 : ℕ) : ℝ) * (ε / 2)) (((n + 1 : ℕ) : ℝ) * (ε / 2)),
        HasDerivAt u (f (u t)) t := by
    induction n with
    | zero =>
      obtain ⟨u, hu₀, hu⟩ := hloc x
      refine ⟨u, hu₀, fun t ht => hu t ?_⟩
      simp only [neg_mul] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    | succ n ih =>
      obtain ⟨u, hu₀, hu⟩ := ih
      have hr : ε / 2 ≤ ((n + 1 : ℕ) : ℝ) * (ε / 2) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith
      have h := hext hr hu₀ (by simpa only [neg_mul] using hu)
      convert h using 1 <;> push_cast
      <;> ring_nf
  have hfinite (a : ℝ) : ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Ioo (-a) a, HasDerivAt u (f (u t)) t := by
    obtain ⟨n, hn'⟩ := exists_nat_gt (a / (ε / 2))
    have ha : a < ((n + 1 : ℕ) : ℝ) * (ε / 2) := by
      have h := (div_lt_iff₀ (by linarith : 0 < ε / 2)).mp hn'
      push_cast
      nlinarith
    obtain ⟨u, hu₀, hu⟩ := hn n
    exact ⟨u, hu₀, fun t ht => hu t ⟨by linarith [ht.1], ht.2.trans ha⟩⟩
  choose γ hγ₀ hγ using hfinite
  have hcompat {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      EqOn (γ a) (γ b) (Ioo (-a) a) := by
    exact ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
      (fun _ _ => hf.lipschitzOnWith) ⟨by linarith, ha⟩
      (fun t ht => ⟨hγ a t ht, mem_univ _⟩)
      (fun t ht => ⟨hγ b t ⟨by linarith [ht.1], ht.2.trans_le hab⟩, mem_univ _⟩)
      (by rw [hγ₀, hγ₀])
  let u := fun t => γ (|t| + 1) t
  have heq (a : ℝ) : EqOn u (γ a) (Ioo (-a) a) := by
    intro t ht
    by_cases h : |t| + 1 ≤ a
    · exact hcompat (by positivity) h (abs_lt.mp (by linarith : |t| < |t| + 1))
    · exact (hcompat (by linarith [ht.1, ht.2]) (le_of_not_ge h) ht).symm
  refine ⟨u, hγ₀ _, fun t => ?_⟩
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (by linarith)
  have he : u =ᶠ[𝓝 t] γ (|t| + 1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact heq (|t| + 1) hs
  rw [he.eq_of_nhds]
  exact (hγ (|t| + 1) t ht).congr_of_eventuallyEq he

/-- Global classical existence on all real times for a globally Lipschitz
vector field on any real Banach space. -/
theorem global_solution_of_lipschitz {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → E) (L : ℝ≥0)
    (hf : LipschitzWith L f) (x : E) :
    ∃ u : ℝ → E, u 0 = x ∧ ∀ t, HasDerivAt u (f (u t)) t := by
  apply global_solution_of_uniform_local f hf
    (ε := ((L : ℝ) + 1)⁻¹) (by positivity) _ x
  intro y
  obtain ⟨u, hu₀, hu⟩ := local_solution_of_lipschitz f L hf y
  exact ⟨u, hu₀, fun t ht => (hu t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)⟩

/-- Every positive Yosida parameter has a global classical flow. Choice is
made only after existence has been proved; nonpositive parameters are unused. -/
theorem approximation_family : Spec.ApproximationFamily.{u} := by
  classical
  intro H _ _ _ A hmono honto
  have hex (lam : ℝ) (hlam : 0 < lam) (x : H) :
      ∃ u : ℝ → H, Spec.GlobalApproximation A lam (honto lam hlam) x u := by
    exact global_solution_of_lipschitz
      (fun y => -yosida H A lam (honto lam hlam) y)
      ⟨lam⁻¹, inv_nonneg.mpr hlam.le⟩
      (yosida_lipschitz H A hmono lam hlam (honto lam hlam)).neg x
  let F : ℝ → H → ℝ → H := fun lam x =>
    if hlam : 0 < lam then (hex lam hlam x).choose else fun _ => x
  refine ⟨F, fun lam hlam x => ?_⟩
  simpa only [F, dite_eq_left hlam] using (hex lam hlam x).choose_spec

theorem initial_yosida_bound : Spec.InitialYosidaBound.{u} := by
  intro H _ _ A hmono lam hlam honto x a₀ hxa
  let a := yosida H A lam honto x
  let v := resolvent H A lam honto x
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hmono
    (yosida_graph H A lam hlam honto x) hxa
  change 0 ≤ inner ℝ (a - a₀) (v - x) at hm
  have hid : x = v + lam • a := resolvent_identity H A lam hlam honto x
  have hdiff : v - x = -lam • a := by rw [hid]; simp
  rw [hdiff, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hb : ‖a‖ ^ 2 ≤ ‖a‖ * ‖a₀‖ := by
    have hc := real_inner_le_norm a₀ a
    nlinarith
  exact le_of_sq_le_mul (norm_nonneg a₀) hb

/-- Squared distance decreases along any two classical trajectories of the
negative of a monotone map. No existence assertion is assumed in its proof. -/
theorem classical_contraction {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → H)
    (hm : ∀ x y, 0 ≤ inner ℝ (f x - f y) (x - y))
    (u v : ℝ → H) (hu : ∀ t, HasDerivAt u (-f (u t)) t)
    (hv : ∀ t, HasDerivAt v (-f (v t)) t) {s t : ℝ} (hst : s ≤ t) :
    ‖u t - v t‖ ≤ ‖u s - v s‖ := by
  have hd (r : ℝ) := ((hu r).sub (hv r)).norm_sq
  have hanti : Antitone (fun r => ‖u r - v r‖ ^ 2) := by
    apply antitone_of_hasDerivAt_nonpos hd
    intro r
    have h := hm (u r) (v r)
    rw [real_inner_comm] at h
    simp only [Pi.sub_apply, Pi.zero_apply, inner_sub_right, inner_neg_right] at h ⊢
    linarith
  have h := hanti hst
  nlinarith [norm_nonneg (u s - v s), norm_nonneg (u t - v t)]

theorem approximate_contraction : Spec.ApproximateContraction.{u} := by
  intro H _ _ A hmono lam hlam honto x y u v hu hv t ht
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H _).mp
    (yosida_monotone H A hmono lam hlam honto)
  have hc := classical_contraction (yosida H A lam honto)
    (fun p q => hm (show (p, yosida H A lam honto p) ∈
      {p : H × H | p.2 = yosida H A lam honto p.1} from rfl)
      (show (q, yosida H A lam honto q) ∈
      {p : H × H | p.2 = yosida H A lam honto p.1} from rfl)) u v hu.2 hv.2 ht
  simpa only [hu.1, hv.1] using hc

/-- Time translation and contraction control difference quotients before any
derivative of the Lipschitz vector field is considered. -/
theorem classical_speed_bound {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → H)
    (hm : ∀ x y, 0 ≤ inner ℝ (f x - f y) (x - y))
    (u : ℝ → H) (hu : ∀ t, HasDerivAt u (-f (u t)) t)
    {t : ℝ} (ht : 0 ≤ t) : ‖f (u t)‖ ≤ ‖f (u 0)‖ := by
  have hshift (h r : ℝ) :
      HasDerivAt (fun r => u (r + h)) (-f (u (r + h))) r := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hu (r + h)).scomp r ((hasDerivAt_id r).add_const h)
  have hdiff (h : ℝ) : ‖u (t + h) - u t‖ ≤ ‖u (0 + h) - u 0‖ :=
    classical_contraction f hm (fun r => u (r + h)) u (hshift h) hu ht
  have hlim := le_of_tendsto_of_tendsto'
    (hu t).tendsto_slope_zero.norm (hu 0).tendsto_slope_zero.norm (fun h =>
      show ‖h⁻¹ • (u (t + h) - u t)‖ ≤ ‖h⁻¹ • (u (0 + h) - u 0)‖ from by
        simpa only [norm_smul] using
          mul_le_mul_of_nonneg_left (hdiff h) (norm_nonneg h⁻¹))
  simpa only [norm_neg] using hlim

theorem approximate_speed_bound : Spec.ApproximateSpeedBound.{u} := by
  intro H _ _ A hmono lam hlam honto x a₀ u hxa hu t ht
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H _).mp
    (yosida_monotone H A hmono lam hlam honto)
  have hs := classical_speed_bound (yosida H A lam honto)
    (fun p q => hm (show (p, yosida H A lam honto p) ∈
      {p : H × H | p.2 = yosida H A lam honto p.1} from rfl)
      (show (q, yosida H A lam honto q) ∈
      {p : H × H | p.2 = yosida H A lam honto p.1} from rfl)) u hu.2 ht
  rw [hu.1] at hs
  exact hs.trans (initial_yosida_bound H A hmono lam hlam honto x a₀ hxa)

theorem approximate_lipschitz : Spec.ApproximateLipschitz.{u} := by
  intro H _ _ A hmono lam hlam honto x a₀ u hxa hu
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ici 0)
    (fun t _ => (hu.2 t).hasDerivWithinAt)
  intro t ht
  change ‖-yosida H A lam honto (u t)‖ ≤ ‖a₀‖
  rw [norm_neg]
  exact approximate_speed_bound H A hmono lam hlam honto x a₀ u hxa hu t ht

theorem parameter_comparison : Spec.ParameterComparison.{u} := by
  intro H _ _ A hmono lam μ hlam hμ hlamonto hμonto x y C ha hb
  let a := yosida H A lam hlamonto x
  let b := yosida H A μ hμonto y
  let v := resolvent H A lam hlamonto x
  let w := resolvent H A μ hμonto y
  change ‖a‖ ≤ C at ha
  change ‖b‖ ≤ C at hb
  change -inner ℝ (a - b) (x - y) ≤ _
  have hC : 0 ≤ C := (norm_nonneg a).trans ha
  have hab : ‖a - b‖ ≤ 2 * C := (norm_sub_le a b).trans (by linarith)
  have hna : -inner ℝ (a - b) a ≤ 2 * C ^ 2 := by
    have hi := (neg_le_abs (inner ℝ (a - b) a)).trans (abs_real_inner_le_norm _ _)
    have hp := mul_le_mul hab ha (norm_nonneg a) (by positivity : 0 ≤ 2 * C)
    nlinarith
  have hnb : inner ℝ (a - b) b ≤ 2 * C ^ 2 := by
    have hi := real_inner_le_norm (a - b) b
    have hp := mul_le_mul hab hb (norm_nonneg b) (by positivity : 0 ≤ 2 * C)
    nlinarith
  have hm := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hmono
    (yosida_graph H A lam hlam hlamonto x) (yosida_graph H A μ hμ hμonto y)
  change 0 ≤ inner ℝ (a - b) (v - w) at hm
  have hx : x = v + lam • a := resolvent_identity H A lam hlam hlamonto x
  have hy : y = w + μ • b := resolvent_identity H A μ hμ hμonto y
  have hd : x - y = (v - w) + lam • a - μ • b := by rw [hx, hy]; abel
  rw [hd, inner_sub_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right]
  have ha' := mul_le_mul_of_nonneg_left hna hlam.le
  have hb' := mul_le_mul_of_nonneg_left hnb hμ.le
  nlinarith

theorem approximate_cauchy_estimate : Spec.ApproximateCauchyEstimate.{u} := by
  intro H _ _ A hmono lam μ hlam hμ hlamonto hμonto x a₀ u v hxa hu hv t ht
  have hd (r : ℝ) : HasDerivAt (fun r => ‖u r - v r‖ ^ 2)
      (2 * inner ℝ (u r - v r)
        (-Spec.R.Y H A lam hlamonto (u r) - -Spec.R.Y H A μ hμonto (v r))) r := by
    simpa only [Pi.sub_apply] using ((hu.2 r).sub (hv.2 r)).norm_sq
  have hcont : Continuous (fun r => ‖u r - v r‖ ^ 2) :=
    continuous_iff_continuousAt.mpr (fun r => (hd r).continuousAt)
  have hbound (r : ℝ) (hr : r ∈ interior (Ici (0 : ℝ))) :
      deriv (fun r => ‖u r - v r‖ ^ 2) r ≤ 4 * (lam + μ) * ‖a₀‖ ^ 2 := by
    have hr' : 0 ≤ r := interior_subset hr
    rw [(hd r).deriv]
    have hp := parameter_comparison H A hmono lam μ hlam hμ hlamonto hμonto
      (u r) (v r) ‖a₀‖
      (approximate_speed_bound H A hmono lam hlam hlamonto x a₀ u hxa hu r hr')
      (approximate_speed_bound H A hmono μ hμ hμonto x a₀ v hxa hv r hr')
    rw [real_inner_comm] at hp
    simp only [inner_sub_right, inner_neg_right] at hp ⊢
    linarith
  have h := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    hcont.continuousOn (fun r _ => (hd r).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) t (by simpa using ht) ht
  simpa only [hu.1, hv.1, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero] using h

/-- A square-distance bound that vanishes with both parameters gives uniform
Cauchyness for the entire positive-parameter filter. -/
theorem uniform_cauchy_of_sq_bound {H : Type u} [NormedAddCommGroup H]
    (F : ℝ → ℝ → H) (s : Set ℝ) (B : ℝ)
    (hbound : ∀ lam : ℝ, 0 < lam → ∀ μ : ℝ, 0 < μ →
      ∀ t ∈ s, ‖F lam t - F μ t‖ ^ 2 ≤ (lam + μ) * B) :
    UniformCauchySeqOn F (𝓝[>] (0 : ℝ)) s := by
  intro V hV
  obtain ⟨ε, hε, hVε⟩ := Metric.mem_uniformity_dist.mp hV
  have hfst : Tendsto (fun q : ℝ × ℝ => q.1)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have hsnd : Tendsto (fun q : ℝ × ℝ => q.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hlim : Tendsto (fun q : ℝ × ℝ => (q.1 + q.2) * B)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0) := by
    simpa only [zero_add, zero_mul] using (hfst.add hsnd).mul_const B
  have hsmall := hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  have hpos₁ : ∀ᶠ q : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)), 0 < q.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hpos₂ : ∀ᶠ q : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)), 0 < q.2 :=
    tendsto_snd.eventually self_mem_nhdsWithin
  filter_upwards [hsmall, hpos₁, hpos₂] with q hq hq₁ hq₂
  intro t ht
  apply hVε
  rw [dist_eq_norm]
  have h := hbound q.1 hq₁ q.2 hq₂ t ht
  nlinarith [norm_nonneg (F q.1 t - F q.2 t)]

theorem approximate_uniform_limit : Spec.ApproximateUniformLimit.{u} := by
  intro H _ _ _ A hmono honto F hF x a₀ hxa
  have hcauchy (T : ℝ) (hT : 0 < T) :
      UniformCauchySeqOn (fun lam => F lam x) (𝓝[>] (0 : ℝ)) (Icc 0 T) := by
    apply uniform_cauchy_of_sq_bound _ _ (4 * ‖a₀‖ ^ 2 * T)
    intro lam hlam μ hμ t ht
    have h := approximate_cauchy_estimate H A hmono lam μ hlam hμ
      (honto lam hlam) (honto μ hμ) x a₀ (F lam x) (F μ x) hxa
      (hF lam hlam x) (hF μ hμ x) t ht.1
    have hnonneg : 0 ≤ 4 * (lam + μ) * ‖a₀‖ ^ 2 := by positivity
    have htT := mul_le_mul_of_nonneg_left ht.2 hnonneg
    nlinarith
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      ∃ y : H, Tendsto (fun lam => F lam x t) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    apply cauchy_map_iff_exists_tendsto.mp
    exact (hcauchy (t + 1) (by linarith)).cauchy_map ⟨ht, by linarith⟩
  let u : ℝ → H := fun t => if ht : 0 ≤ t then (hpoint t ht).choose else x
  have hu (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun lam => F lam x t) (𝓝[>] (0 : ℝ)) (𝓝 (u t)) := by
    simpa only [u, dite_eq_left ht] using (hpoint t ht).choose_spec
  refine ⟨u, ?_, ?_, ?_⟩
  · apply tendsto_nhds_unique (hu 0 le_rfl)
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact (hF lam hlam x).1.symm
  · apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    apply le_of_tendsto ((hu s hs).dist (hu t ht))
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact (approximate_lipschitz H A hmono lam hlam (honto lam hlam) x a₀
      (F lam x) hxa (hF lam hlam x)).dist_le_mul s hs t ht
  · intro T hT
    exact (hcauchy T hT).tendstoUniformlyOn_of_tendsto (fun t ht => hu t ht.1)


/-- The integral form of a global classical autonomous trajectory. -/
theorem classical_solution_primitive {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → E) {L : ℝ≥0}
    (hf : LipschitzWith L f) (u : ℝ → E) (x : E) (h₀ : u 0 = x)
    (hu : ∀ t, HasDerivAt u (-f (u t)) t) (t : ℝ) :
    u t = x - ∫ r in (0 : ℝ)..t, f (u r) := by
  have hc : Continuous u := continuous_iff_continuousAt.mpr (fun r => (hu r).continuousAt)
  have hfc : Continuous (fun r => f (u r)) := hf.continuous.comp hc
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r ∈ uIcc (0 : ℝ) t) => hu r) (hfc.neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg, h₀] at hi
  calc
    u t = (u t - x) + x := (sub_add_cancel _ _).symm
    _ = -(∫ r in (0 : ℝ)..t, f (u r)) + x := by rw [← hi]
    _ = x - ∫ r in (0 : ℝ)..t, f (u r) := by abel



/-- Continuous curves belong to every finite-interval Bochner Lp space. -/
theorem continuous_memLp_Icc {E : Type u} [NormedAddCommGroup E]
    {u : ℝ → E} (hc : Continuous u) (p : ℝ≥0∞) (a b : ℝ) :
    MemLp u p (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (mem_image_of_mem _ ht)

/-- A pointwise bound on an interval controls the norm of its L² representative. -/
theorem toLp_norm_bound_Icc {E : Type u} [NormedAddCommGroup E]
    {u : ℝ → E} {a b C : ℝ}
    (hm : MemLp u 2 (volume.restrict (Icc a b))) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Icc a b, ‖u t‖ ≤ C) :
    ‖hm.toLp u‖ ≤
      (measureUnivNNReal (volume.restrict (Icc a b)) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * C := by
  apply Lp.norm_le_of_ae_bound hC
  filter_upwards [hm.coeFn_toLp, ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  exact hb t hmem


/-- A bounded weakly convergent net pairs continuously with a strongly
convergent net. In particular this applies in Hilbert-valued L² spaces. -/
theorem weak_strong_inner {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type v} {l : Filter ι}
    {a v : ι → E} {b w : E} {C : ℝ}
    (ha : ∀ z : E, Tendsto (fun i => inner ℝ (a i) z) l (𝓝 (inner ℝ b z)))
    (hbound : ∀ᶠ i in l, ‖a i‖ ≤ C) (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => inner ℝ (a i) (v i)) l (𝓝 (inner ℝ b w)) := by
  have herr : Tendsto (fun i => inner ℝ (a i) (v i - w)) l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun i => C * ‖v i - w‖)
    · filter_upwards [hbound] with i hi
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    · simpa only [sub_self, norm_zero, mul_zero] using
        (hv.sub (tendsto_const_nhds (x := w))).norm.const_mul C
  have h := (ha w).add herr
  simpa only [inner_sub_right, add_sub_cancel, add_zero] using h

/-- Strong–weak closedness of a monotone graph with onto I+A, for bounded
nets. A single resolvent test proves membership, so no indexed exceptional
sets enter when the Hilbert space is itself L². -/
theorem strong_weak_graph_closed {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type v} {l : Filter ι} [l.NeBot]
    (A : Set (E × E))
    (hm : ∀ ⦃x y a b : E⦄, (x, a) ∈ A → (y, b) ∈ A →
      0 ≤ inner ℝ (a - b) (x - y))
    (honto : Spec.R.onto E A 1) {v a : ι → E} {u b : E} {C : ℝ}
    (hgraph : ∀ᶠ i in l, (v i, a i) ∈ A)
    (hbound : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hv : Tendsto v l (𝓝 u))
    (ha : ∀ z : E, Tendsto (fun i => inner ℝ (a i) z) l (𝓝 (inner ℝ b z))) :
    (u, b) ∈ A := by
  let q := resolvent E A 1 honto (u + b)
  let c := yosida E A 1 honto (u + b)
  have hqc : (q, c) ∈ A := yosida_graph E A 1 zero_lt_one honto (u + b)
  have hid : u + b = q + c := by
    have h := resolvent_identity E A 1 zero_lt_one honto (u + b)
    change u + b = q + (1 : ℝ) • c at h
    simpa only [one_smul] using h
  have hweak : ∀ z : E, Tendsto (fun i => inner ℝ (a i - c) z) l
      (𝓝 (inner ℝ (b - c) z)) := by
    intro z
    simpa only [inner_sub_left] using (ha z).sub_const (inner ℝ c z)
  have hbounded : ∀ᶠ i in l, ‖a i - c‖ ≤ C + ‖c‖ := by
    filter_upwards [hbound] with i hi
    exact (norm_sub_le _ _).trans (add_le_add hi le_rfl)
  have hlim := weak_strong_inner hweak hbounded (hv.sub_const q)
  have hn : 0 ≤ inner ℝ (b - c) (u - q) :=
    ge_of_tendsto hlim (hgraph.mono fun i hi => hm hi hqc)
  have hd : u - q = -(b - c) := by
    rw [neg_sub]
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hid)
  rw [hd, inner_neg_right, real_inner_self_eq_norm_sq] at hn
  have he : b = c := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (b - c)]))
  have hu : u = q := sub_eq_zero.mp (by simpa only [he, sub_self, neg_zero] using hd)
  simpa only [hu, he] using hqc

/-- A bounded net in an arbitrary real Hilbert space has a weak limit along
an ultrafilter refining its original filter. This form needs no separability. -/
theorem bounded_weak_cluster {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ι : Type v}
    (l : Filter ι) [l.NeBot] (a : ι → E) (C : ℝ)
    (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ (b : E) (p : Filter ι), p.NeBot ∧ p ≤ l ∧ ‖b‖ ≤ C ∧
      ∀ z : E, Tendsto (fun i => inner ℝ (a i) z) p (𝓝 (inner ℝ b z)) := by
  let g : ι → WeakDual ℝ E := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (a i))
  have hmem : Filter.map g l ≤
      𝓟 (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) C) := by
    rw [le_principal_iff]
    change ∀ᶠ i in l, g i ∈ _
    exact Eventually.of_forall (fun i => by
      change dist (InnerProductSpace.toDual ℝ E (a i)) 0 ≤ C
      simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using ha i)
  obtain ⟨φ, hφ, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) C).exists_mapClusterPt hmem
  obtain ⟨p, hpl, hp⟩ := mapClusterPt_iff_ultrafilter.mp hc
  let b := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual φ)
  have hb : InnerProductSpace.toDual ℝ E b = WeakDual.toStrongDual φ :=
    (InnerProductSpace.toDual ℝ E).apply_symm_apply _
  refine ⟨b, (p : Filter ι), inferInstance, hpl, ?_, fun z => ?_⟩
  · change dist (WeakDual.toStrongDual φ) 0 ≤ C at hφ
    simpa only [← hb, dist_zero_right, LinearIsometryEquiv.norm_map] using hφ
  · have he := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hp) z
    change Tendsto (fun i => inner ℝ (a i) z) (p : Filter ι)
      (𝓝 ((WeakDual.toStrongDual φ) z)) at he
    simpa only [← hb, InnerProductSpace.toDual_apply_apply] using he

/-- On any finite measure space the pointwise graph inherits the onto
property on L². Subtracting J(0) permits arbitrary graphs, including those
that do not contain the origin. -/
theorem l2_graph_shift_onto {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : Type v} [MeasurableSpace X]
    (m : Measure X) [IsFiniteMeasure m] (A : Set (E × E))
    (hm : ExpandedFA.Monotone.Spec.MonotoneValue E
      (ExpandedFA.Monotone.Spec.HilbertGraphValue E A))
    (honto : Spec.R.onto E A 1) :
    Spec.R.onto (Lp E 2 m) {p | ∀ᵐ t ∂m, (p.1 t, p.2 t) ∈ A} 1 := by
  intro h
  let J := resolvent E A 1 honto
  have hJ : LipschitzWith 1 J := resolvent_nonexpansive E A hm 1 zero_lt_one honto
  have hV : MemLp (fun t => J (h t)) 2 m := by
    have hqJ : LipschitzWith 1 (fun x => J x - J 0) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hJ.norm_sub_le x y
    have hq : MemLp (fun t => J (h t) - J 0) 2 m :=
      hqJ.comp_memLp (by simp) (Lp.memLp h)
    convert hq.add (memLp_const (J 0)) using 1
    ext t
    simp only [Pi.add_apply, sub_add_cancel]
  let V := hV.toLp (fun t => J (h t))
  refine ⟨V, h - V, ?_, ?_⟩
  · change ∀ᵐ t ∂m, (V t, (h - V) t) ∈ A
    filter_upwards [hV.coeFn_toLp, Lp.coeFn_sub h V] with t ht hs
    change V t = J (h t) at ht
    simp only [Pi.sub_apply] at hs
    rw [hs, ht]
    have hg := yosida_graph E A 1 zero_lt_one honto (h t)
    change (J (h t), (1 : ℝ)⁻¹ • (h t - J (h t))) ∈ A at hg
    simpa only [inv_one, one_smul] using hg
  · simp only [one_smul, add_sub_cancel]

/-- Monotonicity passes to the pointwise graph in L². All exceptional sets
here involve only the two pairs in the assertion. -/
theorem l2_graph_monotone {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : Type v} [MeasurableSpace X]
    (m : Measure X) (A : Set (E × E))
    (hm : ∀ ⦃x y a b : E⦄, (x, a) ∈ A → (y, b) ∈ A →
      0 ≤ inner ℝ (a - b) (x - y))
    {u v a b : Lp E 2 m}
    (hua : ∀ᵐ t ∂m, (u t, a t) ∈ A)
    (hvb : ∀ᵐ t ∂m, (v t, b t) ∈ A) :
    0 ≤ inner ℝ (a - b) (u - v) := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hua, hvb, Lp.coeFn_sub a b, Lp.coeFn_sub u v] with t ht hs hab huv
  simpa only [hab, huv, Pi.sub_apply, Pi.zero_apply] using hm ht hs

/-- The full weak–strong graph limit in L², without an uncountable
intersection of null sets or any separability assumption. -/
theorem l2_strong_weak_graph_closed {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : Type v} [MeasurableSpace X]
    (m : Measure X) [IsFiniteMeasure m] (A : Set (E × E))
    (hm : ExpandedFA.Monotone.Spec.MonotoneValue E
      (ExpandedFA.Monotone.Spec.HilbertGraphValue E A))
    (honto : Spec.R.onto E A 1) {ι : Type*} {l : Filter ι} [l.NeBot]
    {v a : ι → Lp E 2 m} {u b : Lp E 2 m} {C : ℝ}
    (hgraph : ∀ᶠ i in l, ∀ᵐ t ∂m, (v i t, a i t) ∈ A)
    (hbound : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hv : Tendsto v l (𝓝 u))
    (ha : ∀ z : Lp E 2 m, Tendsto (fun i => inner ℝ (a i) z) l (𝓝 (inner ℝ b z))) :
    ∀ᵐ t ∂m, (u t, b t) ∈ A := by
  have hmono := (ExpandedFA.Monotone.monotone_hilbertGraph_iff E A).mp hm
  exact strong_weak_graph_closed {p : Lp E 2 m × Lp E 2 m |
      ∀ᵐ t ∂m, (p.1 t, p.2 t) ∈ A}
    (fun {_ _ _ _} hx hy => l2_graph_monotone m A hmono hx hy)
    (l2_graph_shift_onto m A hm honto) hgraph hbound hv ha

/-- Uniform convergence on a finite-measure set implies strong L²
convergence whenever the functions are represented in L². -/
theorem uniform_to_l2 {E : Type u} [NormedAddCommGroup E] {X : Type v}
    [MeasurableSpace X] {m : Measure X} {s : Set X} (hs : MeasurableSet s)
    [IsFiniteMeasure (m.restrict s)] {ι : Type*} {l : Filter ι}
    {F : ι → X → E} {u : X → E}
    (hF : ∀ i, MemLp (F i) 2 (m.restrict s)) (hu : MemLp u 2 (m.restrict s))
    (hconv : TendstoUniformlyOn F u l s) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hu.toLp u)) := by
  let K : ℝ := (measureUnivNNReal (m.restrict s) : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / (K + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (ε / (K + 1)) hδ] with i hi
  have hbound : ∀ᵐ t ∂(m.restrict s),
      ‖((hF i).toLp (F i) - hu.toLp u) t‖ ≤ ε / (K + 1) := by
    filter_upwards [(hF i).coeFn_toLp, hu.coeFn_toLp,
      Lp.coeFn_sub ((hF i).toLp (F i)) (hu.toLp u), ae_restrict_mem hs] with t ht ht' hsub hts
    rw [hsub]
    simp only [Pi.sub_apply, ht, ht']
    simpa only [dist_eq_norm, norm_sub_rev] using (hi t hts).le
  have hn := Lp.norm_le_of_ae_bound hδ.le hbound
  rw [dist_eq_norm]
  change ‖(hF i).toLp (F i) - hu.toLp u‖ ≤ K * (ε / (K + 1)) at hn
  have hsmall : K * (ε / (K + 1)) < ε := by
    apply (mul_lt_mul_iff_left₀ (show 0 < K + 1 by positivity)).mp
    field_simp
    nlinarith
  exact hn.trans_lt hsmall

/-- Weak L² convergence determines the limit of all time primitives by
testing against constant vectors on subintervals. -/
theorem l2_weak_limit_primitive {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ι : Type v} {l : Filter ι} [l.NeBot]
    {T : ℝ} {a : ι → Lp E 2 (volume.restrict (Icc (0 : ℝ) T))}
    {b : Lp E 2 (volume.restrict (Icc (0 : ℝ) T))}
    {F : ι → ℝ → E} {u : ℝ → E} {x : E}
    (ha : ∀ z, Tendsto (fun i => inner ℝ (a i) z) l (𝓝 (inner ℝ b z)))
    (hF : ∀ t ∈ Icc 0 T, Tendsto (fun i => F i t) l (𝓝 (u t)))
    (hprim : ∀ i, ∀ t ∈ Icc 0 T, F i t = x - ∫ r in (0 : ℝ)..t, a i r) :
    ∀ t ∈ Icc 0 T, u t = x - ∫ r in (0 : ℝ)..t, b r := by
  intro t ht
  have hsub : Ioc (0 : ℝ) t ⊆ Icc 0 T := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have heval (f : Lp E 2 (volume.restrict (Icc (0 : ℝ) T))) (z : E) :
      inner ℝ f (indicatorConstLp (s := Ioc (0 : ℝ) t) 2 measurableSet_Ioc (by finiteness) z) =
        inner ℝ (∫ r in (0 : ℝ)..t, f r) z := by
    rw [real_inner_comm, L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ]
    rw [Measure.restrict_restrict_of_subset hsub, ← intervalIntegral.integral_of_le ht.1,
      real_inner_comm]
  apply ext_inner_right ℝ
  intro z
  have hlim : Tendsto (fun i => inner ℝ (x - F i t) z) l
      (𝓝 (inner ℝ (∫ r in (0 : ℝ)..t, b r) z)) := by
    have h := ha (indicatorConstLp (s := Ioc (0 : ℝ) t) 2 measurableSet_Ioc (by finiteness) z)
    simp only [heval] at h
    convert h using 1
    ext i
    rw [hprim i t ht]
    simp only [sub_sub_cancel]
  have hlim' : Tendsto (fun i => inner ℝ (x - F i t) z) l
      (𝓝 (inner ℝ (x - u t) z)) :=
    (tendsto_const_nhds.sub (hF t ht)).inner tendsto_const_nhds
  have he := tendsto_nhds_unique hlim' hlim
  simp only [inner_sub_left] at he ⊢
  linarith

/-- The Bochner Lebesgue differentiation theorem recovers the strong
Hilbert-space derivative from an L² primitive, on the original interval. -/
theorem ae_derivative_of_l2_primitive {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {T : ℝ} (hT : 0 < T)
    (b : Lp E 2 (volume.restrict (Icc (0 : ℝ) T))) (u : ℝ → E) (x : E)
    (hprim : ∀ t ∈ Icc 0 T, u t = x - ∫ r in (0 : ℝ)..t, b r) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), HasDerivAt u (-b t) t := by
  have hint : IntervalIntegrable b volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
    exact MemLp.integrable (by norm_num) (Lp.memLp b)
  have hd := hint.ae_hasDerivAt_integral
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hd, (by simp [ae_iff] : ∀ᵐ t : ℝ, t ≠ 0), (by simp [ae_iff] : ∀ᵐ t : ℝ, t ≠ T)] with t ht h₀ h₁
  intro htT
  have hinside : t ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_le_of_ne htT.1 (Ne.symm h₀), lt_of_le_of_ne htT.2 h₁⟩
  have heq : u =ᶠ[𝓝 t] fun s => x - ∫ r in (0 : ℝ)..s, b r := by
    filter_upwards [Ioo_mem_nhds hinside.1 hinside.2] with s hs
    exact hprim s (Ioo_subset_Icc_self hs)
  have hb := ht (by simpa only [uIcc_of_le hT.le] using htT) 0
    (by simpa only [uIcc_of_le hT.le] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩))
  simpa only [zero_sub] using
    ((hasDerivAt_const t x).sub hb).congr_of_eventuallyEq heq

theorem integrated_minty : Spec.IntegratedMinty.{u,v} := by
  intro H _ _ X _ m A honto u a
  let v := fun t => resolvent H A 1 honto (u t + a t)
  let b := fun t => u t + a t - v t
  change Integrable (fun t => ‖a t - b t‖ ^ 2) m →
    0 ≤ (∫ t, inner ℝ (a t - b t) (u t - v t) ∂m) → _
  intro hint htest
  have hdiff (t : X) : u t - v t = -(a t - b t) := by dsimp [b]; abel
  have hid : (fun t => inner ℝ (a t - b t) (u t - v t)) =
      (fun t => -(‖a t - b t‖ ^ 2)) := by
    funext t
    rw [hdiff, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hid, integral_neg] at htest
  have hzero : (∫ t, ‖a t - b t‖ ^ 2 ∂m) = 0 :=
    le_antisymm (by linarith) (integral_nonneg (fun _ => sq_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp hzero
  filter_upwards [hae] with t ht
  have hab : a t = b t := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp ht))
  have huv : u t = v t := sub_eq_zero.mp (by rw [hdiff, hab, sub_self, neg_zero])
  have hg := yosida_graph H A 1 zero_lt_one honto (u t + a t)
  have hbid : b t = yosida H A 1 honto (u t + a t) := by
    change u t + a t - resolvent H A 1 honto (u t + a t) =
      (1 : ℝ)⁻¹ • (u t + a t - resolvent H A 1 honto (u t + a t))
    simp
  change (v t, yosida H A 1 honto (u t + a t)) ∈ A at hg
  rw [← hbid, ← hab, ← huv] at hg
  exact hg

theorem yosida_limit_on_interval (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A))
    (honto : ∀ lam : ℝ, 0 < lam → Spec.R.onto H A lam)
    (F : ℝ → H → ℝ → H)
    (hF : ∀ (lam : ℝ) (hlam : 0 < lam) (x : H),
      Spec.GlobalApproximation A lam (honto lam hlam) x (F lam x))
    (x a₀ : H) (hxa : (x, a₀) ∈ A) (u : ℝ → H)
    (hux : u 0 = x) (hu : LipschitzOnWith ‖a₀‖₊ u (Ici 0))
    (T : ℝ) (hT : 0 < T)
    (hconv : TendstoUniformlyOn (fun lam => F lam x) u (𝓝[>] (0 : ℝ)) (Icc 0 T)) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t := by
  let m : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hlam (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlim : Tendsto lam atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hlam⟩
  let f : ℕ → ℝ → H := fun n => F (lam n) x
  let a : ℕ → ℝ → H := fun n t => Spec.R.Y H A (lam n) (honto (lam n) (hlam n)) (f n t)
  have hcF (n : ℕ) : Continuous (f n) :=
    continuous_iff_continuousAt.mpr (fun t => ((hF (lam n) (hlam n) x).2 t).continuousAt)
  have hY (n : ℕ) : Continuous (Spec.R.Y H A (lam n) (honto (lam n) (hlam n))) :=
    (yosida_lipschitz H A hm (lam n) (hlam n) (honto (lam n) (hlam n))).continuous
  have hca (n : ℕ) : Continuous (a n) := (hY n).comp (hcF n)
  have hab (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : ‖a n t‖ ≤ ‖a₀‖ :=
    approximate_speed_bound H A hm (lam n) (hlam n) (honto (lam n) (hlam n))
      x a₀ (f n) hxa (hF (lam n) (hlam n) x) t ht
  have haMem (n : ℕ) : MemLp (a n) 2 m := by
    apply MemLp.of_bound ((hca n).continuousOn.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc) ‖a₀‖
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hab n t ht.1
  have hfLip (n : ℕ) : LipschitzOnWith ‖a₀‖₊ (f n) (Ici 0) :=
    approximate_lipschitz H A hm (lam n) (hlam n) (honto (lam n) (hlam n)) x a₀
      (f n) hxa (hF (lam n) (hlam n) x)
  have hfb (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖f n t‖ ≤ ‖x‖ + ‖a₀‖ * T := by
    have hdist := (hfLip n).dist_le_mul t ht.1 0 (by simp)
    rw [show f n 0 = x from (hF (lam n) (hlam n) x).1, Real.dist_eq,
      sub_zero, abs_of_nonneg ht.1] at hdist
    change dist (f n t) x ≤ ‖a₀‖ * t at hdist
    have hn := norm_le_norm_sub_add (f n t) x
    rw [← dist_eq_norm] at hn
    exact hn.trans (by nlinarith [norm_nonneg a₀, ht.2])
  have hfMem (n : ℕ) : MemLp (f n) 2 m := by
    apply MemLp.of_bound ((hcF n).continuousOn.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc) (‖x‖ + ‖a₀‖ * T)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hfb n t ht
  have hub (t : ℝ) (ht : t ∈ Icc 0 T) : ‖u t‖ ≤ ‖x‖ + ‖a₀‖ * T := by
    have hdist := hu.dist_le_mul t ht.1 0 (by simp)
    rw [hux, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at hdist
    change dist (u t) x ≤ ‖a₀‖ * t at hdist
    have hn := norm_le_norm_sub_add (u t) x
    rw [← dist_eq_norm] at hn
    exact hn.trans (by nlinarith [norm_nonneg a₀, ht.2])
  have huMem : MemLp u 2 m := by
    apply MemLp.of_bound ((hu.continuousOn.mono (fun t ht => ht.1)).aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc) (‖x‖ + ‖a₀‖ * T)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht using hub t ht
  let aa : ℕ → Lp H 2 m := fun n => (haMem n).toLp (a n)
  let ff : ℕ → Lp H 2 m := fun n => (hfMem n).toLp (f n)
  let uu : Lp H 2 m := huMem.toLp u
  let K : ℝ := (measureUnivNNReal m : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * ‖a₀‖
  have haa (n : ℕ) : ‖aa n‖ ≤ K := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg _)
    filter_upwards [(haMem n).coeFn_toLp, ae_restrict_mem measurableSet_Icc] with t ht hs
    rw [ht]
    exact hab n t hs.1
  obtain ⟨bb, p, hp, hpat, hbb, haweak⟩ := bounded_weak_cluster atTop aa K haa
  let : p.NeBot := hp
  have hff : Tendsto ff atTop (𝓝 uu) := by
    apply uniform_to_l2 measurableSet_Icc hfMem huMem
    exact fun V hV => hlim.eventually (hconv V hV)
  have hal : Tendsto (fun n => (lam n) • aa n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => lam n * K)
    · exact Eventually.of_forall (fun n => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hlam n)]
        exact mul_le_mul_of_nonneg_left (haa n) (hlam n).le)
    · simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const K
  let vv : ℕ → Lp H 2 m := fun n => ff n - (lam n) • aa n
  have hvv : Tendsto vv p (𝓝 uu) := by
    simpa only [sub_zero] using (hff.sub hal).mono_left hpat
  have hg (n : ℕ) : ∀ᵐ t ∂m, (vv n t, aa n t) ∈ A := by
    filter_upwards [Lp.coeFn_sub (ff n) ((lam n) • aa n), Lp.coeFn_smul (lam n) (aa n),
      (hfMem n).coeFn_toLp, (haMem n).coeFn_toLp] with t hsub hsmul hft hat
    simp only [vv, hsub, hsmul, Pi.sub_apply, Pi.smul_apply, ff, aa] at *
    rw [hft, hat]
    have hident := resolvent_identity H A (lam n) (hlam n) (honto (lam n) (hlam n)) (f n t)
    have hgr := yosida_graph H A (lam n) (hlam n) (honto (lam n) (hlam n)) (f n t)
    change (f n t - (lam n) • a n t, a n t) ∈ A
    have he : f n t - (lam n) • a n t =
        Spec.R.J H A (lam n) (honto (lam n) (hlam n)) (f n t) := by
      change f n t - (lam n) • yosida H A (lam n) (honto (lam n) (hlam n)) (f n t) = _
      exact sub_eq_iff_eq_add.mpr hident
    rw [he]
    exact hgr
  have hgraph : ∀ᵐ t ∂m, (uu t, bb t) ∈ A :=
    l2_strong_weak_graph_closed m A hm (honto 1 zero_lt_one)
      (Eventually.of_forall hg) (Eventually.of_forall haa) hvv haweak
  have hprim : ∀ n, ∀ t ∈ Icc 0 T, f n t = x - ∫ r in (0 : ℝ)..t, aa n r := by
    intro n t ht
    have he := classical_solution_primitive _
      (yosida_lipschitz H A hm (lam n) (hlam n) (honto (lam n) (hlam n)))
      (f n) x (hF (lam n) (hlam n) x).1
      (hF (lam n) (hlam n) x).2 t
    change f n t = x - ∫ r in (0 : ℝ)..t, a n r at he
    rw [he]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    exact Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset
      (fun (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) t) => (show r ∈ Icc (0 : ℝ) T from ⟨hr.1.le, hr.2.trans ht.2⟩))
      (haMem n).coeFn_toLp)
  have hup : ∀ t ∈ Icc 0 T, u t = x - ∫ r in (0 : ℝ)..t, bb r := by
    apply l2_weak_limit_primitive haweak _ hprim
    intro t ht
    exact ((hconv.tendsto_at ht).comp hlim).mono_left hpat
  have hder := ae_derivative_of_l2_primitive hT bb u x hup
  filter_upwards [hgraph, hder, huMem.coeFn_toLp] with t hg hd he
  exact ⟨bb t, by simpa only [uu, he] using hg, hd⟩

/-- Almost-everywhere assertions on all bounded forward intervals cover the
whole forward time axis by a countable union. -/
theorem ae_on_nonneg_of_on_intervals {P : ℝ → Prop}
    (h : ∀ T : ℝ, 0 < T → ∀ᵐ t ∂(volume.restrict (Icc 0 T)), P t) :
    ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))), P t := by
  have hcover : (Ici (0 : ℝ)) = ⋃ n : ℕ, Icc (0 : ℝ) (n + 1 : ℕ) := by
    ext t
    simp only [mem_Ici, mem_iUnion, mem_Icc]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact ⟨n, ht, by push_cast; linarith⟩
    · rintro ⟨n, ht, _⟩
      exact ht
  rw [hcover, ae_restrict_iUnion_iff]
  intro n
  exact h (n + 1 : ℕ) (by positivity)

/-- The global Yosida approximation family converges to a Lipschitz solution
of the original differential inclusion, for every graph-domain initial value. -/
theorem yosida_evolution : Spec.YosidaEvolution.{u} := by
  intro H _ _ _ A hm honto
  obtain ⟨F, hF⟩ := approximation_family H A hm honto
  refine ⟨F, hF, ?_, ?_⟩
  · intro lam hlam x y t ht
    exact approximate_contraction H A hm lam hlam (honto lam hlam) x y
      (F lam x) (F lam y) (hF lam hlam x) (hF lam hlam y) t ht
  · intro x a₀ hxa
    refine ⟨?_, ?_⟩
    · intro lam hlam t ht
      exact approximate_speed_bound H A hm lam hlam (honto lam hlam) x a₀
        (F lam x) hxa (hF lam hlam x) t ht
    · obtain ⟨u, hux, hu, hconv⟩ := approximate_uniform_limit H A hm honto F hF x a₀ hxa
      refine ⟨u, hux, hu, hconv, ?_⟩
      apply ae_on_nonneg_of_on_intervals
      intro T hT
      exact yosida_limit_on_interval H A hm honto F hF x a₀ hxa u hux hu T hT (hconv T hT)

end ExpandedFA.Evolution.NonlinearYosidaEvolution
