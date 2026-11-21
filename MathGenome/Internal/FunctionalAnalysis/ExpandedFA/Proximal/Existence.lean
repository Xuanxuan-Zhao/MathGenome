import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Existence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06FenchelMoreau
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-! Existence and uniqueness for the Hilbert proximal problem.
The proof works with real heights in the closed epigraph. The affine minorant
bounds their quadratic energies below. Convexity and the parallelogram law
force approximate minimizers to form a Cauchy sequence. -/
noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private def quadratic (μ : ℝ) (f v : H) : ℝ := ‖f - v‖ ^ 2 / (2 * μ)

private lemma quadratic_midpoint (μ : ℝ) (hμ : 0 < μ) (f v w : H) :
    quadratic μ f ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) =
      (quadratic μ f v + quadratic μ f w) / 2 - ‖v - w‖ ^ 2 / (8 * μ) := by
  have hp := parallelogram_law_with_norm ℝ (f - v) (f - w)
  have ha : (f - v) + (f - w) =
      (2 : ℝ) • (f - ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w)) := by module
  have hb : (f - v) - (f - w) = -(v - w) := by abel
  rw [ha, hb, norm_smul, norm_neg] at hp
  norm_num at hp
  dsimp [quadratic]
  field_simp
  nlinarith

/-- Midpoint improvement, expressed with real upper bounds on the energy. -/
private lemma midpoint_energy_bound (φ : ExtendedFunction H)
    (hc : ExtendedConvex H φ) (μ : ℝ) (hμ : 0 < μ) (f v w : H) (r s : ℝ)
    (hv : φ v ≤ ((r - quadratic μ f v : ℝ) : WithTop ℝ))
    (hw : φ w ≤ ((s - quadratic μ f w : ℝ) : WithTop ℝ)) :
    φ ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) ≤
      (((r + s) / 2 - ‖v - w‖ ^ 2 / (8 * μ) -
        quadratic μ f ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) : ℝ) : WithTop ℝ) := by
  have hepi := (convex_iff_convex_epigraph H φ).mp hc
  have hm := hepi (show (v, r - quadratic μ f v) ∈ realEpigraph H φ from hv)
    (show (w, s - quadratic μ f w) ∈ realEpigraph H φ from hw)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  change φ ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) ≤
    (((1 / 2 : ℝ) * (r - quadratic μ f v) +
      (1 / 2 : ℝ) * (s - quadratic μ f w) : ℝ) : WithTop ℝ) at hm
  convert hm using 1
  rw [quadratic_midpoint μ hμ]
  congr 1; ring

/-- A continuous affine minorant suffices even when φ is unbounded below. -/
private lemma affine_quadratic_lower_bound (φ : ExtendedFunction H)
    (h : H →L[ℝ] ℝ) (c : ℝ) (hm : P1.AffineMinorants.IsContinuousAffineMinorant φ h c)
    (μ : ℝ) (hμ : 0 < μ) (f v : H) (r : ℝ)
    (hv : φ v ≤ ((r - quadratic μ f v : ℝ) : WithTop ℝ)) :
    h f + c - μ * ‖h‖ ^ 2 / 2 ≤ r := by
  have hp : h v + c ≤ r - quadratic μ f v :=
    WithTop.coe_le_coe.mp ((hm v).trans hv)
  have hf : h f - h v ≤ ‖h‖ * ‖f - v‖ := by
    calc
      h f - h v = h (f - v) := (map_sub h f v).symm
      _ ≤ ‖h (f - v)‖ := le_abs_self _
      _ ≤ ‖h‖ * ‖f - v‖ := h.le_opNorm _
  have hq : ‖h‖ * ‖f - v‖ - μ * ‖h‖ ^ 2 / 2 ≤ quadratic μ f v := by
    dsimp [quadratic]
    apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).mpr
    nlinarith [sq_nonneg (‖f - v‖ - μ * ‖h‖)]
  linarith

/-- A finite real lower bound, and nonempty closed convex epigraph, give
attainment of the quadratic energy. The midpoint improvement is quantitative. -/
private lemma exists_minimum_energy [CompleteSpace H] (φ : ExtendedFunction H)
    (hp : Proper H φ) (hc : ExtendedConvex H φ) (hl : LowerSemicontinuous H φ)
    (μ : ℝ) (hμ : 0 < μ) (f : H) :
    ∃ (d : ℝ) (u : H),
      φ u ≤ ((d - quadratic μ f u : ℝ) : WithTop ℝ) ∧
      ∀ (v : H) (r : ℝ), φ v ≤ ((r - quadratic μ f v : ℝ) : WithTop ℝ) → d ≤ r := by
  let T : Set ℝ := {r | ∃ v : H, φ v ≤ ((r - quadratic μ f v : ℝ) : WithTop ℝ)}
  have hT : T.Nonempty := by
    obtain ⟨v, s, hs⟩ := (proper_iff_finite_value H φ).mp hp
    refine ⟨s + quadratic μ f v, v, ?_⟩
    simpa using hs.le
  have hbd : BddBelow T := by
    obtain ⟨h, c, hm⟩ := P1.AffineMinorants.exists_continuous_affine_minorant H φ hp hc hl
    refine ⟨h f + c - μ * ‖h‖ ^ 2 / 2, ?_⟩
    rintro r ⟨v, hv⟩
    exact affine_quadratic_lower_bound φ h c hm μ hμ f v r hv
  let d : ℝ := sInf T
  have hd (v : H) (r : ℝ) (hv : φ v ≤ ((r - quadratic μ f v : ℝ) : WithTop ℝ)) :
      d ≤ r := csInf_le hbd ⟨v, hv⟩
  have happrox (n : ℕ) : ∃ v : H,
      φ v ≤ ((d + 1 / (n + 1 : ℝ) - quadratic μ f v : ℝ) : WithTop ℝ) := by
    obtain ⟨r, ⟨v, hv⟩, hr⟩ := exists_lt_of_csInf_lt hT
      (show d < d + 1 / (n + 1 : ℝ) from lt_add_of_pos_right d Nat.one_div_pos_of_nat)
    exact ⟨v, hv.trans (WithTop.coe_le_coe.mpr (by linarith))⟩
  choose v hv using happrox
  have hdist (n k N : ℕ) (hn : N ≤ n) (hk : N ≤ k) :
      ‖v n - v k‖ ^ 2 ≤ 8 * μ * (1 / (N + 1 : ℝ)) := by
    have hm := midpoint_energy_bound φ hc μ hμ f (v n) (v k)
      (d + 1 / (n + 1 : ℝ)) (d + 1 / (k + 1 : ℝ)) (hv n) (hv k)
    have hh := hd _ _ hm
    have hnn : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := Nat.one_div_le_one_div hn
    have hkk : 1 / (k + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := Nat.one_div_le_one_div hk
    have hh' : ‖v n - v k‖ ^ 2 / (8 * μ) ≤ 1 / (N + 1 : ℝ) := by linarith
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0 < 8 * μ)).mp hh'
  have hcauchy : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hz : Tendsto (fun n : ℕ => 8 * μ * (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    obtain ⟨N, hN⟩ := (hz.eventually (gt_mem_nhds (sq_pos_of_pos hε))).exists
    refine ⟨N, ?_⟩
    intro n hn k hk
    rw [dist_eq_norm]
    have hh := hdist n k N hn hk
    nlinarith [norm_nonneg (v n - v k)]
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hq : Tendsto (fun n => quadratic μ f (v n)) atTop (𝓝 (quadratic μ f u)) := by
    exact ((tendsto_const_nhds.sub hu).norm.pow 2).div_const (2 * μ)
  have ht : Tendsto (fun n : ℕ => d + 1 / (n + 1 : ℝ) - quadratic μ f (v n))
      atTop (𝓝 (d - quadratic μ f u)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).sub hq
  have hepi := (lowerSemicontinuous_iff_closed_epigraph H φ).mp hl
  have hlim : (u, d - quadratic μ f u) ∈ realEpigraph H φ :=
    hepi.mem_of_tendsto (hu.prodMk_nhds ht) (Eventually.of_forall hv)
  exact ⟨d, u, hlim, hd⟩

private lemma objective_le_real_iff (φ : ExtendedFunction H) (μ : ℝ) (f v : H) (r : ℝ) :
    proximalObjective H φ μ f v ≤ (r : WithTop ℝ) ↔
      φ v ≤ ((r - quadratic μ f v : ℝ) : WithTop ℝ) := by
  change φ v + ((quadratic μ f v : ℝ) : WithTop ℝ) ≤ (r : WithTop ℝ) ↔ _
  by_cases hv : φ v = ⊤
  · simp [hv]
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hv
    rw [← hs, ← WithTop.coe_add]
    simp only [WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

/-- The source's analytic well-posedness theorem, without restrictions on the
finite domain or a lower bound on the original function. -/
theorem exists_unique_proximalMinimizer : ExistenceSpec.UniqueMinimizer.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  obtain ⟨d, u, hu, hd⟩ := exists_minimum_energy φ hp hc hl μ hμ f
  have huobj : proximalObjective H φ μ f u ≤ (d : WithTop ℝ) :=
    (objective_le_real_iff φ μ f u d).mpr hu
  have hglobal (v : H) : (d : WithTop ℝ) ≤ proximalObjective H φ μ f v := by
    by_cases hv : proximalObjective H φ μ f v = ⊤
    · simp [hv]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hv
      rw [← hr]
      exact WithTop.coe_le_coe.mpr (hd v r ((objective_le_real_iff φ μ f v r).mp hr.ge))
  have humin : IsProximalMinimizer H φ μ f u := by
    refine ⟨ne_top_of_le_ne_top WithTop.coe_ne_top hu, ?_⟩
    exact fun v => huobj.trans (hglobal v)
  refine ⟨u, humin, ?_⟩
  intro w hw
  have hwobj : proximalObjective H φ μ f w ≤ (d : WithTop ℝ) := (hw.2 u).trans huobj
  have hw' := (objective_le_real_iff φ μ f w d).mp hwobj
  have hmid := midpoint_energy_bound φ hc μ hμ f u w d d hu hw'
  have hgap := hd _ _ hmid
  have hdiv : ‖u - w‖ ^ 2 / (8 * μ) ≤ 0 := by linarith
  have hsq : ‖u - w‖ ^ 2 ≤ 0 := by
    simpa using (div_le_iff₀ (by positivity : 0 < 8 * μ)).mp hdiv
  have heq : u = w := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u - w)]))
  exact heq.symm

/-- The actual extended-real infimum is a finite real number. -/
theorem moreauEnvelope_finite : ExistenceSpec.FiniteEnvelope.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  exact moreauEnvelope_finite_of_minimizer H φ μ f
    (exists_unique_proximalMinimizer H φ hp hc hl μ hμ f).exists

/-- The already defined total choice selects the unique finite-energy minimizer. -/
theorem proximalMap_minimizes : ExistenceSpec.ProximalMapMinimizes.{u} := by
  intro H _ _ _ φ hp hc hl μ hμ f
  exact proximalMap_isMinimizer H φ μ f
    (exists_unique_proximalMinimizer H φ hp hc hl μ hμ f).exists

end ExpandedFA.Proximal
