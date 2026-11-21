import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.GenericNondifferentiability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01ExamplesComplete
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace ExpandedFA.Supplements.GenericNondifferentiability
/-- At every base point there is a secant of length less than `r`
whose slope in norm exceeds `n`. The strict inequality forces distinct points. -/
def largeSecants (𝕜 : Type*) [RCLike 𝕜] (n r : ℝ) : Set C(Interval, 𝕜) :=
  {f | ∀ x : Interval, ∃ y : Interval,
    dist y x < r ∧ n * dist y x < dist (f y) (f x)}

/-- Compactness of the interval makes the uniform-in-the-base-point condition open. -/
theorem isOpen_largeSecants (𝕜 : Type*) [RCLike 𝕜] (n r : ℝ) :
    IsOpen (largeSecants 𝕜 n r) := by
  classical
  let H : Set (C(Interval, 𝕜) × Interval) :=
    {p | ∃ y : Interval, dist y p.2 < r ∧ n * dist y p.2 < dist (p.1 y) (p.1 p.2)}
  have hH : IsOpen H := by
    change IsOpen {p : C(Interval, 𝕜) × Interval | ∃ y : Interval, _}
    simp only [ofPred_exists]
    apply isOpen_iUnion
    intro y
    apply IsOpen.inter
    · exact isOpen_lt (continuous_const.dist continuous_snd) continuous_const
    · exact isOpen_lt
        (continuous_const.mul (continuous_const.dist continuous_snd))
        (((continuous_eval_const y).comp continuous_fst).dist continuous_eval)
  have heq : largeSecants 𝕜 n r = (Prod.fst '' Hᶜ)ᶜ := by
    ext f
    change (∀ x : Interval, ∃ y : Interval,
      dist y x < r ∧ n * dist y x < dist (f y) (f x)) ↔ f ∉ Prod.fst '' Hᶜ
    constructor
    · intro hf hbad
      obtain ⟨⟨g, x⟩, hnot, hgf⟩ := hbad
      change g = f at hgf
      subst g
      exact hnot (hf x)
    · intro hf x
      by_contra hnot
      exact hf ⟨(f, x), hnot, rfl⟩
  rw [heq]
  exact (isClosedMap_fst_of_compactSpace _ hH.isClosed_compl).isOpen_compl
/-- Every sufficiently short period supplies both extreme values of a cosine
inside a short interval containing a prescribed point, including at endpoints. -/
theorem cosine_extrema_near (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (x : Interval) :
    ∃ y z : Interval, dist y x ≤ p ∧ dist z x ≤ p ∧
      Real.cos (2 * Real.pi / p * (y : ℝ)) = 1 ∧
      Real.cos (2 * Real.pi / p * (z : ℝ)) = -1 := by
  let a : ℝ := min (x : ℝ) (1 - p)
  have ha0 : 0 ≤ a := le_min x.property.1 (by linarith)
  have hax : a ≤ x := min_le_left _ _
  have hap : a + p ≤ 1 := by dsimp [a]; linarith [min_le_right (x : ℝ) (1-p)]
  have hxa : (x : ℝ) ≤ a + p := by
    dsimp [a]
    rw [← min_add_add_right]
    exact le_min (by linarith) (by linarith [x.property.2])
  let w : ℝ → ℝ := fun t => Real.cos (2 * Real.pi / p * t)
  have hper : Function.Periodic w p := by
    intro t
    dsimp [w]
    have heq : 2 * Real.pi / p * (t + p) = 2 * Real.pi / p * t + 2 * Real.pi := by
      field_simp
    rw [heq, Real.cos_add_two_pi]
  have hplus : (1 : ℝ) ∈ Set.range w := by
    exact ⟨0, by simp [w]⟩
  have hminus : (-1 : ℝ) ∈ Set.range w := by
    refine ⟨p / 2, ?_⟩
    dsimp [w]
    have heq : 2 * Real.pi / p * (p / 2) = Real.pi := by field_simp
    rw [heq, Real.cos_pi]
  rw [← hper.image_Icc hp a] at hplus hminus
  obtain ⟨y, hy, hyc⟩ := hplus
  obtain ⟨z, hz, hzc⟩ := hminus
  have hin (t : ℝ) (ht : t ∈ Icc a (a+p)) : t ∈ Icc (0 : ℝ) 1 :=
    ⟨le_trans ha0 ht.1, le_trans ht.2 hap⟩
  refine ⟨⟨y, hin y hy⟩, ⟨z, hin z hz⟩, ?_, ?_, hyc, hzc⟩
  · change |y - (x : ℝ)| ≤ p
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · change |z - (x : ℝ)| ≤ p
    exact abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- Arbitrarily small cosine perturbations create large secants everywhere. -/
theorem dense_largeSecants (𝕜 : Type*) [RCLike 𝕜]
    (n r : ℝ) (hn : 0 ≤ n) (hr : 0 < r) : Dense (largeSecants 𝕜 n r) := by
  classical
  rw [Metric.dense_iff]
  intro f ε hε
  let a : ℝ := ε / 2
  have ha : 0 < a := half_pos hε
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp huc a ha
  have hsmall : 0 < min 1 (min r (min (δ / 2) (a / (2 * (n+1))))) := by
    positivity
  obtain ⟨p, hp, hpbound⟩ := exists_between hsmall
  have hp1 : p < 1 := lt_of_lt_of_le hpbound (min_le_left _ _)
  have hpr : p < r := lt_of_lt_of_le hpbound
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hpδ : p < δ / 2 := lt_of_lt_of_le hpbound
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hpa : p < a / (2 * (n+1)) := lt_of_lt_of_le hpbound
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hnpa : 2 * n * p < a := by
    have := (lt_div_iff₀ (show 0 < 2 * (n+1) by positivity)).mp hpa
    nlinarith
  let w : C(Interval, 𝕜) := ⟨fun t =>
    ((a * Real.cos (2 * Real.pi / p * (t : ℝ)) : ℝ) : 𝕜), by fun_prop⟩
  let g : C(Interval, 𝕜) := f + w
  have hw : ‖w‖ ≤ a := by
    apply (ContinuousMap.norm_le w ha.le).mpr
    intro t
    change ‖((a * Real.cos (2 * Real.pi / p * (t : ℝ)) : ℝ) : 𝕜)‖ ≤ a
    rw [RCLike.norm_ofReal, abs_mul, abs_of_pos ha]
    nlinarith [Real.abs_cos_le_one (2 * Real.pi / p * (t : ℝ))]
  refine ⟨g, ?_, ?_⟩
  · change dist g f < ε
    calc
      dist g f = ‖w‖ := by simp [g, dist_eq_norm]
      _ ≤ a := hw
      _ < ε := by dsimp [a]; linarith
  · intro x
    by_contra hbad
    push Not at hbad
    obtain ⟨y, z, hy, hz, hyc, hzc⟩ := cosine_extrema_near p hp hp1.le x
    have hgy : dist (g y) (g x) ≤ n * p :=
      (hbad y (hy.trans_lt hpr)).trans (mul_le_mul_of_nonneg_left hy hn)
    have hgz : dist (g z) (g x) ≤ n * p :=
      (hbad z (hz.trans_lt hpr)).trans (mul_le_mul_of_nonneg_left hz hn)
    have hgyz : dist (g y) (g z) ≤ 2 * n * p := by
      have := dist_triangle (g y) (g x) (g z)
      rw [dist_comm (g x) (g z)] at this
      linarith
    have hyz : dist y z < δ := by
      have := dist_triangle y x z
      rw [dist_comm x z] at this
      linarith
    have hfyz : dist (f y) (f z) < a := hfδ hyz
    have hid : ((2 * a : ℝ) : 𝕜) = (g y - g z) - (f y - f z) := by
      simp only [g, ContinuousMap.add_apply, w, ContinuousMap.coe_mk, hyc, hzc]
      push_cast
      ring
    have hnorm := norm_sub_le (g y - g z) (f y - f z)
    rw [← hid, RCLike.norm_ofReal, abs_of_pos (show 0 < 2*a by positivity)] at hnorm
    rw [← dist_eq_norm, ← dist_eq_norm] at hnorm
    linarith

/-- Unbounded secants at arbitrarily small scales exclude every finite limit of
secant quotients. The argument takes place in the interval subtype, so it applies
unchanged to the two endpoint neighborhood filters. -/
theorem not_hasFiniteDerivative_of_largeSecants
    {𝕜 : Type*} [RCLike 𝕜] {f : C(Interval, 𝕜)}
    (hf : ∀ n m : ℕ, f ∈ largeSecants 𝕜 (n : ℝ) (1 / ((m : ℝ) + 1)))
    (x : Interval) : ¬ HasFiniteDerivative f x := by
  rintro ⟨d, hd⟩
  obtain ⟨δ, hδ, hdδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp hd 1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_gt (1 + ‖d‖)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  obtain ⟨y, hyr, hys⟩ := hf n m x
  have hyne : y ≠ x := by
    intro heq
    subst y
    simp at hys
  have hq := hdδ (by simpa only [mem_compl_iff, mem_singleton_iff] using hyne)
    (hyr.trans hm)
  have hqbound : ‖(f y - f x) / (((y : ℝ) - (x : ℝ) : ℝ) : 𝕜)‖ < (n : ℝ) := by
    calc
      _ ≤ dist ((f y - f x) / (((y : ℝ) - (x : ℝ) : ℝ) : 𝕜)) d + ‖d‖ :=
        by rw [dist_eq_norm]; exact norm_le_norm_sub_add _ _
      _ < 1 + ‖d‖ := by linarith
      _ < (n : ℝ) := hn
  have heq : ‖(f y - f x) / (((y : ℝ) - (x : ℝ) : ℝ) : 𝕜)‖ =
      dist (f y) (f x) / dist y x := by
    simp only [norm_div, RCLike.norm_ofReal, dist_eq_norm, Subtype.dist_eq,
      Real.norm_eq_abs]
  rw [heq] at hqbound
  have hlt := (div_lt_iff₀ (dist_pos.mpr hyne)).mp hqbound
  linarith
/-- A typical scalar continuous function on the real unit interval has no finite
derivative anywhere, with the appropriate one-sided interpretation at endpoints. -/
theorem generic_nondifferentiability : Spec.GenericNondifferentiability := by
  intro 𝕜 _
  let : BaireSpace C(Interval, 𝕜) :=
    ExpandedFA.P1.C07Baire.baireSpace_of_completeMetric _
  let U : ℕ × ℕ → Set C(Interval, 𝕜) := fun k =>
    largeSecants 𝕜 (k.1 : ℝ) (1 / ((k.2 : ℝ) + 1))
  have ho : ∀ k, IsOpen (U k) := fun k => isOpen_largeSecants 𝕜 _ _
  have hd : ∀ k, Dense (U k) := fun k =>
    dense_largeSecants 𝕜 _ _ (Nat.cast_nonneg _) (by positivity)
  refine ⟨⋂ k, U k, dense_iInter_of_isOpen ho hd, IsGδ.iInter_of_isOpen ho, ?_⟩
  intro f hf x
  apply not_hasFiniteDerivative_of_largeSecants (f := f) _ x
  intro n m
  exact mem_iInter.mp hf (n, m)

end ExpandedFA.Supplements.GenericNondifferentiability
