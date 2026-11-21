import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.IndentedHalfDisk
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.IndentedContourCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators

namespace D12Complex.IndentedHalfDisk
open Definitions

/-- This bridge uses the actual finite set, rather than denominator roots or a
simple-pole assumption. -/
theorem mem_realSingularities (A : Finset ℂ) (x : ℝ) :
    x ∈ realSingularities A ↔ (x : ℂ) ∈ A := by
  classical
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hz' := Finset.mem_filter.mp hz
    have he : (z.re : ℂ) = z := by
      apply Complex.ext <;> simp [hz'.2]
    exact he.symm ▸ hz'.1
  · intro hx
    exact Finset.mem_image.mpr ⟨(x : ℂ), Finset.mem_filter.mpr ⟨hx, by simp⟩, by simp⟩

theorem deletedDiameter_isCompact (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) :
    IsCompact (deletedDiameter s r ε) :=
  isCompact_Icc.diff (isOpen_iUnion (fun _ => isOpen_Ioo))

theorem deletedDiameter_avoids (A : Finset ℂ) (r : ℝ)
    (ε : realSingularities A → ℝ) (hε : ∀ a, 0 < ε a) :
    ∀ x ∈ deletedDiameter (realSingularities A) r ε, (x : ℂ) ∉ A := by
  intro x hx hxA
  let a : realSingularities A := ⟨x, (mem_realSingularities A x).mpr hxA⟩
  exact hx.2 (mem_iUnion.mpr ⟨a, show x ∈ Ioo (a.val - ε a) (a.val + ε a) from
    ⟨by dsimp [a]; linarith [hε a], by dsimp [a]; linarith [hε a]⟩⟩)

theorem deletedDiameter_integrable (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f)
    (r : ℝ) (ε : realSingularities A → ℝ) (hε : ∀ a, 0 < ε a) :
    IntegrableOn (fun x : ℝ => f (x : ℂ))
      (deletedDiameter (realSingularities A) r ε) := by
  apply ContinuousOn.integrableOn_compact (deletedDiameter_isCompact _ _ _)
  intro x hx
  exact ((hf.2 (x : ℂ) ⟨mem_univ _, deletedDiameter_avoids A r ε hε x hx⟩).continuousAt.comp
    Complex.continuous_ofReal.continuousAt).continuousWithinAt

/-- The outer circle misses all excluded points; this uses strict enclosure. -/
theorem outer_circle_avoids (A : Finset ℂ) (r : ℝ) (hr : 0 < r)
    (hAr : ∀ a ∈ A, ‖a‖ < r) (t : ℝ) : circleMap 0 r t ∉ A := by
  intro ht
  have hn : ‖circleMap 0 r t‖ = r := by
    simpa only [dist_zero_right, abs_of_pos hr] using
      mem_sphere.mp (circleMap_mem_sphere' 0 r t)
  exact (ne_of_lt (hAr _ ht)) hn

/-- Continuity on the circle, without any regularity assumption at the poles. -/
theorem arc_integrable_of_avoids (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f) (a : ℂ) (ρ : ℝ)
    (havoid : ∀ t ∈ Icc (0 : ℝ) Real.pi, circleMap a ρ t ∉ A) :
    IntervalIntegrable (arcIntegrand f a ρ) volume 0 Real.pi := by
  apply ContinuousOn.intervalIntegrable_of_Icc Real.pi_pos.le
  apply ContinuousOn.mul
  · intro t ht
    exact ((hf.2 _ ⟨mem_univ _, havoid t ht⟩).continuousAt.comp
      (continuous_circleMap a ρ).continuousAt).continuousWithinAt
  · exact ((continuous_circleMap 0 ρ).mul continuous_const).continuousOn

theorem outer_arc_integrable (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f)
    (r : ℝ) (hr : 0 < r) (hAr : ∀ a ∈ A, ‖a‖ < r) :
    IntervalIntegrable (arcIntegrand f 0 r) volume 0 Real.pi :=
  arc_integrable_of_avoids A f hf 0 r (fun t _ => outer_circle_avoids A r hr hAr t)


private theorem positive_lower_bound {α : Type*} (s : Finset α) (g : α → ℝ)
    (hg : ∀ a ∈ s, 0 < g a) : ∃ η : ℝ, 0 < η ∧ ∀ a ∈ s, η < g a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hs⟩ := ih (fun b hb => hg b (Finset.mem_insert_of_mem hb))
    refine ⟨min (g a / 2) δ, lt_min (by linarith [hg a (Finset.mem_insert_self a s)]) hδ, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with he | hb
    · subst b
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith [hg a (Finset.mem_insert_self a s)])
    · exact lt_of_le_of_lt (min_le_right _ _) (hs b hb)

/-- A single strictly positive bound works for arbitrary independent radii,
including when A is empty. The factor four leaves room for doubled balls. -/
theorem uniform_indentation_radius (A : Finset ℂ) (r : ℝ)
    (hAr : ∀ a ∈ A, ‖a‖ < r) :
    ∃ η : ℝ, 0 < η ∧
      (∀ a ∈ A, 4 * η < r - ‖a‖) ∧
      ∀ a ∈ A, ∀ b ∈ A, b ≠ a → 4 * η < dist b a := by
  classical
  obtain ⟨δ, hδ, hδA⟩ := positive_lower_bound A (fun a => (r - ‖a‖) / 4)
    (by intro a ha; linarith [hAr a ha])
  let pairs := (A ×ˢ A).filter (fun p => p.1 ≠ p.2)
  obtain ⟨δ', hδ', hδA'⟩ := positive_lower_bound pairs
    (fun p => dist p.1 p.2 / 4) (by
      intro p hp
      have hne := (Finset.mem_filter.mp hp).2
      exact div_pos (dist_pos.mpr hne) (by norm_num))
  refine ⟨min δ δ', lt_min hδ hδ', ?_, ?_⟩
  · intro a ha
    have := hδA a ha
    have := min_le_left δ δ'
    linarith
  · intro a ha b hb hba
    have hp : (b, a) ∈ pairs := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hba⟩
    have := hδA' (b, a) hp
    have := min_le_right δ δ'
    linarith

/-- Every little closed ball is strictly inside the outer disk, with its
center as its only possible excluded point. -/
theorem indentation_ball_properties (A : Finset ℂ) (r η : ℝ)
    (hη : 0 < η) (hmargin : ∀ a ∈ A, 4 * η < r - ‖a‖)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → 4 * η < dist b a)
    (a : realSingularities A) (ρ : ℝ) (hρ : 0 < ρ ∧ ρ < η) :
    closedBall (a.val : ℂ) (2 * ρ) ⊆ ball 0 r ∧
      ∀ b ∈ A, b ≠ (a.val : ℂ) → 2 * ρ < dist b (a.val : ℂ) := by
  have ha : (a.val : ℂ) ∈ A := (mem_realSingularities A a.val).mp a.property
  constructor
  · intro z hz
    rw [mem_ball, dist_zero_right]
    have hz' := mem_closedBall.mp hz
    have hn : ‖z‖ ≤ dist z (a.val : ℂ) + ‖(a.val : ℂ)‖ :=
      by simpa only [dist_eq_norm, add_comm] using norm_le_insert' z (a.val : ℂ)
    linarith [hmargin _ ha]
  · intro b hb hba
    linarith [hsep _ ha b hb hba]

theorem small_circle_avoids (A : Finset ℂ) (a : realSingularities A)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ b ∈ A, b ≠ (a.val : ℂ) → ρ < dist b (a.val : ℂ))
    (t : ℝ) : circleMap (a.val : ℂ) ρ t ∉ A := by
  intro hz
  have hd : dist (circleMap (a.val : ℂ) ρ t) (a.val : ℂ) = ρ := by
    simpa only [abs_of_pos hρ] using mem_sphere.mp (circleMap_mem_sphere' (a.val : ℂ) ρ t)
  by_cases he : circleMap (a.val : ℂ) ρ t = (a.val : ℂ)
  · rw [he, dist_self] at hd
    linarith
  · exact (ne_of_gt (hsep _ hz he)) hd

/-- Distinct dents have disjoint closed doubled neighborhoods. -/
theorem indentation_balls_disjoint (A : Finset ℂ) (η : ℝ) (hη : 0 < η)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → 4 * η < dist b a)
    (ε : realSingularities A → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a < η)
    (a b : realSingularities A) (hab : a ≠ b) :
    Disjoint (closedBall (a.val : ℂ) (2 * ε a))
      (closedBall (b.val : ℂ) (2 * ε b)) := by
  apply disjoint_left.mpr
  intro z hza hzb
  have ha := (mem_realSingularities A a.val).mp a.property
  have hb := (mem_realSingularities A b.val).mp b.property
  have hba : (b.val : ℂ) ≠ (a.val : ℂ) := by
    intro he
    apply hab
    exact Subtype.ext (Complex.ofReal_injective he.symm)
  have hd := hsep _ ha _ hb hba
  have htri := dist_triangle (b.val : ℂ) z (a.val : ℂ)
  have hza' := mem_closedBall.mp hza
  have hzb' := mem_closedBall.mp hzb
  rw [dist_comm (b.val : ℂ) z] at htri
  linarith [(hε a).2, (hε b).2]

/-- All displayed integrals are genuine integrals for all sufficiently small,
independently chosen positive radii. -/
theorem integrability_for_small_radii (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f) (r : ℝ) (hr : 0 < r)
    (hAr : ∀ a ∈ A, ‖a‖ < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : realSingularities A → ℝ,
      (∀ a, 0 < ε a ∧ ε a < η) →
      IntegrableOn (fun x : ℝ => f (x : ℂ))
        (deletedDiameter (realSingularities A) r ε) ∧
      IntervalIntegrable (arcIntegrand f 0 r) volume 0 Real.pi ∧
      ∀ a : realSingularities A,
        IntervalIntegrable (arcIntegrand f (a.val : ℂ) (ε a)) volume 0 Real.pi := by
  obtain ⟨η, hη, hmargin, hsep⟩ := uniform_indentation_radius A r hAr
  refine ⟨η, hη, ?_⟩
  intro ε hε
  refine ⟨deletedDiameter_integrable A f hf r ε (fun a => (hε a).1),
    outer_arc_integrable A f hf r hr hAr, ?_⟩
  intro a
  have hball := indentation_ball_properties A r η hη hmargin hsep a (ε a) (hε a)
  apply arc_integrable_of_avoids A f hf
  intro t _
  exact small_circle_avoids A a (ε a) (hε a).1
    (fun b hb hba => lt_trans (by linarith [(hε a).1]) (hball.2 b hb hba)) t


/-- The trace set used in the specification is compact, with all arc endpoints
included. This is a statement about a set, not yet a path construction. -/
theorem boundaryTrace_isCompact (A : Finset ℂ) (r : ℝ)
    (ε : realSingularities A → ℝ) : IsCompact (boundaryTrace A r ε) := by
  classical
  exact (((deletedDiameter_isCompact _ _ _).image Complex.continuous_ofReal).union
    (isCompact_Icc.image (continuous_circleMap 0 r))).union
      (isCompact_iUnion (fun a => isCompact_Icc.image (continuous_circleMap (a.val : ℂ) (ε a))))

/-- The intended trace avoids every excluded point for small independent radii. -/
theorem boundaryTrace_disjoint (A : Finset ℂ) (r η : ℝ) (hr : 0 < r) (hη : 0 < η)
    (hAr : ∀ a ∈ A, ‖a‖ < r) (hmargin : ∀ a ∈ A, 4 * η < r - ‖a‖)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, b ≠ a → 4 * η < dist b a)
    (ε : realSingularities A → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a < η) :
    Disjoint (boundaryTrace A r ε) (A : Set ℂ) := by
  apply disjoint_left.mpr
  intro z hz hzA
  rcases hz with (⟨x, hx, rfl⟩ | ⟨t, _, rfl⟩) | hz
  · exact deletedDiameter_avoids A r ε (fun a => (hε a).1) x hx hzA
  · exact outer_circle_avoids A r hr hAr t hzA
  · obtain ⟨a, t, _, rfl⟩ := mem_iUnion.mp hz
    have hball := indentation_ball_properties A r η hη hmargin hsep a (ε a) (hε a)
    exact small_circle_avoids A a (ε a) (hε a).1
      (fun b hb hba => lt_trans (by linarith [(hε a).1]) (hball.2 b hb hba)) t hzA

/-- Once a genuine avoiding cycle and its indices have been proved, the accepted
residue theorem gives the desired finite upper-half-plane residue sum. -/
theorem residue_equation_of_indices (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f) (Γ : IntegralCycle)
    (havoid : Disjoint Γ.trace (A : Set ℂ))
    (hindex : ∀ a ∈ A, Γ.index a = if 0 < a.im then 1 else 0) :
    Γ.integral f = (2 * Real.pi * Complex.I : ℂ) *
      ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a := by
  classical
  obtain ⟨s, hs, he⟩ := ResidueCycle.residue_theorem Set.univ (A : Set ℂ) f Γ
    isOpen_univ (subset_univ _) (A.finite_toSet.isClosed.preimage continuous_subtype_val)
    A.finite_toSet.isDiscrete hf (subset_univ _) havoid (by simp)
  have hsEq : s = A.filter (fun a => 0 < a.im) := by
    ext a
    rw [hs a, Finset.mem_filter]
    constructor
    · rintro ⟨ha, hi⟩
      refine ⟨ha, ?_⟩
      by_contra hn
      exact hi (by rw [hindex a ha, ite_eq_right hn])
    · rintro ⟨ha, hi⟩
      exact ⟨ha, by rw [hindex a ha, ite_eq_left hi]; exact one_ne_zero⟩
  rw [hsEq] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨ha, hi⟩ := Finset.mem_filter.mp ha
  rw [hindex a ha, ite_eq_left hi, one_mul]


open private smoothPath from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
open Specs.D12Complex.Ch04.IndexComputations (half_disk_traversal)

/-- An actual half-disk boundary whose contour integral has the angular form
used in this goal. This is used only when the diameter avoids the singularities. -/
theorem half_disk_integral_witness (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hline : ContinuousOn f (Complex.ofReal '' Icc (-r) r))
    (harc : ContinuousOn f (circleMap 0 r '' Icc 0 Real.pi)) :
    ∃ γ : PiecewiseC1Path, half_disk_traversal γ 0 1 r ∧
      γ.integral f = (∫ x in (-r)..r, f (x : ℂ)) +
        ∫ t in (0 : ℝ)..Real.pi, arcIntegrand f 0 r t := by
  let p := smoothPath (-r) r (by linarith) Complex.ofReal Complex.ofRealCLM.contDiff
  let q := smoothPath 0 Real.pi Real.pi_pos.le (circleMap 0 r) (contDiff_circleMap 0 r)
  have hp : ContinuousOn f p.trace := hline
  have hq : ContinuousOn f q.trace := harc
  have hcompat : p.path.target = q.path.source := by
    change (r : ℂ) = circleMap 0 r 0
    simp [circleMap]
  obtain ⟨γ, ha, hb, h₁, h₂, hint⟩ := PiecewiseC1Path.concatenation p q f hcompat hp hq
  refine ⟨γ, ⟨ha, hb, ?_, ?_⟩, ?_⟩
  · intro t ht
    rw [h₁ ht]
    change ((-r + (r - -r) * t : ℝ) : ℂ) = 0 + ((r * (2 * t - 1) : ℝ) : ℂ) * 1
    push_cast; ring
  · intro t ht
    rw [h₂ ht]
    change circleMap 0 r (0 + (Real.pi - 0) * (t - 1)) = _
    simp [circleMap]
  · have hpint : p.integral f = ∫ x in (-r)..r, f (x : ℂ) := by
      rw [PiecewiseC1Path.integral_congr_representative p Complex.ofReal f hp (fun _ _ => rfl)]
      change (∫ t in (-r)..r, f (t : ℂ) * deriv Complex.ofReal t) = _
      have hd : ∀ t, deriv Complex.ofReal t = 1 := fun t =>
        Complex.ofRealCLM.hasDerivAt.deriv
      simp_rw [hd, mul_one]
    have hqint : q.integral f = ∫ t in (0 : ℝ)..Real.pi, arcIntegrand f 0 r t := by
      rw [PiecewiseC1Path.integral_congr_representative q (circleMap 0 r) f hq (fun _ _ => rfl)]
      simp only [deriv_circleMap]
      rfl
    exact hint.trans (congrArg₂ (· + ·) hpint hqint)

/-- A closed canonical path gives a genuine single-component integral cycle. -/
def pathCycle (γ : PiecewiseC1Path) (hγ : γ.IsClosed) : IntegralCycle :=
  ⟨Finsupp.single γ (1 : ℤ), by
    intro δ hδ
    have he : δ = γ := by
      have hpair : δ = γ ∧ (1 : ℤ) ≠ 0 := by
        simpa only [Finsupp.mem_support_single] using hδ
      exact hpair.1
    exact he ▸ hγ⟩

@[simp] theorem pathCycle_trace (γ : PiecewiseC1Path) (hγ : γ.IsClosed) :
    (pathCycle γ hγ).trace = γ.trace := by
  classical
  ext z
  simp [pathCycle, IntegralCycle.trace, IntegralCycle.chain, IntegralChain.trace]

@[simp] theorem pathCycle_integral (γ : PiecewiseC1Path) (hγ : γ.IsClosed) (f : ℂ → ℂ) :
    (pathCycle γ hγ).integral f = γ.integral f := by
  classical
  simp [pathCycle, IntegralCycle.integral, IntegralCycle.chain, IntegralChain.integral]

@[simp] theorem pathCycle_index (γ : PiecewiseC1Path) (hγ : γ.IsClosed) (a : ℂ) :
    (pathCycle γ hγ).index a = γ.index a := rfl

/-- The explicit traversal has precisely the diameter and upper semicircle as
its trace. Both inclusions include the two joining endpoints. -/
theorem half_disk_trace_eq (γ : PiecewiseC1Path) (r : ℝ) (hr : 0 < r)
    (ht : half_disk_traversal γ 0 1 r) :
    γ.trace = Complex.ofReal '' Icc (-r) r ∪ circleMap 0 r '' Icc 0 Real.pi := by
  rcases ht with ⟨ha, hb, hline, harc⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    change t ∈ Icc γ.path.a γ.path.b at ht
    rw [ha, hb] at ht
    by_cases ht1 : t ≤ 1
    · left
      refine ⟨r * (2 * t - 1), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [ht.1]
      · nlinarith
      · simpa using (hline t ⟨ht.1, ht1⟩).symm
    · right
      refine ⟨Real.pi * (t - 1), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos, ht.2]
      · simpa [circleMap] using (harc t ⟨le_of_not_ge ht1, ht.2⟩).symm
  · rintro (⟨x, hx, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · let t := (x / r + 1) / 2
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor
        · have : -1 ≤ x / r := (le_div_iff₀ hr).mpr (by linarith [hx.1])
          nlinarith
        · have : x / r ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using hx.2)
          nlinarith
      refine ⟨t, by simpa [ha, hb] using ⟨ht.1, le_trans ht.2 (by norm_num : (1 : ℝ) ≤ 2)⟩, ?_⟩
      rw [hline t ht]
      have hx' : r * (2 * t - 1) = x := by dsimp [t]; field_simp; ring
      simp [hx']
    · let t := 1 + θ / Real.pi
      have ht : t ∈ Icc (1 : ℝ) 2 := by
        dsimp [t]
        constructor
        · have := div_nonneg hθ.1 Real.pi_pos.le
          linarith
        · have : θ / Real.pi ≤ 1 := (div_le_iff₀ Real.pi_pos).mpr (by simpa using hθ.2)
          linarith
      refine ⟨t, by simpa [ha, hb] using ⟨le_trans (by norm_num : (0 : ℝ) ≤ 1) ht.1, ht.2⟩, ?_⟩
      rw [harc t ht]
      have hθ' : Real.pi * (t - 1) = θ := by dsimp [t]; field_simp; ring
      simp [circleMap, hθ']

/-- The no-real-singularity finite identity. A may be empty and the excluded
points may have arbitrary isolated singularity types. -/
theorem no_real_singularities_identity (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f) (r : ℝ) (hr : 0 < r)
    (hAr : ∀ a ∈ A, ‖a‖ < r) (hreal : ∀ a ∈ A, a.im ≠ 0) :
    (∫ x in Icc (-r) r, f (x : ℂ)) +
      (∫ t in (0 : ℝ)..Real.pi, arcIntegrand f 0 r t) =
      (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ A.filter (fun a => 0 < a.im), Residue.residue f a := by
  have hline : ContinuousOn f (Complex.ofReal '' Icc (-r) r) := by
    rintro z ⟨x, _, rfl⟩
    apply ContinuousAt.continuousWithinAt
    apply (hf.2 _ ⟨mem_univ _, ?_⟩).continuousAt
    intro hxA
    exact hreal (x : ℂ) hxA (by simp)
  have harc : ContinuousOn f (circleMap 0 r '' Icc 0 Real.pi) := by
    rintro z ⟨t, _, rfl⟩
    exact (hf.2 _ ⟨mem_univ _, outer_circle_avoids A r hr hAr t⟩).continuousAt.continuousWithinAt
  obtain ⟨γ, ht, hint⟩ := half_disk_integral_witness f r hr hline harc
  have hγ := IndexComputations.half_disk_closed γ ht
  let Γ := pathCycle γ hγ
  have havoid : Disjoint Γ.trace (A : Set ℂ) := by
    rw [pathCycle_trace]
    apply disjoint_left.mpr
    intro z hz hzA
    have hc := (IndexComputations.half_disk_trace_coordinates γ (by simp) hr ht z hz).2
    simp only [sub_zero, div_one] at hc
    rcases hc with hn | hi
    · exact (ne_of_lt (hAr z hzA)) hn
    · exact hreal z hzA hi
  have hindex : ∀ a ∈ A, Γ.index a = if 0 < a.im then 1 else 0 := by
    intro a ha
    rw [pathCycle_index]
    by_cases hi : 0 < a.im
    · rw [ite_eq_left hi]
      apply IndexComputations.half_disk_index_interior γ 0 1 a r (by simp) hr ht
      simpa using And.intro (hAr a ha) hi
    · rw [ite_eq_right hi]
      apply IndexComputations.half_disk_index_exterior γ 0 1 a r (by simp) hr ht
      right
      simpa using lt_of_le_of_ne (le_of_not_gt hi) (hreal a ha)
  have he := residue_equation_of_indices A f hf Γ havoid hindex
  rw [pathCycle_integral, hint, intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    ← integral_Icc_eq_integral_Ioc] at he
  exact he


/-- With no real excluded point the full cycle witness exists, including the
exact trace and integral decomposition. The deletion index type is then empty,
so no condition on its (vacuous) radii is needed. -/
theorem no_real_singularities_cycle (A : Finset ℂ) (f : ℂ → ℂ)
    (hf : HolomorphicOn (Set.univ \ (A : Set ℂ)) f) (r : ℝ) (hr : 0 < r)
    (hAr : ∀ a ∈ A, ‖a‖ < r) (hreal : ∀ a ∈ A, a.im ≠ 0)
    (ε : realSingularities A → ℝ) :
    ∃ Γ : IntegralCycle,
      Γ.trace = boundaryTrace A r ε ∧ Disjoint Γ.trace (A : Set ℂ) ∧
      (∀ a ∈ A, Γ.index a = if 0 < a.im then 1 else 0) ∧
      Γ.integral f = boundaryIntegral A f r ε := by
  classical
  have hs : realSingularities A = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    exact hreal (x : ℂ) ((mem_realSingularities A x).mp hx) (by simp)
  haveI : IsEmpty (realSingularities A) := ⟨fun a => by simpa [hs] using a.property⟩
  have hline : ContinuousOn f (Complex.ofReal '' Icc (-r) r) := by
    rintro z ⟨x, _, rfl⟩
    apply ContinuousAt.continuousWithinAt
    apply (hf.2 _ ⟨mem_univ _, ?_⟩).continuousAt
    intro hxA
    exact hreal (x : ℂ) hxA (by simp)
  have harc : ContinuousOn f (circleMap 0 r '' Icc 0 Real.pi) := by
    rintro z ⟨t, _, rfl⟩
    exact (hf.2 _ ⟨mem_univ _, outer_circle_avoids A r hr hAr t⟩).continuousAt.continuousWithinAt
  obtain ⟨γ, ht, hint⟩ := half_disk_integral_witness f r hr hline harc
  have hγ := IndexComputations.half_disk_closed γ ht
  refine ⟨pathCycle γ hγ, ?_, ?_, ?_, ?_⟩
  · rw [pathCycle_trace, half_disk_trace_eq γ r hr ht]
    simp [boundaryTrace, deletedDiameter]
  · rw [pathCycle_trace, half_disk_trace_eq γ r hr ht]
    apply disjoint_left.mpr
    intro z hz hzA
    rcases hz with ⟨x, _, rfl⟩ | ⟨t, _, rfl⟩
    · exact hreal (x : ℂ) hzA (by simp)
    · exact outer_circle_avoids A r hr hAr t hzA
  · intro a ha
    rw [pathCycle_index]
    by_cases hi : 0 < a.im
    · rw [ite_eq_left hi]
      apply IndexComputations.half_disk_index_interior γ 0 1 a r (by simp) hr ht
      simpa using And.intro (hAr a ha) hi
    · rw [ite_eq_right hi]
      apply IndexComputations.half_disk_index_exterior γ 0 1 a r (by simp) hr ht
      right
      simpa using lt_of_le_of_ne (le_of_not_gt hi) (hreal a ha)
  · rw [pathCycle_integral, hint, intervalIntegral.integral_of_le (by linarith : -r ≤ r),
      ← integral_Icc_eq_integral_Ioc]
    simp [boundaryIntegral, deletedDiameter]


/-- An upward dent and the outer upper arc stay in the closed upper half-plane. -/
theorem boundaryTrace_im_nonneg (A : Finset ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ε : realSingularities A → ℝ) (hε : ∀ a, 0 ≤ ε a) :
    ∀ z ∈ boundaryTrace A r ε, 0 ≤ z.im := by
  have harc (a : ℂ) (ha : a.im = 0) (ρ : ℝ) (hρ : 0 ≤ ρ)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) : 0 ≤ (circleMap a ρ t).im := by
    simpa [circleMap, Complex.add_im, Complex.mul_im, Complex.exp_im, ha] using
      mul_nonneg hρ (Real.sin_nonneg_of_mem_Icc ht)
  intro z hz
  rcases hz with (⟨x, _, rfl⟩ | ⟨t, ht, rfl⟩) | hz
  · simp
  · exact harc 0 (by simp) r hr t ht
  · obtain ⟨a, t, ht, rfl⟩ := mem_iUnion.mp hz
    exact harc (a.val : ℂ) (by simp) (ε a) (hε a) t ht

/-- A downward ray proves index zero directly, even at a removed real pole.
No index of an unindented path at a point on its diameter is used. -/
theorem closed_path_index_zero_below (γ : PiecewiseC1Path) (hγ : γ.IsClosed)
    (hupper : ∀ z ∈ γ.trace, 0 ≤ z.im) (a : ℂ) (ha : a.im ≤ 0)
    (havoid : a ∉ γ.trace) : γ.index a = 0 := by
  apply IndexComputations.closed_path_index_zero_of_avoids_ray γ a (-Complex.I) hγ
    (neg_ne_zero.mpr Complex.I_ne_zero)
  intro t ht
  rintro ⟨s, hs, he⟩
  have him := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.neg_im,
    Complex.I_im, Complex.ofReal_im, Complex.neg_re, Complex.I_re, neg_zero,
    mul_zero, add_zero, mul_neg, mul_one] at him
  have hγt := hupper (γ t) ⟨t, ht, rfl⟩
  have hs0 : s = 0 := by linarith
  have heq : γ t = a := sub_eq_zero.mp (by simpa only [hs0, Complex.ofReal_zero, zero_mul] using he)
  exact havoid ⟨t, ht, heq⟩

/-- Thus every closed path with the intended trace has the required zero index
at every real or lower excluded point, regardless of traversal details. -/
theorem boundary_path_index_nonpositive (A : Finset ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ε : realSingularities A → ℝ) (hε : ∀ a, 0 ≤ ε a)
    (γ : PiecewiseC1Path) (hγ : γ.IsClosed) (htrace : γ.trace ⊆ boundaryTrace A r ε)
    (havoid : Disjoint γ.trace (A : Set ℂ)) (a : ℂ) (haA : a ∈ A) (ha : a.im ≤ 0) :
    γ.index a = 0 :=
  closed_path_index_zero_below γ hγ
    (fun z hz => boundaryTrace_im_nonneg A r hr ε hε z (htrace hz)) a ha
    (fun ht => disjoint_left.mp havoid ht haA)

/-- The exact finite indented contour theorem. The ordered indented diameter
and the outer arc form a genuine avoiding cycle before residues are applied. -/
theorem finite_indented_half_disk :
    Specs.D12Complex.Ch08.IndentedHalfDisk.finite_indented_half_disk_type := by
  intro A f r hf hr hAr
  obtain ⟨η, hη, hmargin, hsep⟩ := uniform_indentation_radius A r hAr
  refine ⟨η, hη, ?_⟩
  intro ε hε
  have hsmall : ∀ a : realSingularities A,
      IntervalIntegrable (arcIntegrand f (a.val : ℂ) (ε a)) volume 0 Real.pi := by
    intro a
    have hball := indentation_ball_properties A r η hη hmargin hsep a (ε a) (hε a)
    apply arc_integrable_of_avoids A f hf
    intro t _
    exact small_circle_avoids A a (ε a) (hε a).1
      (fun b hb hba => lt_trans (by linarith [(hε a).1]) (hball.2 b hb hba)) t
  have hcycle : ∃ Γ : IntegralCycle,
      Γ.trace = boundaryTrace A r ε ∧ Disjoint Γ.trace (A : Set ℂ) ∧
      (∀ a ∈ A, Γ.index a = if 0 < a.im then 1 else 0) ∧
      Γ.integral f = boundaryIntegral A f r ε := by
    have hgeometry : Specs.D12Complex.Ch08.IndentedContourCalculus.Geometry
        (realSingularities A) r ε := by
      refine ⟨hr, ?_, ?_⟩
      · intro x
        have hx := (mem_realSingularities A x.val).mp x.property
        have hm := hmargin _ hx
        rw [Complex.norm_real, Real.norm_eq_abs] at hm
        exact ⟨(hε x).1, by linarith [(hε x).2]⟩
      · intro x y hxy
        have hx := (mem_realSingularities A x.val).mp x.property
        have hy := (mem_realSingularities A y.val).mp y.property
        have hne : (x.val : ℂ) ≠ (y.val : ℂ) :=
          fun he => hxy (Subtype.ext (Complex.ofReal_injective he))
        have hs := hsep _ hy _ hx hne
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hs
        linarith [(hε x).2, (hε y).2]
    obtain ⟨n, e, start, stop, γ, δ, _hg, _ht, _hs, _hu, _hd, _ho,
      hclosed, htrace, hcalc, hupper, hlower⟩ :=
      IndentedContourCalculus.contour_calculus (realSingularities A) r ε hgeometry
    have havoid := boundaryTrace_disjoint A r η hr hη hAr hmargin hsep ε hε
    have hcont : ContinuousOn f (boundaryTrace A r ε) := by
      intro z hz
      exact (hf.2 z ⟨mem_univ _, fun hzA => disjoint_left.mp havoid hz hzA⟩).continuousAt.continuousWithinAt
    have htrace' : δ.trace = boundaryTrace A r ε := htrace
    refine ⟨pathCycle δ hclosed, ?_, ?_, ?_, ?_⟩
    · exact (pathCycle_trace δ hclosed).trans htrace'
    · rw [pathCycle_trace, htrace']
      exact havoid
    · intro a ha
      rw [pathCycle_index]
      by_cases hi : 0 < a.im
      · rw [ite_eq_left hi]
        apply (hupper a (hAr a ha) hi ?_).2
        intro x
        have hx := (mem_realSingularities A x.val).mp x.property
        have hne : a ≠ (x.val : ℂ) := by
          intro he
          have := congrArg Complex.im he
          simp only [Complex.ofReal_im] at this
          linarith
        have hs := hsep _ hx _ ha hne
        rw [dist_eq_norm] at hs
        linarith [(hε x).2]
      · rw [ite_eq_right hi]
        apply hlower a (le_of_not_gt hi)
        exact fun hz => disjoint_left.mp havoid hz ha
    · exact (pathCycle_integral δ hclosed f).trans (hcalc f hcont).2.2
  refine ⟨deletedDiameter_integrable A f hf r ε (fun a => (hε a).1),
    outer_arc_integrable A f hf r hr hAr, hsmall, hcycle, ?_⟩
  obtain ⟨Γ, _, havoid, hi, hint⟩ := hcycle
  rw [← hint]
  exact residue_equation_of_indices A f hf Γ havoid hi

end D12Complex.IndentedHalfDisk
