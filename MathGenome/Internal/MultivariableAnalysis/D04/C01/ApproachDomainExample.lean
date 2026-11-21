import MathGenome.Internal.MultivariableAnalysis.D04.C01.SequentialContinuity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.ApproachDomainExample
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
namespace D04.ApproachDomainExample

@[simp] theorem point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_one (x y : ℝ) : point x y 1 = y := rfl

private theorem point_ne_zero {x y : ℝ} (hx : x ≠ 0) : point x y ≠ 0 := by
  intro h
  exact hx (congrArg (fun p : E 2 => p 0) h)

private theorem point_eta (p : E 2) : point (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

private theorem scalar_tendsto_iff {u : ℕ → ℝ} {b : ℝ} :
    Tendsto (fun k => scalar (u k)) atTop (𝓝 (scalar b)) ↔
      Tendsto u atTop (𝓝 b) := by
  rw [tendsto_iff_coordinate_tendsto]
  simp [scalar]

private theorem limitOn_iff_sequence (A : Set (E 2)) (b : ℝ)
    (ha : AccumulationPoint A 0) :
    limitOn A b ↔ ∀ s : ℕ → A, (∀ k, (s k : E 2) ≠ 0) →
      Tendsto (fun k => (s k : E 2)) atTop (𝓝 0) →
      Tendsto (fun k => value (s k)) atTop (𝓝 b) := by
  change RelativeLimit A (fun p => scalar (value p)) 0 (scalar b) ↔ _
  rw [relativeLimit_iff_sequence _ _ _ _ ha]
  simp_rw [scalar_tendsto_iff]

private def small (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
private theorem small_pos (k : ℕ) : 0 < small k := by
  unfold small
  positivity
private theorem small_tendsto : Tendsto small atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem point_tendsto {u v : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun k => point (u k) (v k)) atTop (𝓝 0) := by
  apply (tendsto_iff_coordinate_tendsto _ _).mpr
  intro i
  fin_cases i
  · exact hu
  · exact hv

private theorem line_accumulation (m : ℝ) : AccumulationPoint (lineSet m) 0 := by
  apply (accumulationPoint_iff_sequence _ _).mpr
  refine ⟨fun k => point (small k) (m * small k), ?_, ?_⟩
  · intro k
    have hn := point_ne_zero (y := m * small k) (small_pos k).ne'
    exact ⟨⟨hn, rfl⟩, hn⟩
  · exact point_tendsto small_tendsto (by simpa using small_tendsto.const_mul m)

private theorem parabola_accumulation : AccumulationPoint positiveParabola 0 := by
  apply (accumulationPoint_iff_sequence _ _).mpr
  refine ⟨fun k => point (small k) (small k ^ 2), ?_, ?_⟩
  · intro k
    exact ⟨⟨small_pos k, rfl⟩, point_ne_zero (small_pos k).ne'⟩
  · exact point_tendsto small_tendsto (by simpa using small_tendsto.pow 2)

private theorem line_value (m x : ℝ) (hx : x ≠ 0) :
    value (point x (m * x)) = m * x / (x ^ 2 + m ^ 2) := by
  simp only [value, point_zero, point_one]
  have hden : x ^ 2 + m ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg
    (sq_pos_of_ne_zero hx) (sq_nonneg m))
  have hfactor : x ^ 4 + (m * x) ^ 2 = x ^ 2 * (x ^ 2 + m ^ 2) := by ring
  rw [hfactor]
  field_simp

theorem vertical_value (p : puncturedPlane) (hp : (p : E 2) 0 = 0) : f p = 0 := by
  simp [f, value, hp]

theorem parabola_value (x : ℝ) (hx : x ≠ 0) :
    value (point x (x ^ 2)) = 1 / 2 := by
  simp only [value, point_zero, point_one]
  have hpow : x ^ 4 ≠ 0 := pow_ne_zero _ hx
  have hden : x ^ 4 + (x ^ 2) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem line_limit (m : ℝ) : limitOn (lineSet m) 0 := by
  apply (limitOn_iff_sequence _ _ (line_accumulation m)).mpr
  intro s hs ht
  have hx : Tendsto (fun k => (s k : E 2) 0) atTop (𝓝 0) :=
    (tendsto_iff_coordinate_tendsto _ _).mp ht 0
  have hval (k : ℕ) : value (s k) =
      m * (s k : E 2) 0 / ((s k : E 2) 0 ^ 2 + m ^ 2) := by
    have hp := (s k).property
    have hnonzero : (s k : E 2) 0 ≠ 0 := by
      intro hz
      apply hp.1
      rw [← point_eta (s k), hp.2, hz]
      simp [point]
    rw [← point_eta (s k), hp.2]
    exact line_value _ _ hnonzero
  simp_rw [hval]
  by_cases hm : m = 0
  · simp [hm]
  · have h := (hx.const_mul m).div ((hx.pow 2).add_const (m ^ 2))
      (by simpa using pow_ne_zero 2 hm)
    convert h using 1
    simp

theorem positiveParabola_limit : limitOn positiveParabola (1 / 2) := by
  apply (limitOn_iff_sequence _ _ parabola_accumulation).mpr
  intro s hs ht
  have hval (k : ℕ) : value (s k) = 1 / 2 := by
    rw [← point_eta (s k), (s k).property.2]
    exact parabola_value _ (s k).property.1.ne'
  simpa only [hval] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop _)

theorem horizontal_limit : limitOn horizontalSet 0 := line_limit 0

private theorem vertical_accumulation : AccumulationPoint verticalSet 0 := by
  apply (accumulationPoint_iff_sequence _ _).mpr
  refine ⟨fun k => point 0 (small k), ?_, point_tendsto tendsto_const_nhds small_tendsto⟩
  intro k
  have hn : point 0 (small k) ≠ 0 := by
    intro he
    exact (small_pos k).ne' (congrArg (fun p : E 2 => p 1) he)
  exact ⟨⟨hn, rfl⟩, hn⟩

theorem vertical_limit : limitOn verticalSet 0 := by
  apply (limitOn_iff_sequence _ _ vertical_accumulation).mpr
  intro s hs ht
  have hval (k : ℕ) : value (s k) = 0 := by
    exact vertical_value ⟨s k, (s k).property.1⟩ (s k).property.2
  simpa only [hval] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop _)

private theorem limitOn_mono {A B : Set (E 2)} {b : ℝ} (hBA : B ⊆ A)
    (hB : AccumulationPoint B 0) (h : limitOn A b) : limitOn B b := by
  refine ⟨hB, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := h.2 ε hε
  exact ⟨δ, hδ, fun x => hd ⟨x.val, hBA x.property⟩⟩

private theorem limitOn_unique {A : Set (E 2)} {b c : ℝ}
    (hb : limitOn A b) (hc : limitOn A c) : b = c := by
  have he : scalar b = scalar c :=
    relativeLimit_unique A (fun p => scalar (value p)) 0 _ _ hb.1 hb hc
  exact congrArg (fun z : E 1 => z 0) he

theorem no_plane_limit : ¬ ∃ b : ℝ, limitOn puncturedPlane b := by
  rintro ⟨b, hb⟩
  have hh : limitOn horizontalSet b :=
    limitOn_mono (fun _ hp => hp.1) (line_accumulation 0) hb
  have hsub : positiveParabola ⊆ puncturedPlane := by
    intro p hp he
    exact hp.1.ne' (congrArg (fun z : E 2 => z 0) he)
  have hp : limitOn positiveParabola b :=
    limitOn_mono hsub parabola_accumulation hb
  have hzero : b = 0 := limitOn_unique hh horizontal_limit
  have hhalf : b = 1 / 2 := limitOn_unique hp positiveParabola_limit
  linarith

end D04.ApproachDomainExample
