import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.HilbertProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
universe u
namespace VariationalNotes.Existence

/-- Projection onto a nonempty closed convex subset of a real Hilbert space. -/
def realProjection {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) : H → H := Specs.realProjection C hne hclosed hconv

section Real
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)

private theorem realProjection_minimum (x : H) :
    realProjection C hne hclosed hconv x ∈ C ∧
    ‖x - realProjection C hne hclosed hconv x‖ = ⨅ w : C, ‖x - w‖ :=
  Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv x)

theorem realProjection_nearest (x : H) :
    realProjection C hne hclosed hconv x ∈ C ∧
    ∀ y ∈ C, ‖x - realProjection C hne hclosed hconv x‖ ≤ ‖x - y‖ := by
  refine ⟨(realProjection_minimum C hne hclosed hconv x).1, ?_⟩
  intro y hy
  rw [(realProjection_minimum C hne hclosed hconv x).2]
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨y, hy⟩ : C)

omit [CompleteSpace H] in
/-- Two variational inequalities give the quantitative firm estimate. -/
theorem firm_bound_of_variational {x z p q : H}
    (hp : inner ℝ (x - p) (q - p) ≤ 0) (hq : inner ℝ (z - q) (p - q) ≤ 0) :
    ‖p - q‖ ^ 2 ≤ inner ℝ (p - q) (x - z) := by
  have hid : inner ℝ (p - q) (x - z) - ‖p - q‖ ^ 2 =
      -inner ℝ (x - p) (q - p) - inner ℝ (z - q) (p - q) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    simp only [real_inner_comm p x, real_inner_comm q x,
      real_inner_comm p z, real_inner_comm q z, real_inner_comm q p]
    ring
  linarith

omit [CompleteSpace H] in
private theorem variational_unique {x p q : H}
    (hp : inner ℝ (x - p) (q - p) ≤ 0) (hq : inner ℝ (x - q) (p - q) ≤ 0) : p = q := by
  have h := firm_bound_of_variational hp hq
  simp only [sub_self, inner_zero_right] at h
  have hn : ‖p - q‖ = 0 := by nlinarith [norm_nonneg (p - q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem realProjection_unique (x p : H) :
    (p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x-y‖) ↔
      p = realProjection C hne hclosed hconv x := by
  constructor
  · rintro ⟨hp, hmin⟩
    let : Nonempty C := hne.to_subtype
    have heq : ‖x - p‖ = ⨅ w : C, ‖x - w‖ := by
      apply le_antisymm
      · exact le_ciInf (fun w => hmin w w.property)
      · exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨p, hp⟩ : C)
    have hpvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mp heq
    have hproj := realProjection_minimum C hne hclosed hconv x
    have hqvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hproj.1).mp hproj.2
    exact variational_unique (hpvar _ hproj.1) (hqvar _ hp)
  · rintro rfl
    exact realProjection_nearest C hne hclosed hconv x

include hne hclosed hconv in
theorem realProjection_existsUnique (x : H) :
    ∃! p : H, p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x-y‖ := by
  exact ⟨realProjection C hne hclosed hconv x,
    realProjection_nearest C hne hclosed hconv x,
    fun p hp => (realProjection_unique C hne hclosed hconv x p).mp hp⟩

theorem realProjection_variational (x p : H) :
    p = realProjection C hne hclosed hconv x ↔
    p ∈ C ∧ ∀ y ∈ C, inner ℝ (x - p) (y-p) ≤ 0 := by
  constructor
  · rintro rfl
    have h := realProjection_minimum C hne hclosed hconv x
    exact ⟨h.1, (norm_eq_iInf_iff_real_inner_le_zero hconv h.1).mp h.2⟩
  · rintro ⟨hp, hvar⟩
    apply (realProjection_unique C hne hclosed hconv x p).mp
    refine ⟨hp, ?_⟩
    have heq := (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mpr hvar
    intro y hy
    rw [heq]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨y, hy⟩ : C)

theorem realProjection_firm (x z : H) :
    ‖realProjection C hne hclosed hconv x - realProjection C hne hclosed hconv z‖ ^ 2 ≤
    inner ℝ (realProjection C hne hclosed hconv x - realProjection C hne hclosed hconv z) (x - z) := by
  have hx := (realProjection_variational C hne hclosed hconv x _).mp rfl
  have hz := (realProjection_variational C hne hclosed hconv z _).mp rfl
  exact firm_bound_of_variational (hx.2 _ hz.1) (hz.2 _ hx.1)

theorem realProjection_nonexpansive : LipschitzWith 1 (realProjection C hne hclosed hconv) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  have hfirm := realProjection_firm C hne hclosed hconv x z
  have hcs := real_inner_le_norm
    (realProjection C hne hclosed hconv x - realProjection C hne hclosed hconv z) (x - z)
  nlinarith [norm_nonneg (realProjection C hne hclosed hconv x - realProjection C hne hclosed hconv z),
    norm_nonneg (x - z)]

theorem realProjection_continuous : Continuous (realProjection C hne hclosed hconv) :=
  (realProjection_nonexpansive C hne hclosed hconv).continuous

end Real

section Complex
attribute [local instance] InnerProductSpace.complexToReal

/-- Projection in a complex Hilbert space, using real convexity and the original metric. -/
def complexProjection {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) : H → H := Specs.complexProjection C hne hclosed hconv

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)

theorem complexProjection_nearest :
    ∀ x : H, complexProjection C hne hclosed hconv x ∈ C ∧
    ∀ y ∈ C, ‖x - complexProjection C hne hclosed hconv x‖ ≤ ‖x - y‖ := by
  exact realProjection_nearest C hne hclosed hconv

theorem complexProjection_unique :
    ∀ x p : H,
    (p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖) ↔
      p = complexProjection C hne hclosed hconv x := by
  exact realProjection_unique C hne hclosed hconv

include hne hclosed hconv in
theorem complexProjection_existsUnique :
    ∀ x : H, ∃! p : H, p ∈ C ∧ ∀ y ∈ C, ‖x - p‖ ≤ ‖x - y‖ := by
  exact realProjection_existsUnique C hne hclosed hconv

theorem complexProjection_variational :
    ∀ x p : H, p = complexProjection C hne hclosed hconv x ↔
    p ∈ C ∧ ∀ y ∈ C, (inner ℂ (x - p) (y - p)).re ≤ 0 := by
  exact realProjection_variational C hne hclosed hconv

theorem complexProjection_firm :
    ∀ x z : H,
    ‖complexProjection C hne hclosed hconv x - complexProjection C hne hclosed hconv z‖ ^ 2 ≤
    (inner ℂ (complexProjection C hne hclosed hconv x - complexProjection C hne hclosed hconv z) (x - z)).re := by
  exact realProjection_firm C hne hclosed hconv

theorem complexProjection_nonexpansive :
    LipschitzWith 1 (complexProjection C hne hclosed hconv) := by
  exact realProjection_nonexpansive C hne hclosed hconv

theorem complexProjection_continuous :
    Continuous (complexProjection C hne hclosed hconv) := by
  exact realProjection_continuous C hne hclosed hconv

end Complex
end VariationalNotes.Existence
