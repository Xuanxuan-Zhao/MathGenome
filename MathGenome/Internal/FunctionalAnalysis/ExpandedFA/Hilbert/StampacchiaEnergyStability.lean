import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.StampacchiaEnergyStability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.StampacchiaSolvability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Energy equivalence and stability for the coercive Stampacchia inequality.
The converse energy implication uses the existing variational solution and
the strictly positive energy gap. All geometry remains the original geometry.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.StampacchiaEnergyStability
universe u v

/-- The real-valued Hermitian energy, with datum represented in the antidual. -/
def energy : Spec.EnergyType.{u, v} := Spec.EnergyValue

/-- Hermitian diagonal values equal their real parts, so taking the real
part in the energy does not change the source's Hermitian quadratic term. -/
theorem hermitian_diagonal_real (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ha : Conventions.FormHermitian 𝕜 H a) (x : H) :
    (RCLike.re (a x x) : 𝕜) = a x x :=
  RCLike.conj_eq_iff_re.mp (ha x x).symm

/-- Exact expansion of the Hermitian energy about an arbitrary point. -/
theorem energy_difference (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ha : Conventions.FormHermitian 𝕜 H a)
    (f x h : H) :
    energy 𝕜 H a f (x + h) - energy 𝕜 H a f x =
      (RCLike.re (a h x) - RCLike.re ⟪h, f⟫_𝕜) + RCLike.re (a h h) / 2 := by
  have hsym : RCLike.re (a x h) = RCLike.re (a h x) := by
    rw [ha x h, RCLike.conj_re]
  change RCLike.re (a (x + h) (x + h)) / 2 - RCLike.re ⟪x + h, f⟫_𝕜 -
    (RCLike.re (a x x) / 2 - RCLike.re ⟪x, f⟫_𝕜) = _
  rw [a.map_add]
  simp only [add_apply, map_add, inner_add_left, hsym]
  ring

theorem stampacchia_exists_unique : Spec.ExistenceUniqueness.{u, v} :=
  StampacchiaSolvability.stampacchia_exists_unique

theorem stampacchia_hermitian_minimization : Spec.HermitianMinimization.{u, v} := by
  intro 𝕜 H _ _ _ _ a M α ha hc hh f C hne hclosed hconvex
  let J := energy 𝕜 H a f
  have hgap (u : H)
      (hu : ∀ v ∈ C, RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u))
      (v : H) (hv : v ∈ C) : α / 2 * ‖v - u‖ ^ 2 ≤ J v - J u := by
    have hd := energy_difference 𝕜 H a hh f u (v - u)
    rw [add_sub_cancel] at hd
    have hlinear := hu v hv
    have hquad := hc.2 (v - u)
    change α / 2 * ‖v - u‖ ^ 2 ≤ energy 𝕜 H a f v - energy 𝕜 H a f u
    linarith
  have hmin (u : H)
      (hu : ∀ v ∈ C, RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u)) :
      ∀ v ∈ C, J u ≤ J v := by
    intro v hv
    have hg := hgap u hu v hv
    have hn : 0 ≤ α / 2 * ‖v - u‖ ^ 2 :=
      mul_nonneg (by linarith [hc.1]) (sq_nonneg _)
    linarith
  have heq (u : H)
      (hu : ∀ v ∈ C, RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u))
      (v : H) (hv : v ∈ C) : J v = J u → v = u := by
    intro he
    have hg := hgap u hu v hv
    rw [he, sub_self] at hg
    have hz : ‖v - u‖ ^ 2 ≤ 0 :=
      nonpos_of_mul_nonpos_right hg (by linarith [hc.1])
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (v - u)]))
  obtain ⟨s, hs, _⟩ := stampacchia_exists_unique 𝕜 H a M α ha hc f C hne hclosed hconvex
  have hiff (u : H) :
      (u ∈ C ∧ ∀ v ∈ C,
        RCLike.re ⟪v - u, f⟫_𝕜 ≤ RCLike.re (a (v - u) u)) ↔
      (u ∈ C ∧ ∀ v ∈ C, J u ≤ J v) := by
    constructor
    · rintro ⟨hu, hvar⟩
      exact ⟨hu, hmin u hvar⟩
    · rintro ⟨hu, hmu⟩
      have hus : u = s := heq s hs.2 u hu (le_antisymm (hmu s hs.1) (hmin s hs.2 u hu))
      simpa only [hus] using hs
  refine ⟨hiff, s, ⟨hs.1, hmin s hs.2⟩, ?_⟩
  intro w hw
  exact heq s hs.2 w hw.1 (le_antisymm (hw.2 s hs.1) (hmin s hs.2 w hw.1))

theorem stampacchia_stability : Spec.Stability.{u, v} := by
  intro 𝕜 H _ _ _ _ a M α _ha hc C _hne _hclosed _hconvex f g uf ug huf hug
  have hf := huf.2 ug hug.1
  have hg := hug.2 uf huf.1
  have hneg : ug - uf = -(uf - ug) := by abel
  rw [hneg] at hf
  simp only [inner_neg_left, map_neg, neg_apply] at hf
  have hmono : RCLike.re (a (uf - ug) (uf - ug)) ≤
      RCLike.re ⟪uf - ug, f - g⟫_𝕜 := by
    rw [(a (uf - ug)).map_sub, inner_sub_right, map_sub (RCLike.re : 𝕜 →+ ℝ), map_sub (RCLike.re : 𝕜 →+ ℝ)]
    linarith
  have hbound : α * ‖uf - ug‖ ^ 2 ≤ ‖uf - ug‖ * ‖f - g‖ :=
    (hc.2 (uf - ug)).trans (hmono.trans
      ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)))
  apply (le_div_iff₀ hc.1).mpr
  by_cases hz : ‖uf - ug‖ = 0
  · simp only [hz, zero_mul]
    exact norm_nonneg _
  · have hp : 0 < ‖uf - ug‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

end ExpandedFA.Hilbert.StampacchiaEnergyStability
