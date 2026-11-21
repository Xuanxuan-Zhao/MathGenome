import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ConeGeometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06OpenSeparation
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! An interior separating point, `paper.tex`, fa2:p5:cone-geometry.
We project an interior point onto the positive polar cone. The variational
inequality and open-cone separation force that projection into the original
open cone, where all its pairings are strictly positive. -/

noncomputable section
open Set Metric
open scoped InnerProductSpace Pointwise

namespace ExpandedFA.PartV.ConeGeometry
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A nonzero vector nonnegative on an open set has strictly positive
pairing at every point of that set. -/
lemma inner_pos_of_nonneg_on_open {S : Set H} (ho : IsOpen S) {u : H} (hu : u ≠ 0)
    (hn : ∀ x ∈ S, 0 ≤ ⟪x, u⟫_ℝ) {x : H} (hx : x ∈ S) : 0 < ⟪x, u⟫_ℝ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho x hx
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let t : ℝ := r / (2 * ‖u‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) hun)
  have htu : ‖t • u‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp
    nlinarith
  have hmem : x - t • u ∈ S := hball (by
    simpa only [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using htu)
  have h := hn (x - t • u) hmem
  rw [inner_sub_left, real_inner_smul_left] at h
  have huu : 0 < ⟪u, u⟫_ℝ := real_inner_self_pos.mpr hu
  nlinarith

variable [CompleteSpace H]

/-- Separation of an exterior point from an open cone by a vector in its
positive polar. The separating level is zero because the set is a cone. -/
lemma exists_polar_separator (C : ConvexCone ℝ H) (ho : IsOpen (C : Set H))
    (hne : (C : Set H).Nonempty) {x : H} (hx : x ∉ C) :
    ∃ u : H, u ≠ 0 ∧ u ∈ ProperCone.innerDual (C : Set H) ∧ ⟪x, u⟫_ℝ ≤ 0 := by
  have hd : Disjoint (C : Set H) {x} := Set.disjoint_singleton_right.mpr hx
  obtain ⟨f, α, hfn, hC, hxα⟩ := ExpandedFA.P1.C06.real_open_convex_separation
    (C : Set H) {x} hne (singleton_nonempty x) C.convex (convex_singleton x) hd ho
  have hfx : α ≤ f x := hxα x (mem_singleton x)
  have hnonpos : ∀ c ∈ C, f c ≤ 0 := by
    intro c hc
    by_contra! hpos
    let t : ℝ := (|α| + 1) / f c
    have ht : 0 < t := div_pos (by positivity) hpos
    have h := hC (t • c) (C.smul_mem ht hc)
    rw [map_smul, smul_eq_mul] at h
    have heq : t * f c = |α| + 1 := div_mul_cancel₀ _ hpos.ne'
    rw [heq] at h
    linarith [le_abs_self α]
  have hfx0 : 0 ≤ f x := by
    by_contra! hneg
    obtain ⟨c, hc⟩ := hne
    have hfc : f c < 0 := (hC c hc).trans_le hfx |>.trans hneg
    let t : ℝ := f x / (2 * f c)
    have ht : 0 < t := div_pos_of_neg_of_neg hneg (by linarith)
    have h := (hC (t • c) (C.smul_mem ht hc)).trans_le hfx
    rw [map_smul, smul_eq_mul] at h
    have heq : t * f c = f x / 2 := by dsimp [t]; field_simp [hfc.ne]
    rw [heq] at h
    linarith
  let u : H := (InnerProductSpace.toDual ℝ H).symm (-f)
  have hu : ∀ y : H, ⟪y, u⟫_ℝ = -f y := by
    intro y
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨u, ?_, ?_, ?_⟩
  · intro hz
    apply hfn
    ext y
    have hy := hu y
    rw [hz, inner_zero_right] at hy
    simpa using hy.symm
  · intro c hc
    change 0 ≤ ⟪c, u⟫_ℝ
    rw [hu]
    exact neg_nonneg.mpr (hnonpos c hc)
  · rw [hu]
    exact neg_nonpos.mpr hfx0

/-- In a nonempty open convex cone excluding zero there is a point whose
pairing with every cone point is positive. -/
lemma exists_positive_point_in_open_cone (C : ConvexCone ℝ H)
    (ho : IsOpen (C : Set H)) (hne : (C : Set H).Nonempty) (hz : (0 : H) ∉ C) :
    ∃ a ∈ C, ∀ c ∈ C, 0 < ⟪a, c⟫_ℝ := by
  obtain ⟨ω, hω⟩ := hne
  let P := ProperCone.innerDual (C : Set H)
  obtain ⟨a, ⟨ha, hmin⟩, _⟩ := ExpandedFA.Hilbert.Projection.existsUnique_nearestPoint
    ℝ H (P : Set H) ⟨0, P.zero_mem⟩ P.isClosed P.convex ω
  have hvar : ∀ z ∈ P, ⟪ω - a, z - a⟫_ℝ ≤ 0 :=
    (ExpandedFA.Hilbert.Projection.minimizer_iff_variational ℝ H
      (P : Set H) P.convex ω a ha).mp hmin
  have hpair : ∀ u ∈ P, ⟪ω, u⟫_ℝ ≤ ⟪a, u⟫_ℝ := by
    intro u hu
    have h := hvar (a + u) (P.add_mem ha hu)
    rw [add_sub_cancel_left, inner_sub_left] at h
    linarith
  have haC : a ∈ C := by
    by_contra hn
    obtain ⟨u, hun, huP, hau⟩ := exists_polar_separator C ho ⟨ω, hω⟩ hn
    have hpos : 0 < ⟪ω, u⟫_ℝ :=
      inner_pos_of_nonneg_on_open ho hun (fun c hc => huP hc) hω
    exact (hpos.trans_le (hpair u huP)).not_ge hau
  refine ⟨a, haC, ?_⟩
  have han : a ≠ 0 := fun heq => hz (heq ▸ haC)
  intro c hc
  rw [real_inner_comm]
  exact inner_pos_of_nonneg_on_open ho han (fun z hz => ha hz) hc

/-- The full interior-point conclusion, including an arbitrary exterior point. -/
theorem interior_point_separation : Spec.InteriorPointSeparation.{u} := by
  intro H _ _ _ D x₀ hne ho hv hx₀
  let S : Set H := {y | y + x₀ ∈ D}
  have hoS : IsOpen S := ho.preimage (continuous_id.add continuous_const)
  have hnS : S.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    exact ⟨w - x₀, by simpa [S] using hw⟩
  have hvS : Convex ℝ S := by
    intro y hy z hz a b ha hb hab
    change (a • y + b • z) + x₀ ∈ D
    have hid : (a • y + b • z) + x₀ = a • (y + x₀) + b • (z + x₀) := by
      calc
        _ = (a • y + b • z) + (a + b) • x₀ := by rw [hab, one_smul]
        _ = _ := by simp only [add_smul, smul_add]; abel
    rw [hid]
    exact hv hy hz ha hb hab
  have hzS : (0 : H) ∉ S := by simpa [S] using hx₀
  let C : ConvexCone ℝ H := ConvexCone.hull ℝ S
  have hCeq : (C : Set H) = ⋃ t > (0 : ℝ), t • S := by
    ext y
    simp only [C, SetLike.mem_coe, ConvexCone.mem_hull_of_convex hvS, mem_iUnion, exists_prop]
  have hoC : IsOpen (C : Set H) := by
    rw [hCeq]
    exact isOpen_iUnion fun t => isOpen_iUnion fun ht => hoS.smul₀ (ne_of_gt ht)
  have hnC : (C : Set H).Nonempty := hnS.mono ConvexCone.subset_hull
  have hzC : (0 : H) ∉ C := by
    intro hz
    obtain ⟨t, ht, y, hy, heq⟩ := (ConvexCone.mem_hull_of_convex hvS).mp hz
    have hy0 : y = 0 := (smul_eq_zero.mp heq).resolve_left ht.ne'
    exact hzS (hy0 ▸ hy)
  obtain ⟨a, ha, hpos⟩ := exists_positive_point_in_open_cone C hoC hnC hzC
  obtain ⟨t, ht, y, hy, heq⟩ := (ConvexCone.mem_hull_of_convex hvS).mp ha
  refine ⟨y + x₀, hy, ?_⟩
  intro w hw
  have hwS : w - x₀ ∈ S := by simpa [S] using hw
  have h := hpos (w - x₀) (ConvexCone.subset_hull hwS)
  rw [← heq, real_inner_smul_left] at h
  simpa only [add_sub_cancel_right] using (pos_of_mul_pos_right h ht.le)

end ExpandedFA.PartV.ConeGeometry
