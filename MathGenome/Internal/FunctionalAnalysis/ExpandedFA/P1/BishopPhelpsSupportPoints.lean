import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BishopPhelpsSupportPoints
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Ekeland
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06OpenSeparation

/-! Support points are dense in the boundary, including for unbounded sets.
We separate from a strict sublevel set of the penalized distance function.
This avoids requiring a support functional at the initial boundary point. -/
namespace ExpandedFA.P1.BishopPhelpsSupportPoints

open Set Metric

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A minimizer of the penalized distance to a point outside a convex set
is a support point. The penalty coefficient is strictly less than one. -/
theorem support_of_penalized_distance {C : Set E} (hC : Convex ℝ C)
    {x z : E} (hx : x ∈ C) (hz : z ∉ C)
    (hmin : ∀ y ∈ C, dist x z ≤ dist y z + (1 / 2 : ℝ) * dist y x) :
    Spec.IsRealSupportPoint C x := by
  let F : E → ℝ := fun y => dist y z + (1 / 2 : ℝ) * dist y x
  have hF : ConvexOn ℝ univ F :=
    (convexOn_univ_dist z).add ((convexOn_univ_dist x).smul (by norm_num : (0 : ℝ) ≤ 1/2))
  have hFx : F x = dist x z := by simp [F]
  have hzx : z ≠ x := fun h => hz (h.symm ▸ hx)
  have hFz : F z < F x := by
    simp only [F, dist_self, zero_add, mul_zero, add_zero]
    rw [dist_comm z x]
    have := dist_pos.mpr hzx.symm
    linarith
  let D : Set E := {y | F y < F x}
  have hD : Convex ℝ D := by
    simpa only [D, sep_univ] using hF.convex_lt (F x)
  have ho : IsOpen D := by
    exact isOpen_lt (by dsimp [F]; fun_prop) continuous_const
  have hd : Disjoint D C := by
    apply disjoint_left.mpr
    intro y hy hyC
    exact (not_lt_of_ge (hmin y hyC)) (by simpa only [D, mem_ofPred, hFx] using hy)
  have hseg : openSegment ℝ z x ⊆ D := by
    rintro y ⟨a, b, ha, hb, hab, rfl⟩
    change F (a • z + b • x) < F x
    calc
      _ ≤ a • F z + b • F x := hF.2 (mem_univ _) (mem_univ _) ha.le hb.le hab
      _ < a • F x + b • F x := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hFz ha) le_rfl
      _ = F x := by rw [← add_smul, hab, one_smul]
  have hxc : x ∈ closure D :=
    closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ z x))
  obtain ⟨f, a, hf, hfa, hfc⟩ := C06.real_normed_open_convex_separation
    D C ⟨z, hFz⟩ ⟨x, hx⟩ hD hC hd ho
  have hfx : f x ≤ a := by
    exact closure_minimal (fun y hy => (hfa y hy).le)
      (isClosed_le f.continuous continuous_const) hxc
  refine ⟨hx, -f, neg_ne_zero.mpr hf, ?_⟩
  intro y hy
  simpa only [neg_apply, neg_le_neg_iff] using hfx.trans (hfc y hy)

/-- Ekeland's distance estimate produces support points near every point of
the set whenever there is a nearby point outside it. -/
theorem exists_support_point_near {C : Set E} [CompleteSpace E]
    (hc : IsClosed C) (hv : Convex ℝ C) {b z : E} (hb : b ∈ C) (hz : z ∉ C) :
    ∃ x, Spec.IsRealSupportPoint C x ∧ dist x b ≤ 2 * dist b z := by
  have : CompleteSpace C := hc.isComplete.completeSpace_coe
  let b₀ : C := ⟨b, hb⟩
  let f : C → ℝ := fun y => dist (y : E) z
  have hf : LowerSemicontinuous f :=
    (continuous_subtype_val.dist continuous_const).lowerSemicontinuous
  have hbound : BddBelow (range f) := ⟨0, by rintro _ ⟨y, rfl⟩; exact dist_nonneg⟩
  have hnear : ∀ y : C, f b₀ ≤ f y + (1 / 2 : ℝ) * (2 * dist b z) := by
    intro y
    dsimp [f, b₀]
    linarith [dist_nonneg (x := (y : E)) (y := z)]
  obtain ⟨x, hdist, _, hstrict⟩ :=
    ExpandedFA.P1.ekeland_real hf hbound b₀ (by norm_num : (0 : ℝ) < 1/2) hnear
  refine ⟨x, support_of_penalized_distance hv x.property hz ?_, hdist⟩
  intro y hy
  by_cases hyx : y = (x : E)
  · simp [hyx]
  · have hne : (⟨y, hy⟩ : C) ≠ x := fun h => hyx (congrArg Subtype.val h)
    have hi := hstrict ⟨y, hy⟩ hne
    change dist (x : E) z - (1/2 : ℝ) * dist y (x : E) < dist y z at hi
    linarith

/-- The real Bishop--Phelps boundary assertion, without a boundedness
hypothesis on the closed convex set. -/
theorem real_boundary_density : Spec.RealBoundaryDensity.{u} := by
  intro E _ _ _ C _ hc hv b hb
  have hbC : b ∈ C := hc.closure_eq ▸ frontier_subset_closure hb
  have hbcomp : b ∈ closure Cᶜ :=
    ((frontier_eq_closure_inter_closure (s := C)) ▸ hb).2
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, hz, hzb⟩ := Metric.mem_closure_iff.mp hbcomp (ε / 3) (by positivity)
  obtain ⟨x, hx, hxb⟩ := exists_support_point_near hc hv hbC hz
  refine ⟨x, hx, ?_⟩
  rw [dist_comm b x]
  linarith

/-- A real support functional on the underlying real space corresponds to
the real part of a nonzero continuous complex-linear functional. -/
theorem complex_support_of_real {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {C : Set F} {x : F} (hx : Spec.IsRealSupportPoint C x) :
    Spec.IsComplexSupportPoint C x := by
  obtain ⟨hxc, h, hn, hh⟩ := hx
  let f : F →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : ∀ y, (f y).re = h y := fun y =>
    StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h y
  refine ⟨hxc, f, ?_, ?_⟩
  · intro hz
    apply hn
    ext y
    simpa only [hz, zero_apply, Complex.zero_re] using (hre y).symm
  · intro y hy
    rw [hre, hre]
    exact hh y hy

/-- The complex Bishop--Phelps boundary assertion uses the scalar-linear
dual and real convexity, with no boundedness assumption. -/
theorem complex_boundary_density : Spec.ComplexBoundaryDensity.{u} := by
  intro E _ _ _ C hne hc hv
  exact (real_boundary_density E C hne hc hv).trans
    (closure_mono fun _ hx => complex_support_of_real hx)

end ExpandedFA.P1.BishopPhelpsSupportPoints
