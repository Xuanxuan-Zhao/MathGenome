import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.MFCQTangency
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.TangentInclusion
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.EqualityChart
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology ContDiff
noncomputable section
universe u v w
namespace VariationalNotes.Ch06

/-- A curve feasible for small positive parameters witnesses the manuscript's
positive-time sequential tangent, without a straight-ray assumption. -/
lemma tangent_of_feasible_curve
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {C : Set X} {x d : X} {γ : ℝ → X}
    (hγ0 : γ 0 = x) (hγ : HasDerivAt γ d 0)
    (hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ C) :
    d ∈ VariationalNotes.ConvexGeometry.Specs.contingentTangent C x := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ t : ℝ, 0 < t ∧ t < r n ∧ γ t ∈ C := by
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r n :=
      (eventually_lt_nhds (hr n)).filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    exact (hpos.and (hsmall.and hfeas)).exists
  choose t ht hsmall hC using hex
  have ht0 : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun n => (ht n).le) (fun n => (hsmall n).le) hr0
  have htGT : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0, Eventually.of_forall ht⟩
  refine ⟨γ ∘ t, t, hC, ht, ht0, ?_⟩
  simpa only [Function.comp_def, zero_add, hγ0] using hγ.tendsto_slope_zero_right.comp htGT

/-- Negative derivative and a zero value imply strict feasibility on the right. -/
lemma eventually_neg_of_hasDerivAt
    {φ : ℝ → ℝ} {a : ℝ} (hφ : HasDerivAt φ a 0) (ha : a < 0)
    (hzero : φ 0 = 0) : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t < 0 := by
  have hlim := hφ.tendsto_slope_zero_right
  have hneg := hlim.eventually (gt_mem_nhds ha)
  filter_upwards [hneg, self_mem_nhdsWithin] with t hneg ht
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at hneg
  by_contra hn
  exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr ht.le) (le_of_not_gt hn))) hneg

/-- Independent finite continuous linear forms have a surjective coordinate map.
The argument identifies its range with the span of all evaluation vectors. -/
lemma coordinateMap_surjective_of_linearIndependent
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : Type v} [Fintype A] (l : A → X →L[ℝ] ℝ)
    (hli : LinearIndependent ℝ l) :
    Function.Surjective (fun x i => l i x) := by
  let coeL : (X →L[ℝ] ℝ) →ₗ[ℝ] (X → ℝ) :=
    { toFun := fun f => f
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hli' : LinearIndependent ℝ (fun i x => l i x) :=
    hli.map' coeL (LinearMap.ker_eq_bot.mpr
      (fun _ _ h => ContinuousLinearMap.ext (congrFun h)))
  let L : X →ₗ[ℝ] (A → ℝ) := LinearMap.pi (fun i => (l i).toLinearMap)
  have hspan : Submodule.span ℝ (Set.range L) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli'
  have hrange : L.range = ⊤ := by
    rw [← LinearMap.coe_range, Submodule.span_eq] at hspan
    exact hspan
  exact LinearMap.range_eq_top.mp hrange

/-- Strict active linearizations are realized by equality-feasible curves. -/
lemma strict_linearized_mem_tangent
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X)
    (hs : Specs.SmoothConstraintData U f g h) (hx : x ∈ Specs.feasibleSet U g h)
    (hsurj : Function.Surjective (Specs.equalityDerivative h x))
    (d : X) (hd : Specs.equalityDerivative h x d = 0)
    (hstrict : ∀ i ∈ Specs.activeSet g x, fderiv ℝ (g i) x d < 0) :
    d ∈ Specs.constraintTangentCone U g h x := by
  let : CompleteSpace X := FiniteDimensional.complete ℝ X
  obtain ⟨_, hg, hh⟩ := smoothConstraintData_hasFDerivAt U f g h x hs hx.1
  have hHD : HasFDerivAt (fun y j => h j y) (Specs.equalityDerivative h x) x :=
    equalityDerivative_hasFDerivAt h x (fun j => (hh j).differentiableAt)
  obtain ⟨R, hR, hgraph, hambient, hcurves⟩ :=
    EqualityChart.finiteTargetEqualityChart X (J → ℝ) 1 le_rfl U hs.1
      (fun y j => h j y) (contDiffOn_pi.mpr hs.2.2.2) x hx.1
      (funext hx.2.2) (Specs.equalityDerivative h x) hHD hsurj
  obtain ⟨ε, γ, hε, hγ0, hγC, hγD, hγF⟩ := hcurves ⟨d, hd⟩
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U ∧ (∀ j, h j (γ t) = 0) := by
    have hinterval : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, hε⟩
    filter_upwards [hinterval] with t ht
    exact ⟨(hγF t ht).1, fun j => congrFun (hγF t ht).2 j⟩
  have hinequalities : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), g i (γ t) ≤ 0 := by
    intro i
    have hgi : HasFDerivAt (g i) (fderiv ℝ (g i) x) (γ 0) := by
      rw [hγ0]; exact hg i
    have hcomp : HasDerivAt (fun t => g i (γ t)) (fderiv ℝ (g i) x d) 0 :=
      hgi.comp_hasDerivAt 0 hγD
    by_cases hi : i ∈ Specs.activeSet g x
    · exact (eventually_neg_of_hasDerivAt hcomp (hstrict i hi)
        (by rw [hγ0]; exact hi)).mono (fun _ ht => ht.le)
    · have hslack : g i (γ 0) < 0 := by
        rw [hγ0]
        exact lt_of_le_of_ne (hx.2.1 i) hi
      exact ((hcomp.continuousAt.eventually (gt_mem_nhds hslack)).mono
        (fun _ ht => ht.le)).filter_mono nhdsWithin_le_nhds
  apply tangent_of_feasible_curve hγ0 hγD
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    eventually_all.mpr hinequalities] with t ht hgt
  exact ⟨ht.1, hgt, ht.2⟩

theorem linearized_subset_tangent_of_mfcq : Specs.linearized_subset_tangent_of_mfcq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hm d hd
  obtain ⟨hx, hsurj, w, hw, hstrict⟩ := hm
  have hperturb (ε : ℝ) (hε : 0 < ε) :
      d + ε • w ∈ Specs.constraintTangentCone U g h x := by
    apply strict_linearized_mem_tangent U f g h x hs hx hsurj
    · simp only [map_add, map_smul, hd.1, hw, smul_zero, add_zero]
    · intro i hi
      rw [map_add, map_smul, smul_eq_mul]
      exact add_neg_of_nonpos_of_neg (hd.2 i hi) (mul_neg_of_pos_of_neg hε (hstrict i hi))
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id
  have hlim : Tendsto (fun ε : ℝ => d + ε • w) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_smul, add_zero] using
      ((tendsto_const_nhds (x := d)).add (hid.smul_const w)).mono_left
        nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  exact (constraintTangentCone_isClosed U g h x).mem_of_tendsto hlim
    (hpos.mono fun ε hε => hperturb ε hε)

theorem tangent_eq_linearized_of_mfcq : Specs.tangent_eq_linearized_of_mfcq.{u,v,w} := by
  intro X _ _ _ I J _ _ U f g h x hs hm
  exact Set.Subset.antisymm (tangent_subset_linearized U f g h x hs hm.1)
    (linearized_subset_tangent_of_mfcq U f g h x hs hm)

theorem licq_implies_mfcq : Specs.licq_implies_mfcq.{u,v,w} := by
  classical
  intro X _ _ _ I J _ _ U g h x hl
  let A := {i // i ∈ Specs.activeSet g x}
  let l : Sum A J → X →L[ℝ] ℝ :=
    Sum.elim (fun i : A => fderiv ℝ (g i.val) x) (fun j : J => fderiv ℝ (h j) x)
  have hsurj : Function.Surjective (fun z i => l i z) :=
    coordinateMap_surjective_of_linearIndependent l hl.2
  refine ⟨hl.1, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := hsurj (Sum.elim (fun _ : A => 0) y)
    exact ⟨z, funext fun j => congrFun hz (Sum.inr j)⟩
  · obtain ⟨z, hz⟩ := hsurj (Sum.elim (fun _ : A => (-1 : ℝ)) (fun _ : J => 0))
    refine ⟨z, funext (fun j => congrFun hz (Sum.inr j)), ?_⟩
    intro i hi
    have heq : fderiv ℝ (g i) x z = -1 := congrFun hz (Sum.inl ⟨i, hi⟩)
    rw [heq]
    norm_num

/-- All three assertions of Proposition `prop:tangent-mfcq`. -/
theorem tangent_mfcq : Specs.tangent_mfcq.{u,v,w} := by
  intro X _ _ _ I J _ _ U g h x hU hg hh hx
  have hs : Specs.SmoothConstraintData U (fun _ => 0) g h :=
    ⟨hU, contDiffOn_const, hg, hh⟩
  exact ⟨tangent_subset_linearized U (fun _ => 0) g h x hs hx,
    tangent_eq_linearized_of_mfcq U (fun _ => 0) g h x hs,
    licq_implies_mfcq U g h x⟩

end VariationalNotes.Ch06
