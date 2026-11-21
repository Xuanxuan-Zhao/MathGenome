import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.DeficiencyHalfPlaneConstancy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section
universe u
namespace ExpandedFA.Unbounded

section HilbertCardinal
variable {E F I J : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded injection compares arbitrary Hilbert cardinal dimensions.
The finite target case uses linear independence; the infinite case uses
countable orthonormal supports of images under the adjoint. -/
theorem hilbertBasis_card_le_of_injective (b : HilbertBasis I ℂ E)
    (c : HilbertBasis J ℂ F) (T : E →L[ℂ] F) (hT : Function.Injective T) :
    Cardinal.mk I ≤ Cardinal.mk J := by
  classical
  cases finite_or_infinite J with
  | inl hJ =>
    let := Fintype.ofFinite J
    exact linearIndependent_le_basis c.toOrthonormalBasis.toBasis
      (fun i => T (b i))
      (b.orthonormal.linearIndependent.map' T.toLinearMap (LinearMap.ker_eq_bot.mpr hT))
  | inr hJ =>
    let A : J → Set I := fun j => Function.support (fun i => b.repr (T.adjoint (c j)) i)
    have hcount (j : J) : (A j).Countable := by
      have hs := (b.hasSum_repr (T.adjoint (c j))).summable.countable_support
      have he : Function.support (fun i => b.repr (T.adjoint (c j)) i • b i) = A j := by
        ext i
        change (_ • b i ≠ 0) ↔ _ ≠ 0
        constructor
        · intro h hz
          dsimp only at hz
          exact h (by rw [hz, zero_smul])
        · intro h hz
          have hh := congrArg norm hz
          rw [norm_smul, b.orthonormal.norm_eq_one i, mul_one, norm_zero] at hh
          exact h (norm_eq_zero.mp hh)
      rwa [he] at hs
    have hcover : (⋃ j, A j) = Set.univ := by
      ext i
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_contra! hi
      have he : T (b i) = 0 := by
        apply c.repr.injective
        apply lp.ext
        funext j
        have hh : inner ℂ (b i) (T.adjoint (c j)) = 0 := by
          simpa only [A, Function.mem_support, HilbertBasis.repr_apply_apply,
            not_not] using hi j
        rw [ContinuousLinearMap.adjoint_inner_right] at hh
        simpa only [HilbertBasis.repr_apply_apply, map_zero, lp.coeFn_zero,
          Pi.zero_apply] using (inner_eq_zero_symm.mp hh)
      have : b i = 0 := hT (by simpa using he)
      exact (b.orthonormal.ne_zero i) this
    calc
      Cardinal.mk I = Cardinal.mk (⋃ j, A j) := by rw [hcover, Cardinal.mk_univ]
      _ ≤ Cardinal.sum (fun j => Cardinal.mk (A j)) := Cardinal.mk_iUnion_le_sum_mk
      _ ≤ Cardinal.sum (fun _ : J => Cardinal.aleph0) :=
        Cardinal.sum_le_sum _ _ (fun j => (hcount j).le_aleph0)
      _ = Cardinal.mk J * Cardinal.aleph0 := by simp
      _ = Cardinal.mk J := Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk J)
end HilbertCardinal

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Nearby adjoint eigenspaces meet the orthogonal complement trivially.
The conjugate in the shift is essential for the inner-product convention. -/
theorem deficiencySpace_inter_orthogonal_eq_zero (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (z w : ℂ)
    (hzw : ‖w - z‖ < |z.im|) (u : H)
    (hw : u ∈ deficiencySpace S w) (hz : u ∈ (deficiencySpace S z).orthogonal) :
    u = 0 := by
  have hz0 : z.im ≠ 0 := by
    have := lt_of_le_of_lt (norm_nonneg (w - z)) hzw
    exact abs_pos.mp this
  have hr := closed_symmetric_shift_range S hc hS (starRingEnd ℂ z)
    (by simpa only [Complex.conj_im, neg_ne_zero] using hz0)
  simp only [starRingEnd_self_apply] at hr
  rw [← hr] at hz
  change ∃ x : S.domain, (starRingEnd ℂ z) • (x : H) - S x = u at hz
  obtain ⟨x, hx⟩ := hz
  obtain ⟨hu, hwu⟩ := (mem_deficiencySpace_iff S w u).mp hw
  have hpair : inner ℂ u u = (z - w) * inner ℂ (x : H) u := by
    calc
      inner ℂ u u = inner ℂ ((starRingEnd ℂ z) • (x : H) - S x) u :=
        congrArg (fun v : H => inner ℂ v u) hx.symm
      _ = (z - w) * inner ℂ (x : H) u := by
        rw [inner_sub_left, inner_smul_left,
          hilbertAdjoint_inner S hS.1 ⟨u, hu⟩ x, hwu, inner_smul_right]
        simp only [starRingEnd_self_apply]
        ring
  have hsq : ‖u‖ ^ 2 ≤ ‖w - z‖ * ‖(x : H)‖ * ‖u‖ := by
    calc
      ‖u‖ ^ 2 = ‖inner ℂ u u‖ := by
        simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg u)]
      _ = ‖z - w‖ * ‖inner ℂ (x : H) u‖ := by rw [hpair, norm_mul]
      _ ≤ ‖z - w‖ * (‖(x : H)‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖w - z‖ * ‖(x : H)‖ * ‖u‖ := by rw [norm_sub_rev]; ring
  have hlo := hS.nonreal_lower_bound (starRingEnd ℂ z) x
  rw [norm_sub_rev, hx] at hlo
  simp only [Complex.conj_im, abs_neg] at hlo
  by_contra hu0
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hxpos : 0 < ‖(x : H)‖ := by
    by_contra hxpos
    have hx0 : (x : H) = 0 :=
      norm_eq_zero.mp (le_antisymm (le_of_not_gt hxpos) (norm_nonneg _))
    have : x = 0 := Subtype.ext hx0
    rw [this] at hx
    change (starRingEnd ℂ z) • (0 : H) - S.toFun 0 = u at hx
    rw [smul_zero, map_zero, sub_zero] at hx
    exact hu0 hx.symm
  have hle : ‖u‖ ≤ ‖w - z‖ * ‖(x : H)‖ := by nlinarith
  have hlt := mul_lt_mul_of_pos_right hzw hxpos
  linarith

/-- Projection to a nearby deficiency space is a bounded injection. -/
theorem deficiencyIndex_le_of_near (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (z w : ℂ)
    (hzw : ‖w - z‖ < |z.im|) :
    deficiencyIndex S hS.1 w ≤ deficiencyIndex S hS.1 z := by
  let : CompleteSpace (deficiencySpace S z) :=
    (deficiencySpace_isClosed S hS.1 z).isComplete.completeSpace_coe
  let : CompleteSpace (deficiencySpace S w) :=
    (deficiencySpace_isClosed S hS.1 w).isComplete.completeSpace_coe
  let T : deficiencySpace S w →L[ℂ] deficiencySpace S z :=
    (deficiencySpace S z).orthogonalProjectionOnto.comp (deficiencySpace S w).subtypeL
  have hT : Function.Injective T := by
    suffices hh : T.toLinearMap.ker = ⊥ from LinearMap.ker_eq_bot.mp hh
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    have hp : (deficiencySpace S z).orthogonalProjectionOnto (u : H) = 0 := hu
    have horth := (deficiencySpace S z).orthogonalProjectionOnto_eq_zero_iff.mp hp
    apply Subtype.ext
    exact deficiencySpace_inter_orthogonal_eq_zero S hc hS z w hzw u u.prop horth
  obtain ⟨I, b, hb⟩ := deficiencyIndex_hasBasis S hS.1 w
  obtain ⟨J, c, hc⟩ := deficiencyIndex_hasBasis S hS.1 z
  rw [hb, hc]
  exact hilbertBasis_card_le_of_injective b c T hT

/-- A uniform small disk around any nonreal parameter has the same index. -/
theorem deficiencyIndex_eq_of_near (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (z w : ℂ) (hz : z.im ≠ 0)
    (hzw : ‖w - z‖ < |z.im| / 2) :
    deficiencyIndex S hS.1 w = deficiencyIndex S hS.1 z := by
  have hp := abs_pos.mpr hz
  have hi : |w.im - z.im| ≤ ‖w - z‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
  have ht : |z.im| ≤ |w.im| + ‖w - z‖ := by
    have h := abs_add_le w.im (z.im - w.im)
    have he : w.im + (z.im - w.im) = z.im := by ring
    rw [he, abs_sub_comm] at h
    linarith
  apply le_antisymm
  · exact deficiencyIndex_le_of_near S hc hS z w (by linarith)
  · apply deficiencyIndex_le_of_near S hc hS w z
    rw [norm_sub_rev]
    linarith

/-- Local constancy is constant on any convex set avoiding the real axis. -/
theorem deficiencyIndex_eq_on_convex (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (s : Set ℂ)
    (hs : Convex ℝ s) (hn : ∀ z ∈ s, z.im ≠ 0)
    (z w : ℂ) (hz : z ∈ s) (hw : w ∈ s) :
    deficiencyIndex S hS.1 z = deficiencyIndex S hS.1 w := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.isPreconnected
  have hlc : IsLocallyConstant (fun z : s => deficiencyIndex S hS.1 (z : ℂ)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨|z.val.im| / 2, half_pos (abs_pos.mpr (hn z z.prop)), ?_⟩
    intro w hw
    apply deficiencyIndex_eq_of_near S hc hS z w (hn z z.prop)
    simpa only [Subtype.dist_eq, dist_eq_norm] using hw
  exact hlc.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨w, hw⟩

/-- Deficiency Hilbert cardinalities are constant separately in the upper
and lower open half-planes, including all nonseparable cardinalities. -/
theorem deficiencyIndex_halfPlane_constancy (S : Operator ℂ H H)
    (hc : IsClosed S) (hS : IsSymmetric S) (z w : ℂ)
    (hzw : (0 < z.im ∧ 0 < w.im) ∨ (z.im < 0 ∧ w.im < 0)) :
    deficiencyIndex S hS.1 z = deficiencyIndex S hS.1 w := by
  rcases hzw with hzw | hzw
  · exact deficiencyIndex_eq_on_convex S hc hS {z : ℂ | 0 < z.im}
      ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm)
      (fun z hz => ne_of_gt hz) z w hzw.1 hzw.2
  · exact deficiencyIndex_eq_on_convex S hc hS {z : ℂ | z.im < 0}
      ((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm)
      (fun z hz => ne_of_lt hz) z w hzw.1 hzw.2

end ExpandedFA.Unbounded
