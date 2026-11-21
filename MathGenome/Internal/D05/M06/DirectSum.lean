import MathGenome.Internal.Specs.D05.M06.DirectSum
import MathGenome.Internal.D05.M02.SumIntersection

/-! K05.06.direct_sum: finite internal direct sums, with actual summation maps. -/

namespace D05.M06.DirectSum

open Specs.D05.M06.DirectSum (UniqueDecomposition summationMap)

/-- The assertion of an internal direct sum is unique component expansion. -/
abbrev internalDirectSum (K V ι : Type*) [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (U : ι → Submodule K V) : Prop :=
  UniqueDecomposition U

/-- Addition of the actual included subspace components. -/
noncomputable abbrev summation (K V ι : Type*) [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (U : ι → Submodule K V) :
    (∀ i, U i) →ₗ[K] V := summationMap U

theorem internal_iff_bijective : Specs.D05.M06.DirectSum.internal_iff_bijective := by
  intro K V ι _ _ _ _ U
  exact (Function.bijective_iff_existsUnique (summationMap U)).symm

theorem finite_sum_comparison : Specs.D05.M06.DirectSum.finite_sum_comparison := by
  intro K V ι _ _ _ _ _ U c
  classical
  rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]
  change c.sum (fun _ x => (x : V)) = ∑ i, (c i : V)
  apply DFinsupp.sum_eq_sum_fintype
  intro i
  rfl

theorem range_summation : Specs.D05.M06.DirectSum.range_summation := by
  intro K V ι _ _ _ _ U
  classical
  let e := _root_.DirectSum.linearEquivFunOnFintype K ι (fun i => U i)
  have hmap : _root_.DirectSum.coeLinearMap U = (summationMap U).comp e.toLinearMap := by
    apply LinearMap.ext
    intro c
    exact finite_sum_comparison U c
  rw [← _root_.DirectSum.range_coeLinearMap (A := U), hmap,
    LinearMap.range_comp_of_range_eq_top _ e.range]

theorem zero_sum_iff_injective : Specs.D05.M06.DirectSum.zero_sum_iff_injective := by
  intro K V ι _ _ _ _ U
  constructor
  · intro hz c d hcd
    have hs : (∑ i, ((c - d) i : V)) = 0 := by
      change summationMap U (c - d) = 0
      rw [map_sub, hcd, sub_self]
    have hc := hz (c - d) hs
    funext i
    apply Subtype.ext
    exact sub_eq_zero.mp (hc i)
  · intro hi c hc i
    have hzero : c = 0 := hi (hc.trans (map_zero (summationMap U)).symm)
    exact congrArg (fun d : ∀ i, U i => (d i : V)) hzero

theorem internal_iff_spanning_zero_sum :
    Specs.D05.M06.DirectSum.internal_iff_spanning_zero_sum := by
  intro K V ι _ _ _ _ U
  rw [internal_iff_bijective U, zero_sum_iff_injective U,
    ← range_summation U, LinearMap.range_eq_top]
  exact and_comm

theorem internal_iff_mathlib : Specs.D05.M06.DirectSum.internal_iff_mathlib := by
  intro K V ι _ _ _ _ _ U
  rw [internal_iff_bijective U]
  let e := _root_.DirectSum.linearEquivFunOnFintype K ι (fun i => U i)
  have hmap : (fun c => _root_.DirectSum.coeLinearMap U c) =
      (fun c => summationMap U (e c)) := by
    funext c
    exact finite_sum_comparison U c
  change Function.Bijective (summationMap U) ↔
    Function.Bijective (fun c => _root_.DirectSum.coeLinearMap U c)
  rw [hmap]
  exact (e.bijective.of_comp_iff (f := summationMap U)).symm

theorem summation_equiv : Specs.D05.M06.DirectSum.summation_equiv := by
  intro K V ι _ _ _ _ U h
  exact ⟨LinearEquiv.ofBijective (summationMap U) ((internal_iff_bijective U).mp h),
    fun _ => rfl⟩

theorem pair_zero_sum_iff_inf_bot : Specs.D05.M06.DirectSum.pair_zero_sum_iff_inf_bot := by
  intro K V _ _ _ U W
  constructor
  · intro hz
    apply le_antisymm
    · intro x hx
      have h := hz ⟨x, hx.1⟩ ⟨-x, W.neg_mem hx.2⟩ (add_neg_cancel x)
      exact h.1
    · exact bot_le
  · intro h u w huw
    have huW : (u : V) ∈ W := by
      have heq : (u : V) = -(w : V) := eq_neg_of_add_eq_zero_left huw
      rw [heq]
      exact W.neg_mem w.property
    have hu : (u : V) = 0 := by
      have hm : (u : V) ∈ U ⊓ W := ⟨u.property, huW⟩
      rw [h] at hm
      exact hm
    exact ⟨hu, by simpa only [hu, zero_add] using huw⟩

theorem pair_internal_iff_sup_inf : Specs.D05.M06.DirectSum.pair_internal_iff_sup_inf := by
  intro K V _ _ _ U W
  rw [internal_iff_spanning_zero_sum]
  have hsup : (⨆ b : Bool, if b then W else U) = U ⊔ W := by
    simp only [iSup_bool_eq, Bool.false_eq_true, ↓reduceIte, sup_comm]
  rw [hsup]
  apply and_congr_right
  intro _
  rw [← pair_zero_sum_iff_inf_bot U W]
  constructor
  · intro h u w huw
    let c : (b : Bool) → ↥(if b then W else U) := fun b =>
      match b with
      | false => u
      | true => w
    have hc : (∑ b, (c b : V)) = 0 := by
      simpa only [Fintype.sum_bool, c, add_comm] using huw
    exact ⟨h c hc false, h c hc true⟩
  · intro h c hc b
    have hc' : (c false : V) + (c true : V) = 0 := by
      simpa only [Fintype.sum_bool, add_comm] using hc
    have hz := h (c false) (c true) hc'
    cases b
    · exact hz.1
    · exact hz.2

theorem pair_internal_iff_sum_intersection :
    Specs.D05.M06.DirectSum.pair_internal_iff_sum_intersection := by
  intro K V _ _ _ U W
  rw [pair_internal_iff_sup_inf U W,
    ← D05.M02.SumIntersection.sum_eq_sup U W]
  constructor
  · rintro ⟨h, hz⟩
    exact ⟨by rw [h]; rfl, hz⟩
  · rintro ⟨h, hz⟩
    exact ⟨SetLike.coe_injective h, hz⟩

theorem empty_internal_iff_zero : Specs.D05.M06.DirectSum.empty_internal_iff_zero := by
  intro K V ι _ _ _ _ _ U
  constructor
  · intro h x
    obtain ⟨c, hc, _⟩ := h x
    simpa using hc.symm
  · intro hz x
    refine ⟨(fun i => isEmptyElim i), ?_, ?_⟩
    · simpa using (hz x).symm
    · intro d _
      exact funext fun i => isEmptyElim i

end D05.M06.DirectSum
