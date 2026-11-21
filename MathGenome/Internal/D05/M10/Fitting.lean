import MathGenome.Internal.Specs.D05.M10.Fitting
import MathGenome.Internal.D05.M03.EqualDimension
import MathGenome.Internal.D05.M06.DirectSum
import MathGenome.Internal.D05.M10.Nilpotent

/-! K05.10.fitting: the dimension-bounded kernel–image decomposition. -/

namespace D05.M10.Fitting

theorem kernel_invariant : Specs.D05.M10.Fitting.kernel_invariant := by
  intro K V _ _ _ T n x hx
  change (T ^ n) (T x) = 0
  calc
    (T ^ n) (T x) = T ((T ^ n) x) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.pow_self T n).eq]
    _ = 0 := by rw [LinearMap.mem_ker.mp hx, map_zero]

theorem image_invariant : Specs.D05.M10.Fitting.image_invariant := by
  intro K V _ _ _ T n x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨T y, ?_⟩
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.pow_self T n).eq]

theorem decomposition : Specs.D05.M10.Fitting.decomposition := by
  intro K V _ _ _ _ T n hn
  apply (D05.M06.DirectSum.pair_internal_iff_sup_inf
    (LinearMap.ker (T ^ n)) (LinearMap.range (T ^ n))).mpr
  have hdis : Disjoint (LinearMap.ker (T ^ n)) (LinearMap.range (T ^ n)) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    obtain ⟨u, hu⟩ := hx.2
    have hu2 : u ∈ LinearMap.ker (T ^ (n + n)) := by
      change (T ^ (n + n)) u = 0
      rw [pow_add, Module.End.mul_apply, hu]
      exact hx.1
    have hu1 : u ∈ LinearMap.ker (T ^ n) := by
      rw [KernelStabilization.kernel_stabilization T n hn n]
      exact hu2
    exact hu.symm.trans (LinearMap.mem_ker.mp hu1)
  exact ⟨Submodule.eq_top_of_disjoint _ _
    (le_of_eq (D05.M03.RankNullity.rank_nullity (T ^ n))) hdis, hdis.eq_bot⟩

theorem kernel_restriction_nilpotent :
    Specs.D05.M10.Fitting.kernel_restriction_nilpotent := by
  intro K V _ _ _ T n h
  have hp : (T.restrict h) ^ n = 0 := by
    ext x
    rw [Module.End.pow_restrict, LinearMap.coe_restrict_apply]
    exact x.property
  have hnil : IsNilpotent (T.restrict h) := ⟨n, hp⟩
  exact ⟨hp, hnil, (D05.M10.Nilpotent.nilpotent_iff_positive_power _).mp hnil⟩

theorem image_restriction_invertible :
    Specs.D05.M10.Fitting.image_restriction_invertible := by
  intro K V _ _ _ _ T n hn h
  have hs : Function.Surjective (T.restrict h) := by
    intro x
    have hx : (x : V) ∈ LinearMap.range (T ^ (n + 1)) := by
      rw [← KernelStabilization.image_stabilization T n hn 1]
      exact x.property
    obtain ⟨u, hu⟩ := hx
    refine ⟨⟨(T ^ n) u, ⟨u, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change T ((T ^ n) u) = (x : V)
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hu
  have hi := (D05.M03.EqualDimension.equal_dimension (T.restrict h) rfl).1.mpr hs
  exact (D05.M03.EqualDimension.equal_dimension (T.restrict h) rfl).2.1.mp hi

theorem fitting : Specs.D05.M10.Fitting.fitting := by
  intro K V _ _ _ _ T n hn
  exact ⟨decomposition T n hn, kernel_invariant T n, image_invariant T n,
    (kernel_restriction_nilpotent T n (kernel_invariant T n)).2.1,
    image_restriction_invertible T n hn (image_invariant T n)⟩

end D05.M10.Fitting
