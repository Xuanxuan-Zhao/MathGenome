import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.ClosedRangeEquivalences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse

/-!
Closed-range equivalences (`paper.tex` 7523–7549).

The restriction from the kernel complement to the actual range is bijective.
If the range is closed, the accepted bounded inverse theorem gives its bounded
inverse. Conversely, a lower bound makes the restriction anti-Lipschitz;
completeness then makes its range closed.

For the adjoint range identity, compose the inverse with the scalar-linear
functional ⟪z, ·⟫ on the kernel complement. Extend this functional to the whole
target by its orthogonal projection onto the closed range, and apply Riesz.
The resulting vector is an adjoint preimage of z. Involution gives symmetry.
-/

noncomputable section

universe u v w

namespace ExpandedFA.Hilbert.ClosedRangeEquivalences

section Helpers

variable {𝕜 H G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G] [CompleteSpace H]

/-- The original map restricted to the kernel complement and its actual range. -/
def kernelComplementMap (T : H →L[𝕜] G) : T.ker.orthogonal →L[𝕜] T.range :=
  (T.domRestrict T.ker.orthogonal).codRestrict T.range fun x => T.mem_range_self x

/-- The restriction is bijective even before the range is known to be closed. -/
theorem kernelComplementMap_bijective (T : H →L[𝕜] G) :
    Function.Bijective (kernelComplementMap T) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hk : (x : H) - y ∈ T.ker := by
      change T ((x : H) - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have ho : (x : H) - y ∈ T.ker.orthogonal :=
      T.ker.orthogonal.sub_mem x.property y.property
    have hbot : (x : H) - y ∈ (⊥ : Submodule 𝕜 H) := by
      rw [← T.ker.inf_orthogonal_eq_bot]
      exact ⟨hk, ho⟩
    exact hbot
  · intro y
    obtain ⟨x, hx⟩ := y.property
    let : CompleteSpace T.ker := T.isClosed_ker.isComplete.completeSpace_coe
    obtain ⟨m, hm, n, hn, hmn⟩ := T.ker.exists_add_mem_mem_orthogonal x
    refine ⟨⟨n, hn⟩, ?_⟩
    apply Subtype.ext
    change T n = (y : G)
    rw [← hx, hmn, map_add]
    change T n = T m + T n
    rw [(show T m = 0 from hm), zero_add]

/-- Restricting the domain to the kernel complement leaves the range unchanged. -/
theorem range_domRestrict_kernelComplement (T : H →L[𝕜] G) :
    Set.range (T.domRestrict T.ker.orthogonal) = (T.range : Set G) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact T.mem_range_self x
  · intro hy
    obtain ⟨x, hx⟩ := (kernelComplementMap_bijective T).2 ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

/-- A lower bound on the complement implies closedness, using completeness
only in the domain. -/
theorem isClosed_range_of_kernelComplement_lower_bound (T : H →L[𝕜] G)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : H, x ∈ T.ker.orthogonal → c * ‖x‖ ≤ ‖T x‖) :
    IsClosed (T.range : Set G) := by
  let : CompleteSpace T.ker.orthogonal :=
    T.ker.isClosed_orthogonal.isComplete.completeSpace_coe
  let f := T.domRestrict T.ker.orthogonal
  have ha : AntilipschitzWith (⟨c⁻¹, inv_nonneg.mpr hc.le⟩ : NNReal) f := by
    apply f.antilipschitz_of_bound
    intro x
    change ‖(x : H)‖ ≤ c⁻¹ * ‖T x‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hbound x x.property)
  have hclosed := ha.isClosed_range f.uniformContinuous
  rwa [range_domRestrict_kernelComplement] at hclosed

end Helpers

/-- Bounded inverse of the restriction when the range is closed. -/
theorem kernelComplement_bounded_inverse_of_isClosed
    {𝕜 H G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    [CompleteSpace H] [CompleteSpace G] (T : H →L[𝕜] G)
    (hclosed : IsClosed (T.range : Set G)) :
    ∃ S : T.range →L[𝕜] T.ker.orthogonal,
      (∀ x : T.ker.orthogonal, S ⟨T x, T.mem_range_self x⟩ = x) ∧
      (∀ y : T.range, T (S y) = (y : G)) := by
  let : CompleteSpace T.ker.orthogonal :=
    T.ker.isClosed_orthogonal.isComplete.completeSpace_coe
  let : CompleteSpace T.range := hclosed.isComplete.completeSpace_coe
  obtain ⟨S, hST, hTS, _⟩ := ExpandedFA.P1.C08BoundedInverse.bounded_inverse 𝕜 T.ker.orthogonal T.range
    (kernelComplementMap T) (kernelComplementMap_bijective T)
  exact ⟨S, hST, fun y => congrArg Subtype.val (hTS y)⟩

/-- A bounded inverse yields a positive constant even if the inverse is zero. -/
theorem kernelComplement_lower_bound_of_bounded_inverse
    {𝕜 H G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
    (T : H →L[𝕜] G) (S : T.range →L[𝕜] T.ker.orthogonal)
    (hST : ∀ x : T.ker.orthogonal, S ⟨T x, T.mem_range_self x⟩ = x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : H, x ∈ T.ker.orthogonal → c * ‖x‖ ≤ ‖T x‖ := by
  have hpos : 0 < ‖S‖ + 1 := by positivity
  refine ⟨1 / (‖S‖ + 1), one_div_pos.mpr hpos, ?_⟩
  intro x hx
  have hb := S.le_opNorm ⟨T x, T.mem_range_self x⟩
  rw [hST ⟨x, hx⟩] at hb
  change ‖x‖ ≤ ‖S‖ * ‖T x‖ at hb
  calc
    (1 / (‖S‖ + 1)) * ‖x‖ = ‖x‖ / (‖S‖ + 1) := by ring
    _ ≤ ‖T x‖ := (div_le_iff₀ hpos).mpr (by nlinarith [norm_nonneg (T x)])

theorem closed_range_iff_lower_bound :
    Spec.ClosedRangeIffLowerBound.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ T
  constructor
  · intro hclosed
    obtain ⟨S, hST, _⟩ := kernelComplement_bounded_inverse_of_isClosed T hclosed
    exact kernelComplement_lower_bound_of_bounded_inverse T S hST
  · rintro ⟨c, hc, hb⟩
    exact isClosed_range_of_kernelComplement_lower_bound T hc hb


section AdjointRange

open scoped InnerProductSpace

variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

/-- A closed range gives actual adjoint preimages of the whole kernel complement. -/
theorem adjoint_range_eq_kernel_orthogonal_of_isClosed
    (T : H →L[𝕜] K) (hclosed : IsClosed (T.range : Set K)) :
    T.adjoint.range = T.ker.orthogonal := by
  apply le_antisymm
  · rw [T.orthogonal_ker]
    exact T.adjoint.range.le_topologicalClosure
  · intro z hz
    obtain ⟨S, hST, _⟩ := kernelComplement_bounded_inverse_of_isClosed T hclosed
    let : CompleteSpace T.range := hclosed.completeSpace_coe
    let f : T.range →L[𝕜] 𝕜 :=
      ((innerSL 𝕜 z).comp T.ker.orthogonal.subtypeL).comp S
    let F : K →L[𝕜] 𝕜 := f.comp T.range.orthogonalProjectionOnto
    have hF (y : T.range) : F y = f y := by
      simp only [F, ContinuousLinearMap.comp_apply,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    obtain ⟨y, hy, _, _⟩ :=
      ExpandedFA.Hilbert.RieszRepresentation.functional_representation 𝕜 K F
    refine ⟨y, ?_⟩
    apply ext_inner_right 𝕜
    intro x
    change ⟪T.adjoint y, x⟫_𝕜 = ⟪z, x⟫_𝕜
    rw [ContinuousLinearMap.adjoint_inner_left T x y, ← hy]
    let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
    obtain ⟨m, hm, n, hn, hmn⟩ := T.ker.exists_add_mem_mem_orthogonal x
    have hT : T x = T n := by
      rw [hmn, map_add, (show T m = 0 from hm), zero_add]
    rw [hT, hF ⟨T n, T.mem_range_self n⟩]
    change ⟪z, (S ⟨T n, T.mem_range_self n⟩ : H)⟫_𝕜 = ⟪z, x⟫_𝕜
    rw [hST ⟨n, hn⟩, hmn, inner_add_right,
      T.ker.inner_left_of_mem_orthogonal hm hz, zero_add]

/-- Closed range of an operator implies closed range of its adjoint. -/
theorem isClosed_adjoint_range_of_isClosed_range
    (T : H →L[𝕜] K) (hclosed : IsClosed (T.range : Set K)) :
    IsClosed (T.adjoint.range : Set H) := by
  rw [adjoint_range_eq_kernel_orthogonal_of_isClosed T hclosed]
  exact T.ker.isClosed_orthogonal

end AdjointRange

theorem closed_range_iff_adjoint_range_closed : Spec.ClosedRangeAdjointIff.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T
  constructor
  · exact isClosed_adjoint_range_of_isClosed_range T
  · intro hclosed
    have h := isClosed_adjoint_range_of_isClosed_range T.adjoint hclosed
    simpa only [ContinuousLinearMap.adjoint_adjoint] using h

theorem closed_range_kernel_range_identities : Spec.ClosedRangeIdentities.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ _ _ T hclosed
  have hstar := (closed_range_iff_adjoint_range_closed 𝕜 H K T).mp hclosed
  have h := adjoint_range_eq_kernel_orthogonal_of_isClosed T.adjoint hstar
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  exact ⟨h, adjoint_range_eq_kernel_orthogonal_of_isClosed T hclosed⟩

end ExpandedFA.Hilbert.ClosedRangeEquivalences
