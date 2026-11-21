import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ReproducingKernelRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ReproducingKernels
import Mathlib.Tactic.Linarith

/-!
The kernel is closed because the integral map is continuous into the product
of its point evaluations. Restriction to its orthogonal complement is a
bijection onto the actual range. Transporting the Hilbert structure through
this bijection gives the range its own norm and topology, rather than the
ambient topology of functions. Pythagoras proves both attainment of the
preimage-norm infimum and uniqueness of the minimizer. The conjugate kernel
rows lie in this complement and give the claimed reproducing vectors.
-/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.PartV.ReproducingKernelRange
universe u v
open Spec

section RangeGeometry
variable {𝕜 : Type} {E : Type u} {Y : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Restriction to the orthogonal complement, with values in actual functions. -/
def orthogonalRangeMap (A : E →ₗ[𝕜] (Y → 𝕜)) :
    A.ker.orthogonal →ₗ[𝕜] A.range :=
  (A.comp A.ker.orthogonal.subtype).codRestrict A.range
    (fun q => ⟨q, rfl⟩)

omit [CompleteSpace E] in
lemma orthogonalRangeMap_injective (A : E →ₗ[𝕜] (Y → 𝕜)) :
    Function.Injective (orthogonalRangeMap A) := by
  intro q r h
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hk : (q : E) - r ∈ A.ker := by
    change A ((q : E) - r) = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h
  have ho := A.ker.orthogonal.sub_mem q.property r.property
  have hmem : (q : E) - r ∈ A.ker ⊓ A.ker.orthogonal := ⟨hk, ho⟩
  simpa only [A.ker.inf_orthogonal_eq_bot, Submodule.mem_bot] using hmem

lemma orthogonalRangeMap_surjective (A : E →ₗ[𝕜] (Y → 𝕜))
    (hc : IsClosed (A.ker : Set E)) :
    Function.Surjective (orthogonalRangeMap A) := by
  let : CompleteSpace A.ker := hc.completeSpace_coe
  rintro ⟨f, u, rfl⟩
  refine ⟨⟨u - A.ker.starProjection u, A.ker.sub_starProjection_mem_orthogonal u⟩, ?_⟩
  apply Subtype.ext
  change A (u - A.ker.starProjection u) = A u
  rw [map_sub, show A (A.ker.starProjection u) = 0 from
    A.ker.starProjection_apply_mem u, sub_zero]

/-- Bijection from the complete orthogonal complement onto the algebraic range. -/
def orthogonalRangeEquiv (A : E →ₗ[𝕜] (Y → 𝕜))
    (hc : IsClosed (A.ker : Set E)) : A.ker.orthogonal ≃ₗ[𝕜] A.range :=
  LinearEquiv.ofBijective (orthogonalRangeMap A)
    ⟨orthogonalRangeMap_injective A, orthogonalRangeMap_surjective A hc⟩

omit [CompleteSpace E] in
lemma orthogonal_preimage_minimal (A : E →ₗ[𝕜] (Y → 𝕜))
    (q : A.ker.orthogonal) (u : E) (h : A u = A q) :
    ‖q‖ ≤ ‖u‖ ∧ (‖u‖ = ‖q‖ ↔ u = q) := by
  have hk : u - (q : E) ∈ A.ker := by
    change A (u - (q : E)) = 0
    rw [map_sub, h, sub_self]
  have hi : ⟪(q : E), u - (q : E)⟫_𝕜 = 0 :=
    A.ker.inner_left_of_mem_orthogonal hk q.property
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (q : E) (u - (q : E)) hi
  rw [add_sub_cancel] at he
  change ‖u‖ * ‖u‖ = ‖q‖ * ‖q‖ + ‖u - (q : E)‖ * ‖u - (q : E)‖ at he
  refine ⟨?_, ?_⟩
  · nlinarith [norm_nonneg q, norm_nonneg u, sq_nonneg ‖u - (q : E)‖]
  · constructor
    · intro hn
      have hs : ‖u - (q : E)‖ * ‖u - (q : E)‖ = 0 := by
        rw [hn] at he
        linarith only [he]
      have hz : ‖u - (q : E)‖ = 0 := mul_self_eq_zero.mp hs
      exact sub_eq_zero.mp (norm_eq_zero.mp hz)
    · rintro rfl
      rfl

omit [CompleteSpace E] in
lemma orthogonal_preimage_unique (A : E →ₗ[𝕜] (Y → 𝕜))
    (q : A.ker.orthogonal) (u : E) :
    (A u = A q ∧ u ∈ A.ker.orthogonal) ↔ u = q := by
  constructor
  · rintro ⟨ha, hu⟩
    have he : orthogonalRangeMap A ⟨u, hu⟩ = orthogonalRangeMap A q :=
      Subtype.ext ha
    exact congrArg Subtype.val (orthogonalRangeMap_injective A he)
  · rintro rfl
    exact ⟨rfl, q.property⟩
end RangeGeometry

variable {𝕜 : Type} {Z : Type u} {X : Type v} [RCLike 𝕜] [MeasurableSpace Z]

lemma integralMap_integral (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) (u : Lp 𝕜 2 μ) (x : X) :
    integralMap μ k hk u x = ∫ z, k x z * u z ∂μ := by
  change ⟪sectionVector μ k hk x, u⟫_𝕜 = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hk x).star.coeFn_toLp] with z hz
  simp [sectionVector, hz, RCLike.inner_apply, RCLike.star_def, mul_comm]

lemma integralMap_continuous (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) : Continuous (integralMap μ k hk) :=
  continuous_pi fun x => (innerSL 𝕜 (sectionVector μ k hk x)).continuous

lemma integralMap_closed_kernel (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) :
    IsClosed ((integralMap μ k hk).ker : Set (Lp 𝕜 2 μ)) :=
  (⟨integralMap μ k hk, integralMap_continuous μ k hk⟩ :
    Lp 𝕜 2 μ →L[𝕜] (X → 𝕜)).isClosed_ker

lemma sectionVector_mem_orthogonal (μ : Measure Z) (k : X → Z → 𝕜)
    (hk : ∀ x, MemLp (k x) 2 μ) (x : X) :
    sectionVector μ k hk x ∈ (integralMap μ k hk).ker.orthogonal := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  exact congrFun hu x

/-- The integral range itself is a Hilbert space with its minimum-preimage norm. -/
theorem integral_range : Spec.IntegralRange.{u, v} := by
  intro 𝕜 Z X _ _ μ k hk
  let A := integralMap μ k hk
  have hc : IsClosed (A.ker : Set (Lp 𝕜 2 μ)) := integralMap_closed_kernel μ k hk
  refine ⟨hc, ?_, ?_⟩
  · intro u x
    refine ⟨?_, integralMap_integral μ k hk u x,
      norm_inner_le_norm (sectionVector μ k hk x) u⟩
    apply (integrable_congr ?_).mp (L2.integrable_inner (𝕜 := 𝕜)
      (sectionVector μ k hk x) u)
    filter_upwards [(hk x).star.coeFn_toLp] with z hz
    simp [sectionVector, hz, RCLike.inner_apply, RCLike.star_def, mul_comm]
  let e := orthogonalRangeEquiv A hc
  let ng : NormedAddCommGroup A.range :=
    NormedAddCommGroup.induced _ _ e.symm.toAddMonoidHom e.symm.injective
  let : UniformSpace A.range := ng.toMetricSpace.toUniformSpace
  let : TopologicalSpace A.range := ng.toMetricSpace.toUniformSpace.toTopologicalSpace
  let ip : InnerProductSpace 𝕜 A.range := InnerProductSpace.induced e.symm.toLinearMap
  let J : A.range ≃ₗᵢ[𝕜] A.ker.orthogonal :=
    { e.symm with norm_map' := fun _ => rfl }
  let cp : CompleteSpace A.range :=
    (J.isometry.isUniformInducing.completeSpace_congr J.surjective).mpr inferInstance
  have hpre (f : A.range) : A (J f) = f.val :=
    congrArg Subtype.val (e.apply_symm_apply f)
  let F : ReproducingKernels.Spec.FunctionSpace 𝕜 X A.range :=
    { functions := A.range.subtype
      injective := Subtype.val_injective
      continuous_eval := fun x => by
        change Continuous (fun f : A.range => f.val x)
        have hcont : Continuous (fun f : A.range => A (J f) x) :=
          (innerSL 𝕜 (sectionVector μ k hk x)).continuous.comp
            (continuous_subtype_val.comp J.continuous)
        simpa only [hpre] using hcont }
  refine ⟨ng, ip, cp, F, J, fun _ => rfl, ?_, ?_⟩
  · intro f
    have hmin (u : Lp 𝕜 2 μ) (hu : A u = f.val) :
        ‖f‖ ≤ ‖u‖ ∧ (‖u‖ = ‖f‖ ↔ u = (J f : Lp 𝕜 2 μ)) := by
      simpa only [J.norm_map] using
        orthogonal_preimage_minimal A (J f) u (hu.trans (hpre f).symm)
    refine ⟨hpre f, ?_, hmin, ?_⟩
    · change ‖f‖ = sInf {r | ∃ u : Lp 𝕜 2 μ, A u = f.val ∧ ‖u‖ = r}
      apply Eq.symm
      apply IsLeast.csInf_eq
      refine ⟨⟨J f, hpre f, ?_⟩, ?_⟩
      · exact (J.norm_map f)
      · rintro r ⟨u, hu, rfl⟩
        exact (hmin u hu).1
    · intro u
      rw [← hpre f]
      exact orthogonal_preimage_unique A (J f) u
  · let q : X → A.ker.orthogonal := fun x =>
      ⟨sectionVector μ k hk x, sectionVector_mem_orthogonal μ k hk x⟩
    let κ : X → A.range := fun x => J.symm (q x)
    have hκ (x : X) : (J (κ x) : Lp 𝕜 2 μ) = sectionVector μ k hk x := by
      exact congrArg Subtype.val (J.apply_symm_apply (q x))
    have hrep : ReproducingKernels.Spec.Reproduces F κ := by
      intro f x
      change f.val x = ⟪κ x, f⟫_𝕜
      rw [← hpre f, ← J.inner_map_map]
      change A (J f) x = ⟪(J (κ x) : Lp 𝕜 2 μ), (J f : Lp 𝕜 2 μ)⟫_𝕜
      rw [hκ]
      rfl
    have hkernel (x y : X) :
        F.functions (κ y) x = ∫ z, k x z * conj (k y z) ∂μ := by
      change (κ y).val x = _
      rw [← hpre (κ y), hκ, integralMap_integral μ k hk]
      apply integral_congr_ae
      filter_upwards [(hk y).star.coeFn_toLp] with z hz
      simp [sectionVector, hz, RCLike.star_def]
    refine ⟨κ, hκ, hrep, hkernel, ?_⟩
    intro x y
    rw [← hrep (κ y) x]
    exact hkernel x y

end ExpandedFA.PartV.ReproducingKernelRange
