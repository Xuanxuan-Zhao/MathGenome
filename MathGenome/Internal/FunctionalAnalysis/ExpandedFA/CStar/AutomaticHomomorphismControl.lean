import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.AutomaticHomomorphismControl
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.Quotient
import Mathlib.Analysis.CStarAlgebra.Hom

noncomputable section
namespace ExpandedFA.CStar.AutomaticHomomorphismControl
universe u v
open scoped CStarAlgebra

/-- The first part of the proposition is supplied by the accepted ideal and
actual-distance-quotient constructions. -/
theorem closed_ideals : Spec.ClosedIdeals.{u} :=
  ⟨IdealApproximateIdentities.star_invariant,
    IdealApproximateIdentities.approximate_identity, Quotient.quotient_cstar⟩

theorem contractive : Spec.Contractive.{u,v} := by
  intro A B _ _ f a
  exact NonUnitalStarAlgHom.norm_apply_le f a

theorem injective_isometry : Spec.InjectiveIsometry.{u,v} := by
  intro A B _ _ f hf
  exact NonUnitalStarAlgHom.isometry f hf

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Continuity is obtained from automatic contractivity, before forming the kernel. -/
def closedKernel (f : A →⋆ₙₐ[ℂ] B) : Quotient.Spec.ClosedTwoSidedIdeal A where
  toSubmodule := LinearMap.ker (f : A →ₗ[ℂ] B)
  isClosed := isClosed_singleton.preimage (map_continuous f)
  isTwoSided := by
    constructor
    · intro a b hb
      change f (a * b) = 0
      change f b = 0 at hb
      rw [map_mul, hb, mul_zero]
    · intro a b ha
      change f (a * b) = 0
      change f a = 0 at ha
      rw [map_mul, ha, zero_mul]

section Factor
variable (f : A →⋆ₙₐ[ℂ] B)
local instance : NonUnitalCStarAlgebra (A ⧸ (closedKernel f).toSubmodule) :=
  Quotient.quotientCStarAlgebra (closedKernel f)

/-- The algebraic quotient lift, endowed with its induced multiplication and star. -/
def kernelLift : (A ⧸ (closedKernel f).toSubmodule) →⋆ₙₐ[ℂ] B where
  toFun := (closedKernel f).toSubmodule.liftQ (f : A →ₗ[ℂ] B) le_rfl
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := (closedKernel f).toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := (closedKernel f).toSubmodule.mkQ_surjective y
    exact map_mul f a b
  map_star' := by
    intro x
    obtain ⟨a, rfl⟩ := (closedKernel f).toSubmodule.mkQ_surjective x
    exact map_star f a

@[simp] lemma kernelLift_mk (a : A) :
    kernelLift f ((closedKernel f).toSubmodule.mkQ a) = f a := rfl

lemma kernelLift_injective : Function.Injective (kernelLift f) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (closedKernel f).toSubmodule.mkQ_surjective x
  obtain ⟨b, rfl⟩ := (closedKernel f).toSubmodule.mkQ_surjective y
  apply (Submodule.Quotient.eq (closedKernel f).toSubmodule).mpr
  change f (a - b) = 0
  rw [map_sub, sub_eq_zero]
  exact h

lemma kernelLift_range : Set.range (kernelLift f) = Set.range f := by
  ext b
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (closedKernel f).toSubmodule.mkQ_surjective x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(closedKernel f).toSubmodule.mkQ a, rfl⟩

end Factor

theorem kernel_factorization : Spec.KernelFactorization.{u,v} := by
  intro A B _ _ f
  letI := Quotient.quotientCStarAlgebra (closedKernel f)
  refine ⟨closedKernel f, fun _ => Iff.rfl,
    Quotient.quotientCStarAlgebra (closedKernel f), rfl, rfl, rfl, rfl,
    (fun _ _ => rfl), (fun _ => rfl), kernelLift f, kernelLift_mk f,
    kernelLift_injective f, ?_, kernelLift_range f⟩
  exact NonUnitalStarAlgHom.isometry (kernelLift f) (kernelLift_injective f)

/-- Completeness belongs to the actual C*-quotient; its isometric image is closed. -/
theorem closed_range : Spec.ClosedRange.{u,v} := by
  intro A B _ _ f
  letI := Quotient.quotientCStarAlgebra (closedKernel f)
  rw [← kernelLift_range f]
  exact (NonUnitalStarAlgHom.isometry (kernelLift f)
    (kernelLift_injective f)).isClosedEmbedding.isClosed_range

end ExpandedFA.CStar.AutomaticHomomorphismControl
