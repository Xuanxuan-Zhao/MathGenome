import MathGenome.Internal.LinearPDE.P201Specs.Common.Cutoff
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionSupport
import Mathlib.Tactic.Ring

noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace P201
open P201Specs (SmoothCoefficient distributionMultiply cutoffLaplacianCoefficient
  cutoffGradientPairing)

/-- The first-order distributional Leibniz rule, with the positive coefficient term. -/
theorem cutoffFirstDerivative : P201Specs.cutoffFirstDerivativeStatement := by
  intro n 𝕜 _ Ω χ u j
  exact (P102.U4.distributionMultiplier_productRule χ u j).trans (add_comm _ _)

private theorem cutoffSecondDerivative {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Domain n} (χ : SmoothCoefficient 𝕜 Ω) (u : Distribution 𝕜 Ω) (j : Fin n) :
    distributionDerivative ({j, j} : MultiIndex n) (distributionMultiply χ u) =
      distributionMultiply χ (distributionDerivative ({j, j} : MultiIndex n) u) +
      (2 : 𝕜) • distributionMultiply (P102.U4.coefficientPartial j χ)
        (distributionDerivative {j} u) +
      distributionMultiply (P102.U4.coefficientPartial j (P102.U4.coefficientPartial j χ)) u := by
  have hm : ({j, j} : MultiIndex n) = {j} + {j} := rfl
  simp only [hm, distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.derivative_add n 𝕜 Ω, P102.U4.distributionMultiplier_productRule,
    P102.U4.distributionPartial_add]
  ext φ
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Summing the second-order rules gives all three terms of the cutoff identity. -/
theorem cutoffLaplacian : P201Specs.cutoffLaplacianStatement := by
  intro n 𝕜 _ Ω χ u
  change (∑ j : Fin n, distributionDerivative ({j, j} : MultiIndex n)
    (distributionMultiply χ u)) = _
  simp_rw [cutoffSecondDerivative]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · exact (map_sum (P102.U4.distributionMultiplier χ) _ _).symm
    · exact Finset.smul_sum.symm
  · ext φ
    change (∑ j : Fin n,
      P102.U4.distributionMultiplier
        (P102.U4.coefficientPartial j (P102.U4.coefficientPartial j χ)) u) φ = _
    rw [sum_apply]
    simp only [P102.U4.distributionMultiplier_apply, distributionMultiply]
    rw [← map_sum]
    apply congrArg u
    ext x
    simp [cutoffLaplacianCoefficient, P201Specs.laplacian,
      P201Specs.multiPartial, P102.U4.multiPartial, P102.U4.coefficientPartial,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Multiset.sort_cons j {j} (· ≤ ·) (by simp), Multiset.sort_singleton]
    rfl

/-- Compactness is intrinsic to Ω, independently of the representative off Ω. -/
theorem cutoffCompactSupport : P201Specs.cutoffCompactSupportStatement := by
  intro n 𝕜 _ Ω χ u hχ
  let v := distributionMultiply χ u
  have hs : P102.U4.relativeSupport v ⊆ (Ω : Set (Space n)) ∩ tsupport χ.val := by
    intro x hx
    exact (P102.U4.multiplierSupport n 𝕜 Ω P102.U4.testMultiplier
      (fun _ _ _ => rfl) χ u hx).1
  have ht : (Subtype.val : Ω → Space n) ⁻¹' tsupport χ.val =
      tsupport (fun x : Ω => χ.val x) := by
    unfold tsupport
    exact Ω.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (Function.support χ.val)
  have hc : IsCompact ((Subtype.val : Ω → Space n) ⁻¹' P102.U4.relativeSupport v) := by
    apply hχ.of_isClosed_subset (P102.U4.relativelyClosed n 𝕜 Ω v)
    rw [← ht]
    exact fun x hx => (hs hx).2
  have hi : (Subtype.val : Ω → Space n) ''
      ((Subtype.val : Ω → Space n) ⁻¹' P102.U4.relativeSupport v) =
      P102.U4.relativeSupport v := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, (hs hx).1⟩, hx, rfl⟩
  exact ⟨hi ▸ hc.image continuous_subtype_val, fun x hx => (hs hx).1⟩

end P201
