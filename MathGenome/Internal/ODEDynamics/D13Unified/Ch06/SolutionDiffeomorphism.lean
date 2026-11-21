import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.SolutionDiffeomorphism
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.Rebase
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.OpenDomain

/-! Finite-time solution diffeomorphisms on the entire survival domains. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch06.SolutionDiffeomorphism
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch06.SolutionDiffeomorphism
open C1Dependence
universe u v

/-- The actual survival domain; no extension of the equation's domain is made. -/
def survivalDomain : survivalDomainType := survivalDomainValue

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma isOpen_survivalDomain (F : ParameterODE E P) (hF : F.LocallyLipschitzInState)
    (s t : ℝ) (p : P) : IsOpen (survivalDomainValue F s t p) := by
  exact (Ch05.OpenDomain.open_domain F hF).preimage
    (continuous_const.prodMk ((continuous_const.prodMk continuous_id).prodMk continuous_const))

/-- A solution reaching t can be traced back to s, on precisely the same
maximal interval. The reverse value is the original initial state. -/
lemma reverse_solution (F : ParameterODE E P) (hF : F.LocallyLipschitzInState)
    {s t : ℝ} {ξ : E} {p : P} (hξ : ξ ∈ survivalDomainValue F s t p) :
    solution F (t,((s,ξ),p)) ∈ survivalDomainValue F t s p ∧
      solution F (s,((t,solution F (t,((s,ξ),p))),p)) = ξ := by
  have hmem : (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F := hξ
  have hx := ParameterODE.solutionValue_ivp F hF s ξ p hmem.1
  have hgraph := (ParameterODE.solutionValue_on_domain F hF t s ξ p hmem).2
  obtain ⟨hI, he⟩ := ParameterODE.rebase F hF s ξ p hmem.1 t hmem.2
    (solution F (t,((s,ξ),p))) rfl
  refine ⟨⟨hgraph, hI.symm ▸ hx.2.1⟩, ?_⟩
  exact (he s hx.2.1).trans hx.2.2

lemma contDiffOn_solution_slice (k : ℕ) (hk : 1 ≤ k) (F : ParameterODE E P)
    (hF : ContDiffOn ℝ k (field F) F.domain) (s t : ℝ) (p : P) :
    ContDiffOn ℝ k (fun ξ => solution F (t,((s,ξ),p)))
      (survivalDomainValue F s t p) := by
  exact (CkDependence.joint_ck k hk F hF).2.comp
    (contDiffOn_const.prodMk ((contDiffOn_const.prodMk contDiffOn_id).prodMk contDiffOn_const))
    (fun _ hξ => hξ)

/-- Forward and reverse solution maps form a Cᵏ diffeomorphism with their
full actual domains as source and target. -/
theorem solution_diffeomorphism : Diffeomorphism.{u,v} := by
  intro E _ _ _ P _ _ _ k hk F hF s t p
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by exact_mod_cast hk)
  have hL := F.locallyLipschitzInState_of_contDiffOn hF1
  have ho := isOpen_survivalDomain F hL s t p
  have hor := isOpen_survivalDomain F hL t s p
  have hc := contDiffOn_solution_slice k hk F hF s t p
  have hcr := contDiffOn_solution_slice k hk F hF t s p
  have hi : (fun ξ => solution F (t,((s,ξ),p))) '' survivalDomainValue F s t p =
      survivalDomainValue F t s p := by
    apply Subset.antisymm
    · rintro _ ⟨ξ,hξ,rfl⟩
      exact (reverse_solution F hL hξ).1
    · intro η hη
      exact ⟨_, (reverse_solution F hL hη).1, (reverse_solution F hL hη).2⟩
  let e : OpenPartialHomeomorph E E :=
    { toFun := fun ξ => solution F (t,((s,ξ),p))
      invFun := fun η => solution F (s,((t,η),p))
      source := survivalDomainValue F s t p
      target := survivalDomainValue F t s p
      map_source' := fun _ hξ => (reverse_solution F hL hξ).1
      map_target' := fun _ hη => (reverse_solution F hL hη).1
      left_inv' := fun _ hξ => (reverse_solution F hL hξ).2
      right_inv' := fun _ hη => (reverse_solution F hL hη).2
      continuousOn_toFun := hc.continuousOn
      continuousOn_invFun := hcr.continuousOn
      open_source := ho
      open_target := hor }
  exact ⟨ho,hor,hi,e,rfl,rfl,rfl,rfl,hc,hcr⟩

/-- Differentiate the inverse identity on an open neighborhood of the datum. -/
lemma reverse_derivative_comp (k : ℕ) (hk : 1 ≤ k) (F : ParameterODE E P)
    (hF : ContDiffOn ℝ k (field F) F.domain) {s t : ℝ} {ξ : E} {p : P}
    (hξ : ξ ∈ survivalDomainValue F s t p) :
    (stateVariation F t (solution F (t,((s,ξ),p))) p s).comp
      (stateVariation F s ξ p t) = ContinuousLinearMap.id ℝ E := by
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by exact_mod_cast hk)
  have hL := F.locallyLipschitzInState_of_contDiffOn hF1
  have ho := isOpen_survivalDomain F hL s t p
  have hor := isOpen_survivalDomain F hL t s p
  have hη := (reverse_solution F hL hξ).1
  have hc := contDiffOn_solution_slice 1 (by omega) F hF1 s t p
  have hcr := contDiffOn_solution_slice 1 (by omega) F hF1 t s p
  have hdf := (hc.differentiableOn_one.differentiableAt (ho.mem_nhds hξ)).hasFDerivAt
  have hdg := (hcr.differentiableOn_one.differentiableAt (hor.mem_nhds hη)).hasFDerivAt
  have hcomp := hdg.comp ξ hdf
  have hid : HasFDerivAt
      (fun x => solution F (s,((t,solution F (t,((s,x),p))),p)))
      (ContinuousLinearMap.id ℝ E) ξ := by
    apply (hasFDerivAt_id ξ).congr_of_eventuallyEq
    filter_upwards [ho.mem_nhds hξ] with x hx
    exact (reverse_solution F hL hx).2
  exact hcomp.unique hid

/-- The reverse-time derivative is an actual continuous linear inverse. -/
theorem derivative_inverse : DerivativeInverse.{u,v} := by
  intro E _ _ _ P _ _ _ k hk F hF s t ξ p hξ
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by exact_mod_cast hk)
  have hL := F.locallyLipschitzInState_of_contDiffOn hF1
  have hr := reverse_solution F hL hξ
  have hleft := reverse_derivative_comp k hk F hF hξ
  have hright := reverse_derivative_comp k hk F hF hr.1
  rw [hr.2] at hright
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft, hleft, hright⟩

end D13Unified.Ch06.SolutionDiffeomorphism
