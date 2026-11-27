import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.ObstructionAndClassification
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.FiniteStageObstructions

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

open _root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem (FiniteStage)
open _root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.Specification
open CategoryTheory
open scoped IsMulCommutative

universe u v w

noncomputable section

section FiniteStages

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q)

theorem finiteStage_properties : FiniteStageProperties P :=
  fun U => ⟨inferInstance, U.discrete, U.finite⟩

variable {P} (U : P.FiniteStage)

private theorem stage_rho_projection (g : Γ) : U.rho (U.projection g) = P.rho g :=
  rfl

private theorem stage_rho_transition {V : P.FiniteStage} (h : V ≤ U) :
    U.rho.toMonoidHom.comp (U.transition h).toMonoidHom = V.rho.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

private def stageOfWeakSolution (s : P.WeakSolution) : P.FiniteStage :=
  ⟨s.lift.toMonoidHom.ker,
    (isOpen_discrete ({1} : Set B)).preimage s.lift.continuous,
    inferInstance,
    fun g hg => by
      change P.rho g = 1
      change s.lift g = 1 at hg
      rw [← s.commutes_apply, hg, map_one]⟩

private def descendWeakSolution (s : P.WeakSolution) :
    (stageOfWeakSolution s).problem.WeakSolution where
  lift := ⟨QuotientGroup.lift _ s.lift.toMonoidHom le_rfl, continuous_of_discreteTopology⟩
  commutes := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact s.commutes_apply g

private def pullbackWeakSolution (s : U.problem.WeakSolution) : P.WeakSolution where
  lift := s.lift.comp U.projection
  commutes := by
    ext g
    exact (WeakSolution.commutes_apply s (U.projection g)).trans (stage_rho_projection U g)

variable [IsMulCommutative P.kernel]

local notation "A" => Additive P.kernel
local instance : DistribMulAction Q A := P.quotientKernelAction
local instance stageAction (T : P.FiniteStage) : DistribMulAction (Γ ⧸ T.val) A := T.kernelAction

local instance stageKernelAbelian (T : P.FiniteStage) : IsMulCommutative T.problem.kernel :=
  ‹IsMulCommutative P.kernel›

private theorem stage_obstruction_comparison :
    GH.ordinaryCohomologyEquiv.{u,v,max w v} (Γ ⧸ U.val) A 2
        (weakLiftObstruction U.problem) = U.obstruction := by
  rw [show weakLiftObstruction U.problem =
    GH.continuousCohomologyMap U.rho.toMonoidHom U.rho.continuous
      (AddMonoidHom.id A) (fun _ _ => rfl) 2 (continuousExtensionClass P) from rfl]
  rw [GH.ordinaryCohomologyEquiv_map.{w,v,0,u,v} U.rho.toMonoidHom U.rho.continuous
    (AddMonoidHom.id A) (fun _ _ => rfl)]
  rw [show continuousExtensionClass P =
    GH.continuousClass Q A 2 (factorCocycle P (normalizedSection P)) from rfl]
  rw [GH.ordinaryCohomologyEquiv_class]
  rfl

private theorem nonempty_stage_weakSolution_iff :
    Nonempty U.problem.WeakSolution ↔ U.obstruction = 0 := by
  rw [nonempty_weakSolution_iff_obstruction_eq_zero]
  let e := GH.ordinaryCohomologyEquiv.{u,v,max w v} (Γ ⧸ U.val) A 2
  rw [← stage_obstruction_comparison U, ← map_zero e]
  exact e.injective.eq_iff.symm

variable (P)

/-- A weak solution exists exactly when some finite quotient has zero ordinary obstruction. -/
theorem finiteStage_detection :
    FiniteStageDetection P := by
  constructor
  · rintro ⟨s⟩
    exact ⟨stageOfWeakSolution s, (nonempty_stage_weakSolution_iff _).mp ⟨descendWeakSolution s⟩⟩
  · rintro ⟨U, h⟩
    obtain ⟨s⟩ := (nonempty_stage_weakSolution_iff U).mpr h
    exact ⟨pullbackWeakSolution U s⟩

variable {P}

private theorem stage_action_transition {U V : P.FiniteStage} (h : V ≤ U) (x : Γ ⧸ V.val)
    (a : A) : (U.transition h x) • a = x • a := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

variable (P)

/-- The transition on ordinary cohomology transports the obstruction by inflation. -/
theorem finiteStage_inflation :
    FiniteStageInflation P := by
  intro U V h
  let f := U.rho.toMonoidHom
  let g := (U.transition h).toMonoidHom
  let f' := GH.liftGroupHom.{w,max u v w,u} f
  let g' := GH.liftGroupHom.{u,max u v w,u} g
  let fCoefficients := GH.liftCoefficientMap.{w,v,max u w,u,v} f (AddMonoidHom.id A) (fun _ _ => rfl)
  let gCoefficients := GH.liftCoefficientMap.{u,v,max u w,u,v} g (AddMonoidHom.id A)
    (stage_action_transition h)
  let fV := GH.liftGroupHom.{w,max u v w,u} V.rho.toMonoidHom
  let finerCoefficients := GH.liftCoefficientMap.{w,v,max u w,u,v} V.rho.toMonoidHom
    (AddMonoidHom.id A) (fun _ _ => rfl)
  let c := Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.FiniteStage.extensionClassAtStageUniverse
    (P := P)
  change groupCohomology.map g' gCoefficients 2
      (groupCohomology.map f' fCoefficients 2 c) =
    (groupCohomology.map fV finerCoefficients 2) c
  change (groupCohomology.map f' fCoefficients 2 ≫ groupCohomology.map g' gCoefficients 2) c = _
  rw [← groupCohomology.map_comp]
  have heq : f'.comp g' = fV :=
    MonoidHom.ext fun x => ULift.ext (DFunLike.congr_fun (stage_rho_transition U h) x.down)
  have hmap : groupCohomology.map (f'.comp g')
      ((Rep.resFunctor g').map fCoefficients ≫ gCoefficients) 2 =
        groupCohomology.map fV finerCoefficients 2 :=
    groupCohomology.map_congr heq (LinearMap.ext fun _ => rfl) 2
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hmap) c

end FiniteStages

section AbsoluteGalois

open GH.KrullLayers

variable {k : Type u} {Ω : Type w} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
  (E : FiniteGaloisIntermediateField k Ω)
  {B : Type v} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k Ω) B (LayerGroup E))

/-- Stages over a prescribed Galois quotient are the containing finite Galois layers.
The stage projection and the transitions agree with the field restrictions. -/
theorem galois_finiteStage_identification : GaloisStageIdentification E P := by
  intro hρ
  have hker : P.rho.toMonoidHom.ker = layerKernel E :=
    (congrArg (fun f : Gal(Ω/k) →ₜ* LayerGroup E => f.toMonoidHom.ker) hρ).trans (restrict_ker E)
  let stage (F : {F : FiniteGaloisIntermediateField k Ω // E ≤ F}) : P.FiniteStage :=
    ⟨layerKernel F.val, layerKernel_isOpen F.val, inferInstance,
      hker.symm ▸ layerKernel_le_iff.mpr F.prop⟩
  have stage_le (F D : {F : FiniteGaloisIntermediateField k Ω // E ≤ F}) :
      stage D ≤ stage F ↔ F ≤ D :=
    layerKernel_le_iff
  have surj : Function.Surjective stage := by
    intro U
    obtain ⟨corr, hc, _⟩ := openNormalCorrespondence k Ω
    let H : OpenNormalSubgroup k Ω := ⟨U.val, U.prop.1, U.prop.2.1⟩
    let F := corr.symm (OrderDual.toDual H)
    have hF : layerKernel F = U.val :=
      (hc F).symm.trans (congrArg (fun W => (OrderDual.ofDual W).val) (corr.apply_symm_apply _))
    have hEF : E ≤ F := layerKernel_le_iff.mp (hF.symm ▸ hker ▸ U.prop.2.2)
    exact ⟨⟨F, hEF⟩, Subtype.ext hF⟩
  let stages : {F : FiniteGaloisIntermediateField k Ω // E ≤ F} ≃o P.FiniteStageᵒᵈ :=
    { Equiv.ofBijective (fun F => OrderDual.toDual (stage F))
        ⟨fun F D h => by
          have hh : stage F = stage D := congrArg OrderDual.ofDual h
          exact le_antisymm ((stage_le F D).mp hh.ge) ((stage_le D F).mp hh.le), surj⟩ with
      map_rel_iff' := fun {F D} => stage_le F D }
  choose identify hid using fun (F : {F : FiniteGaloisIntermediateField k Ω // E ≤ F}) =>
    ExistsUnique.exists (quotient_restriction F.val)
  refine ⟨stages, fun _ => rfl, identify, hid, ?_, ?_⟩
  · intro F x
    change (stage F).rho x = transition F.prop (identify F x)
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    calc
      _ = P.rho γ := rfl
      _ = restrict E γ := DFunLike.congr_fun hρ γ
      _ = transition F.prop (restrict F.val γ) := DFunLike.congr_fun (restrict_comp F.prop) γ
      _ = _ := congrArg (transition F.prop) (hid F γ).symm
  · intro F D h x
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    change identify F (QuotientGroup.mk γ) = transition (show F.val ≤ D.val from h) (identify D (QuotientGroup.mk γ))
    calc
      _ = restrict F.val γ := hid F γ
      _ = transition (show F.val ≤ D.val from h) (restrict D.val γ) :=
        DFunLike.congr_fun (restrict_comp (show F.val ≤ D.val from h)) γ
      _ = _ := congrArg (transition (show F.val ≤ D.val from h)) (hid D γ).symm

end AbsoluteGalois

end
end GaloisFormalization.IG.FiniteEmbeddingProblem
