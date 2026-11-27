import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.LiftCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.KrullLayers

/-! Finite-stage detection of weak solutions in Corollary IG05. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem

open _root_.GaloisFormalization.GH.Model
open scoped IsMulCommutative

universe u v w

noncomputable section

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q)

/-- The open normal subgroups through which the prescribed quotient factors. -/
abbrev FiniteStage :=
  {U : Subgroup Γ // IsOpen (U : Set Γ) ∧ U.Normal ∧ U ≤ P.rho.toMonoidHom.ker}

namespace FiniteStage

variable {P} (U : P.FiniteStage)

instance normal : U.val.Normal := U.prop.2.1

instance discrete : DiscreteTopology (Γ ⧸ U.val) :=
  QuotientGroup.discreteTopology U.prop.1

instance finite : Finite (Γ ⧸ U.val) :=
  finite_of_compact_of_discrete

/-- The canonical projection from the profinite group to the stage. -/
def projection : Γ →ₜ* Γ ⧸ U.val :=
  ⟨QuotientGroup.mk' U.val, QuotientGroup.continuous_mk⟩

/-- The map to the prescribed quotient induced by the original map. -/
def rho : (Γ ⧸ U.val) →ₜ* Q :=
  ⟨QuotientGroup.lift U.val P.rho.toMonoidHom U.prop.2.2,
    continuous_of_discreteTopology⟩

/-- The canonical transition from a finer stage to a coarser stage. -/
def transition {V : P.FiniteStage} (h : V ≤ U) : (Γ ⧸ V.val) →ₜ* Γ ⧸ U.val :=
  ⟨QuotientGroup.lift V.val (QuotientGroup.mk' U.val)
    (by rw [QuotientGroup.ker_mk']; exact h), continuous_of_discreteTopology⟩

/-- The same embedding problem with the source replaced by the finite quotient. -/
def problem : FiniteEmbeddingProblem (Γ ⧸ U.val) B Q where
  rho := U.rho
  pi := P.pi
  rho_surjective :=
    QuotientGroup.lift_surjective_of_surjective U.val P.rho.toMonoidHom P.rho_surjective U.prop.2.2
  pi_surjective := P.pi_surjective

variable [IsMulCommutative P.kernel]

local notation "A" => Additive P.kernel

local instance : DistribMulAction Q A := P.quotientKernelActionValue

/-- The stage acts on the original kernel via its map to the prescribed quotient. -/
@[instance_reducible]
def kernelAction : DistribMulAction (Γ ⧸ U.val) A :=
  DistribMulAction.compHom A U.rho.toMonoidHom

local instance stageAction (T : P.FiniteStage) : DistribMulAction (Γ ⧸ T.val) A :=
  T.kernelAction

/-- The extension class in a universe common to the three groups, represented by
the original normalized factor set. -/
def extensionClassAtStageUniverse :
    groupCohomology (integralRepresentation.{w,v,max u v w} Q A) 2 :=
  groupCohomology.π _ 2
    (ordinaryCyclesMk.{w,v,u} Q A 2 (factorCocycle P (normalizedSection P)))

/-- The ordinary class obtained by pulling back the extension class along ρ_U. -/
def obstruction : groupCohomology (integralRepresentation.{u,v,max u v w} (Γ ⧸ U.val) A) 2 :=
  groupCohomology.map
    (liftGroupHom.{w,max u v w,u} U.rho.toMonoidHom)
    (liftCoefficientMap.{w,v,max u w,u,v} U.rho.toMonoidHom (AddMonoidHom.id A)
      (fun _ _ => rfl)) 2 (extensionClassAtStageUniverse (P := P))

/-- Ordinary inflation along the transition, with the identity on the kernel. -/
def inflation {V : P.FiniteStage} (h : V ≤ U) :
    groupCohomology (integralRepresentation.{u,v,max u v w} (Γ ⧸ U.val) A) 2 →ₗ[ULift.{max u v w} ℤ]
      groupCohomology (integralRepresentation.{u,v,max u v w} (Γ ⧸ V.val) A) 2 :=
  (groupCohomology.map
    (liftGroupHom.{u,max u v w,u} (U.transition h).toMonoidHom)
    (liftCoefficientMap.{u,v,max u w,u,v} (U.transition h).toMonoidHom (AddMonoidHom.id A)
      (fun x a => by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
        rfl)) 2).hom

end FiniteStage

namespace Specification

/-- All stage quotients are compact, discrete and finite. -/
def FiniteStageProperties : Prop :=
  ∀ U : P.FiniteStage, CompactSpace (Γ ⧸ U.val) ∧ DiscreteTopology (Γ ⧸ U.val) ∧
    Finite (Γ ⧸ U.val)

/-- A weak solution exists exactly when an ordinary obstruction vanishes at a stage. -/
def FiniteStageDetection [IsMulCommutative P.kernel] : Prop :=
  Nonempty P.WeakSolution ↔ ∃ U : P.FiniteStage, U.obstruction = 0

/-- Finer stages carry the inflation of the coarser stage obstruction. -/
def FiniteStageInflation [IsMulCommutative P.kernel] : Prop :=
  ∀ {U V : P.FiniteStage} (h : V ≤ U), U.inflation h U.obstruction = V.obstruction

end Specification

end

namespace Specification

private def ForEveryProblem
    (statement : ∀ {Γ : Type u} {B : Type v} {Q : Type w}
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
      [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
      [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
      [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
      FiniteEmbeddingProblem Γ B Q → Prop) : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q), statement P

def FiniteStagePropertiesStatement : Prop :=
  ForEveryProblem.{u,v,w} fun P => FiniteStageProperties P

def FiniteStageDetectionStatement : Prop :=
  ForEveryProblem.{u,v,w} fun P => ∀ [IsMulCommutative P.kernel], FiniteStageDetection P

def FiniteStageInflationStatement : Prop :=
  ForEveryProblem.{u,v,w} fun P => ∀ [IsMulCommutative P.kernel], FiniteStageInflation P

open _root_.Specs.GaloisFormalization.GH.KrullLayers

/-- With the prescribed restriction to E, stages are the finite Galois layers
containing E, and the quotient maps are the corresponding restrictions. -/
def GaloisStageIdentification {k : Type u} {Ω : Type w}
    [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (E : FiniteGaloisIntermediateField k Ω)
    {B : Type v} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k Ω) B (LayerGroup E)) : Prop :=
  P.rho = restrict E →
    ∃ stages : {F : FiniteGaloisIntermediateField k Ω // E ≤ F} ≃o P.FiniteStageᵒᵈ,
      (∀ F, (OrderDual.ofDual (stages F)).val = layerKernel F.val) ∧
      ∃ identify : ∀ F, (Gal(Ω/k) ⧸ (OrderDual.ofDual (stages F)).val) ≃ₜ* LayerGroup F.val,
        (∀ F γ, identify F ((OrderDual.ofDual (stages F)).projection γ) = restrict F.val γ) ∧
        (∀ F x, (OrderDual.ofDual (stages F)).rho x = transition F.prop (identify F x)) ∧
        ∀ (F D) (h : F ≤ D) x,
          identify F ((OrderDual.ofDual (stages F)).transition
            (show OrderDual.ofDual (stages D) ≤ OrderDual.ofDual (stages F) from
              stages.monotone h) x) =
            transition (show F.val ≤ D.val from h) (identify D x)

def GaloisStageIdentificationStatement : Prop :=
  ∀ {k : Type u} {Ω : Type w}
    [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (E : FiniteGaloisIntermediateField k Ω)
    {B : Type v} [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (P : FiniteEmbeddingProblem (AbsoluteGaloisGroup k Ω) B (LayerGroup E)),
    GaloisStageIdentification E P

end Specification
end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem
