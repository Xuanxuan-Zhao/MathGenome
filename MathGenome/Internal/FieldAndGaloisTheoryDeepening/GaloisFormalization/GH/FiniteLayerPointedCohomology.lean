import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteCochainDescent
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.NonabelianH1

/-! The pointed finite-layer comparison for continuous nonabelian degree-one cohomology. -/

namespace GaloisFormalization.GH.FiniteLayerPointedCohomology

open KrullLayers (restrict_comp restrict_surjective layerKernels_basis layerKernel_le_iff)
open NonabelianH1.Spec hiding restrict
open Specs.GaloisFormalization.GH.KrullLayers (LayerGroup restrict transition)
open Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology
open scoped Specs.GaloisFormalization.GH.FiniteLayerPointedCohomology

universe u v w

noncomputable section

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] [IsGalois k L]
variable {B : Type w} [Group B] [MulDistribMulAction Gal(L/k) B]
variable [TopologicalSpace B] [DiscreteTopology B]

private theorem inflateCocycle_stageCocycleMap {E F : FiniteGaloisIntermediateField k L}
    (h : E ≤ F) (c : OrdinaryCocycle (LayerGroup E) (Coefficients B E)) :
    inflateCocycle B F (stageCocycleMap h c) = inflateCocycle B E c := by
  apply NonabelianH1.Cocycle.ext
  intro g
  change (c (transition h (restrict F g)) : B) = (c (restrict E g) : B)
  exact congrArg (fun σ => (c σ : B)) (DFunLike.congr_fun (restrict_comp h) g).symm

private theorem stageInflation_comp {E F : FiniteGaloisIntermediateField k L}
    (h : E ≤ F) (x : Stage B E) :
    stageInflation B E x = stageInflation B F (stageMap B h x) := by
  refine Quotient.inductionOn x fun c => ?_
  change stageInflation B E (ordinaryClassOf c) =
    stageInflation B F (stageMap B h (ordinaryClassOf c))
  rw [stageMap_classOf, stageInflation_classOf, stageInflation_classOf,
    inflateCocycle_stageCocycleMap]

variable (B) in
private def colimitInflation : Colimit (k := k) (L := L) B → H1 Gal(L/k) B :=
  DirectLimit.lift (fun _ _ h => stageMap B h) (stageInflation B)
    (fun _ _ h x => stageInflation_comp h x)

variable [ContinuousSMul Gal(L/k) B]

private theorem exists_inflateCocycle (c : Cocycle Gal(L/k) B) :
    ∃ (E : FiniteGaloisIntermediateField k L)
      (cE : OrdinaryCocycle (LayerGroup E) (Coefficients B E)), inflateCocycle B E cE = c := by
  let f : (Fin 1 → Gal(L/k)) → B := fun g => c (g 0)
  obtain ⟨E, _, fE, hfE⟩ := FiniteCochainDescent.finiteCochainFactorization f
    (c.property.1.comp (continuous_apply 0)) (⊥ : FiniteGaloisIntermediateField k L)
  let cE (σ : LayerGroup E) : Coefficients B E := fE (fun _ => σ)
  have hcE (g : Gal(L/k)) : (cE (restrict E g) : B) = c g := hfE (fun _ => g)
  have hcocycle : IsCocycle cE := by
    intro σ τ
    obtain ⟨g, rfl⟩ := restrict_surjective E σ
    obtain ⟨h, rfl⟩ := restrict_surjective E τ
    apply Subtype.ext
    change (cE (restrict E g * restrict E h) : B) =
      (cE (restrict E g) : B) *
        ((restrict E g • cE (restrict E h) : Coefficients B E) : B)
    rw [← map_mul (restrict E), restrict_smul, hcE, hcE, hcE]
    exact c.property.2 g h
  refine ⟨E, ⟨cE, hcocycle⟩, NonabelianH1.Cocycle.ext ?_⟩
  exact hcE

private theorem colimitInflation_surjective :
    Function.Surjective (colimitInflation (k := k) (L := L) B) := by
  intro x
  refine Quotient.inductionOn x fun c => ?_
  obtain ⟨E, cE, hcE⟩ := exists_inflateCocycle c
  refine ⟨ofStage B E (ordinaryClassOf cE), ?_⟩
  change stageInflation B E (ordinaryClassOf cE) = classOf c
  rw [stageInflation_classOf, hcE]

/-- A single coefficient is fixed at some finite layer extending the given layer. -/
private theorem exists_layer_fixing (E : FiniteGaloisIntermediateField k L) (b : B) :
    ∃ F : FiniteGaloisIntermediateField k L, E ≤ F ∧ b ∈ Coefficients B F := by
  have hone : (1 : Gal(L/k)) ∈ MulAction.stabilizer Gal(L/k) b :=
    (MulAction.stabilizer Gal(L/k) b).one_mem
  obtain ⟨D, _, hD⟩ := (layerKernels_basis k L).mem_iff.mp
    ((stabilizer_isOpen Gal(L/k) b).mem_nhds hone)
  refine ⟨E ⊔ D, le_sup_left, fun g => hD ?_⟩
  exact layerKernel_le_iff.mpr le_sup_right g.property

private theorem colimitInflation_injective :
    Function.Injective (colimitInflation (k := k) (L := L) B) := by
  intro x y
  refine DirectLimit.induction₂ (fun _ _ h => stageMap B h) ?_ x y
  intro E xE yE
  refine Quotient.inductionOn₂ xE yE fun c d heq => ?_
  change stageInflation B E (ordinaryClassOf c) = stageInflation B E (ordinaryClassOf d) at heq
  rw [stageInflation_classOf, stageInflation_classOf] at heq
  obtain ⟨b, hb⟩ := NonabelianH1.classOf_eq_iff.mp heq
  obtain ⟨F, hEF, hfix⟩ := exists_layer_fixing E b
  refine Quotient.sound ⟨F, hEF, hEF, ?_⟩
  change stageMap B hEF (ordinaryClassOf c) = stageMap B hEF (ordinaryClassOf d)
  rw [stageMap_classOf, stageMap_classOf]
  let bF : Coefficients B F := ⟨b, hfix⟩
  refine Quotient.sound ⟨bF, fun σ => ?_⟩
  obtain ⟨g, rfl⟩ := restrict_surjective F σ
  apply Subtype.ext
  change inflateCocycle B F (stageCocycleMap hEF d) g =
    b⁻¹ * inflateCocycle B F (stageCocycleMap hEF c) g *
      ((restrict F g • bF : Coefficients B F) : B)
  rw [inflateCocycle_stageCocycleMap, inflateCocycle_stageCocycleMap, restrict_smul]
  exact hb g

/-- Inflation induces the canonical pointed bijection from the finite-layer colimit. -/
theorem comparison : comparison_type.{u, v, w} := by
  intro k L _ _ _ _ B _ _ _ _ _
  refine ⟨Equiv.ofBijective (colimitInflation B)
    ⟨colimitInflation_injective, colimitInflation_surjective⟩, fun _ _ => rfl, ?_⟩
  let E : FiniteGaloisIntermediateField k L := ⊥
  change stageInflation B E (ordinaryClassOf (ordinaryTrivial _ _)) = classOf (trivial _ _)
  rw [stageInflation_classOf]
  exact congrArg classOf (NonabelianH1.Cocycle.ext fun _ => rfl)

end

end GaloisFormalization.GH.FiniteLayerPointedCohomology
