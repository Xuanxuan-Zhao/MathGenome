import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteFieldDegreeTwo
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CyclicDegreeTwo
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.FiniteLayerCohomology
import Mathlib.FieldTheory.Finite.GaloisField

import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.CyclicDegreeTwo
namespace GaloisFormalization.GH

open Model
open KrullLayers
open Specs.GaloisFormalization.GH.FiniteLayerCohomology
open scoped Algebra

universe u v

private theorem finiteRelativeHTwo
    (fieldEquiv : CyclicDegreeTwo.Specification.FieldEquivalence.{u,v})
    (k : Type u) (E : Type v) [Field k] [Finite k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E]
    [tG : TopologicalSpace Gal(E/k)] [DiscreteTopology Gal(E/k)]
    [tU : TopologicalSpace Eˣ] [DiscreteTopology Eˣ] :
    Subsingleton (ContinuousH Gal(E/k) (Additive Eˣ) 2) := by
  have htG : tG = ⊥ := DiscreteTopology.eq_bot
  have htU : tU = ⊥ := DiscreteTopology.eq_bot
  subst tG
  subst tU
  have : Finite E := Module.finite_of_finite k
  obtain ⟨e⟩ := fieldEquiv k E
  have hrange : (CyclicDegreeTwo.fieldUnitNorm k E).range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _ (FiniteField.unitsMap_norm_surjective k E)
  have : Subsingleton (kˣ ⧸ (CyclicDegreeTwo.fieldUnitNorm k E).range) :=
    hrange ▸ QuotientGroup.subsingleton_quotient_top
  exact e.injective.subsingleton

private theorem finiteLayerHTwo
    (fieldEquiv : CyclicDegreeTwo.Specification.FieldEquivalence.{u,v})
    {k : Type u} {S : Type v} [Field k] [Finite k] [Field S] [Algebra k S] [IsGalois k S]
    [TopologicalSpace Sˣ] [DiscreteTopology Sˣ]
    (E : FiniteGaloisIntermediateField k S) :
    Subsingleton (LayerH (Additive Sˣ) E 2) := by
  let : TopologicalSpace Eˣ := ⊥
  have : DiscreteTopology Eˣ := discreteTopology_bot _
  let M := LayerCoefficients (Additive Sˣ) E
  obtain ⟨unitsEquiv, unitsEquiv_val⟩ := fixedUnits_layer E
  let includeUnits : Additive Eˣ →+ Additive Sˣ :=
    ((FixedPoints.subgroup (layerKernel E) Sˣ).subtype.comp unitsEquiv.toMonoidHom).toAdditive
  let coeffMap : Additive Eˣ →+ M := includeUnits.codRestrict M fun a =>
    (Model.mem_fixedCoefficients _ _ _ _).mpr fun g hg =>
      (FixedPoints.mem_subgroup _ _ _).mp (unitsEquiv a.toMul).property ⟨g, hg⟩
  have coeffMap_val (a : Additive Eˣ) :
      (coeffMap a : Additive Sˣ) = Additive.ofMul (Units.map (algebraMap E S) a.toMul) :=
    unitsEquiv_val a.toMul
  have coeffMap_bijective : Function.Bijective coeffMap := by
    constructor
    · intro a b hab
      exact unitsEquiv.injective (Subtype.ext (congrArg Subtype.val hab))
    · intro b
      have hb : (b : Additive Sˣ).toMul ∈ FixedPoints.subgroup (layerKernel E) Sˣ :=
        (FixedPoints.mem_subgroup _ _ _).mpr fun g =>
          (Model.mem_fixedCoefficients _ _ _ _).mp b.property g g.property
      obtain ⟨a, ha⟩ := unitsEquiv.surjective ⟨(b : Additive Sˣ).toMul, hb⟩
      exact ⟨Additive.ofMul a, Subtype.ext (congrArg Subtype.val ha)⟩
  have coeffMap_smul (g : LayerGroup E) (a : Additive Eˣ) :
      coeffMap (g • a) = g • coeffMap a := by
    have hsurj : Function.Surjective (Specs.GaloisFormalization.GH.KrullLayers.restrict E) :=
      restrict_surjective E
    obtain ⟨σ, rfl⟩ := hsurj g
    apply Subtype.ext
    rw [layerAction_restrict, coeffMap_val, coeffMap_val]
    exact congrArg Additive.ofMul (restrict_units_apply E σ a.toMul)
  let e := AddEquiv.ofBijective coeffMap coeffMap_bijective
  have hEinv (g : LayerGroup E) (b : M) : e.symm (g • b) = g • e.symm b := by
    apply e.injective
    rw [e.apply_symm_apply]
    change g • b = coeffMap (g • e.symm b)
    rw [coeffMap_smul]
    exact congrArg (g • ·) (e.apply_symm_apply b).symm
  let φ := MonoidHom.id (LayerGroup E)
  let push := continuousCohomologyMap φ continuous_id coeffMap coeffMap_smul 2
  let pull := continuousCocycleMap φ continuous_id e.symm.toAddMonoidHom hEinv 2
  have hpush : Function.Surjective push := by
    intro x
    obtain ⟨c, rfl⟩ := continuousClass_surjective 2 x
    refine ⟨continuousClass (LayerGroup E) (Additive Eˣ) 2 (pull c), ?_⟩
    change continuousCohomologyMap φ continuous_id coeffMap coeffMap_smul 2
      (continuousClass (LayerGroup E) (Additive Eˣ) 2 (pull c)) = _
    rw [continuousCohomologyMap_class]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact e.apply_symm_apply _
  have := finiteRelativeHTwo fieldEquiv k E
  have : Subsingleton (ContinuousH (LayerGroup E) M 2) := hpush.subsingleton
  exact (ordinaryCohomologyEquiv.{v,v,0} (LayerGroup E) M 2).surjective.subsingleton

/-- Conditional proof of the finite-field calculation using the cyclic relative
cohomology formula and the finite-layer comparison. -/
theorem finite_field_degree_two_conditional
    (_ : CyclicDegreeTwo.Specification.EquivalenceWithCarry.{u,v})
    (_ : CyclicDegreeTwo.Specification.OrderOneTriviality.{u,v})
    (fieldEquiv : CyclicDegreeTwo.Specification.FieldEquivalence.{u,v}) :
    FiniteFieldDegreeTwo.Specification.Vanishing.{u,v} := by
  intro k S _ _ _ _ _
  let : TopologicalSpace Sˣ := ⊥
  have : DiscreteTopology Sˣ := discreteTopology_bot _
  have := continuous_unitsAction k S
  change Subsingleton (ContinuousH Gal(S/k) (Additive Sˣ) 2)
  obtain ⟨e, _⟩ := FiniteLayerCohomology.finiteLayerComparison (k := k) (L := S) (Additive Sˣ) 2
  have hzero (x : LayerLimit (k := k) (L := S) (Additive Sˣ) 2) : x = 0 := by
    let ι := FiniteGaloisIntermediateField k S
    let : DecidableEq ι := Classical.decEq _
    let A (E : ι) : Type v := LayerH (Additive Sˣ) E 2
    let f (E F : ι) (h : E ≤ F) : A E →ₗ[ℤ] A F := stageTransition (Additive Sˣ) E F 2 h
    obtain ⟨E, a, ha⟩ := Module.DirectLimit.exists_of (R := ℤ) (ι := ι) (G := A) (f := f) x
    have := finiteLayerHTwo fieldEquiv E
    rw [← ha, Subsingleton.elim a 0, map_zero]
  have : Subsingleton (LayerLimit (k := k) (L := S) (Additive Sˣ) 2) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  exact e.symm.injective.subsingleton

end GaloisFormalization.GH

universe v8_closure_2a41d677a469ea45_u0 v8_closure_2a41d677a469ea45_u1
theorem _root_.«GaloisFormalization».«GH».«finite_field_degree_two» : _root_.«GaloisFormalization».«GH».«FiniteFieldDegreeTwo».«Specification».«Vanishing».{v8_closure_2a41d677a469ea45_u0, v8_closure_2a41d677a469ea45_u1} :=
  @_root_.«GaloisFormalization».«GH».«finite_field_degree_two_conditional».{v8_closure_2a41d677a469ea45_u0, v8_closure_2a41d677a469ea45_u1} (@_root_.«GaloisFormalization».«GH».«cyclic_degree_two».{v8_closure_2a41d677a469ea45_u0, v8_closure_2a41d677a469ea45_u1}) (@_root_.«GaloisFormalization».«GH».«cyclic_degree_two_order_one».{v8_closure_2a41d677a469ea45_u0, v8_closure_2a41d677a469ea45_u1}) (@_root_.«GaloisFormalization».«GH».«cyclic_field_degree_two».{v8_closure_2a41d677a469ea45_u0, v8_closure_2a41d677a469ea45_u1})
