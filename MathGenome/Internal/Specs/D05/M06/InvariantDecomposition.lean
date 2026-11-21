import MathGenome.Internal.Specs.D05.M06.ExternalSum
import MathGenome.Internal.Specs.D05.M06.Invariant

/-!
K05.06.invariant_decomposition, paper.tex:995–1001.
The internal decomposition is bijectivity of the upstream external summation
map. The finite-family statement is bridged to `UniqueDecomposition` below.
The same construction also works for arbitrary index sets, since the external
sum has finite support. There is no finite-dimensional hypothesis.
-/
namespace Specs.D05.M06.InvariantDecomposition

open Specs.D05.M06.ExternalSum (summationMap)
open Specs.D05.M06.Invariant (invariant_value restriction_value)

/-- The actual external-to-internal summation isomorphism. -/
noncomputable def summationEquiv {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (U : ι → Submodule K V)
    (h : Function.Bijective (summationMap U)) :
    _root_.DirectSum ι (fun i => U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (summationMap U) h

/-- Extract the i-component and include it into the ambient space. -/
noncomputable def componentProjection {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] (U : ι → Submodule K V)
    (h : Function.Bijective (summationMap U)) (i : ι) : Module.End K V :=
  (U i).subtype.comp
    ((_root_.DirectSum.component K ι (fun j => U j) i).comp
      (summationEquiv U h).symm.toLinearMap)

/-- Apply the genuine restriction of T separately in every component. -/
def restrictedSum {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (T : Module.End K V)
    (hT : ∀ i, invariant_value K V (U i) T) :
    Module.End K (_root_.DirectSum ι (fun i => U i)) :=
  _root_.DirectSum.lmap (fun i => restriction_value K V (U i) T (hT i))

/-- Identifies precisely the decomposition assumption in the finite source convention. -/
def finite_internal_iff_bijective : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V),
    Specs.D05.M06.DirectSum.UniqueDecomposition U ↔
      Function.Bijective (summationMap U)

/-- The forward map of the isomorphism really is summation. -/
def summationEquiv_apply : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (x : _root_.DirectSum ι (fun i => U i)),
    summationEquiv U h x = summationMap U x

/-- This identifies the projections with the components of the unique expansion. -/
def componentProjection_on_sum : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (x : _root_.DirectSum ι (fun i => U i)) (i : ι),
    componentProjection U h i (summationMap U x) = (x i : V)

/-- Each component projection fixes its own summand. -/
def componentProjection_on_summand : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (i : ι) (u : U i), componentProjection U h i (u : V) = (u : V)

/-- These are algebraic idempotent projections with exactly the stated images. -/
def componentProjection_properties : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U)) (i : ι),
    (componentProjection U h i) ^ 2 = componentProjection U h i ∧
      LinearMap.range (componentProjection U h i) = U i ∧
      ∀ v : V, componentProjection U h i v = v ↔ v ∈ U i

/-- The two-sided commuting-projection criterion. -/
def invariant_iff_commuting : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (T : Module.End K V),
    (∀ i, invariant_value K V (U i) T) ↔
      ∀ i, (componentProjection U h i).comp T = T.comp (componentProjection U h i)

/-- Summing the restrictions intertwines them with T; no directness is needed. -/
def direct_sum_intertwines : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (T : Module.End K V)
    (hT : ∀ i, invariant_value K V (U i) T),
    T.comp (summationMap U) = (summationMap U).comp (restrictedSum U T hT)

/-- Every transformed coordinate is exactly the restriction applied to that coordinate. -/
def transformed_component : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T) (v : V) (i : ι),
    ((summationEquiv U h).symm (T v)) i =
      restriction_value K V (U i) T (hT i) (((summationEquiv U h).symm v) i)

/-- The full block-diagonal conclusion as equality of actual linear maps. -/
def direct_sum_conjugacy : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : ι → Submodule K V) (h : Function.Bijective (summationMap U))
    (T : Module.End K V) (hT : ∀ i, invariant_value K V (U i) T),
    (summationEquiv U h).symm.toLinearMap.comp (T.comp (summationEquiv U h).toLinearMap) =
      restrictedSum U T hT

/-- The source's finite-family formulation, including its empty family case. -/
def finite_invariant_decomposition : Prop :=
  ∀ {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (U : ι → Submodule K V) (_hU : Specs.D05.M06.DirectSum.UniqueDecomposition U)
    (T : Module.End K V),
    ∃ h : Function.Bijective (summationMap U),
      ((∀ i, invariant_value K V (U i) T) ↔
        ∀ i, (componentProjection U h i).comp T = T.comp (componentProjection U h i)) ∧
      ∀ hT : ∀ i, invariant_value K V (U i) T,
        (summationEquiv U h).symm.toLinearMap.comp
          (T.comp (summationEquiv U h).toLinearMap) = restrictedSum U T hT

end Specs.D05.M06.InvariantDecomposition
