import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Algebra

/-!
Independent statements for the operator part of paper.tex,
`fa2:p5:continuous-kernel`, lines 21677–21685. The transpose and continuous/L²
identifications are allocated to their own goals and use this same operator.

The domain spaces carry their canonical supremum norms. We state the stronger
finite positive Borel measure result; every finite positive Radon measure in
the source is such a measure. No metrizability, nonemptiness or positive mass
is required. Uniqueness of the bounded operator specified by the integral
formula makes the construction canonical for the later bridges.
-/

open MeasureTheory
universe u v w
namespace ExpandedFA.PartV.ContinuousKernel.Spec

def KernelIntegralType :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y], Measure Y → C(X × Y, 𝕜) → C(Y, 𝕜) → X → 𝕜

noncomputable def KernelIntegralValue : KernelIntegralType :=
  fun _ _ _ _ _ _ _ ν k u x => ∫ y, k (x, y) * u y ∂ν

/-! Canonical shared construction. The side conditions for packaging the
integral as a continuous linear map are proved below, rather than assumed as
certificates. The candidate proves its pointwise formula and compactness.
Downstream independent Specs can refer to `KernelOperatorValue` directly. -/

section Construction
variable {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsFiniteMeasure ν] (k : C(X × Y, 𝕜))

/-- View each kernel section as an element of the Banach space C(X). -/
def kernelSection : C(Y, C(X, 𝕜)) :=
  (k.comp ⟨Prod.swap, continuous_swap⟩).curry

omit [T2Space X] [T2Space Y] in
lemma kernel_section_integrable (u : C(Y, 𝕜)) :
    Integrable (fun y => u y • kernelSection k y) ν := by
  exact (u.continuous.smul (kernelSection k).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integration in C(X) builds a continuous output before taking evaluations. -/
noncomputable def kernelImage (u : C(Y, 𝕜)) : C(X, 𝕜) :=
  ∫ y, u y • kernelSection k y ∂ν

omit [T2Space X] [T2Space Y] in
lemma kernelImage_apply (u : C(Y, 𝕜)) (x : X) :
    kernelImage ν k u x = KernelIntegralValue 𝕜 X Y ν k u x := by
  rw [kernelImage, ContinuousMap.integral_apply (kernel_section_integrable ν k u)]
  simp [KernelIntegralValue, kernelSection, mul_comm]

omit [CompactSpace X] [T2Space X] [T2Space Y] in
lemma kernel_integrable_section (u : C(Y, 𝕜)) (x : X) :
    Integrable (fun y => k (x, y) * u y) ν := by
  exact (((k.continuous.comp (continuous_const.prodMk continuous_id)).mul
    u.continuous)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma kernelImage_norm_le (u : C(Y, 𝕜)) :
    ‖kernelImage ν k u‖ ≤ (ν.real Set.univ * ‖k‖) * ‖u‖ := by
  apply ((kernelImage ν k u).norm_le (by positivity)).mpr
  intro x
  rw [kernelImage_apply]
  calc
    ‖KernelIntegralValue 𝕜 X Y ν k u x‖ ≤ (‖k‖ * ‖u‖) * ν.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with y
      exact (norm_mul_le _ _).trans
        (mul_le_mul (k.norm_coe_le_norm (x, y)) (u.norm_coe_le_norm y)
          (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

noncomputable def kernelLinearMap : C(Y, 𝕜) →ₗ[𝕜] C(X, 𝕜) where
  toFun := kernelImage ν k
  map_add' u v := by
    ext x
    simp only [kernelImage_apply, KernelIntegralValue, ContinuousMap.add_apply, mul_add]
    exact integral_add (kernel_integrable_section ν k u x) (kernel_integrable_section ν k v x)
  map_smul' a u := by
    ext x
    simp only [kernelImage_apply, KernelIntegralValue, ContinuousMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm (k _) a, mul_assoc]
    exact integral_const_mul a _

/-- The continuous kernel's bounded linear integral operator. -/
noncomputable def KernelOperatorValue : C(Y, 𝕜) →L[𝕜] C(X, 𝕜) :=
  (kernelLinearMap ν k).mkContinuous (ν.real Set.univ * ‖k‖)
    (kernelImage_norm_le ν k)

lemma KernelOperatorValue_apply (u : C(Y, 𝕜)) (x : X) :
    KernelOperatorValue ν k u x = KernelIntegralValue 𝕜 X Y ν k u x :=
  kernelImage_apply ν k u x

lemma KernelOperatorValue_norm_le : ‖KernelOperatorValue ν k‖ ≤ ν.real Set.univ * ‖k‖ := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end Construction

/-- Type of the canonical bounded continuous-kernel operator. -/
def KernelOperatorType :=
  ∀ {𝕜 : Type u} {X : Type v} {Y : Type w} [RCLike 𝕜]
    [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν],
    C(X × Y, 𝕜) → C(Y, 𝕜) →L[𝕜] C(X, 𝕜)

def Integrability : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)) (u : C(Y, 𝕜)) (x : X),
    Integrable (fun y => k (x, y) * u y) ν

def OutputContinuity : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)) (u : C(Y, 𝕜)),
    Continuous (KernelIntegralValue 𝕜 X Y ν k u)

/-- The integral formula determines a unique bounded linear operator with the
required operator norm estimate. The canonical norms are supremum norms,
including on empty domains. -/
def BoundedOperator : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)),
    ∃! T : C(Y, 𝕜) →L[𝕜] C(X, 𝕜),
      (∀ u x, T u x = KernelIntegralValue 𝕜 X Y ν k u x) ∧
      ‖T‖ ≤ ν.real Set.univ * ‖k‖

/-- These degenerate cases give the zero operator, without divisions by mass
or nonzero norms. -/
def ZeroCases : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)) (T : C(Y, 𝕜) →L[𝕜] C(X, 𝕜)),
    (∀ u x, T u x = KernelIntegralValue 𝕜 X Y ν k u x) →
    (ν = 0 ∨ IsEmpty X ∨ IsEmpty Y) → T = 0

/-- Every bounded set has relatively norm-compact image under the operator
specified by the actual integral formula. -/
def CompactImages : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)) (T : C(Y, 𝕜) →L[𝕜] C(X, 𝕜)),
    (∀ u x, T u x = KernelIntegralValue 𝕜 X Y ν k u x) →
    ∀ S : Set C(Y, 𝕜), Bornology.IsBounded S → IsCompact (closure (T '' S))

/-- The full continuous-kernel theorem, retaining its formula, boundedness,
quantitative norm estimate, and compactness in the norm topology. -/
def FullTheorem : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)),
    ∃! T : C(Y, 𝕜) →L[𝕜] C(X, 𝕜),
      (∀ u x, T u x = KernelIntegralValue 𝕜 X Y ν k u x) ∧
      ‖T‖ ≤ ν.real Set.univ * ‖k‖ ∧ IsCompactOperator T ∧
      ∀ S : Set C(Y, 𝕜), Bornology.IsBounded S → IsCompact (closure (T '' S))

/-- All required properties of the very same canonical operator that is
exported for use by transpose and continuous/L² bridges. -/
def CanonicalOperatorProperties : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : C(X × Y, 𝕜)),
    (∀ (u : C(Y, 𝕜)) (x : X),
      Integrable (fun y => k (x, y) * u y) ν ∧
      KernelOperatorValue ν k u x = KernelIntegralValue 𝕜 X Y ν k u x) ∧
    ‖KernelOperatorValue ν k‖ ≤ ν.real Set.univ * ‖k‖ ∧
    IsCompactOperator (KernelOperatorValue ν k) ∧
    ∀ S : Set C(Y, 𝕜), Bornology.IsBounded S →
      IsCompact (closure (KernelOperatorValue ν k '' S))

end ExpandedFA.PartV.ContinuousKernel.Spec
