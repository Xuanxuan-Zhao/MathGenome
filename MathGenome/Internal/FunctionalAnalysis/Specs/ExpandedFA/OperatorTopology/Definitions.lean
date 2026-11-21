import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Independent specifications for the operator-topology definitions in
`fa2:p1:operator-topologies` and `fa2:p2:double-commutant`.
The underlying operators are the existing bounded scalar-linear maps.
The original norms and norm-continuous dual are fixed before introducing either
topology. No completeness is assumed except in the Hilbert-space identification,
where only the target must be complete. All results include zero spaces.
-/

namespace ExpandedFA.OperatorTopology.Spec

open scoped Topology InnerProductSpace
noncomputable section
universe u v w

def StrongSeminormType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], SeminormFamily 𝕜 (E →L[𝕜] F) E

def StrongSeminormValue : StrongSeminormType :=
  fun _ _ _ _ _ _ _ _ x => {
    toFun := fun T => ‖T x‖
    map_zero' := by simp
    add_le' := fun T S => by simpa using norm_add_le (T x) (S x)
    neg' := fun T => by simp
    smul' := fun a T => by simp [norm_smul]
  }

def WeakSeminormType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], SeminormFamily 𝕜 (E →L[𝕜] F) (E × (F →L[𝕜] 𝕜))

def WeakSeminormValue : WeakSeminormType :=
  fun _ _ _ _ _ _ _ _ p => {
    toFun := fun T => ‖p.2 (T p.1)‖
    map_zero' := by simp
    add_le' := fun T S => by simpa using norm_add_le (p.2 (T p.1)) (p.2 (S p.1))
    neg' := fun T => by simp
    smul' := fun a T => by simp
  }

def StrongTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], TopologicalSpace (E →L[𝕜] F)

/-- Pointwise convergence in the original norm topology of F. -/
def StrongTopologyValue : StrongTopologyType :=
  fun _ _ _ _ _ _ _ _ => .induced (fun T x => T x) Pi.topologicalSpace

def WeakTopologyType := StrongTopologyType.{u,v,w}

/-- Scalar tests use the original continuous linear dual of F. -/
def WeakTopologyValue : WeakTopologyType :=
  fun 𝕜 E F _ _ _ _ _ => .induced
    (fun (T : E →L[𝕜] F) (p : E × (F →L[𝕜] 𝕜)) => p.2 (T p.1)) Pi.topologicalSpace

def HilbertCoefficientTopologyType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [InnerProductSpace 𝕜 F], TopologicalSpace (E →L[𝕜] F)

/-- The first inner-product variable is conjugate-linear. -/
def HilbertCoefficientTopologyValue : HilbertCoefficientTopologyType :=
  fun 𝕜 E F _ _ _ _ _ => .induced
    (fun T (p : E × F) => ⟪p.2, T p.1⟫_𝕜) Pi.topologicalSpace

def StrongSeminormFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], ∀ (x : E) (T : E →L[𝕜] F),
    StrongSeminormValue 𝕜 E F x T = ‖T x‖

def WeakSeminormFormula : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], ∀ (x : E) (g : F →L[𝕜] 𝕜) (T : E →L[𝕜] F),
    WeakSeminormValue 𝕜 E F (x, g) T = ‖g (T x)‖

def StrongWithSeminorms : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    @WithSeminorms 𝕜 (E →L[𝕜] F) E _ _ _ (StrongSeminormValue 𝕜 E F)
      (StrongTopologyValue 𝕜 E F)

def WeakWithSeminorms : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    @WithSeminorms 𝕜 (E →L[𝕜] F) (E × (F →L[𝕜] 𝕜)) _ _ _ (WeakSeminormValue 𝕜 E F)
      (WeakTopologyValue 𝕜 E F)

def StrongInitial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    StrongTopologyValue 𝕜 E F =
      ⨅ x : E, TopologicalSpace.induced (fun T : E →L[𝕜] F => T x) inferInstance

def WeakInitial : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    WeakTopologyValue 𝕜 E F = ⨅ x : E, ⨅ g : F →L[𝕜] 𝕜,
      TopologicalSpace.induced (fun T : E →L[𝕜] F => g (T x)) inferInstance

def StrongTendsto : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    ∀ (α : Type*) (l : Filter α) (f : α → E →L[𝕜] F) (T : E →L[𝕜] F),
    Filter.Tendsto f l (@nhds _ (StrongTopologyValue 𝕜 E F) T) ↔
      ∀ x : E, Filter.Tendsto (fun a => f a x) l (𝓝 (T x))

def WeakTendsto : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    ∀ (α : Type*) (l : Filter α) (f : α → E →L[𝕜] F) (T : E →L[𝕜] F),
    Filter.Tendsto f l (@nhds _ (WeakTopologyValue 𝕜 E F) T) ↔
      ∀ (x : E) (g : F →L[𝕜] 𝕜),
        Filter.Tendsto (fun a => g (f a x)) l (𝓝 (g (T x)))

def HilbertIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [InnerProductSpace 𝕜 F], ∀ [CompleteSpace F],
    WeakTopologyValue 𝕜 E F = HilbertCoefficientTopologyValue 𝕜 E F

def HilbertTendsto : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [InnerProductSpace 𝕜 F], ∀ [CompleteSpace F],
    ∀ (α : Type*) (l : Filter α) (f : α → E →L[𝕜] F) (T : E →L[𝕜] F),
    Filter.Tendsto f l (@nhds _ (WeakTopologyValue 𝕜 E F) T) ↔
      ∀ (x : E) (y : F),
        Filter.Tendsto (fun a => ⟪y, f a x⟫_𝕜) l (𝓝 ⟪y, T x⟫_𝕜)

/-- Compatibility with Mathlib's canonical WOT type copy, by the identity
on underlying bounded operators. -/
def WeakNative : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    WeakTopologyValue 𝕜 E F = TopologicalSpace.induced
      (ContinuousLinearMapWOT.ofCLM : (E →L[𝕜] F) → (E →WOT[𝕜] F)) inferInstance

/-- Lean's topology order is reversed relative to inclusion of open sets. -/
def StrongCoarsest : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], ∀ t : TopologicalSpace (E →L[𝕜] F),
    (∀ x : E, @Continuous _ F t inferInstance (fun T => T x)) ↔
      t ≤ StrongTopologyValue 𝕜 E F

def WeakCoarsest : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F], ∀ t : TopologicalSpace (E →L[𝕜] F),
    (∀ (x : E) (g : F →L[𝕜] 𝕜),
      @Continuous _ 𝕜 t inferInstance (fun T => g (T x))) ↔
      t ≤ WeakTopologyValue 𝕜 E F

end
end ExpandedFA.OperatorTopology.Spec
