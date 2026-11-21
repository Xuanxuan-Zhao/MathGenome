import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.Algebra.Module.Basic

/-! Independent specification of Proposition `fa2:p1:c04:dual-maps`,
paper.tex 816–825. All duals are continuous scalar-linear duals with the
operator norm; closures and closed spans use the given norm topologies.
The input sets are arbitrary and restrictions are to arbitrary subspaces.
Only the quotient clause requires a closed subspace. There is no completeness
or nontriviality assumption, and `RCLike` covers both real and complex scalars.
The annihilator and preannihilator are already bundled linear subspaces in
the upstream specification, so the closedness clauses make them closed linear
subspaces. The quotient is the original algebraic quotient, with the shared
distance norm, and the displayed formula fixes its isometry as pullback. -/

namespace ExpandedFA.P1.C04DualMaps.Spec

universe u v

/-- The annihilator is a norm-closed linear subspace of the continuous dual. -/
def AnnihilatorClosed : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    IsClosed (C04Annihilators.Spec.AnnihilatorValue 𝕜 E A : Set (E →L[𝕜] 𝕜))

/-- The preannihilator is a norm-closed linear subspace of the original space. -/
def PreannihilatorClosed : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (B : Set (E →L[𝕜] 𝕜)),
    IsClosed (C04Annihilators.Spec.PreannihilatorValue 𝕜 E B : Set E)

/-- Passing to the norm-closed scalar-linear span does not change A^⊥. -/
def AnnihilatorClosedSpan : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    C04Annihilators.Spec.AnnihilatorValue 𝕜 E
        ((Submodule.span 𝕜 A).topologicalClosure : Set E) =
      C04Annihilators.Spec.AnnihilatorValue 𝕜 E A

/-- The span and its closure here are in the continuous dual with its operator norm. -/
def PreannihilatorClosedSpan : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (B : Set (E →L[𝕜] 𝕜)),
    C04Annihilators.Spec.PreannihilatorValue 𝕜 E
        ((Submodule.span 𝕜 B).topologicalClosure : Set (E →L[𝕜] 𝕜)) =
      C04Annihilators.Spec.PreannihilatorValue 𝕜 E B

/-- Inclusion reversal for arbitrary subsets of the original space. -/
def AnnihilatorAntitone : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A₁ A₂ : Set E),
    A₁ ⊆ A₂ →
      C04Annihilators.Spec.AnnihilatorValue 𝕜 E A₂ ≤
        C04Annihilators.Spec.AnnihilatorValue 𝕜 E A₁

/-- Inclusion reversal for arbitrary subsets of the continuous dual. -/
def PreannihilatorAntitone : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (B₁ B₂ : Set (E →L[𝕜] 𝕜)),
    B₁ ⊆ B₂ →
      C04Annihilators.Spec.PreannihilatorValue 𝕜 E B₂ ≤
        C04Annihilators.Spec.PreannihilatorValue 𝕜 E B₁

end ExpandedFA.P1.C04DualMaps.Spec

namespace ExpandedFA.P1.C04DualMaps.Spec

universe u v w z

/-- Restriction is a bounded linear map between the actual normed dual spaces. -/
def DualRestrictionType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    (E →L[𝕜] 𝕜) →L[𝕜] (M →L[𝕜] 𝕜)

/-- Composition with the subspace inclusion, hence exactly f ↦ f|M. -/
noncomputable def DualRestrictionValue : DualRestrictionType :=
  fun 𝕜 E _ _ _ M => (ContinuousLinearMap.compL 𝕜 M E 𝕜).flip M.subtypeL

def DualRestrictionEvaluation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (f : E →L[𝕜] 𝕜) (x : M),
    DualRestrictionValue 𝕜 E M f x = f (x : E)

def DualRestrictionNormBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    ‖DualRestrictionValue 𝕜 E M‖ ≤ 1

def DualRestrictionContraction : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (f : E →L[𝕜] 𝕜),
    ‖DualRestrictionValue 𝕜 E M f‖ ≤ ‖f‖

/-- The upstream transpose is already a bounded 𝕜-linear map; this records
the quantitative bound on its operator norm. -/
def BanachTransposeNormBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ‖C04Annihilators.Spec.BanachTransposeValue 𝕜 E F T‖ ≤ ‖T‖

/-- Transposition reverses the order of any composable pair. -/
def BanachTransposeComposition : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F),
    C04Annihilators.Spec.BanachTransposeValue 𝕜 E G (S.comp T) =
      (C04Annihilators.Spec.BanachTransposeValue 𝕜 E F T).comp
        (C04Annihilators.Spec.BanachTransposeValue 𝕜 F G S)

end ExpandedFA.P1.C04DualMaps.Spec

namespace ExpandedFA.P1.C04DualMaps.Spec

universe u v

/-- Pullback along the quotient map is a scalar-linear isometric bijection
onto exactly the continuous functionals that vanish on the submodule. The
formula fixes the bijection, including its complex scalar convention. -/
def QuotientDualIsometry : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 E M hM
    ∃ e : ((E ⧸ M) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜]
        C04Annihilators.Spec.AnnihilatorValue 𝕜 E (M : Set E),
      ∀ (f : (E ⧸ M) →L[𝕜] 𝕜) (x : E),
        (e f).val x = f (M.mkQ x)

/-- Every annihilating functional descends uniquely through the quotient,
with exactly the same operator norm. Uniqueness is among all continuous
linear maps satisfying the factorization formula, without assuming a norm. -/
def NormPreservingFactorization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 E M hM
    ∀ f : C04Annihilators.Spec.AnnihilatorValue 𝕜 E (M : Set E),
    ∃ U : (E ⧸ M) →L[𝕜] 𝕜,
      (∀ x : E, U (M.mkQ x) = f.val x) ∧
      ‖U‖ = ‖f‖ ∧
      ∀ V : (E ⧸ M) →L[𝕜] 𝕜,
        (∀ x : E, V (M.mkQ x) = f.val x) → V = U

end ExpandedFA.P1.C04DualMaps.Spec
