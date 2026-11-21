import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.Normed.Operator.Extend

/-! Independent scalar-linear Banach-adjoint interface for
`paper.tex`, fa2:p3:banach-closed-range. The graph construction below is
canonical; the candidate must prove that its domain is exactly the ambient
norm boundedness domain, that it gives the unique continuous extension, and
that its graph is closed. No conjugation occurs in either pairing.

The assertions hold even without completeness or closedness of the original
operator, so in particular apply to the closed Banach-space operators in the
source. Density remains an explicit hypothesis in every adjoint law. -/

noncomputable section
namespace ExpandedFA.Unbounded.BanachAdjointSpec

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- The boundedness here uses the inherited X norm, not the graph norm. -/
abbrev DomainType := Operator 𝕜 X Y → Submodule 𝕜 (Y →L[𝕜] 𝕜)

def domainValue : DomainType (𝕜 := 𝕜) (X := X) (Y := Y) := fun A =>
  { carrier := {q | ∃ C : ℝ, ∀ x : A.domain, ‖q (A x)‖ ≤ C * ‖(x : X)‖}
    zero_mem' := ⟨0, by simp⟩
    add_mem' := by
      rintro q r ⟨C, hC⟩ ⟨D, hD⟩
      refine ⟨C + D, fun x => ?_⟩
      calc
        ‖(q + r) (A x)‖ ≤ ‖q (A x)‖ + ‖r (A x)‖ := norm_add_le _ _
        _ ≤ C * ‖(x : X)‖ + D * ‖(x : X)‖ := add_le_add (hC x) (hD x)
        _ = (C + D) * ‖(x : X)‖ := (add_mul _ _ _).symm
    smul_mem' := by
      rintro c q ⟨C, hC⟩
      refine ⟨‖c‖ * C, fun x => ?_⟩
      calc
        ‖(c • q) (A x)‖ = ‖c‖ * ‖q (A x)‖ := by rw [smul_apply, norm_smul]
        _ ≤ ‖c‖ * (C * ‖(x : X)‖) := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = (‖c‖ * C) * ‖(x : X)‖ := (mul_assoc _ _ _).symm }

/-- The continuous extension relation, ordered as (y', x'). -/
def extensionRelation (A : Operator 𝕜 X Y) :
    Submodule 𝕜 ((Y →L[𝕜] 𝕜) × (X →L[𝕜] 𝕜)) where
  carrier := {p | ∀ x : A.domain, p.2 (x : X) = p.1 (A x)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq x
    change p.2 (x : X) + q.2 (x : X) = p.1 (A x) + q.1 (A x)
    rw [hp x, hq x]
  smul_mem' := by
    intro c p hp x
    change c • p.2 (x : X) = c • p.1 (A x)
    rw [hp x]

abbrev AdjointType := Operator 𝕜 X Y → Operator 𝕜 (Y →L[𝕜] 𝕜) (X →L[𝕜] 𝕜)

/-- On a dense domain the relation is a graph; that fact is a proof target.
No claim is made for the library's fallback value on nondense domains. -/
def adjointValue : AdjointType (𝕜 := 𝕜) (X := X) (Y := Y) :=
  fun A => (extensionRelation A).toLinearPMap

def DomainLaw : Prop :=
  ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) →
    (adjointValue A).domain = domainValue A

def ExtensionLaw : Prop :=
  ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) →
    ∀ (q : (adjointValue A).domain) (x : A.domain),
      adjointValue A q (x : X) = (q : Y →L[𝕜] 𝕜) (A x)

def UniqueExtensionLaw : Prop :=
  ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) →
    ∀ (q : (adjointValue A).domain) (f : X →L[𝕜] 𝕜),
      (∀ x : A.domain, f (x : X) = (q : Y →L[𝕜] 𝕜) (A x)) →
        f = adjointValue A q

def ClosedLaw : Prop :=
  ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) →
    (adjointValue A).IsClosed

/-- Norm closure of the actual range, with the preannihilator of ker A'. -/
def RangeClosureLaw : Prop :=
  ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) →
    _root_.closure (A.toFun.range : Set Y) =
      {y | ∀ q : Y →L[𝕜] 𝕜, q ∈ (adjointValue A).ker → q y = 0}

/-- The annihilator is in X' × Y', under the scalar-linear sum pairing. -/
def GraphAnnihilatorLaw : Prop :=
  ∀ (A : Operator 𝕜 X Y), Dense (A.domain : Set X) →
    {p : (X →L[𝕜] 𝕜) × (Y →L[𝕜] 𝕜) |
      ∀ z : X × Y, z ∈ A.graph → p.1 z.1 + p.2 z.2 = 0} =
    {p | ∃ q : (adjointValue A).domain,
      p = (-adjointValue A q, (q : Y →L[𝕜] 𝕜))}

end ExpandedFA.Unbounded.BanachAdjointSpec

/-! Closed specifications, quantifying over the ambient spaces as well as A. -/
namespace ExpandedFA.Unbounded.BanachAdjointSpec.Expected

def DomainType :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.DomainType (𝕜 := 𝕜) (X := X) (Y := Y)

def AdjointType :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.AdjointType (𝕜 := 𝕜) (X := X) (Y := Y)

noncomputable def domainValue : DomainType := @BanachAdjointSpec.domainValue

noncomputable def adjointValue : AdjointType := @BanachAdjointSpec.adjointValue

def DomainLaw : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.DomainLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def ExtensionLaw : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.ExtensionLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def UniqueExtensionLaw : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.UniqueExtensionLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def ClosedLaw : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.ClosedLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def RangeClosureLaw : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.RangeClosureLaw (𝕜 := 𝕜) (X := X) (Y := Y)

def GraphAnnihilatorLaw : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
    BanachAdjointSpec.GraphAnnihilatorLaw (𝕜 := 𝕜) (X := X) (Y := Y)

end ExpandedFA.Unbounded.BanachAdjointSpec.Expected
