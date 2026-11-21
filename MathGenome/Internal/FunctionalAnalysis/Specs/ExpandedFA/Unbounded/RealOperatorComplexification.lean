import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification

/-! Exact-domain complexification on the existing Hilbert pair model.
No density or closedness is imposed on the construction. -/
noncomputable section
namespace ExpandedFA.Unbounded.RealOperatorComplexification
open TraceIdeals.RealComplexification
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification (complexPair csmul ip)
universe u v
namespace Spec
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Both coordinates must belong to the original domain. -/
def complexDomain (A : Operator ℝ H K) : Submodule ℂ (Space H) where
  carrier := {p | p.1 ∈ A.domain ∧ p.2 ∈ A.domain}
  zero_mem' := ⟨A.domain.zero_mem, A.domain.zero_mem⟩
  add_mem' hp hq := ⟨A.domain.add_mem hp.1 hq.1, A.domain.add_mem hp.2 hq.2⟩
  smul_mem' a p hp := by
    rw [csmul]
    exact ⟨A.domain.sub_mem (A.domain.smul_mem a.re hp.1) (A.domain.smul_mem a.im hp.2),
      A.domain.add_mem (A.domain.smul_mem a.im hp.1) (A.domain.smul_mem a.re hp.2)⟩

/-- The canonical complex-linear extension, retaining its full domain. -/
def complexifyValue (A : Operator ℝ H K) : Operator ℂ (Space H) (Space K) where
  domain := complexDomain A
  toFun :=
    { toFun := fun p => complexPair K (A ⟨p.1.1, p.2.1⟩) (A ⟨p.1.2, p.2.2⟩)
      map_add' := by
        intro p q
        exact congrArg₂ (complexPair K)
          (A.map_add (⟨p.1.1, p.2.1⟩ : A.domain) ⟨q.1.1, q.2.1⟩)
          (A.map_add (⟨p.1.2, p.2.2⟩ : A.domain) ⟨q.1.2, q.2.2⟩)
      map_smul' := by
        intro a p
        have h₁ : (⟨(a • p).1.1, (a • p).2.1⟩ : A.domain) =
            a.re • (⟨p.1.1, p.2.1⟩ : A.domain) - a.im • ⟨p.1.2, p.2.2⟩ :=
          Subtype.ext (congrArg Prod.fst (csmul H a p.1))
        have h₂ : (⟨(a • p).1.2, (a • p).2.2⟩ : A.domain) =
            a.im • (⟨p.1.1, p.2.1⟩ : A.domain) + a.re • ⟨p.1.2, p.2.2⟩ :=
          Subtype.ext (congrArg Prod.snd (csmul H a p.1))
        change complexPair K (A _) (A _) = a • complexPair K (A _) (A _)
        rw [h₁, h₂, csmul]
        exact congrArg₂ (complexPair K)
          ((A.map_sub _ _).trans (congrArg₂ (· - ·) (A.map_smul _ _) (A.map_smul _ _)))
          ((A.map_add _ _).trans (congrArg₂ (· + ·) (A.map_smul _ _) (A.map_smul _ _))) }


/-- The public constructor has no density or closedness hypotheses. -/
def ComplexifyType := ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K],
  Operator ℝ H K → Operator ℂ (Space H) (Space K)

def DomainCoordinates : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K) (p : Space H),
  p ∈ (complexifyValue A).domain ↔ p.1 ∈ A.domain ∧ p.2 ∈ A.domain

def DomainDecomposition : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K) (p : Space H),
  p ∈ (complexifyValue A).domain ↔ ∃ x y : A.domain,
    p = TraceIdeals.RealComplexification.Spec.inclusion (x : H) + Complex.I • TraceIdeals.RealComplexification.Spec.inclusion (y : H)

def Evaluation : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K) (p : (complexifyValue A).domain),
  complexifyValue A p = complexPair K (A ⟨p.1.1, p.2.1⟩) (A ⟨p.1.2, p.2.2⟩)

def Graph : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K) (p : Space H) (q : Space K),
  (p, q) ∈ (complexifyValue A).graph ↔
    (p.1, q.1) ∈ A.graph ∧ (p.2, q.2) ∈ A.graph

def Density : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K),
  Dense ((complexifyValue A).domain : Set (Space H)) ↔ Dense (A.domain : Set H)

def Closed : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K), (complexifyValue A).IsClosed ↔ A.IsClosed

def ConjugationDomain : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K) (p : Space H),
  TraceIdeals.RealComplexification.Spec.conjugation p ∈ (complexifyValue A).domain ↔ p ∈ (complexifyValue A).domain

def ConjugationEvaluation : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (A : Operator ℝ H K) (p : (complexifyValue A).domain),
  ∃ hp : TraceIdeals.RealComplexification.Spec.conjugation p.1 ∈ (complexifyValue A).domain,
    complexifyValue A ⟨TraceIdeals.RealComplexification.Spec.conjugation p.1, hp⟩ =
      TraceIdeals.RealComplexification.Spec.conjugation (complexifyValue A p)

def Bounded : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  (T : H →L[ℝ] K), complexifyValue (T.toLinearMap.toPMap ⊤) =
    (TraceIdeals.RealComplexification.Spec.operator T).toLinearMap.toPMap ⊤

def ResolventEquivalence : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (A : Operator ℝ H H) (r : ℝ),
  Nonempty (ResolventInverse A r) ↔
    Nonempty (ResolventInverse (complexifyValue A) (r : ℂ))

def ResolventInverseIdentification : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (A : Operator ℝ H H) (r : ℝ) (R : ResolventInverse A r)
  (S : ResolventInverse (complexifyValue A) (r : ℂ)),
  S.inverse = TraceIdeals.RealComplexification.Spec.operator R.inverse

/-- Equality of the canonical resolvents, on the intrinsic real resolvent set. -/
def ResolventValue : Prop := ∀ {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (A : Operator ℝ H H) (r : ℝ), Nonempty (ResolventInverse A r) →
  OperatorDomainsSpec.resolventValue (r : ℂ) (complexifyValue A) =
    TraceIdeals.RealComplexification.Spec.operator (OperatorDomainsSpec.resolventValue r A)

local instance [CompleteSpace H] : CompleteSpace (Space H) :=
  TraceIdeals.RealComplexification.Spec.completeSpace
local instance [CompleteSpace K] : CompleteSpace (Space K) :=
  TraceIdeals.RealComplexification.Spec.completeSpace

def Adjoint : Prop :=
  ∀ {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [CompleteSpace H] [CompleteSpace K] (A : Operator ℝ H K),
  Dense (A.domain : Set H) →
    HilbertAdjointSpec.adjointValue (complexifyValue A) =
      complexifyValue (HilbertAdjointSpec.adjointValue A)

def SelfAdjoint : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (A : Operator ℝ H H), Dense (A.domain : Set H) →
  (HilbertAdjointSpec.adjointValue (complexifyValue A) = complexifyValue A ↔
    HilbertAdjointSpec.adjointValue A = A)

end Spec
end ExpandedFA.Unbounded.RealOperatorComplexification
