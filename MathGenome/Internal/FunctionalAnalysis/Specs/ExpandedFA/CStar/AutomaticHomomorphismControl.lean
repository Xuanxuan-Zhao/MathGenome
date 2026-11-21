import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Quotient

/-! Independent statements for `fa2:p2:cstar-quotient` (paper.tex 12283–12325).
Homomorphisms here are algebraic complex-linear star homomorphisms. They need
neither preserve a unit nor carry a continuity or closed-range certificate.
All algebras and ideals, including the zero algebra and improper ideal, are allowed. -/
noncomputable section
namespace ExpandedFA.CStar.AutomaticHomomorphismControl.Spec
universe u v

/-- The ideal and quotient assertions of the proposition. -/
def ClosedIdeals : Prop :=
  IdealApproximateIdentities.Spec.StarInvariant.{u} ∧
  IdealApproximateIdentities.Spec.ApproximateIdentity.{u} ∧
  Quotient.Spec.QuotientCStar.{u}

def Contractive : Prop := ∀ (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (a : A), ‖f a‖ ≤ ‖a‖

def InjectiveIsometry : Prop := ∀ (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B), Function.Injective f → Isometry f

/-- Factor through the closed kernel and the original algebraic quotient,
retaining its distance norm, metric, vector space, product and involution.
The induced injection is isometric and has precisely the original range. -/
def KernelFactorization : Prop := ∀ (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B),
    ∃ I : Quotient.Spec.ClosedTwoSidedIdeal A,
      (∀ a : A, a ∈ I ↔ f a = 0) ∧
      (letI := P1.C02QuotientNorm.Spec.quotientNormedGroupValue ℂ A I.toSubmodule I.isClosed
       ∃ C : NonUnitalCStarAlgebra (A ⧸ I.toSubmodule),
         C.toNorm = (inferInstance : Norm (A ⧸ I.toSubmodule)) ∧
         C.toMetricSpace = (inferInstance : MetricSpace (A ⧸ I.toSubmodule)) ∧
         C.toAddCommGroup = (inferInstance : AddCommGroup (A ⧸ I.toSubmodule)) ∧
         C.toSMul = (inferInstance : SMul ℂ (A ⧸ I.toSubmodule)) ∧
         (letI := C
          (∀ a b : A, I.toSubmodule.mkQ (a * b) =
            I.toSubmodule.mkQ a * I.toSubmodule.mkQ b) ∧
          (∀ a : A, I.toSubmodule.mkQ (star a) = star (I.toSubmodule.mkQ a)) ∧
          ∃ g : @NonUnitalStarAlgHom ℂ (A ⧸ I.toSubmodule) B inferInstance
            C.toNonUnitalNonAssocSemiring C.toDistribMulAction C.toStar
            inferInstance inferInstance inferInstance,
            (∀ a : A, g (I.toSubmodule.mkQ a) = f a) ∧
            Function.Injective g ∧ Isometry g ∧ Set.range g = Set.range f))

def ClosedRange : Prop := ∀ (A : Type u) (B : Type v)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B), IsClosed (Set.range f)

end ExpandedFA.CStar.AutomaticHomomorphismControl.Spec
