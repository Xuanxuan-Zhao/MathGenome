import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.DualSystems
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RieszSchauder

/-! Fredholm alternative in nondegenerate dual systems, paper.tex:10529–10540.
The algebraic bilinear pairing has no continuity assumption. Compactness means
compact closure of the unit-ball image in the original, possibly incomplete,
normed space. The sesquilinear convention is conjugate-linear in X. -/
namespace ExpandedFA.Fredholm.DualFredholmSpec

universe u v
open DualSystemsSpec

/-- Full conclusion for the two original operators and pairing. -/
def Conclusion {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (C : Y → X → ℂ) (K : X →ₗ[ℂ] X) (L : Y →ₗ[ℂ] Y) : Prop :=
  let A : X →ₗ[ℂ] X := LinearMap.id - K
  let B : Y →ₗ[ℂ] Y := LinearMap.id - L
  FiniteDimensional ℂ A.ker ∧ FiniteDimensional ℂ B.ker ∧
  Module.finrank ℂ A.ker = Module.finrank ℂ B.ker ∧
  ((Function.Bijective A ∧ Function.Bijective B) ∨
    (0 < Module.finrank ℂ A.ker ∧ 0 < Module.finrank ℂ B.ker)) ∧
  (∀ f : X, f ∈ A.range ↔ ∀ y : Y, y ∈ B.ker → C y f = 0) ∧
  (∀ g : Y, g ∈ B.range ↔ ∀ x : X, x ∈ A.ker → C g x = 0)

def BilinearFredholm : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (D : DualSystemData X Y) (K : X →ₗ[ℂ] X) (L : Y →ₗ[ℂ] Y),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue L →
    (∀ x y, D.pairing y (K x) = D.pairing (L y) x) →
    Conclusion (fun y x => D.pairing y x) K L

/-- On the first variable, use the conjugated action a •conj x = star a • x.
The conclusion is stated on the original spaces, including original kernel
complex dimensions, not just on their type copies. -/
def SesquilinearFredholm : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (S : SesquilinearSystemData X Y) (K : X →ₗ[ℂ] X) (L : Y →ₗ[ℂ] Y),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue L →
    (∀ x y, S.pairing y (K x) = S.pairing (L y) x) →
    Conclusion (fun y x => S.pairing y x) K L

end ExpandedFA.Fredholm.DualFredholmSpec
