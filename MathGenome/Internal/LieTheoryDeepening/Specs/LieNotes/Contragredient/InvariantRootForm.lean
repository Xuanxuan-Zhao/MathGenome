import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.ReflectionAutomorphisms
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Complex.Module

/-! The symmetric form of a symmetrizable Cartan matrix in real simple-root coordinates. -/

namespace Specs.LieNotes.Contragredient.InvariantRootForm

open CartanData ReflectionAutomorphisms

noncomputable section

set_option linter.checkUnivs false

universe u v

variable {I : Type u} {A : Matrix I I ℤ}
variable {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]

def RealRootSpanType := Type u → Type u

/-- Real simple-root coordinates for the real span of the root lattice. -/
abbrev RealRootSpan (I : Type u) := I →₀ ℝ

def SymmetrizingFamilyType := ∀ {I : Type u}, Matrix I I ℤ → (I → ℝ) → Prop

def SymmetrizingFamily (A : Matrix I I ℤ) (d : I → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ (∀ i j, d i * (A i j : ℝ) = d j * (A j i : ℝ))

def SimpleRootType := ∀ {I : Type u}, I → RealRootSpan I

def simpleRoot (i : I) : RealRootSpan I := Finsupp.single i 1

def LatticeToRealType := ∀ {I : Type u}, Q I →+ RealRootSpan I

def latticeToReal : Q I →+ RealRootSpan I :=
  Finsupp.mapRange.addMonoidHom (Int.castAddHom ℝ)

def RealRootWeightType :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I],
    Realization A H → (RealRootSpan I →ₗ[ℝ] Module.Dual ℂ H)

/-- The real linear combination of the simple roots in the original Cartan dual. -/
def realRootWeight (R : Realization A H) : RealRootSpan I →ₗ[ℝ] Module.Dual ℂ H :=
  Finsupp.linearCombination ℝ R.α

def RealCorootPairingType :=
  ∀ {I : Type u}, Matrix I I ℤ → I → (RealRootSpan I →ₗ[ℝ] ℝ)

/-- Evaluation at the original coroot, in real coordinates. -/
def realCorootPairing (A : Matrix I I ℤ) (i : I) : RealRootSpan I →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun j ↦ (A i j : ℝ)

def RealRootReflectionType :=
  ∀ {I : Type u}, Matrix I I ℤ → I → (RealRootSpan I →ₗ[ℝ] RealRootSpan I)

def realRootReflection (A : Matrix I I ℤ) (i : I) : RealRootSpan I →ₗ[ℝ] RealRootSpan I :=
  LinearMap.id - (realCorootPairing A i).smulRight (simpleRoot i)

def RootFormType :=
  ∀ {I : Type u}, Matrix I I ℤ → (I → ℝ) → LinearMap.BilinForm ℝ (RealRootSpan I)

/-- The bilinear extension of the matrix scaled by the symmetrizing diagonal. -/
def rootForm (A : Matrix I I ℤ) (d : I → ℝ) : LinearMap.BilinForm ℝ (RealRootSpan I) :=
  Finsupp.linearCombination ℝ fun i ↦ d i • realCorootPairing A i

/-- The coordinate realization identifies the integral and real reflection actions. -/
def RealRootSpanIdentification : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H] [Finite I]
    (R : Realization A H),
    Function.Injective (realRootWeight R) ∧
    (realRootWeight R).range = Submodule.span ℝ (Set.range R.rootWeight) ∧
    (∀ i : I, latticeToReal (simpleDegree i) = simpleRoot i) ∧
    (∀ q, realRootWeight R (latticeToReal q) = R.rootWeight q) ∧
    (∀ i x, realRootWeight R x (R.h i) = (realCorootPairing A i x : ℂ)) ∧
    (∀ i q, realRootReflection A i (latticeToReal q) = latticeToReal (rootReflection A i q)) ∧
    (∀ i x, realRootWeight R (realRootReflection A i x) = R.weightReflection i (realRootWeight R x)) ∧
    (∀ j (w : List I),
      realRootWeight R (latticeToReal (w.foldr (fun i q ↦ rootReflection A i q) (simpleDegree j))) =
        w.foldr (fun i β ↦ R.weightReflection i β) (R.α j))

/-- The form is allowed to be degenerate and of arbitrary signature. -/
def InvariantFormAndLengths : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} [Finite I], IsGeneralizedCartanMatrix A →
    ∀ d : I → ℝ, SymmetrizingFamily A d →
      (rootForm A d).IsSymm ∧
      (∀ i j, rootForm A d (simpleRoot i) (simpleRoot j) = d i * (A i j : ℝ)) ∧
      (∀ i x, realCorootPairing A i x = rootForm A d (simpleRoot i) x / d i) ∧
      (∀ i, rootForm A d (simpleRoot i) (simpleRoot i) = 2 * d i) ∧
      (∀ i x y, rootForm A d (realRootReflection A i x) (realRootReflection A i y) =
        rootForm A d x y) ∧
      (∀ j (w : List I),
        let β := latticeToReal (w.foldr (fun i q ↦ rootReflection A i q) (simpleDegree j))
        rootForm A d β β = 2 * d j)

/-- The reflection automorphisms and real-root conclusions in the contragredient quotient. -/
def ReflectionAutomorphismsAndRealRoots : Prop :=
  ReflectionAutomorphismExistsUnique.{u, v} ∧ CartanReflectionInvolutive.{u, v} ∧
    ReflectionAutomorphismOnCartan.{u, v} ∧ ReflectionAutomorphismOnWeightSpaces.{u, v} ∧
    RootLatticePreserved.{u, v} ∧ RealRootMultiplicity.{u, v} ∧
    RealRootSpanIdentification.{u, v} ∧ InvariantFormAndLengths.{u}

end

end Specs.LieNotes.Contragredient.InvariantRootForm
