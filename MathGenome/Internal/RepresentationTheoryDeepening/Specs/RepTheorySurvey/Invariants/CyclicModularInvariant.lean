import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs

namespace RepTheorySurvey.Invariants.Specs.CyclicModularInvariant

open Polynomial
universe u

noncomputable section

/-- The two-variable polynomial ring, written as polynomials in `y` over `k[x]`. -/
abbrev Bivariate (k : Type*) [Field k] := Polynomial (Polynomial k)

abbrev x (k : Type*) [Field k] : Bivariate k := C X

abbrev y (k : Type*) [Field k] : Bivariate k := X

/-- The standard generator of the additive cyclic group, viewed multiplicatively. -/
abbrev generator (p : ℕ) : Multiplicative (ZMod p) := Multiplicative.ofAdd 1

abbrev parameter (k : Type*) [Field k] (p : ℕ) [CharP k p]
    (g : Multiplicative (ZMod p)) : Polynomial k :=
  C (ZMod.castHom (dvd_refl p) k g.toAdd) * X

def ActionType := ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
  GroupAlgebraAction k (Multiplicative (ZMod p)) (Bivariate k)

/-- The group element represented by `a` translates `y` by `a * x`. -/
def action (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p] :
    GroupAlgebraAction k (Multiplicative (ZMod p)) (Bivariate k) where
  toFun g := (taylorEquiv (parameter k p g)).restrictScalars k
  map_one' := by
    apply AlgEquiv.ext
    intro f
    change taylor (parameter k p 1) f = f
    simp [parameter]
  map_mul' g h := by
    apply AlgEquiv.ext
    intro f
    change taylor (parameter k p (g * h)) f =
      taylor (parameter k p g) (taylor (parameter k p h) f)
    rw [taylor_taylor]
    have hadd : parameter k p (g * h) = parameter k p g + parameter k p h := by
      simp only [parameter, show (g * h).toAdd = g.toAdd + h.toAdd from rfl,
        map_add, add_mul]
    rw [hadd]

def NormType := ∀ (k : Type u) [Field k], ℕ → Bivariate k

/-- The polynomial `y ^ p - x ^ (p - 1) * y`. -/
def norm (k : Type u) [Field k] (p : ℕ) : Bivariate k :=
  y k ^ p - x k ^ (p - 1) * y k

def generated (k : Type u) [Field k] (p : ℕ) : Subalgebra k (Bivariate k) :=
  Algebra.adjoin k {x k, norm k p}

def GeneratorCoordinates : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    action k p (generator p) (x k) = x k ∧
    action k p (generator p) (y k) = y k + x k

def GroupCardinality : Prop :=
  ∀ (p : ℕ) [NeZero p], Fintype.card (Multiplicative (ZMod p)) = p

def GeneratorOrder : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    orderOf (action k p (generator p)) = p

def NormFixed : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    norm k p ∈ groupFixedSubalgebra (action k p)

def FixedSubalgebra : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    groupFixedSubalgebra (action k p) = generated k p

def AlgebraicIndependence : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    AlgebraicIndependent k ![x k, norm k p]

def PowersBasis : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    ∃ b : Module.Basis (Fin p) (generated k p) (Bivariate k),
      ∀ i, b i = y k ^ (i : ℕ)

def NoEquivariantRetraction : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    ¬ ∃ P : Bivariate k →ₗ[k] groupFixedSubalgebra (action k p),
      (groupRepresentation (action k p)).IsIntertwiningMap
        (Representation.trivial k (Multiplicative (ZMod p))
          (groupFixedSubalgebra (action k p))) P ∧
      ∀ a : groupFixedSubalgebra (action k p), P (a : Bivariate k) = a

def NoReynoldsOperator : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p],
    ¬ ∃ P : Bivariate k →ₗ[k] groupFixedSubalgebra (action k p),
      groupIsReynolds (action k p) P

end

end RepTheorySurvey.Invariants.Specs.CyclicModularInvariant
