import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.LinearAlgebra.Basis.Defs
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.ClassSumIntegrality

noncomputable section

open scoped MonoidAlgebra
open P103.Ch08.ClassSumIntegrality (classSum)

namespace RepTheorySurvey.Modular.GroupAlgebraCenter

universe u v w

variable {G : Type u} [Group G]

/-- Read one coefficient for each conjugacy class. For central elements the choice
of representative will be immaterial. -/
def classCoefficients (R : Type v) [CommRing R] :
    Subalgebra.center R R[G] →ₗ[R] (ConjClasses G → R) where
  toFun z C := z.val.coeff (Quotient.out C)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Form the linear combination of the canonical class sums with the given weights. -/
def classSumCombination {R : Type v} [CommRing R] [Fintype G]
    (f : ConjClasses G → R) : R[G] :=
  letI := Fintype.ofFinite (ConjClasses G)
  ∑ C, f C • classSum R C

namespace Specs

def memCenterIffType : Prop :=
  ∀ {G : Type u} [Group G] {R : Type v} [CommRing R] (z : R[G]),
    z ∈ Subalgebra.center R R[G] ↔
      ∀ x y : G, ConjClasses.mk x = ConjClasses.mk y → z.coeff x = z.coeff y

def classSumMemCenterType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (R : Type v) [CommRing R] (C : ConjClasses G),
    classSum R C ∈ Subalgebra.center R R[G]

def centerClassEquivType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (R : Type v) [CommRing R],
    ∃ e : Subalgebra.center R R[G] ≃ₗ[R] (ConjClasses G → R),
      (∀ (z : Subalgebra.center R R[G]) (g : G), e z (ConjClasses.mk g) = z.val.coeff g) ∧
      (∀ f : ConjClasses G → R, (e.symm f).val = classSumCombination f)

def classSumBasisType : Prop :=
  ∀ {G : Type u} [Group G] [Fintype G] (R : Type v) [CommRing R],
    ∃ b : Module.Basis (ConjClasses G) R (Subalgebra.center R R[G]),
      ∀ C, (b C).val = classSum R C

def mapCenterType : Prop :=
  ∀ {G : Type u} [Group G] {R : Type v} [CommRing R] {S : Type w} [CommRing S]
    (φ : R →+* S),
    ∃ φZ : Subalgebra.center R R[G] →+* Subalgebra.center S S[G],
      (∀ z, (φZ z).val = MonoidAlgebra.mapRingHom G φ z.val) ∧
      (∀ (z : Subalgebra.center R R[G]) (C : ConjClasses G),
        classCoefficients S (φZ z) C = φ (classCoefficients R z C))

end Specs
end RepTheorySurvey.Modular.GroupAlgebraCenter
