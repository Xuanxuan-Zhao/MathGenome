import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ComoduleFiniteness
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic

open scoped TensorProduct

namespace LinearAlgebraicGroups.RegularTorusCohomology

noncomputable section

variable {R M W : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]

/-- Right coactions of the split character Hopf algebra over an arbitrary base ring. -/
structure TorusComodule (R M W : Type*) [CommRing R] [CommGroup M]
    [AddCommGroup W] [Module R W] where
  coaction : W →ₗ[R] W ⊗[R] MonoidAlgebra R M
  coassoc (w : W) :
    TensorProduct.assoc R W (MonoidAlgebra R M) (MonoidAlgebra R M)
        (coaction.rTensor _ (coaction w)) =
      (Coalgebra.comul (R := R) (A := MonoidAlgebra R M)).lTensor W (coaction w)
  counit (w : W) :
    TensorProduct.rid R W ((Coalgebra.counit (R := R)).lTensor W (coaction w)) = w

/-- The field-valued upstream coaction is an instance of the same construction. -/
def TorusComodule.ofField {k : Type*} [Field k]
    [Module k W] (ρ : RightComodule k (MonoidAlgebra k M) W) :
    TorusComodule k M W :=
  ⟨ρ.coaction, ρ.coassoc, ρ.counit⟩

/-- Coefficients against the canonical character basis, for any coefficient module. -/
def tensorCoefficients (R D W : Type*) [CommRing R] [CommMonoid D]
    [AddCommGroup W] [Module R W] :
    (W ⊗[R] MonoidAlgebra R D) ≃ₗ[R] (D →₀ W) := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight (MonoidAlgebra.basis D R)

def coactionCoefficients (ρ : TorusComodule R M W) : W →ₗ[R] (M →₀ W) :=
  (tensorCoefficients R M W).toLinearMap.comp ρ.coaction

universe u

/-- Iterated tensor power of the coordinate module, with the first factor exposed. -/
def coordinatePower (R M : Type u) [CommRing R] [CommGroup M] : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | n + 1 => ModuleCat.of R (MonoidAlgebra R M ⊗[R] coordinatePower R M n)

/-- A regular polynomial on n torus variables in the product character basis. -/
abbrev Regular (M W : Type*) [Zero W] (n : ℕ) := (Fin n → M) →₀ W

/-- The zero-character coefficient functional. -/
def constantCoefficient (R M : Type*) [CommRing R] [CommGroup M] :
    MonoidAlgebra R M →ₗ[R] R :=
  (Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- The tensor basis whose indices record the character of every variable. -/
def coordinateBasis (R M : Type u) [CommRing R] [CommGroup M] :
    (n : ℕ) → Module.Basis (Fin n → M) R (coordinatePower R M n)
  | 0 => Module.Basis.singleton (Fin 0 → M) R
  | n + 1 =>
    ((MonoidAlgebra.basis M R).tensorProduct (coordinateBasis R M n)).reindex
      (Fin.consEquiv (fun _ => M))

/-- The first tensor factor of the coordinates is integrated by the zero-character
functional, leaving the coefficient module and all the other variables in place. -/
def averageFirstTensor {R M : Type u} [CommRing R] [CommGroup M]
    {W : Type*} [AddCommGroup W] [Module R W] (n : ℕ) :
    (W ⊗[R] coordinatePower R M (n + 1)) →ₗ[R] (W ⊗[R] coordinatePower R M n) :=
  ((TensorProduct.lid R (coordinatePower R M n)).toLinearMap.lTensor W).comp
    (((constantCoefficient R M).rTensor (coordinatePower R M n)).lTensor W)

/-- The tensor and coefficient models of module-valued regular polynomials. -/
def regularTensorEquiv (R M : Type u) [CommRing R] [CommGroup M]
    (W : Type*) [AddCommGroup W] [Module R W] (n : ℕ) :
    (W ⊗[R] coordinatePower R M n) ≃ₗ[R] Regular M W n := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight (coordinateBasis R M n)

/-- Translation by an algebra-valued point after scalar extension to the point's ring. -/
def translation {S : Type*} [CommRing S] (t : M →* Sˣ) :
    MonoidAlgebra S M →ₐ[S] MonoidAlgebra S M :=
  MonoidAlgebra.lift S (MonoidAlgebra S M) M
    (((algebraMap S (MonoidAlgebra S M)).toMonoidHom.comp (Units.coeHom S)).comp t *
      MonoidAlgebra.of S M)

/-- An omitted coordinate has trivial exponent. -/
def omitVariable (n : ℕ) (i : Fin (n + 1)) :
    Regular M W n →ₗ[R] Regular M W (n + 1) :=
  Finsupp.lmapDomain _ _ (@Fin.insertNth n (fun _ => M) i 1)

/-- Integrate the variable in position i against its zero-character coefficient. -/
def average (n : ℕ) (i : Fin (n + 1)) :
    Regular M W (n + 1) →ₗ[R] Regular M W n :=
  Finsupp.lcomapDomain (@Fin.insertNth n (fun _ => M) i 1) (@Fin.insertNth_right_injective n (fun _ => M) i 1)

/-- Pullback by simultaneous left translation, with the translating variable last. -/
def diagonalPull (n : ℕ) :
    Regular M W n →ₗ[R] ((Fin n → M) × M) →₀ W :=
  Finsupp.lmapDomain _ _ fun a => (a, ∏ i, a i)

/-- The action on the coefficients with the acting variable last. -/
def coefficientPull (ρ : TorusComodule R M W) (n : ℕ) :
    Regular M W n →ₗ[R] ((Fin n → M) × M) →₀ W :=
  Finsupp.lsum R fun a =>
    (Finsupp.lmapDomain _ _ (Prod.mk a)).comp (coactionCoefficients ρ)

/-- The identity of regular polynomials expressing homogeneous equivariance. -/
def Equivariant (ρ : TorusComodule R M W) {n : ℕ} (f : Regular M W n) : Prop :=
  diagonalPull (R := R) n f = coefficientPull ρ n f

/-- Alternating omission, indexed by the number of input variables. -/
def differential (n : ℕ) : Regular M W n →ₗ[R] Regular M W (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • omitVariable n i

/-- Substitute a torus point given by a map of characters into a variable group
with character group D. The resulting operation includes the action on W. -/
def actPolynomial {D : Type*} [CommGroup D] (ρ : TorusComodule R M W)
    (g : M →* D) : (D →₀ W) →ₗ[R] (D →₀ W) :=
  Finsupp.lsum R fun a =>
    (Finsupp.lmapDomain _ _ (fun m => a * g m)).comp (coactionCoefficients ρ)

/-- Evaluation of a regular polynomial after extension to a commutative R-algebra.
For a character group D, the function used for evaluation is the character
monoid homomorphism underlying a D-torus point. -/
def evaluatePolynomial {D S : Type*} [CommRing S] [Algebra R S] (t : D → S) :
    (D →₀ W) →ₗ[R] S ⊗[R] W :=
  Finsupp.lsum R fun a => TensorProduct.mk R S W (t a)

/-- The character homomorphism of a tuple of torus points. -/
def tupleCharacter {S : Type*} [CommRing S] {n : ℕ} (p : Fin n → M →* S) :
    (Fin n → M) →* S where
  toFun a := ∏ i, p i (a i)
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

/-- The action of an S-point, induced on the scalar-extended coefficient module
by the right coaction. A character homomorphism into S takes values in units. -/
def pointAction {S : Type*} [CommRing S] [Algebra R S]
    (ρ : TorusComodule R M W) (t : M →* S) : S ⊗[R] W →ₗ[S] S ⊗[R] W :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton S _
      ((evaluatePolynomial t).comp (coactionCoefficients ρ)))

/-- Inhomogeneous degree zero differential, t ↦ t · w - w. -/
def inhomogeneousZero (ρ : TorusComodule R M W) : W →ₗ[R] (M →₀ W) :=
  coactionCoefficients ρ - Finsupp.lsingle 1

/-- Inhomogeneous degree one differential, at (t,s). -/
def inhomogeneousOne (ρ : TorusComodule R M W) :
    (M →₀ W) →ₗ[R] ((M × M) →₀ W) :=
  (actPolynomial ρ (MonoidHom.inl M M)).comp (Finsupp.lmapDomain _ _ fun a => (1, a)) -
    Finsupp.lmapDomain _ _ (fun a => (a, a)) +
    Finsupp.lmapDomain _ _ (fun a => (a, 1))

/-- Inhomogeneous degree two differential, at (t,s,z). -/
def inhomogeneousTwo (ρ : TorusComodule R M W) :
    ((M × M) →₀ W) →ₗ[R] (((M × M) × M) →₀ W) :=
  (actPolynomial ρ ((MonoidHom.inl (M × M) M).comp (MonoidHom.inl M M))).comp
      (Finsupp.lmapDomain _ _ fun a => ((1, a.1), a.2)) -
    Finsupp.lmapDomain _ _ (fun a => ((a.1, a.1), a.2)) +
    Finsupp.lmapDomain _ _ (fun a => (a, a.2)) -
    Finsupp.lmapDomain _ _ (fun a => (a, 1))

/-- Integrate the last coordinate of a product of character groups. -/
def lastCoefficient {D : Type*} : ((D × M) →₀ W) →ₗ[R] (D →₀ W) :=
  Finsupp.lcomapDomain (fun d => (d, 1)) (fun _ _ h => congrArg Prod.fst h)

/-- Integrate the last variable of a regular 2-cochain. -/
abbrev averageLast : ((M × M) →₀ W) →ₗ[R] (M →₀ W) := lastCoefficient

end

end LinearAlgebraicGroups.RegularTorusCohomology

namespace LinearAlgebraicGroups.Specs.RegularTorusCohomology

universe u

open LinearAlgebraicGroups.RegularTorusCohomology

/-- The coefficient functional commutes with every scalar extension and is
invariant under all translations on the extended torus. -/
def TranslationInvariant : Prop :=
  ∀ (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommGroup M],
    (∀ (r : S) (p : MonoidAlgebra R M),
      constantCoefficient S M (MonoidAlgebra.scalarTensorEquiv R S (r ⊗ₜ[R] p)) =
        r * algebraMap R S (constantCoefficient R M p)) ∧
    (∀ (t : M →* Sˣ) (p : MonoidAlgebra S M),
      constantCoefficient S M (translation t p) = constantCoefficient S M p)

/-- In the iterated tensor model, the homotopy is averaging the inserted
first variable by the zero-character coefficient functional. -/
def TensorAveraging : Prop :=
  ∀ {R M : Type u} [CommRing R] [CommGroup M] {W : Type*} [AddCommGroup W] [Module R W]
    (n : ℕ) (f : W ⊗[R] coordinatePower R M (n + 1)),
    regularTensorEquiv R M W n (averageFirstTensor n f) =
      average (R := R) n 0 (regularTensorEquiv R M W (n + 1) f)

/-- Equivariance in the product character basis of the simultaneous translation identity. -/
def EquivarianceCriterion : Prop :=
  ∀ {R M W : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]
    (ρ : TorusComodule R M W) (n : ℕ) (f : Regular M W n),
    Equivariant ρ f ↔ ∀ a : Fin n → M,
      ρ.coaction (f a) = f a ⊗ₜ[R] MonoidAlgebra.of R M (∏ i, a i)

/-- The alternating omission complex and its first-variable contraction in
every positive cohomological degree. Degree n has n + 1 variables. -/
def HomogeneousContraction : Prop :=
  ∀ {R M W : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]
    (ρ : TorusComodule R M W) (n : ℕ),
    (∀ (f : Regular M W (n + 1)), Equivariant ρ f →
      Equivariant ρ (differential (R := R) (n + 1) f) ∧
      differential (R := R) (n + 2) (differential (R := R) (n + 1) f) = 0) ∧
    (∀ (f : Regular M W (n + 2)), Equivariant ρ f →
      Equivariant ρ (average (R := R) (n + 1) 0 f) ∧
      differential (R := R) (n + 1) (average (R := R) (n + 1) 0 f) +
        average (R := R) (n + 2) 0 (differential (R := R) (n + 2) f) = f)

/-- Algebraic equivariance is agreement between simultaneous translation and
the action on values over every test algebra. -/
def HomogeneousPointCriterion : Prop :=
  ∀ {R M : Type u} [CommRing R] [CommGroup M] {W : Type*} [AddCommGroup W] [Module R W]
    (ρ : TorusComodule R M W) (n : ℕ) (f : Regular M W n),
    Equivariant ρ f ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] (t : M →* S) (p : Fin n → M →* S),
        evaluatePolynomial (tupleCharacter (fun i => t * p i)) f =
          pointAction ρ t (evaluatePolynomial (tupleCharacter p) f)

/-- The coordinate omission maps evaluate to omission of the corresponding point. -/
def OmissionPointFormula : Prop :=
  ∀ {R M W S : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]
    [CommRing S] [Algebra R S] (n : ℕ) (i : Fin (n + 1)) (p : Fin (n + 1) → M →* S)
    (f : Regular M W n),
    evaluatePolynomial (R := R) (tupleCharacter p) (omitVariable (R := R) n i f) =
      evaluatePolynomial (R := R) (tupleCharacter (fun j => p (i.succAbove j))) f

/-- The universal coordinate formulas evaluate to the usual inhomogeneous
differentials at every tuple in every commutative test algebra. -/
def InhomogeneousPointFormulas : Prop :=
  ∀ {R M W S : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]
    [CommRing S] [Algebra R S] (ρ : TorusComodule R M W) (t s z : M →* S),
    (∀ w : W, evaluatePolynomial t (inhomogeneousZero ρ w) =
      pointAction ρ t (1 ⊗ₜ[R] w) - 1 ⊗ₜ[R] w) ∧
    (∀ c : M →₀ W, evaluatePolynomial (t.coprod s) (inhomogeneousOne ρ c) =
      pointAction ρ t (evaluatePolynomial s c) - evaluatePolynomial (t * s : M →* S) c +
        evaluatePolynomial t c) ∧
    (∀ c : (M × M) →₀ W,
      evaluatePolynomial ((t.coprod s).coprod z) (inhomogeneousTwo ρ c) =
        pointAction ρ t (evaluatePolynomial (s.coprod z) c) -
        evaluatePolynomial ((t * s).coprod z) c +
        evaluatePolynomial (t.coprod (s * z)) c -
        evaluatePolynomial (t.coprod s) c)

/-- Testing over all commutative test algebras detects the regular cocycle
identities in each of the two low degrees. -/
def InhomogeneousCocycleCriterion : Prop :=
  ∀ {R M : Type u} [CommRing R] [CommGroup M] {W : Type*} [AddCommGroup W] [Module R W]
    (ρ : TorusComodule R M W),
    (∀ c : M →₀ W, inhomogeneousOne ρ c = 0 ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] (t s : M →* S),
        pointAction ρ t (evaluatePolynomial s c) - evaluatePolynomial (t * s : M →* S) c +
          evaluatePolynomial t c = 0) ∧
    (∀ c : (M × M) →₀ W, inhomogeneousTwo ρ c = 0 ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] (t s z : M →* S),
        pointAction ρ t (evaluatePolynomial (s.coprod z) c) -
          evaluatePolynomial ((t * s).coprod z) c +
          evaluatePolynomial (t.coprod (s * z)) c -
          evaluatePolynomial (t.coprod s) c = 0)

/-- The explicit inhomogeneous primitives are the negative mean of a 1-cocycle
and the mean in the last variable of a 2-cocycle. -/
def InhomogeneousCoboundaries : Prop :=
  ∀ {R M W : Type*} [CommRing R] [CommGroup M] [AddCommGroup W] [Module R W]
    (ρ : TorusComodule R M W),
    (∀ c : M →₀ W, inhomogeneousOne ρ c = 0 →
      inhomogeneousZero ρ (-(c 1)) = c) ∧
    (∀ c : (M × M) →₀ W, inhomogeneousTwo ρ c = 0 →
      inhomogeneousOne ρ (averageLast (R := R) c) = c)

end LinearAlgebraicGroups.Specs.RegularTorusCohomology
