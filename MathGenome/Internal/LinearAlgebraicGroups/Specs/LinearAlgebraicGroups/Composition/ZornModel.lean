import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.Adjoints
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The coordinate split octonion algebra and its scalar extension. -/

namespace LinearAlgebraicGroups.Composition

open scoped Matrix TensorProduct

universe u v
variable {R : Type u}

/-- Zorn coordinates with their Zorn multiplication. The type synonym distinguishes this
multiplication from the pointwise multiplication on the underlying product module. -/
def Zorn (R : Type u) := Specification.ZornCoordinates R

namespace Zorn

instance [CommRing R] : AddCommGroup (Zorn R) :=
  inferInstanceAs (AddCommGroup (Specification.ZornCoordinates R))

instance [CommRing R] : Module R (Zorn R) :=
  inferInstanceAs (Module R (Specification.ZornCoordinates R))

/-- Read the scalar, upper vector, lower vector, and scalar slots, in that order. -/
def coordinates (R : Type u) [CommRing R] : Zorn R ≃ₗ[R] Specification.ZornCoordinates R :=
  LinearEquiv.refl R (Specification.ZornCoordinates R)

variable [CommRing R]

/-- Form a Zorn matrix from its four slots. -/
abbrev ofCoordinates (x : Specification.ZornCoordinates R) : Zorn R :=
  (coordinates R).symm x

private lemma product_add_left (x y z : Specification.ZornCoordinates R) :
    Specification.zornProduct (x + y) z =
      Specification.zornProduct x z + Specification.zornProduct y z := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, w, t, d⟩
  rcases z with ⟨e, p, q, f⟩
  simp only [Specification.zornProduct, Prod.mk_add_mk, Prod.mk.injEq, add_mul,
    add_dotProduct, add_smul, smul_add, LinearMap.map_add₂]
  refine ⟨by abel, by abel, by abel, by abel⟩

private lemma product_add_right (x y z : Specification.ZornCoordinates R) :
    Specification.zornProduct x (y + z) =
      Specification.zornProduct x y + Specification.zornProduct x z := by
  rcases x with ⟨a, u, v, b⟩
  rcases y with ⟨c, w, t, d⟩
  rcases z with ⟨e, p, q, f⟩
  simp only [Specification.zornProduct, Prod.mk_add_mk, Prod.mk.injEq, mul_add,
    dotProduct_add, add_smul, smul_add, map_add]
  refine ⟨by abel, by abel, by abel, by abel⟩

instance : NonAssocRing (Zorn R) where
  __ := (inferInstance : AddCommGroup (Zorn R))
  one := ofCoordinates Specification.zornUnit
  mul x y := ofCoordinates <| Specification.zornProduct (coordinates R x) (coordinates R y)
  right_distrib x y z := product_add_left x y z
  left_distrib x y z := product_add_right x y z
  zero_mul x := by
    rcases x with ⟨a, u, v, b⟩
    change Specification.zornProduct (0, 0, 0, 0) (a, u, v, b) = (0, 0, 0, 0)
    simp [Specification.zornProduct]
  mul_zero x := by
    rcases x with ⟨a, u, v, b⟩
    change Specification.zornProduct (a, u, v, b) (0, 0, 0, 0) = (0, 0, 0, 0)
    simp [Specification.zornProduct]
  one_mul x := by
    rcases x with ⟨a, u, v, b⟩
    change Specification.zornProduct (1, 0, 0, 1) (a, u, v, b) = (a, u, v, b)
    simp [Specification.zornProduct]
  mul_one x := by
    rcases x with ⟨a, u, v, b⟩
    change Specification.zornProduct (a, u, v, b) (1, 0, 0, 1) = (a, u, v, b)
    simp [Specification.zornProduct]

instance : IsScalarTower R (Zorn R) (Zorn R) where
  smul_assoc r x y := by
    rcases x with ⟨a, u, v, b⟩
    rcases y with ⟨c, w, t, d⟩
    change Specification.zornProduct (r * a, r • u, r • v, r * b) (c, w, t, d) =
      r • Specification.zornProduct (a, u, v, b) (c, w, t, d)
    simp [Specification.zornProduct, smul_add, smul_sub, smul_smul, mul_assoc, mul_add,
      mul_comm d r, mul_comm c r]

instance : SMulCommClass R (Zorn R) (Zorn R) where
  smul_comm r x y := by
    rcases x with ⟨a, u, v, b⟩
    rcases y with ⟨c, w, t, d⟩
    change r • Specification.zornProduct (a, u, v, b) (c, w, t, d) =
      Specification.zornProduct (a, u, v, b) (r * c, r • w, r • t, r * d)
    simp [Specification.zornProduct, smul_add, smul_sub, smul_smul, mul_add, mul_left_comm,
      mul_comm a r, mul_comm b r]

/-- Regroup as the paired columns `(a,u)` and `(b,-v)`. -/
def pairedColumns (R : Type u) [CommRing R] :
    Zorn R ≃ₗ[R] ((Option (Fin 3) → R) × (Option (Fin 3) → R)) :=
  let e : (Option (Fin 3) → R) ≃ₗ[R] R × (Fin 3 → R) := LinearEquiv.piOptionEquivProd R
  (coordinates R).trans <|
    ({ toFun := fun ⟨a, u, v, b⟩ => ((a, u), (b, -v))
       invFun := fun ⟨⟨a, u⟩, ⟨b, v⟩⟩ => (a, u, -v, b)
       left_inv := by rintro ⟨a, u, v, b⟩; simp
       right_inv := by rintro ⟨⟨a, u⟩, ⟨b, v⟩⟩; simp
       map_add' := by rintro ⟨a, u, v, b⟩ ⟨c, w, t, d⟩; simp [add_comm]
       map_smul' := by rintro r ⟨a, u, v, b⟩; simp } :
      Specification.ZornCoordinates R ≃ₗ[R]
        ((R × (Fin 3 → R)) × (R × (Fin 3 → R)))).trans (e.symm.prodCongr e.symm)

/-- The norm coordinates are a functional and a vector in a free module of rank four. -/
def hyperbolicCoordinates (R : Type u) [CommRing R] :
    Zorn R ≃ₗ[R] Module.Dual R (Option (Fin 3) → R) × (Option (Fin 3) → R) :=
  (pairedColumns R).trans ((dotProductEquiv R (Option (Fin 3))).prodCongr (LinearEquiv.refl R _))

/-- The eight signed coordinate functions, ordered by paired column. -/
def pairedFunctions (R : Type u) [CommRing R] :
    Zorn R ≃ₗ[R] ((Option (Fin 3) ⊕ Option (Fin 3)) → R) :=
  (pairedColumns R).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm

noncomputable def coordinateBasis (R : Type u) [CommRing R] :
    Module.Basis (Option (Fin 3) ⊕ Option (Fin 3)) R (Zorn R) :=
  (Pi.basisFun R _).map (pairedFunctions R).symm

instance : Module.Free R (Zorn R) := Module.Free.of_equiv (pairedColumns R).symm

instance : Module.Finite R (Zorn R) := Module.Finite.equiv (pairedColumns R).symm

end Zorn

namespace ZornSpecification

open Specification

variable (R : Type u) [CommRing R]

def normType := ∀ (R : Type u) [CommRing R], QuadraticForm R (Zorn R)

def norm : QuadraticForm R (Zorn R) :=
  (QuadraticForm.dualProd R (Option (Fin 3) → R)).comp (Zorn.hyperbolicCoordinates R)

def firstType := ∀ (R : Type u) [CommRing R], Zorn R

def first : Zorn R := Zorn.ofCoordinates (1, 0, 0, 0)

def secondType := ∀ (R : Type u) [CommRing R], Zorn R

def second : Zorn R := Zorn.ofCoordinates (0, 0, 0, 1)

def productAndUnit : Prop :=
  ∀ (R : Type u) [CommRing R],
    Zorn.coordinates R 1 = zornUnit ∧
    (∀ x y : Zorn R, Zorn.coordinates R (x * y) =
      zornProduct (Zorn.coordinates R x) (Zorn.coordinates R y)) ∧
    (∀ x : Zorn R, 1 * x = x ∧ x * 1 = x)

def determinantCross : Prop :=
  ∀ (R : Type u) [CommRing R] (x y z : Fin 3 → R),
    dotProduct (crossProduct x y) z = Matrix.det ![x, y, z]

def normFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (x : Zorn R), norm R x = zornNorm (Zorn.coordinates R x)

def normLaws : Prop :=
  ∀ (R : Type u) [CommRing R],
    norm R 1 = 1 ∧ (∀ x y : Zorn R, norm R (x * y) = norm R x * norm R y)

def polarFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (a b c d : R) (u v w t : Fin 3 → R),
    (norm R).polarBilin (Zorn.ofCoordinates (a, u, v, b)) (Zorn.ofCoordinates (c, w, t, d)) =
      a * d + b * c - dotProduct u t - dotProduct w v

def hyperbolic : Prop :=
  ∀ (R : Type u) [CommRing R],
    Nonempty ((norm R).IsometryEquiv (QuadraticForm.dualProd R (Option (Fin 3) → R)))

def perfect : Prop :=
  ∀ (R : Type u) [CommRing R], (norm R).polarBilin.IsPerfPair

def octonion : Prop :=
  ∀ (R : Type u) [CommRing R], OctonionNormConditions (norm R) ∧ splitOctonion (norm R)

def conjugation : Prop :=
  ∀ (R : Type u) [CommRing R] (a b : R) (u v : Fin 3 → R),
    AdjointSpecification.conjugate (norm R) (Zorn.ofCoordinates (a, u, v, b)) =
      Zorn.ofCoordinates (b, -u, -v, a)

def complementaryIdempotents : Prop :=
  ∀ (R : Type u) [CommRing R],
    first R * first R = first R ∧ second R * second R = second R ∧
    first R * second R = 0 ∧ second R * first R = 0 ∧ first R + second R = 1

def nonzeroIdempotents : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R],
    first R ≠ 0 ∧ second R ≠ 0 ∧ norm R (first R) = 0 ∧ norm R (second R) = 0

def fieldIsotropic : Prop :=
  ∀ (k : Type u) [Field k], isotropic (norm k)

/-- Apply a scalar ring homomorphism in all eight slots. -/
def mapCoordinates {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Zorn R) : Zorn S :=
  let (a, u, v, b) := Zorn.coordinates R x
  Zorn.ofCoordinates (f a, f ∘ u, f ∘ v, f b)

set_option linter.checkUnivs false in
def baseChangeType :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S],
    (S ⊗[R] Zorn R) ≃ₗ[S] Zorn S

noncomputable def baseChange (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] : (S ⊗[R] Zorn R) ≃ₗ[S] Zorn S :=
  ((Zorn.coordinateBasis R).baseChange S).equivFun.trans (Zorn.pairedFunctions S).symm

def baseChangeCoordinates : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (s : S) (a b : R) (u v : Fin 3 → R),
    baseChange R S (s ⊗ₜ[R] Zorn.ofCoordinates (a, u, v, b)) =
      Zorn.ofCoordinates (s * algebraMap R S a,
        fun i => s * algebraMap R S (u i), fun i => s * algebraMap R S (v i),
        s * algebraMap R S b)

def baseChangeLaws : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S],
    let e := baseChange R S
    let q := normBaseChange S (norm R)
    e 1 = 1 ∧
    (∀ x y, e (x * y) = e x * e y) ∧
    q = (norm S).comp e.toLinearMap ∧
    q.polarBilin = (norm S).polarBilin.compl₁₂ e.toLinearMap e.toLinearMap ∧
    (∀ x, e (AdjointSpecification.conjugate q x) = AdjointSpecification.conjugate (norm S) (e x)) ∧
    e (1 ⊗ₜ[R] first R) = first S ∧ e (1 ⊗ₜ[R] second R) = second S

/-- The split Cayley–Dickson double of the matrix algebra, in pair coordinates. -/
abbrev MatrixDouble (R : Type u) := Matrix (Fin 2) (Fin 2) R × Matrix (Fin 2) (Fin 2) R

def matrixDoubleUnit (R : Type u) [CommRing R] : MatrixDouble R := (1, 0)

def matrixDoubleProduct {R : Type u} [CommRing R] (x y : MatrixDouble R) : MatrixDouble R :=
  (x.1 * y.1 + y.2.adjugate * x.2, y.2 * x.1 + x.2 * y.1.adjugate)

def matrixDetNorm (R : Type u) [CommRing R] :
    QuadraticForm R (Matrix (Fin 2) (Fin 2) R) :=
  let entry (i j : Fin 2) : Matrix (Fin 2) (Fin 2) R →ₗ[R] R :=
    Matrix.entryLinearMap R R i j
  QuadraticMap.linMulLin (entry 0 0) (entry 1 1) - QuadraticMap.linMulLin (entry 0 1) (entry 1 0)

def matrixDoubleNorm (R : Type u) [CommRing R] : QuadraticForm R (MatrixDouble R) :=
  (matrixDetNorm R).comp (LinearMap.fst R _ _) - (matrixDetNorm R).comp (LinearMap.snd R _ _)

def matrixDoubleNormFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (x : MatrixDouble R),
    matrixDoubleNorm R x = x.1.det - x.2.det

def matrixDoubleModel : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : (matrixDoubleNorm R).IsometryEquiv (norm R),
      e (matrixDoubleUnit R) = 1 ∧
      ∀ x y : MatrixDouble R, e (matrixDoubleProduct x y) = e x * e y

def matrixDoubleDiagonal (R : Type u) [CommRing R] :
    Matrix (Fin 2) (Fin 2) R →ₗ[R] MatrixDouble R :=
  LinearMap.id.prod LinearMap.id

def matrixDoubleSplitNorm : Prop :=
  ∀ (k : Type u) [Field k],
    Module.finrank k (MatrixDouble k) = 8 ∧
    Module.finrank k (matrixDoubleDiagonal k).range = 4 ∧
    (∀ x ∈ (matrixDoubleDiagonal k).range, matrixDoubleNorm k x = 0) ∧
    isotropic (matrixDoubleNorm k) ∧
    Nonempty ((matrixDoubleNorm k).IsometryEquiv
      (QuadraticForm.dualProd k (Option (Fin 3) → k)))

/-- The complementary zero divisors in the doubled matrix presentation use division by two. -/
def matrixDoubleZeroDivisors : Prop :=
  ∀ (k : Type u) [Field k], (2 : k) ≠ 0 →
    let a : MatrixDouble k := (0, 1)
    let e := (2 : k)⁻¹ • (matrixDoubleUnit k + a)
    let f := (2 : k)⁻¹ • (matrixDoubleUnit k - a)
    matrixDoubleProduct a a = matrixDoubleUnit k ∧
    e ≠ 0 ∧ f ≠ 0 ∧ matrixDoubleProduct e f = 0 ∧ matrixDoubleProduct f e = 0

end ZornSpecification
end LinearAlgebraicGroups.Composition
