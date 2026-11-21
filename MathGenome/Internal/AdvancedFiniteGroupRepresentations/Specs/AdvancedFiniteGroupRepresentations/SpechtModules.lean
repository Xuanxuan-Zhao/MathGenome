import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Tabloids
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! FR A04 and the Hermitian-form convention immediately following it.
The existing zero-based tableau and tabloid interfaces are used, including n = 0.
The ambient group-algebra action is the algebra homomorphism of the permutation
representation. The source form reverses the arguments of Mathlib's inner product.
-/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Specs.AdvancedFiniteGroupRepresentations

noncomputable instance columnFintype {n} {p : Partition n} (t : Tableau p) :
    Fintype (columnSubgroup t) := Fintype.ofFinite _

def permutationSign {n} (g : SymmetricGroup n) : ℂ := (Equiv.Perm.sign g : ℤ)

def columnAlternator {n} {p : Partition n} (t : Tableau p) : GroupAlgebra n :=
  ∑ c : columnSubgroup t, MonoidAlgebra.single c.val (permutationSign c.val)

def groupAlgebraAction {n} (p : Partition n) :
    GroupAlgebra n →ₐ[ℂ] Module.End ℂ (PermutationModule p) :=
  (permutationRepresentation p).asAlgebraHom

def polytabloid {n} {p : Partition n} (t : Tableau p) : PermutationModule p :=
  groupAlgebraAction p (columnAlternator t) (MonoidAlgebra.single (tabloid t) 1)

def spechtSpan {n} (p : Partition n) : Submodule ℂ (PermutationModule p) :=
  Submodule.span ℂ (Set.range (polytabloid (p := p)))

abbrev SpechtModule {n} (p : Partition n) : Type := ↥(spechtSpan p)

def tabloidCoordinates {n} {p : Partition n} (x : PermutationModule p) :
    EuclideanSpace ℂ (Tabloid p) := WithLp.toLp 2 (fun q => x.coeff q)

/-- Linear in x, conjugate-linear in y (opposite to Mathlib's convention). -/
def tabloidHermitian {n} {p : Partition n} (x y : PermutationModule p) : ℂ :=
  inner ℂ (tabloidCoordinates y) (tabloidCoordinates x)


/-! Independent full proposition contracts. No candidate module is imported. -/
attribute [local instance] Classical.propDecidable

def permutationSignType := {n : ℕ} → SymmetricGroup n → ℂ

def columnAlternatorType := {n : ℕ} → {p : Partition n} → Tableau p → GroupAlgebra n

def groupAlgebraActionType := {n : ℕ} → (p : Partition n) → GroupAlgebra n →ₐ[ℂ] Module.End ℂ (PermutationModule p)

def polytabloidType := {n : ℕ} → {p : Partition n} → Tableau p → PermutationModule p

def spechtSpanType := {n : ℕ} → (p : Partition n) → Submodule ℂ (PermutationModule p)

def SpechtModuleType := {n : ℕ} → Partition n → Type

def tabloidCoordinatesType := {n : ℕ} → {p : Partition n} → PermutationModule p → EuclideanSpace ℂ (Tabloid p)

def tabloidHermitianType := {n : ℕ} → {p : Partition n} → PermutationModule p → PermutationModule p → ℂ

def polytabloid_sumType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p),
    polytabloid t = ∑ c : columnSubgroup t,
      MonoidAlgebra.single (tabloid (c.val • t)) (permutationSign c.val)

def polytabloid_coefficientType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p),
    (polytabloid t).coeff (tabloid t) = 1

def polytabloid_equivariantType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (g : SymmetricGroup n) (t : Tableau p),
    permutationRepresentation p g (polytabloid t) = polytabloid (g • t)

def polytabloid_columnType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p) (c : columnSubgroup t),
    polytabloid (c.val • t) = permutationSign c.val • polytabloid t

def columnAlternator_polytabloidType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p),
    groupAlgebraAction p (columnAlternator t) (polytabloid t) =
      (Fintype.card (columnSubgroup t) : ℂ) • polytabloid t

def polytabloid_ne_zeroType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p),
    polytabloid t ≠ 0

def polytabloid_mem_spechtType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p),
    polytabloid t ∈ spechtSpan p

def specht_stableType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (g : SymmetricGroup n) (v : PermutationModule p)
    (_hv : v ∈ spechtSpan p),
    permutationRepresentation p g v ∈ spechtSpan p

def specht_inheritedActionType : Prop :=
  ∀ {n : ℕ}, ∀ (p : Partition n),
    ∃ ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p),
      ∀ g v, (ρ g v).val = permutationRepresentation p g v.val

def specht_nonzeroType : Prop :=
  ∀ {n : ℕ}, ∀ (p : Partition n),
    spechtSpan p ≠ ⊥

def specht_cyclicType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p),
    spechtSpan p = Submodule.span ℂ
      (Set.range (fun g : SymmetricGroup n => permutationRepresentation p g (polytabloid t)))

def specht_generatedType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (t : Tableau p) (U : Subrepresentation (permutationRepresentation p))
    (_ht : polytabloid t ∈ U),
    spechtSpan p ≤ U.toSubmodule

def tabloidHermitian_libraryType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x y : PermutationModule p),
    tabloidHermitian x y = inner ℂ (tabloidCoordinates y) (tabloidCoordinates x)

def tabloidHermitian_sumType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x y : PermutationModule p),
    tabloidHermitian x y = ∑ q : Tabloid p, x.coeff q * conj (y.coeff q)

def tabloidHermitian_add_leftType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x y z : PermutationModule p),
    tabloidHermitian (x + y) z = tabloidHermitian x z + tabloidHermitian y z

def tabloidHermitian_smul_leftType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (a : ℂ) (x y : PermutationModule p),
    tabloidHermitian (a • x) y = a * tabloidHermitian x y

def tabloidHermitian_add_rightType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x y z : PermutationModule p),
    tabloidHermitian x (y + z) = tabloidHermitian x y + tabloidHermitian x z

def tabloidHermitian_smul_rightType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (a : ℂ) (x y : PermutationModule p),
    tabloidHermitian x (a • y) = conj a * tabloidHermitian x y

def tabloidHermitian_conj_symmType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x y : PermutationModule p),
    conj (tabloidHermitian y x) = tabloidHermitian x y

def tabloidHermitian_nonnegType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x : PermutationModule p),
    0 ≤ (tabloidHermitian x x).re

def tabloidHermitian_posType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x : PermutationModule p),
    0 < (tabloidHermitian x x).re ↔ x ≠ 0

def tabloidHermitian_definiteType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (x : PermutationModule p),
    tabloidHermitian x x = 0 ↔ x = 0

def tabloidHermitian_basisType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (q r : Tabloid p),
    tabloidHermitian (MonoidAlgebra.single q 1) (MonoidAlgebra.single r 1) =
      if q = r then 1 else 0

def tabloidHermitian_invariantType : Prop :=
  ∀ {n : ℕ} {p : Partition n}, ∀ (g : SymmetricGroup n) (x y : PermutationModule p),
    tabloidHermitian (permutationRepresentation p g x) (permutationRepresentation p g y) =
      tabloidHermitian x y

end Specs.AdvancedFiniteGroupRepresentations
