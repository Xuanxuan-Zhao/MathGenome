import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! The path model and the independent specification of the path algebra. -/

open scoped BigOperators Classical
open Module

universe u v w

namespace RM03

/-- Turn a quiver given by an arrow set and two endpoint maps into a family of hom types. -/
abbrev quiverOfArrows {V : Type u} {E : Type v} (s t : E → V) : Quiver.{v} V :=
  ⟨fun i j => {a : E // s a = i ∧ t a = j}⟩

/-- The arrows with endpoints retained as part of the data. -/
abbrev Arrow (V : Type u) [Quiver.{v} V] :=
  Σ i : V, Σ j : V, Quiver.Hom i j

/-- The paths with endpoints retained as part of the data. -/
abbrev Path (V : Type u) [Quiver.{v} V] :=
  Σ i : V, Σ j : V, Quiver.Path i j

namespace Path

variable {V : Type u} [Quiver.{v} V]

def source (p : Path V) : V := p.1

def target (p : Path V) : V := p.2.1

def length (p : Path V) : ℕ := p.2.2.length

/-- Bundle a path whose endpoints are given by its type. -/
def ofPath {i j : V} (p : Quiver.Path i j) : Path V := ⟨i, j, p⟩

def vertex (i : V) : Path V := ofPath (Quiver.Path.nil : Quiver.Path i i)

def arrow {i j : V} (a : Quiver.Hom i j) : Path V := ofPath (Quiver.Hom.toPath a)

/-- Travel along `q` and then along `p`. -/
def concat (p q : Path V) (h : p.source = q.target) : Path V :=
  ofPath (q.2.2.comp (p.2.2.cast h rfl))

end Path

namespace PathAlgebraSpec

variable (k : Type w) (V : Type u) [Quiver.{v} V]

/-- The underlying vector space is the space of finitely supported path coefficients. -/
def Carrier [Zero k] := Path V →₀ k

noncomputable instance [AddCommGroup k] : AddCommGroup (Carrier k V) :=
  inferInstanceAs (AddCommGroup (Path V →₀ k))

noncomputable instance [Field k] : Module k (Carrier k V) :=
  inferInstanceAs (Module k (Path V →₀ k))

section
variable [Field k]

abbrev BasisType := Basis (Path V) k (Carrier k V)

noncomputable def basis : BasisType k V :=
  Finsupp.basisSingleOne

abbrev OfPathType := Path V → Carrier k V

noncomputable def ofPath : OfPathType k V :=
  fun p => Finsupp.single p 1

abbrev VertexType := V → Carrier k V

noncomputable def vertex : VertexType k V :=
  fun i => ofPath k V (Path.vertex i)

abbrev ArrowType := ∀ {i j : V}, Quiver.Hom i j → Carrier k V

noncomputable def arrow : ArrowType k V :=
  fun a => ofPath k V (Path.arrow a)

abbrev MulType := Carrier k V →ₗ[k] Carrier k V →ₗ[k] Carrier k V

/-- Extend the product of two basis paths linearly in each argument. -/
noncomputable def mul : MulType k V :=
  (basis k V).constr k fun p => (basis k V).constr k fun q =>
    if h : p.source = q.target then ofPath k V (p.concat q h) else 0

noncomputable instance : Mul (Carrier k V) :=
  ⟨fun x y => mul k V x y⟩

abbrev OneType [Fintype V] := Carrier k V

noncomputable def one [Fintype V] : OneType k V :=
  ∑ i : V, vertex k V i

noncomputable instance [Fintype V] : One (Carrier k V) :=
  ⟨one k V⟩

noncomputable def scalarMap [Fintype V] (c : k) : Carrier k V :=
  c • one k V

/-- The range of left multiplication by `e_j` after right multiplication by `e_i`. -/
noncomputable def corner (i j : V) : Submodule k (Carrier k V) :=
  LinearMap.range ((mul k V (vertex k V j)).comp ((mul k V).flip (vertex k V i)))

end

section Signatures

-- These aliases intentionally quantify over independent coefficient, vertex and arrow universes.
set_option linter.checkUnivs false

abbrev CarrierSignature :=
  ∀ (k : Type w) (V : Type u) [Quiver.{v} V] [Zero k], Type (max u v w)

abbrev BasisSignature :=
  ∀ (k : Type w) (V : Type u) [Quiver.{v} V] [Field k], BasisType k V

abbrev OfPathSignature :=
  ∀ (k : Type w) {V : Type u} [Quiver.{v} V] [Field k], OfPathType k V

noncomputable def ofPathValue : OfPathSignature := fun k {V} _ _ => ofPath k V

abbrev VertexSignature :=
  ∀ (k : Type w) {V : Type u} [Quiver.{v} V] [Field k], VertexType k V

noncomputable def vertexValue : VertexSignature := fun k {V} _ _ => vertex k V

abbrev ArrowSignature :=
  ∀ (k : Type w) {V : Type u} [Quiver.{v} V] [Field k], ArrowType k V

noncomputable def arrowValue : ArrowSignature := fun k {V} _ _ => @arrow k V _ _

abbrev MulSignature :=
  ∀ (k : Type w) (V : Type u) [Quiver.{v} V] [Field k], MulType k V

abbrev CornerSignature :=
  ∀ (k : Type w) {V : Type u} [Quiver.{v} V] [Field k], V → V → Submodule k (Carrier k V)

noncomputable def cornerValue : CornerSignature := fun k {V} _ _ => corner k V

end Signatures

def ArrowData : Prop :=
  ∀ {V : Type u} {E : Type v} (s t : E → V),
    ∃ e : @Arrow V (quiverOfArrows s t) ≃ E,
      ∀ a, s (e a) = a.1 ∧ t (e a) = a.2.1

def BasisVectors : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (p : Path V),
    basis k V p = ofPath k V p

def BasisProduct : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (p q : Path V),
    ofPath k V p * ofPath k V q =
      if h : p.source = q.target then ofPath k V (p.concat q h) else 0

def Associative : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (x y z : Carrier k V),
    (x * y) * z = x * (y * z)

def UnitLaws : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] [Fintype V] (x : Carrier k V),
    (1 : Carrier k V) * x = x ∧ x * 1 = x

/-- The ring and algebra structures use the specified vector space, multiplication,
unit and scalar action. -/
def AlgebraStructure : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] [Fintype V],
    ∃ r : Ring (Carrier k V),
      r.toAddCommGroup = inferInstanceAs (AddCommGroup (Carrier k V)) ∧
      r.toSemiring.toMonoidWithZero.toMonoid.toMulOneClass.toMul =
        inferInstanceAs (Mul (Carrier k V)) ∧
      r.toSemiring.toMonoidWithZero.toMonoid.toMulOneClass.toOne =
        inferInstanceAs (One (Carrier k V)) ∧
      ∃ a : @Algebra k (Carrier k V) _ r.toSemiring,
        a.toSMul = inferInstanceAs (SMul k (Carrier k V)) ∧
        ∀ c, a.algebraMap c = scalarMap k V c

def VertexIdempotent : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (i : V),
    vertex k V i * vertex k V i = vertex k V i

def VertexOrthogonal : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (i j : V),
    i ≠ j → vertex k V i * vertex k V j = 0

def SumVertices : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] [Fintype V],
    (∑ i : V, vertex k V i) = (1 : Carrier k V)

def CornerProduct : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (i j : V) (p : Path V),
    vertex k V j * ofPath k V p * vertex k V i =
      if p.source = i ∧ p.target = j then ofPath k V p else 0

def CornerMembership : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (i j : V) (x : Carrier k V),
    x ∈ corner k V i j ↔ ∃ y : Carrier k V, vertex k V j * y * vertex k V i = x

def CornerBasis : Prop :=
  ∀ {k : Type w} {V : Type u} [Quiver.{v} V] [Field k] (i j : V),
    ∃ b : Basis (Quiver.Path i j) k (corner k V i j),
      ∀ p, (b p : Carrier k V) = ofPath k V (Path.ofPath p)

end PathAlgebraSpec
end RM03
