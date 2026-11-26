import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.SplitContractingRadical

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.HermitianRadicalComparison

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open GeometricRadicals (IsReductive)
open BorelProper (IsParabolic)
open StandardParabolicLevi (IsContractingRadical)
open LinearAlgebraicGroups.CocharacterDynamics
open RelativeRayGeneration (unipotentGenerated)

noncomputable section

variable {F E ι : Type u} [Field F] [Field E] [Algebra F E] [Fintype ι] [DecidableEq ι]

/-- The hyperbolic coordinates have pairing one and are perpendicular to every
remaining coordinate. The latter coordinates may form the empty set. -/
structure HyperbolicPair (H : Matrix ι ι E) (e f : ι) : Prop where
  distinct : e ≠ f
  row_e : ∀ j, H e j = if j = f then 1 else 0
  row_f : ∀ j, H f j = if j = e then 1 else 0
  col_e : ∀ i, H i e = if i = f then 1 else 0
  col_f : ∀ i, H i f = if i = e then 1 else 0

abbrev Coeff (E : Type u) [Field E] [Algebra F E] (R : TestAlgebra F) := UnitaryNormEquations.Centre F E R

def changeCoefficients {R S : TestAlgebra F} (a : R ⟶ S) : Coeff E R →ₐ[F] Coeff E S :=
  Algebra.TensorProduct.map a.hom (AlgHom.id F E)

def conjugation (σ : E ≃ₐ[F] E) (R : TestAlgebra F) : Coeff E R →ₐ[F] Coeff E R :=
  Algebra.TensorProduct.map (AlgHom.id F R) σ.toAlgHom

def gram (H : Matrix ι ι E) (R : TestAlgebra F) : Matrix ι ι (Coeff E R) :=
  H.map (Algebra.TensorProduct.includeRight (R := F) (A := R))

def Preserves (σ : E ≃ₐ[F] E) (H : Matrix ι ι E) {R : TestAlgebra F}
    (x : Matrix ι ι (Coeff E R)) : Prop :=
  (x.map (conjugation σ R)).transpose * gram H R * x = gram H R

/-- The comparison with the determinant-one Hermitian equations is natural on
all commutative algebras and respects multiplication. -/
structure Model (G : AffineAlgebraicGroup F) (σ : E ≃ₐ[F] E) (H : Matrix ι ι E) where
  point : ∀ R : TestAlgebra F, GroupPoints G.val R ≃
    {x : Matrix.SpecialLinearGroup ι (Coeff E R) // Preserves σ H x.val}
  mul : ∀ (R : TestAlgebra F) (x y : GroupPoints G.val R),
    (point R (x * y)).val = (point R x).val * (point R y).val
  natural : ∀ {R S : TestAlgebra F} (a : R ⟶ S) (x : GroupPoints G.val R),
    (point S (mapPoints a x)).val.val = ((point R x).val.val).map (changeCoefficients a)

variable {G : AffineAlgebraicGroup F} {σ : E ≃ₐ[F] E} {H : Matrix ι ι E}

def Model.matrix (M : Model G σ H) {R : TestAlgebra F} (x : GroupPoints G.val R) :
    Matrix ι ι (Coeff E R) := (M.point R x).val.val

/-- The weights on the two hyperbolic lines and on the orthogonal complement. -/
def weight (e f : ι) (i : ι) : ℤ := if i = e then 1 else if i = f then -1 else 0

def diagonal (e f : ι) {R : TestAlgebra F} (t : Rˣ) : Matrix ι ι (Coeff E R) :=
  Matrix.diagonal fun i => (algebraMap R (Coeff E R)) ((t ^ weight e f i).val)

/-- Entries of negative weight difference must vanish. -/
def Regular {C : Type*} [Zero C] (e f : ι) (x : Matrix ι ι C) : Prop :=
  ∀ i j, weight e f i < weight e f j → x i j = 0

/-- The specialization keeps precisely the entries of weight difference zero. -/
def zeroWeight {C : Type*} [Zero C] (e f : ι) (x : Matrix ι ι C) : Matrix ι ι C :=
  fun i j => if weight e f i = weight e f j then x i j else 0

def StabilizesLine {C : Type*} [Zero C] (e : ι) (x : Matrix ι ι C) : Prop :=
  ∀ i, i ≠ e → x i e = 0

def Unitriangular {C : Type*} [Zero C] [One C] (e f : ι) (x : Matrix ι ι C) : Prop :=
  Regular e f x ∧ zeroWeight e f x = 1

def DescribesLimits (M : Model G σ H) (c : Cocharacter G.val) (e f : ι) : Prop :=
  ∀ (R : TestAlgebra F) (x z : GroupPoints G.val R),
    HasLimit c x z ↔
      Regular e f (M.matrix x) ∧ M.matrix z = zeroWeight e f (M.matrix x)

def RationalMember (G : AffineAlgebraicGroup F)
    (x : GroupPoints G.val (CommAlgCat.of F F)) : Prop :=
  ∃ s : (𝟙_ (SchemeOver F)) ⟶ G.val.X, s ∈ unipotentGenerated G ∧
    toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ s = x

/-- Matrix calculations for the two cocharacters of a hyperbolic pair. -/
def MatrixComparison : Prop :=
  ∀ {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Fintype ι] [DecidableEq ι]
    (σ : E ≃ₐ[F] E) (_ : σ ≠ 1) (_ : ∀ a, σ (σ a) = a)
    (H : (Matrix ι ι E)ˣ) (_ : (H.val.map σ).transpose = H.val)
    (e f : ι), HyperbolicPair H.val e f →
    ∀ (G : AffineAlgebraicGroup F) (M : Model G σ H.val),
      ∃ c : Cocharacter G.val,
        (∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t) ∧
        (∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g) ∧
        DescribesLimits M c e f ∧ DescribesLimits M (oppositeCocharacter c) f e ∧
        ∀ (R : TestAlgebra F) (x : GroupPoints G.val R),
          (Regular e f (M.matrix x) ↔ StabilizesLine e (M.matrix x)) ∧
          (Regular f e (M.matrix x) ↔ StabilizesLine f (M.matrix x))

/-- For the reductive group of the source, the two limit decompositions are
the line parabolics with their radicals. Membership is read on all test algebras. -/
def RadicalComparison : Prop :=
  ∀ {F E ι : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Fintype ι] [DecidableEq ι]
    (σ : E ≃ₐ[F] E) (_ : σ ≠ 1) (_ : ∀ a, σ (σ a) = a)
    (H : (Matrix ι ι E)ˣ) (_ : (H.val.map σ).transpose = H.val)
    (e f : ι), HyperbolicPair H.val e f →
    ∀ (G : AffineAlgebraicGroup F) (_ : IsReductive G) (M : Model G σ H.val),
      ∃ (c : Cocharacter G.val) (D : LimitDecomposition c)
          (D' : LimitDecomposition (oppositeCocharacter c)),
        (∀ (R : TestAlgebra F) (t : Rˣ), M.matrix (cocharacterPoint c R t) = diagonal e f t) ∧
        (∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes c g) ∧
        IsParabolic G D.parabolic ∧ IsParabolic G D'.parabolic ∧
        IsOpenImmersion (bigCellMap D D').left ∧
        IsContractingRadical D ∧ IsContractingRadical D' ∧
        RepresentsOnAlgebras D.parabolic (fun _ x => StabilizesLine e (M.matrix x)) ∧
        RepresentsOnAlgebras D'.parabolic (fun _ x => StabilizesLine f (M.matrix x)) ∧
        RepresentsOnAlgebras D.centralizer (fun _ x =>
          StabilizesLine e (M.matrix x) ∧ StabilizesLine f (M.matrix x)) ∧
        RepresentsOnAlgebras D'.centralizer (fun _ x =>
          StabilizesLine e (M.matrix x) ∧ StabilizesLine f (M.matrix x)) ∧
        RepresentsOnAlgebras D.contracting (fun _ x => Unitriangular e f (M.matrix x)) ∧
        RepresentsOnAlgebras D'.contracting (fun _ x => Unitriangular f e (M.matrix x)) ∧
        ∀ x : GroupPoints G.val (CommAlgCat.of F F),
          (Unitriangular e f (M.matrix x) ∨ Unitriangular f e (M.matrix x)) → RationalMember G x

end
end LinearAlgebraicGroups.Specs.Arithmetic.HermitianRadicalComparison
