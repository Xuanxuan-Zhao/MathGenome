import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Matrix.Block

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u
noncomputable section

namespace LinearAlgebraicGroups
namespace Specs.Unipotent

/-- The entries on the diagonal are one and those below it are zero. -/
def IsUpperUnitriangular {ι R : Type*} [LinearOrder ι] [Zero R] [One R]
    (M : Matrix ι ι R) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

section Matrices

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] [CommRing R]

omit [DecidableEq ι] in
theorem IsUpperUnitriangular.mul_apply_diag {M N : Matrix ι ι R}
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (i : ι) :
    (M * N) i i = M i i * N i i := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

/-- Upper unitriangular matrices form a subgroup over every commutative ring. -/
def upperUnitriangular (ι R : Type*) [Fintype ι] [LinearOrder ι] [DecidableEq ι] [CommRing R] :
    Subgroup (Matrix.GeneralLinearGroup ι R) where
  carrier := {g | IsUpperUnitriangular g.val}
  one_mem' := ⟨Matrix.blockTriangular_one, Matrix.one_apply_eq⟩
  mul_mem' {g h} hg hh := by
    change IsUpperUnitriangular g.val at hg
    change IsUpperUnitriangular h.val at hh
    refine ⟨hg.1.mul hh.1, fun i ↦ ?_⟩
    change (g.val * h.val) i i = 1
    rw [IsUpperUnitriangular.mul_apply_diag hg.1 hh.1, hg.2, hh.2, one_mul]
  inv_mem' {g} hg := by
    change IsUpperUnitriangular g.val at hg
    change IsUpperUnitriangular g⁻¹.val
    let := g.invertible
    have ht : g⁻¹.val.IsUpperTriangular := by
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hg.1
    refine ⟨ht, fun i ↦ ?_⟩
    have h : g.val * g⁻¹.val = 1 := g.val_inv
    simpa only [IsUpperUnitriangular.mul_apply_diag hg.1 ht, hg.2, one_mul,
      Matrix.one_apply_eq] using congrArg (fun M : Matrix ι ι R ↦ M i i) h

end Matrices

variable (k : Type u) [Field k]

abbrev Index (n : ℕ) := ULift.{u} (Fin n)

abbrev StrictUpper (n : ℕ) := {p : Index.{u} n × Index.{u} n // p.1 < p.2}

abbrev Coordinates (n : ℕ) := MvPolynomial (StrictUpper.{u} n) k

/-- The group functor of upper unitriangular matrices, with entrywise base change. -/
def unitriangularPoints (n : ℕ) : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (upperUnitriangular (Index n) R)
  map a := GrpCat.ofHom <| ((Matrix.GeneralLinearGroup.map a.hom.toRingHom).comp
    (upperUnitriangular (Index n) _).subtype).codRestrict _ fun g ↦ by
      change IsUpperUnitriangular ((Matrix.GeneralLinearGroup.map a.hom.toRingHom) g.val).val
      exact ⟨fun _ _ h ↦ by change a.hom _ = 0; rw [g.property.1 h, map_zero],
        fun i ↦ by change a.hom (g.val.val i i) = 1; rw [g.property.2 i, map_one]⟩
  map_id _ := by apply GrpCat.ext; intro x; apply Subtype.ext; apply Matrix.GeneralLinearGroup.ext; intro i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; apply Subtype.ext; apply Matrix.GeneralLinearGroup.ext; intro i j; rfl

/-- The coordinate matrix, with freely varying entries above the diagonal. -/
def coordinateMatrix (n : ℕ) : Matrix (Index.{u} n) (Index.{u} n) (Coordinates k n) :=
  fun i j ↦ if h : i < j then MvPolynomial.X ⟨(i, j), h⟩ else (1 : Matrix _ _ _) i j

variable {k}

/-- The invariant-vector characterization in the coaction model of rational representations. -/
def HasInvariantVectors (A : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : RightComodule k A V), ∃ v : V, v ≠ 0 ∧ v ∈ RationalRepresentations.invariants A ρ

/-- A basis adapted to a full flag on which each one-dimensional subquotient is trivial.
The first j basis vectors span the j-th term of the flag. -/
def HasFullFlags (A : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : RightComodule k A V),
    ∃ b : Module.Basis (Index.{u} (Module.finrank k V)) k V,
      IsUpperUnitriangular (RationalRepresentations.coefficients A b ρ)

/-- An invariant full flag with trivial action on each successive quotient. A basis
specifies its successive subspaces, with the j-th subspace spanned by the first j vectors.
The projected difference vanishes on a successor subspace modulo its predecessor. -/
def HasFlagsWithTrivialQuotients (A : HopfAlgebraCategory k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : RightComodule k A V),
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V,
      ∀ (j : Fin (Module.finrank k V)) (v : V), v ∈ b.flag j.succ →
        ((b.flag j.castSucc).mkQ.rTensor A) (RationalRepresentations.invariantDifference A ρ v) = 0

def FullFlagComparison : Prop :=
  ∀ {k : Type u} [Field k] (A : HopfAlgebraCategory k),
    HasFullFlags A ↔ HasFlagsWithTrivialQuotients A

/-- The sum of the images of the pairs of tensor factors in the ambient tensor product. -/
def tensorFiltration {A : Type u} [AddCommGroup A] [Module k A]
    (C : ℕ → Submodule k A) (r : ℕ) : Submodule k (A ⊗[k] A) :=
  ⨆ i : Fin (r + 1), LinearMap.range
    (TensorProduct.map (C i.val).subtype (C (r - i.val)).subtype)

/-- A connected exhaustive coalgebra filtration with degree-zero space spanned by one. -/
def HasCoalgebraFiltration (A : HopfAlgebraCategory k) : Prop :=
  ∃ C : ℕ → Submodule k A, Monotone C ∧ (∀ x : A, ∃ r, x ∈ C r) ∧
    C 0 = Submodule.span k {1} ∧
    ∀ r (x : A), x ∈ C r → Coalgebra.comul (R := k) x ∈ tensorFiltration C r

/-- Closed immersion into a group scheme representing the unitriangular point functor. -/
def EmbedsUnitriangular (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (n : ℕ) (N : AffineAlgebraicGroup k),
    Nonempty ((groupPointsFunctor k).obj N.val ≅ unitriangularPoints k n) ∧
    ∃ f : G.val ⟶ N.val, IsClosedImmersion f.hom.hom.left

/-- Unipotence for an affine algebraic group in the coaction model. -/
def IsUnipotent (G : AffineAlgebraicGroup k) : Prop :=
  ∃ A : HopfAlgebraCategory k, Nonempty (((affineHopfSpec k).obj (op A)).val ≅ G.val) ∧
    HasInvariantVectors A

def UnitriangularPointsType :=
  ∀ (k : Type u) [Field k], ℕ → TestAlgebra k ⥤ GrpCat.{u}

def IsUnipotentType := ∀ {k : Type u} [Field k], AffineAlgebraicGroup k → Prop

/-- Representability on all test algebras by the strictly upper entries of the universal matrix. -/
def UnitriangularGroup : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    ∃ h : StandardGroups.HopfOperations k (Coordinates k n),
      letI := h.hopf
      StandardGroups.Represents (Coordinates k n) (unitriangularPoints k n)
        (fun _ f g ↦ g.val.val = f.mapMatrix (coordinateMatrix k n))

/-- The four criteria for an arbitrary affine algebraic group over a field, under any
identification of its coordinate Hopf algebra. -/
def UnipotenceCriteria : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (A : HopfAlgebraCategory k),
    (((affineHopfSpec k).obj (op A)).val ≅ G.val) →
    (IsUnipotent G ↔ HasInvariantVectors A) ∧
    (HasInvariantVectors A ↔ HasFlagsWithTrivialQuotients A) ∧
    (HasFlagsWithTrivialQuotients A ↔ EmbedsUnitriangular G) ∧
    (EmbedsUnitriangular G ↔ HasCoalgebraFiltration A)

end Specs.Unipotent
end LinearAlgebraicGroups
