import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.AmpleFlagWeights
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.CharP.Frobenius

/-! Binary forms, with the covariant action on the degree-one generators. -/

noncomputable section

namespace LinearAlgebraicGroups.Specs.NonsplitSymmetricPower

open MvPolynomial
open scoped BigOperators Matrix

universe u

/-- The degree-`n` piece of the polynomial realization of the symmetric algebra
on the two standard generators. -/
abbrev Forms (R : Type u) [CommRing R] (n : ℕ) :=
  homogeneousSubmodule (Fin 2) R n

/-- Exponents of the monomial `x^(n-i) y^i`. -/
def exponents (n : ℕ) (i : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![n - (i : ℕ), (i : ℕ)]

theorem exponents_degree (n : ℕ) (i : Fin (n + 1)) :
    (exponents n i).degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simpa [exponents] using Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)

/-- The standard monomials in the symmetric power. -/
def term (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) : Forms R n :=
  ⟨monomial (exponents n i) 1, isHomogeneous_monomial _ (exponents_degree n i)⟩

/-- The substitution induced by the natural action on the two generators. -/
def substitution {R : Type u} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval (fun j ↦ ∑ i, C (g i j) * X i)

/-- The action of a matrix on the homogeneous piece. -/
def act {R : Type u} [CommRing R] {n : ℕ} (g : Matrix (Fin 2) (Fin 2) R) :
    Forms R n →ₗ[R] Forms R n :=
  ((substitution g).toLinearMap.comp (homogeneousSubmodule (Fin 2) R n).subtype).codRestrict
    _ (fun f ↦ by
      have hf : (f : MvPolynomial (Fin 2) R).IsHomogeneous n := f.property
      change (substitution g f.val).IsHomogeneous n
      simpa only [substitution, one_mul] using
        hf.aeval _ (fun j ↦ IsHomogeneous.sum _ _ _ (fun i _ ↦
          isHomogeneous_C_mul_X (g i j) i)))

/-- Coefficients are extended along the given algebra map. -/
def extend {k R : Type u} [Field k] [CommRing R] [Algebra k R] {n : ℕ} (f : Forms k n) :
    Forms R n :=
  ⟨map (algebraMap k R) f.val, f.property.map _⟩

/-- Contract coefficients using a base-field linear functional on the test algebra. -/
def contract {k R : Type u} [Field k] [CommRing R] [Algebra k R] {n : ℕ}
    (ℓ : R →ₗ[k] k) (f : Forms R n) : Forms k n :=
  ∑ i : Fin (n + 1), ℓ (f.val.coeff (exponents n i)) • term k n i

/-- Stability under all scheme points, tested by the coefficients of their action.
The determinant-one condition can be replaced by invertibility to test GL₂-stability. -/
def Stable {k : Type u} [Field k] {n : ℕ} (M : Submodule k (Forms k n))
    (special : Bool) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (g : Matrix (Fin 2) (Fin 2) R),
    (if special then g.det = 1 else IsUnit g.det) →
    ∀ (ℓ : R →ₗ[k] k) (v : Forms k n), v ∈ M → contract ℓ (act g (extend v)) ∈ M

/-- The span of the two pure powers in positive degree. -/
def purePowers (k : Type u) [Field k] (p : ℕ) : Submodule k (Forms k p) :=
  Submodule.span k {term k p 0, term k p (Fin.last p)}

/-- Coordinatewise Frobenius on matrices in the split model. -/
def frobeniusMatrix {R : Type u} [CommRing R] (p : ℕ) (g : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  fun i j ↦ (g i j) ^ p

/-- The linear map taking the standard generators to their pure powers. -/
def purePowerMap (R : Type u) [CommRing R] (p : ℕ) : (Fin 2 → R) →ₗ[R] Forms R p where
  toFun v := v 0 • term R p 0 + v 1 • term R p (Fin.last p)
  map_add' v w := by simp [add_smul]; abel
  map_smul' r v := by simp [smul_add, smul_smul]

/-- The natural Frobenius action identifies via the two pure powers. -/
def FrobeniusSubmodule : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    Function.Injective (purePowerMap k p) ∧
    (purePowerMap k p).range = purePowers k p ∧
    ∀ (R : Type u) [CommRing R] [Algebra k R] (g : Matrix (Fin 2) (Fin 2) R)
      (v : Fin 2 → R),
      act g (purePowerMap R p v) = purePowerMap R p ((frobeniusMatrix p g).mulVec v)

/-- The homogeneous polynomial matrix action over every test ring. -/
def PolynomialAction : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    (∀ (R : Type u) [CommRing R],
      act (n := n) (1 : Matrix (Fin 2) (Fin 2) R) = LinearMap.id ∧
      ∀ g h : Matrix (Fin 2) (Fin 2) R, act (n := n) (g * h) = (act g).comp (act h)) ∧
    ∃ entries : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin 2 × Fin 2) k,
      (∀ i j, (entries i j).IsHomogeneous n) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R] (g : Matrix (Fin 2) (Fin 2) R) i j,
        (act g (term R n j)).val.coeff (exponents n i) =
          aeval (fun a : Fin 2 × Fin 2 ↦ g a.1 a.2) (entries i j)

/-- The unique simple submodule and the nonsplit inclusion for both matrix groups. -/
def Nonsplit : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    let S := purePowers k p
    Stable S true ∧ Stable S false ∧ S ≠ ⊥ ∧ Module.finrank k S = 2 ∧
    Module.finrank k (Forms k p) = p + 1 ∧
    (∀ M : Submodule k (Forms k p), Stable M true → M ≠ ⊥ → S ≤ M) ∧
    (∀ special : Bool, ¬ ∃ M : Submodule k (Forms k p), Stable M special ∧ IsCompl S M)

section Induction

open CategoryTheory
open scoped MatrixGroups

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]

/-- Vectors generating free direct-summand lines in the rank-two trivial bundle. -/
abbrev Column (R : Type u) [CommRing R] := {v : Fin 2 → R // IsCoprime (v 0) (v 1)}

def Column.map (a : R →+* S) (v : Column R) : Column S :=
  ⟨a ∘ v.val, v.property.map a⟩

def Column.scale (u : Rˣ) (v : Column R) : Column R :=
  ⟨fun i ↦ (u : R) * v.val i, by
    obtain ⟨x, y, h⟩ := v.property
    refine ⟨x * ↑u⁻¹, y * ↑u⁻¹, ?_⟩
    calc
      _ = x * (↑u⁻¹ * ↑u) * v.val 0 + y * (↑u⁻¹ * ↑u) * v.val 1 := by ring
      _ = 1 := by simpa only [Units.inv_mul, mul_one] using h⟩

abbrev ColumnFunctions (k : Type u) [Field k] :=
  ∀ R : TestAlgebra k, Column R → R

/-- Sections of the dual tautological line to power `n`, evaluated on local
generators of a split line. A change of generator by a unit multiplies the
evaluation by that unit to the `n`th power. -/
def projectiveSections (k : Type u) [Field k] (n : ℕ) : Submodule k (ColumnFunctions k) where
  carrier := { f |
    (∀ {R S : TestAlgebra k} (a : R ⟶ S) (v : Column R), a.hom (f R v) = f S (v.map a.hom.toRingHom)) ∧
    (∀ (R : TestAlgebra k) (u : Rˣ) (v : Column R), f R (v.scale u) = (u : R)^n * f R v) }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨fun a v ↦ by simpa only [Pi.add_apply, map_add] using congrArg₂ (· + ·) (hf.1 a v) (hg.1 a v),
      fun R u v ↦ by simp only [Pi.add_apply, hf.2, hg.2, mul_add]⟩
  smul_mem' := by
    intro c f hf
    refine ⟨fun a v ↦ ?_, fun R u v ↦ ?_⟩
    · simp only [Pi.smul_apply, Algebra.smul_def, map_mul, AlgHom.commutes, hf.1]
    · simp only [Pi.smul_apply, Algebra.smul_def, hf.2]
      ring

/-- The second column marks the negative Borel point (the line through `y`). -/
def secondColumn (g : Matrix.SpecialLinearGroup (Fin 2) R) : Column R :=
  ⟨fun i ↦ g i 1, g.isCoprime_col 1⟩

abbrev GroupFunctions (k : Type u) [Field k] :=
  ∀ R : TestAlgebra k, Matrix.SpecialLinearGroup (Fin 2) R → R

/-- Natural regular functions with right covariance under the actual lower
triangular matrices. On that Borel the weight is the first diagonal entry,
whose inverse is the second diagonal entry. -/
def matrixInduction (k : Type u) [Field k] (n : ℕ) : Submodule k (GroupFunctions k) where
  carrier := { f |
    (∀ {R S : TestAlgebra k} (a : R ⟶ S) (g : Matrix.SpecialLinearGroup (Fin 2) R),
      a.hom (f R g) = f S (Matrix.SpecialLinearGroup.map a.hom.toRingHom g)) ∧
    (∀ (R : TestAlgebra k) (g b : Matrix.SpecialLinearGroup (Fin 2) R),
      b 0 1 = 0 → f R (g * b) = b 1 1 ^ n * f R g) }
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨fun a x ↦ by simpa only [Pi.add_apply, map_add] using congrArg₂ (· + ·) (hf.1 a x) (hg.1 a x),
      fun R x b h ↦ by simp only [Pi.add_apply, hf.2 R x b h, hg.2 R x b h, mul_add]⟩
  smul_mem' := by
    intro c f hf
    refine ⟨fun a x ↦ ?_, fun R x b h ↦ ?_⟩
    · simp only [Pi.smul_apply, Algebra.smul_def, map_mul, AlgHom.commutes, hf.1]
    · simp only [Pi.smul_apply, Algebra.smul_def, hf.2 R x b h]
      ring

/-- Evaluating using the invariant determinant identifies vectors with
linear functions on the plane. -/
def determinantCoordinates (v : Fin 2 → R) : Fin 2 → R :=
  ![v 1, -v 0]

/-- Pullback between the section descriptions, with the indicated base point. -/
def InductionIdentification : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    ∃ (E : Forms k n ≃ₗ[k] projectiveSections k n)
      (F : projectiveSections k n ≃ₗ[k] matrixInduction k n),
      (∀ f R v, (E f).val R v = aeval (determinantCoordinates v.val) f.val) ∧
      (∀ f R g, (F f).val R g = f.val R (secondColumn g)) ∧
      ∀ (R : TestAlgebra k) (g h : Matrix.SpecialLinearGroup (Fin 2) R) (f : Forms k n),
        aeval (determinantCoordinates (secondColumn h).val)
          (act g.val (extend f)).val = (F (E f)).val R (g⁻¹ * h)

end Induction

section SchemeComparisons

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
open StandardGroups (SLCoordinates determinantOneIdeal universalMatrix specialLinearPoints)
open RelativeFrobenius (twist PullbackFormula twistCoordinates)

/-- The relative Frobenius on the actual determinant-one Hopf algebra agrees with
entrywise powers under the identification of the twisted split model with itself. -/
def RelativeFrobeniusComparison : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (h : StandardGroups.HopfOperations k (SLCoordinates k RankOneFlag.Index.{u})),
    letI := h.hopf
    let A := CommHopfAlgCat.of k (SLCoordinates k RankOneFlag.Index.{u})
    let X := universalMatrix k RankOneFlag.Index.{u}
    let q := Ideal.Quotient.mkₐ k (determinantOneIdeal k RankOneFlag.Index.{u})
    ∀ s : (groupPointsFunctor k).obj (specGroup A) ≅ specialLinearPoints k RankOneFlag.Index.{u},
      (∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (i j : RankOneFlag.Index.{u}),
        (s.hom.app R ((testSpec k).map (CommAlgCat.ofHom a).op)).val i j = a (q (X i j))) →
      ∃ (e : twist k p A ≅ specGroup A) (f : twistCoordinates k p A ⟶ A),
        PullbackFormula k p A f ∧
        ∀ (R : TestAlgebra k) (g : Points (specGroup A).X R),
          ((s.hom.app R (g ≫ (specGroupMap f ≫ e.hom).hom.hom)).val.submatrix ULift.up ULift.up) =
            frobeniusMatrix p ((s.hom.app R g).val.submatrix ULift.up ULift.up)

open GeneralLinearStructure (SpecialMatrixPoints)
open SimpleClassification (SocleModel)
open RankOneFlag (plane projectiveLine HasCoordinates)
open ProjectiveSpaces (LineRepresentation)

/-- The actual opposite-Borel quotient is the line scheme. The orbit map sends
a matrix to the line generated by its second column, so the marked trivial fibre
is the dual of the negative weight line. The bundle section comparison uses
the same pullback and the same matrix action as the coordinate calculation. -/
def MarkedFlagAndSocle : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (s : SpecialMatrixPoints G 2),
    ∃ (P : FlagLineBundle.OppositeBorelPair G) (χ : CharacterDescent.Character P.torus.group)
      (U : ClosedSubgroup P.positive.group)
      (H : QuotientEmbedding.Presentation P.negative)
      (r : LineRepresentation k (plane k)) (c : H.scheme ≅ projectiveLine k)
      (V : SocleModel P U (χ ^ p)),
      GeometricRadicals.IsUnipotentRadical
        (Unipotent.closedSubgroupAlgebraicGroup P.positive) U ∧
      (∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ∈ SubgroupSections P.torus ((testSpec k).obj (op R)) ↔
          (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0 ∧ (s.hom.app R g).val ⟨1⟩ ⟨0⟩ = 0) ∧
      (∀ (R : TestAlgebra k) (t : Points P.torus.group.X R),
        CharacterPairing.characterValue χ R t =
          (s.hom.app R (t ≫ P.torus.inclusion.hom.hom)).val ⟨0⟩ ⟨0⟩) ∧
      (∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ∈ SubgroupSections P.positive ((testSpec k).obj (op R)) ↔
          (s.hom.app R g).val ⟨1⟩ ⟨0⟩ = 0) ∧
      (∀ (R : TestAlgebra k) (g : Points G.val.X R),
        g ∈ SubgroupSections P.negative ((testSpec k).obj (op R)) ↔
          (s.hom.app R g).val ⟨0⟩ ⟨1⟩ = 0) ∧
      AmpleFlagWeights.IsHyperplanePullback H V.projection χ c.hom r ∧
      (∀ (R : TestAlgebra k) (g : Points G.val.X R),
        HasCoordinates r R (g ≫ H.projection ≫ c.hom)
          (fun i ↦ (s.hom.app R g).val i ⟨1⟩)) ∧
      ∃ E : Forms k p ≃ₗ[k] (V.I → k),
        (purePowers k p).map E.toLinearMap = V.socle ∧
        Module.finrank k V.socle = 2 ∧ Module.finrank k (V.I → k) = p + 1 ∧
        ∀ (R : TestAlgebra k) (g : Points G.val.X R) (ℓ : R →ₗ[k] k) (v : Forms k p),
          E (contract ℓ (act ((s.hom.app R g).val.submatrix ULift.up ULift.up) (extend v))) =
            PrimitiveLine.orbitCoefficient V.inducedAction R g ℓ (E v)

end SchemeComparisons

end LinearAlgebraicGroups.Specs.NonsplitSymmetricPower
