import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Trace.Defs

/-! Matrix words in the two rank-one models used for local generation in F12. -/

universe u v

namespace LinearAlgebraicGroups.Specs.UnitaryRankOne

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

private theorem exists_quadraticConjugation_ne_one
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] :
    ∃ σ : E ≃ₐ[F] E, σ ≠ 1 := by
  have hdim := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let : FiniteDimensional F E := .of_finrank_pos (hdim ▸ Nat.zero_lt_succ 1)
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 :=
    (IsGalois.card_aut_eq_finrank F E).trans hdim
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).mp hcard
  exact ⟨σ, hσ⟩

/-- The nonidentity automorphism of the separable quadratic field extension. -/
noncomputable def quadraticConjugation (F : Type u) (E : Type v)
    [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E] : E ≃ₐ[F] E :=
  Classical.choose (exists_quadraticConjugation_ne_one F E)

theorem quadraticConjugation_ne_one (F : Type u) (E : Type v)
    [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    [Algebra.IsSeparable F E] : quadraticConjugation F E ≠ 1 :=
  Classical.choose_spec (exists_quadraticConjugation_ne_one F E)

/-- The Gram matrix in the ordered basis formed by the first hyperbolic
vector, the orthogonal middle vector of norm `q`, and the second hyperbolic vector. -/
def hermitianMatrix (q : E) : Matrix (Fin 3) (Fin 3) E :=
  !![0, 0, 1; 0, q, 0; 1, 0, 0]

/-- The usual Hermitian isometry equation in the adapted coordinates. -/
def PreservesForm (σ : E ≃ₐ[F] E) (q : E) (g : Matrix (Fin 3) (Fin 3) E) : Prop :=
  (g.map σ).transpose * hermitianMatrix q * g = hermitianMatrix q

def Admissible (σ : E ≃ₐ[F] E) (q a b : E) : Prop :=
  b + σ b = -(a * σ a) / q

def upper (σ : E ≃ₐ[F] E) (q a b : E) : Matrix (Fin 3) (Fin 3) E :=
  !![1, a, b; 0, 1, -(σ a) / q; 0, 0, 1]

def lower (σ : E ≃ₐ[F] E) (q a b : E) : Matrix (Fin 3) (Fin 3) E :=
  !![1, 0, 0; σ a / q, 1, 0; b, -a, 1]

/-- Interchange the hyperbolic vectors and negate the middle vector. -/
def unitaryWeyl (E : Type v) [Field E] : Matrix (Fin 3) (Fin 3) E :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

def unitaryDiagonal (σ : E ≃ₐ[F] E) (s : E) : Matrix (Fin 3) (Fin 3) E :=
  Matrix.diagonal ![s, σ s / s, (σ s)⁻¹]

/-- The generators are the two unitriangular radicals in the adapted
coordinates, viewed as elements of the ambient determinant-one matrix group. -/
def unitaryRadicalGenerators (σ : E ≃ₐ[F] E) (q : E) :
    Set (Matrix.SpecialLinearGroup (Fin 3) E) :=
  {g | ∃ a b : E, Admissible σ q a b ∧
    (g.val = upper σ q a b ∨ g.val = lower σ q a b)}

/-- A raw coordinate matrix has a representative in the given point subgroup. -/
def RepresentedIn {n : ℕ} (A : Matrix (Fin n) (Fin n) E)
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin n) E)) : Prop :=
  ∃ g ∈ H, g.val = A

section Quadratic

variable [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- Both admissible coordinates describe the full respective unitriangular
part of the special unitary group of the displayed form. -/
def AdmissibleCoordinates : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    (q : Fˣ),
    let σ := quadraticConjugation F E
    let Q := algebraMap F E (q : F)
    (∀ a b c : E,
      PreservesForm σ Q !![1, a, b; 0, 1, c; 0, 0, 1] ↔
        c = -(σ a) / Q ∧ Admissible σ Q a b) ∧
    (∀ a b c : E,
      PreservesForm σ Q !![1, 0, 0; c, 1, 0; b, -a, 1] ↔
        c = σ a / Q ∧ Admissible σ Q a b) ∧
    (∀ a b : E,
      (upper σ Q a b).det = 1 ∧ (lower σ Q a b).det = 1 ∧
        lower σ Q a b = unitaryWeyl E * upper σ Q a b * unitaryWeyl E) ∧
    (unitaryWeyl E).det = 1 ∧ PreservesForm σ Q (unitaryWeyl E) ∧
    unitaryWeyl E * unitaryWeyl E = 1

/-- The interchange word uses two admissible lower coordinates and one upper coordinate. -/
def ThreeFactorInterchange : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    (q : Fˣ) (a b : E),
    let σ := quadraticConjugation F E
    let Q := algebraMap F E (q : F)
    Admissible σ Q a b → b ≠ 0 →
      Admissible σ Q (a / σ b) (σ b)⁻¹ ∧
      Admissible σ Q (a / b) (σ b)⁻¹ ∧
      lower σ Q (a / σ b) (σ b)⁻¹ * upper σ Q a b *
        lower σ Q (a / b) (σ b)⁻¹ = unitaryDiagonal σ b * unitaryWeyl E

/-- Every scale is the ratio of two nonzero admissible top-right entries,
using a common parameter `a` in the two upper matrices. -/
def AdmissibleRatios : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    (q : Fˣ) (s : Eˣ),
    let σ := quadraticConjugation F E
    let Q := algebraMap F E (q : F)
    let tr := Algebra.trace F E
    ∃ (b : Eˣ) (a : E),
      Admissible σ Q a (b : E) ∧ Admissible σ Q a ((s : E) * b) ∧
      ((s : E) ∈ Set.range (algebraMap F E) →
        a = 0 ∧ tr (b : E) = 0 ∧ tr ((s : E) * b) = 0) ∧
      ((s : E) ∉ Set.range (algebraMap F E) →
        a = 1 ∧ tr (b : E) = -(q : F)⁻¹ ∧ tr ((s : E) * b) = -(q : F)⁻¹)

/-- The diagonal torus and the hyperbolic-line interchange are products of
the two radical families. The middle entries realize all norm-one scalars. -/
def UnitaryTorusAndWeylWords : Prop :=
  ∀ {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [Infinite F]
    (q : Fˣ),
    let σ := quadraticConjugation F E
    let Q := algebraMap F E (q : F)
    let H := Subgroup.closure (unitaryRadicalGenerators σ Q)
    (∀ d : Fin 3 → E,
      ((Matrix.diagonal d).det = 1 ∧ PreservesForm σ Q (Matrix.diagonal d)) ↔
        ∃ s : Eˣ, Matrix.diagonal d = unitaryDiagonal σ (s : E)) ∧
    (∀ s : Eˣ,
      RepresentedIn (unitaryDiagonal σ (s : E)) H ∧
        unitaryWeyl E * unitaryDiagonal σ (s : E) * unitaryWeyl E =
          unitaryDiagonal σ ((σ (s : E))⁻¹)) ∧
    RepresentedIn (unitaryWeyl E) H ∧
    (∀ η : E, η * σ η = 1 → ∃ s : Eˣ, σ (s : E) / (s : E) = η)

end Quadratic

section Split

variable {R : Type u} [CommRing R]

def splitUpper (a : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) a

def splitLower (a : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection (i := 1) (j := 0) (by decide) a

def splitWord (t : Rˣ) : Matrix.SpecialLinearGroup (Fin 2) R :=
  splitUpper (t : R) * splitLower (-(↑t⁻¹ : R)) * splitUpper (t : R)

/-- Split rank-one words in the special linear point groups, also with
independent parameters in an orthogonal orbit's product of split factors. -/
def SplitRankOneWords : Prop :=
  (∀ {R : Type u} [CommRing R] (t : Rˣ),
    (splitWord t).val = !![0, (t : R); -(↑t⁻¹ : R), 0] ∧
    (splitWord t * splitWord (-1)).val = Matrix.diagonal ![(t : R), (↑t⁻¹ : R)]) ∧
  (∀ {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)] (t : ∀ i, (R i)ˣ),
    let H := Subgroup.closure
      (Set.range (fun a : ∀ i, R i => fun i => splitUpper (a i)) ∪
       Set.range (fun a : ∀ i, R i => fun i => splitLower (a i)))
    (fun i => splitWord (1 : (R i)ˣ)) ∈ H ∧
      (fun i => splitWord (t i) * splitWord (-1)) ∈ H)

end Split

end LinearAlgebraicGroups.Specs.UnitaryRankOne
