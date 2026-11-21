import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! The intrinsic primary filtration from paper.tex:3275–3311.
`powerImage p n N` is p^n N as a submodule of N. Taking its quotient by
p times itself represents p^n N / p^(n+1) N, including n = 0.
No decomposition data occurs in the definition of the invariant. -/
universe u v w
noncomputable section
namespace Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
open scoped Pointwise

abbrev primary (R : Type u) [CommRing R] (p : R)
    (M : Type v) [AddCommGroup M] [Module R M] : Submodule R M :=
  Submodule.torsion' R M (Submonoid.powers p)

abbrev powerImage {R : Type u} [CommRing R] (p : R) (n : ℕ)
    (N : Type v) [AddCommGroup N] [Module R N] : Submodule R N :=
  p ^ n • (⊤ : Submodule R N)

abbrev gradedPiece {R : Type u} [CommRing R] (p : R) (n : ℕ)
    (N : Type v) [AddCommGroup N] [Module R N] :=
  (powerImage p n N) ⧸ (p • (⊤ : Submodule R (powerImage p n N)))

abbrev primaryLayer {R : Type u} [CommRing R] (p : R) (k : ℕ)
    (M : Type v) [AddCommGroup M] [Module R M] :=
  gradedPiece p (k - 1) (primary R p M)

/-- The actual quotient field R/(p), with its canonical quotient ring operations. -/
abbrev residueField {R : Type u} [CommRing R] [IsPrincipalIdealRing R]
    (p : R) (hp : Irreducible p) : Field (R ⧸ Ideal.span {p}) := by
  letI := PrincipalIdealRing.isMaximal_of_irreducible hp
  exact Ideal.Quotient.field _

def PrimaryMembership : Prop :=
  ∀ (R : Type u) [CommRing R] (p : R)
    (M : Type v) [AddCommGroup M] [Module R M] (x : M),
    x ∈ primary R p M ↔ ∃ n : ℕ, p ^ n • x = 0

/-- Under the inclusion into T_p, the denominator of the represented quotient
is exactly p^k T_p. This fixes the subquotient representation explicitly. -/
def LayerDenominator : Prop :=
  ∀ (R : Type u) [CommRing R] (p : R)
    (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ), 1 ≤ k →
    (p • (⊤ : Submodule R (powerImage p (k - 1) (primary R p M)))).map
      (powerImage p (k - 1) (primary R p M)).subtype =
        powerImage p k (primary R p M)

/-- The intrinsic primary part has precisely the coordinates with associated
prime base. This explicitly excludes the free coordinates and all other primes. -/
def PrimaryCoordinates : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r t : ℕ) (q : Fin t → R) (e : Fin t → ℕ),
    (∀ i, Prime (q i) ∧ 0 < e i) →
    ∀ (E : M ≃ₗ[R] ((Fin r → R) × (∀ i, R ⧸ Ideal.span {q i ^ e i})))
      (p : R), Irreducible p → ∀ x : M,
      x ∈ primary R p M ↔
        (E x).1 = 0 ∧ ∀ i, ¬ Associated p (q i) → (E x).2 i = 0

/-- `k≥1` and all empty lists are included. No normalized choice of associates
is required; the coordinate count is invariant under changing representatives. -/
def LayerDimension : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r t : ℕ) (q : Fin t → R) (e : Fin t → ℕ),
    (∀ i, Prime (q i) ∧ 0 < e i) →
    ∀ (_E : M ≃ₗ[R] ((Fin r → R) × (∀ i, R ⧸ Ideal.span {q i ^ e i})))
      (p : R) (hp : Irreducible p) (k : ℕ), 1 ≤ k →
      letI := residueField p hp
      Module.Finite (R ⧸ Ideal.span {p}) (primaryLayer p k M) ∧
      Module.finrank (R ⧸ Ideal.span {p}) (primaryLayer p k M) =
        Nat.card {i : Fin t // Associated p (q i) ∧ k ≤ e i}

def ExponentMultiplicity : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r t : ℕ) (q : Fin t → R) (e : Fin t → ℕ),
    (∀ i, Prime (q i) ∧ 0 < e i) →
    ∀ (_E : M ≃ₗ[R] ((Fin r → R) × (∀ i, R ⧸ Ideal.span {q i ^ e i})))
      (p : R) (hp : Irreducible p) (k : ℕ), 1 ≤ k →
      letI := residueField p hp
      Module.finrank (R ⧸ Ideal.span {p}) (primaryLayer p k M) -
        Module.finrank (R ⧸ Ideal.span {p}) (primaryLayer p (k + 1) M) =
        Nat.card {i : Fin t // Associated p (q i) ∧ e i = k}

/-- An arbitrary linear isomorphism preserves the actual residue-field layers,
not merely the numerical count computed from one chosen decomposition. -/
def LayerInvariant : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (_E : M ≃ₗ[R] N) (p : R) (hp : Irreducible p) (k : ℕ),
    letI := residueField p hp
    Nonempty (primaryLayer p k M ≃ₗ[R ⧸ Ideal.span {p}] primaryLayer p k N)

/-- Bridge to the finite direct sums used by the upstream structure theorem. -/
def DirectSumLayerDimension : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (r t : ℕ) (q : Fin t → R) (e : Fin t → ℕ),
    (∀ i, Prime (q i) ∧ 0 < e i) →
    ∀ (_E : M ≃ₗ[R] ((Fin r → R) ×
        (DirectSum (Fin t) (fun i => R ⧸ Ideal.span {q i ^ e i}))))
      (p : R) (hp : Irreducible p) (k : ℕ), 1 ≤ k →
      letI := residueField p hp
      Module.Finite (R ⧸ Ideal.span {p}) (primaryLayer p k M) ∧
      Module.finrank (R ⧸ Ideal.span {p}) (primaryLayer p k M) =
        Nat.card {i : Fin t // Associated p (q i) ∧ k ≤ e i}

end Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
