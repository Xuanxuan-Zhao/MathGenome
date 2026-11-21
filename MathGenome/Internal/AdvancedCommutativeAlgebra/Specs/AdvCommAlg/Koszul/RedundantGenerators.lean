import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.TensorDecomposition

/-! RK-06, paper.tex:2240–2257, redundancy and the invariant threshold.
All rings are commutative with identity; the zero ring and arbitrary coefficient
modules are allowed. `IsGreatest` spells out the maximum in the source and
includes nonvanishing in that degree. -/
open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def redundantZeroIso : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R),
  (∀ a ∈ y, a ∈ listIdeal x) →
    Nonempty (coefficientComplex M (x ++ y) ≅
      coefficientComplex M (x ++ List.replicate y.length (0 : R)))

/-- The zero exterior factor is the actual Koszul complex of the zero linear form. -/
def zeroExteriorDifferential : Prop := ∀ {R : Type u} [CommRing R] (s n : ℕ),
  differential (0 : (Fin s → R) →ₗ[R] R) n = 0

/-- The tensor product is Mathlib's signed total tensor product, with the
coefficient module already in the first factor. -/
def redundantTensorIso : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R),
  (∀ a ∈ y, a ∈ listIdeal x) →
    Nonempty (coefficientComplex M (x ++ y) ≅
      HomologicalComplex.mapBifunctor (coefficientComplex M x)
        (complex (0 : (Fin y.length → R) →ₗ[R] R)) moduleTensor (.down ℕ))

/-- Boundedness and H₀=M/(x)M ensure that the maximum is defined. -/
def homologyGreatest : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  Nontrivial (M ⧸ listSubmodule M x) →
    ∃ t : ℕ, IsGreatest {q : ℕ | Nontrivial (homology M x q)} t

/-- Adding s redundant generators raises the largest nonzero degree by s. -/
def redundantHomologyGreatest : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R),
  (∀ a ∈ y, a ∈ listIdeal x) → Nontrivial (M ⧸ listSubmodule M x) →
    ∀ t : ℕ, IsGreatest {q : ℕ | Nontrivial (homology M x q)} t →
      IsGreatest {q : ℕ | Nontrivial (homology M (x ++ y) q)} (t + y.length)

/-- Independence of the generating list, with no locality, Noetherianity,
finiteness of M, or properness of an individual entry assumed. -/
def generatorThresholdInvariant : Prop := ∀ {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (x y : List R),
  listIdeal x = listIdeal y → Nontrivial (M ⧸ listSubmodule M x) →
    ∃ t u : ℕ, IsGreatest {q : ℕ | Nontrivial (homology M x q)} t ∧
      IsGreatest {q : ℕ | Nontrivial (homology M y q)} u ∧
      x.length - t = y.length - u

end Specs.AdvCommAlg.Koszul
