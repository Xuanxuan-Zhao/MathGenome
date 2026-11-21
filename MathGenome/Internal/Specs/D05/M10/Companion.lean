import MathGenome.Internal.Specs.D05.M10.Cyclic
import MathGenome.Internal.Specs.D05.M08.Charpoly

/-! Independent specifications for K05.10.companion, paper.tex:1460–1466.
The quotient is the actual polynomial quotient `AdjoinRoot d`, and the
operator multiplies by the residue class of X. Coordinates are columns in
the ordered residue basis. No splitting or characteristic assumption is used.
All theorem statements retain a monic modulus of positive degree; degree one
is included. Finite dimensionality below is constructed from that modulus.
-/

noncomputable section

namespace Specs.D05.M10.Companion

open Polynomial

def multiplication_type :=
  ∀ (K : Type*) [Field K] (d : K[X]), Module.End K (AdjoinRoot d)

def multiplication_value : multiplication_type := fun K _ d =>
  Algebra.lmul K (AdjoinRoot d) (AdjoinRoot.root d)

def quotientBasis_type :=
  ∀ (K : Type*) [Field K] (d : K[X]), d.Monic →
    Module.Basis (Fin d.natDegree) K (AdjoinRoot d)

def quotientBasis_value : quotientBasis_type := fun _ _ _ hd =>
  (AdjoinRoot.powerBasis' hd).basis

/-- Zero based indices: the last column is -c_i; every earlier column
has its single 1 in row j+1. These conditions handle every positive size. -/
def companionMatrix_type :=
  ∀ (K : Type*) [Field K] (d : K[X]), Matrix (Fin d.natDegree) (Fin d.natDegree) K

def companionMatrix_value : companionMatrix_type := fun _ _ d i j =>
  if (j : ℕ) + 1 = d.natDegree then -d.coeff (i : ℕ)
  else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

def multiplication_apply : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]) (z : AdjoinRoot d),
    multiplication_value K d z = AdjoinRoot.mk d X * z

def residue_basis : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]) (hd : d.Monic), 0 < d.natDegree →
    ∀ i, quotientBasis_value K d hd i = AdjoinRoot.mk d (X ^ (i : ℕ))

def matrix_representation : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]) (hd : d.Monic), 0 < d.natDegree →
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value
      (quotientBasis_value K d hd) (quotientBasis_value K d hd)
      (multiplication_value K d) = companionMatrix_value K d

/-- Explicitly records both displayed entry rules and the remaining zeros. -/
def matrix_entries : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    (∀ (i j : Fin d.natDegree), (j : ℕ) + 1 < d.natDegree →
      (i : ℕ) = (j : ℕ) + 1 → companionMatrix_value K d i j = 1) ∧
    (∀ (i j : Fin d.natDegree), (j : ℕ) + 1 = d.natDegree →
      companionMatrix_value K d i j = -d.coeff (i : ℕ)) ∧
    (∀ (i j : Fin d.natDegree), (j : ℕ) + 1 ≠ d.natDegree →
      (i : ℕ) ≠ (j : ℕ) + 1 → companionMatrix_value K d i j = 0)

def size_one : Prop :=
  ∀ {K : Type*} [Field K] (c : K),
    (X + C c : K[X]).natDegree = 1 ∧
      ∀ i j : Fin (X + C c : K[X]).natDegree,
        companionMatrix_value K (X + C c) i j = -c

def one_cyclic : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    Specs.D05.M10.Cyclic.cyclicSpace_value K (AdjoinRoot d)
      (multiplication_value K d) 1 = ⊤

/-- The vector-annihilator IDEAL, before its monic generator is identified. -/
def one_annihilator_ideal : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    Specs.D05.M10.Cyclic.annihilator_value K (AdjoinRoot d)
      (multiplication_value K d) 1 = Ideal.span {d}

def one_annihilator : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]) (hd : d.Monic), 0 < d.natDegree →
    letI : FiniteDimensional K (AdjoinRoot d) := hd.finite_adjoinRoot
    Specs.D05.M10.Cyclic.vectorAnnihilator_value K (AdjoinRoot d)
      (multiplication_value K d) 1 = d

/-- Evaluation on every residue class is multiplication by the residue of p. -/
def evaluation_formula : Prop :=
  ∀ {K : Type*} [Field K] (d p : K[X]) (z : AdjoinRoot d),
    Specs.D05.M08.Evaluation.evaluation_value K (AdjoinRoot d)
      (multiplication_value K d) p z = AdjoinRoot.mk d p * z

def annihilates_iff_one : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    ∀ p : K[X],
      Specs.D05.M08.Evaluation.evaluation_value K (AdjoinRoot d)
        (multiplication_value K d) p = 0 ↔
      Specs.D05.M08.Evaluation.evaluation_value K (AdjoinRoot d)
        (multiplication_value K d) p 1 = 0

def minimal_polynomial : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]) (hd : d.Monic), 0 < d.natDegree →
    letI : FiniteDimensional K (AdjoinRoot d) := hd.finite_adjoinRoot
    Specs.D05.M08.Minpoly.minimalPolynomial_value K (AdjoinRoot d)
      (multiplication_value K d) = d

def characteristic_polynomial : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]) (hd : d.Monic), 0 < d.natDegree →
    letI : FiniteDimensional K (AdjoinRoot d) := hd.finite_adjoinRoot
    Specs.D05.M08.Charpoly.charpoly_value (multiplication_value K d) = d

def matrix_polynomials : Prop :=
  ∀ {K : Type*} [Field K] (d : K[X]), d.Monic → 0 < d.natDegree →
    minpoly K (companionMatrix_value K d) = d ∧
      Matrix.charpoly (companionMatrix_value K d) = d

end Specs.D05.M10.Companion
