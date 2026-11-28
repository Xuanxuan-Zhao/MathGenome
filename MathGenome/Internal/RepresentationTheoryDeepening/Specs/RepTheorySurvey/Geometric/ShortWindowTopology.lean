import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.BoundedLattices

namespace RepTheorySurvey.Geometric.ShortWindowTopologySpecs

noncomputable section

open LatticeModelSpecs BoundedLatticeSpecs

/-- The upper lattice of the short window lies in the upper lattice of the symmetric window. -/
theorem standard_le_symmetricUpper (m : ℕ) :
    (scalarLattice 2 0).val ≤ (scalarLattice 2 (-(m : ℤ))).val :=
  diagonalLattice_le (fun _ ↦ neg_nonpos.mpr (Int.natCast_nonneg m))

def upperInclusion (m : ℕ) :
    (scalarLattice 2 0).val →ₗ[O] (scalarLattice 2 (-(m : ℤ))).val :=
  Submodule.inclusion (standard_le_symmetricUpper m)

/-- The projection of an upper lattice to its actual window quotient. -/
def windowQuotient (a : ℤ) (m : ℕ) : (scalarLattice 2 a).val →ₗ[O] Window 2 a m :=
  @Submodule.mkQ O ((scalarLattice 2 a).val : Type)
    inferInstance inferInstance inferInstance (windowLower 2 a m)

/-- The coefficient at degree `j` in the short window is at position `m+j` in the
shifted coordinates of the symmetric window. -/
def windowIndexEmbedding (m : ℕ) : (Fin 2 × Fin m) ↪ (Fin 2 × Fin (2 * m)) where
  toFun ij := (ij.1, ⟨m + ij.2.val, by have := ij.2.isLt; omega⟩)
  inj' := by
    intro x y h
    refine Prod.ext (congrArg (fun ij : Fin 2 × Fin (2 * m) ↦ ij.1) h) (Fin.ext ?_)
    exact Nat.add_left_cancel (congrArg (fun ij : Fin 2 × Fin (2 * m) ↦ ij.2.val) h)

/-- The image of the standard lattice in the symmetric window. -/
def standardSupport (m : ℕ) : Submodule ℂ (BoundedWindow 2 m) :=
  latticeSubspace (-(m : ℤ)) (2 * m) (scalarLattice 2 0)

/-- Lattices in the short window whose quotient plane has dimension `m`. The
subtype topology is induced by the actual lattice union. -/
abbrev ShortLattice (m : ℕ) :=
  { L : GL2Lattice // (scalarLattice 2 (m : ℤ)).val ≤ L.val ∧
    L.val ≤ (scalarLattice 2 0).val ∧ Module.finrank ℂ (latticeSubspace 0 m L) = m }

def shortAsBounded {m : ℕ} (L : ShortLattice m) : BoundedLattice 2 m :=
  ⟨L.val, L.property.1, L.property.2.1.trans (standard_le_symmetricUpper m)⟩

def symmetricDimension (m : ℕ) : WindowDimension 2 (-(m : ℤ)) (2 * m) :=
  ⟨m, Nat.lt_succ_of_le (by
    rw [Module.finrank_eq_card_basis (windowBasis 2 (-(m : ℤ)) (2 * m))]
    simp
    omega)⟩

abbrev SymmetricStablePoints (m : ℕ) :=
  StablePoints (windowBasis 2 (-(m : ℤ)) (2 * m))
    (windowDimension_le (symmetricDimension m)) (windowOperator 2 (-(m : ℤ)) (2 * m))

abbrev SupportedStablePoints (m : ℕ) :=
  { p : SymmetricStablePoints m //
    grassmannianSubspace (windowBasis 2 (-(m : ℤ)) (2 * m))
      (windowDimension_le (symmetricDimension m)) p.val ≤ standardSupport m }

/-- The linear comparison of the actual quotients, including the full coordinate formula. -/
def WindowLinearComparison : Prop :=
  ∀ m : ℕ, m = 1 ∨ m = 2 →
    ∃ q : Window 2 0 m →ₗ[O] BoundedWindow 2 m,
      (∀ x : (scalarLattice 2 0).val,
        q (windowQuotient 0 m x) = windowQuotient (-(m : ℤ)) (2 * m) (upperInclusion m x)) ∧
      let f := q.restrictScalars ℂ
      Function.Injective f ∧
      f.range = standardSupport m ∧
      (∀ w, f (windowOperator 2 0 m w) = windowOperator 2 (-(m : ℤ)) (2 * m) (f w)) ∧
      (∀ L : WindowLattice 2 0 m,
        (latticeSubspace 0 m L.val).map f = latticeSubspace (-(m : ℤ)) (2 * m) L.val) ∧
      (∀ (w : Window 2 0 m) (i : Fin 2) (j : Fin (2 * m)), j.val < m →
        windowCoordinates 2 (-(m : ℤ)) (2 * m) (f w) (i, j) = 0) ∧
      (∀ (w : Window 2 0 m) (ij : Fin 2 × Fin m),
        windowCoordinates 2 (-(m : ℤ)) (2 * m) (f w) (windowIndexEmbedding m ij) =
          windowCoordinates 2 0 m w ij)

/-- The analytic comparison using the point of the symmetric stage of the same lattice. -/
def ShortWindowHomeomorphism : Prop :=
  ∀ m : ℕ, m = 1 ∨ m = 2 →
    ∃ e : ShortLattice m ≃ₜ SupportedStablePoints m,
      (∀ L, (⟨symmetricDimension m, (e L).val⟩ : BoundedStage 2 m) =
        boundedPoint (shortAsBounded L)) ∧
      ∀ L, grassmannianSubspace (windowBasis 2 (-(m : ℤ)) (2 * m))
        (windowDimension_le (symmetricDimension m)) (e L).val.val =
        boundedSubspace (shortAsBounded L)

end

end RepTheorySurvey.Geometric.ShortWindowTopologySpecs
