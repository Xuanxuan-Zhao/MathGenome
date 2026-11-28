import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.BoundedLattices

namespace RepTheorySurvey.Geometric.MinusculeAndTwoStepSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver)
open LatticeModelSpecs BoundedLatticeSpecs

abbrev V := Fin 2 → ℂ

/-- When L is contained in L₀, this is the O-module L₀ / L. -/
abbrev StandardQuotient (L : GL2Lattice) :=
  @HasQuotient.Quotient _ _ (@Submodule.hasQuotient O ((scalarLattice 2 0).val : Type)
    inferInstance inferInstance inferInstance) (L.val.comap (scalarLattice 2 0).val.subtype)

def colength (m : ℕ) : Set GL2Lattice :=
  {L | L.val ≤ (scalarLattice 2 0).val ∧
    Module.Finite ℂ (StandardQuotient L) ∧ Module.finrank ℂ (StandardQuotient L) = m}

abbrev Colength (m : ℕ) := ↥(colength m)

def minusculePair : DominantPair := ⟨(1, 0), by decide⟩
def twoStepPair : DominantPair := ⟨(2, 0), by decide⟩
def scalarPair : DominantPair := ⟨(1, 1), by decide⟩
abbrev scalarPoint : GL2Lattice := scalarLattice 2 1

/-- Reduction of the window of length one to the constant coefficient. -/
def constantCoordinates : Window 2 0 1 ≃ₗ[ℂ] V :=
  windowCoordinates 2 0 1 ≪≫ₗ
    { toFun := fun x i ↦ x (i, 0)
      invFun := fun x ij ↦ x ij.1
      left_inv := by
        intro x
        funext ij
        exact congrArg x (Prod.ext rfl (Subsingleton.elim (0 : Fin 1) ij.2))
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Constant and linear coefficients in L₀ / t² L₀, in that order. -/
def twoStepCoordinates : Window 2 0 2 ≃ₗ[ℂ] (V × V) :=
  windowCoordinates 2 0 2 ≪≫ₗ
    { toFun := fun x ↦ (fun i ↦ x (i, 0), fun i ↦ x (i, 1))
      invFun := fun x ij ↦ if ij.2 = 0 then x.1 ij.1 else x.2 ij.1
      left_inv := by
        intro x
        funext ⟨i, j⟩
        fin_cases j <;> rfl
      right_inv := by intro x; rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

def shift : (V × V) →ₗ[ℂ] (V × V) :=
  (LinearMap.inr ℂ V V).comp (LinearMap.fst ℂ V V)

def projectiveBasis : Module.Basis (Fin 2 × Fin 1) ℂ V :=
  (windowBasis 2 0 1).map constantCoordinates

def twoStepBasis : Module.Basis (Fin 2 × Fin 2) ℂ (V × V) :=
  (windowBasis 2 0 2).map twoStepCoordinates

theorem projectiveRank : 1 ≤ Module.finrank ℂ V := by
  simp [V]

theorem twoStepRank : 2 ≤ Module.finrank ℂ (V × V) := by
  simp [V, Module.finrank_prod]

/-- Projective space of lines in V, with the ordinary Grassmannian charts. -/
def projectiveScheme : SchemeOver ℂ :=
  (grassmannianCharts projectiveBasis projectiveRank).scheme

abbrev ProjectivePoints := GrassmannianPoints projectiveBasis projectiveRank

def twoStepScheme : SchemeOver ℂ := stableScheme twoStepBasis twoStepRank shift

abbrev TwoStepPoints := StablePoints twoStepBasis twoStepRank shift

def twoStepSchemeInGrassmannian :
    twoStepScheme ⟶ (grassmannianCharts twoStepBasis twoStepRank).scheme :=
  reducedClosureInclusion _ {p | StablePlane twoStepBasis twoStepRank shift p}

theorem shortWindowRank (m : ℕ) : m ≤ Module.finrank ℂ (Window 2 0 m) := by
  rw [Module.finrank_eq_card_basis (windowBasis 2 0 m)]
  simp
  omega

def shortDimension (m : ℕ) : WindowDimension 2 0 m :=
  ⟨m, Nat.lt_succ_of_le (shortWindowRank m)⟩

theorem standardBoundRank (m : ℕ) : m ≤ Module.finrank ℂ (BoundedWindow 2 m) := by
  rw [Module.finrank_eq_card_basis (windowBasis 2 (-(m : ℤ)) (2*m))]
  simp
  omega

/-- At bound m, a lattice of colength m in L₀ has plane dimension m. -/
def standardBoundDimension (m : ℕ) : WindowDimension 2 (-(m : ℤ)) (2*m) :=
  ⟨m, Nat.lt_succ_of_le (standardBoundRank m)⟩

def MinusculeOrbit : Prop :=
  colength 1 = gl2Orbit minusculePair ∧
  ∀ L : Colength 1, scalarPoint.val ≤ L.val.val

def TwoStepOrbits : Prop :=
  (∀ L : Colength 2, (scalarLattice 2 2).val ≤ L.val.val) ∧
  gl2Orbit scalarPair = {scalarPoint} ∧
  gl2Orbit twoStepPair = colength 2 \ {scalarPoint} ∧
  scalarPoint ∈ colength 2 ∧
  IsClosed (gl2Orbit scalarPair) ∧
  IsOpen ((Subtype.val : Colength 2 → GL2Lattice) ⁻¹' gl2Orbit twoStepPair) ∧
  closure (gl2Orbit twoStepPair) = colength 2

def MinusculeProjective : Prop :=
  (∃ e : Colength 1 ≃ₜ ProjectivePoints,
    (∀ L, grassmannianSubspace projectiveBasis projectiveRank (e L) =
      (latticeSubspace 0 1 L.val).map constantCoordinates.toLinearMap) ∧
    (∀ p, (e.symm p).val.val.restrictScalars ℂ =
      windowInverseImage ((grassmannianSubspace projectiveBasis projectiveRank p).map
        constantCoordinates.symm.toLinearMap))) ∧
  ∃ e : windowStableScheme 2 0 1 (shortDimension 1) ≅ projectiveScheme,
    ∀ q : Points (windowStableScheme 2 0 1 (shortDimension 1)) complexAlgebra,
      grassmannianSubspace projectiveBasis projectiveRank (q ≫ e.hom) =
        (windowSchemeSubspace q).map constantCoordinates.toLinearMap

def TwoStepStableModel : Prop :=
  (∀ w, twoStepCoordinates (windowOperator 2 0 2 w) = shift (twoStepCoordinates w)) ∧
  (∃ e : Colength 2 ≃ₜ TwoStepPoints,
    (∀ L, grassmannianSubspace twoStepBasis twoStepRank (e L).val =
      (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap) ∧
    (∀ p, (e.symm p).val.val.restrictScalars ℂ =
      windowInverseImage ((grassmannianSubspace twoStepBasis twoStepRank p.val).map
        twoStepCoordinates.symm.toLinearMap))) ∧
  IsReduced twoStepScheme.left ∧ IsClosedImmersion twoStepSchemeInGrassmannian.left ∧
  ∃ e : windowStableScheme 2 0 2 (shortDimension 2) ≅ twoStepScheme,
    ∀ q : Points (windowStableScheme 2 0 2 (shortDimension 2)) complexAlgebra,
      grassmannianSubspace twoStepBasis twoStepRank (q ≫ e.hom ≫ twoStepSchemeInGrassmannian) =
        (windowSchemeSubspace q).map twoStepCoordinates.toLinearMap

/-- Realize the shorter window as the reduced orbit closure in the canonical
symmetric bound, comparing the inclusions on actual complex points. -/
def SchubertRealization (m : ℕ) (ab : DominantPair) : Prop :=
  ∀ h : OrbitBound ab m,
    let X := schubertScheme ab m h (standardBoundDimension m)
    let P := windowStableScheme 2 0 m (shortDimension m)
    let b := windowBasis 2 (-(m : ℤ)) (2*m)
    let hd := windowDimension_le (standardBoundDimension m)
    let G := (grassmannianCharts b hd).scheme
    let j : X ⟶ G := reducedClosureInclusion G
      (schubertOrbitPoints ab m h (standardBoundDimension m))
    IsReduced X.left ∧ IsClosedImmersion j.left ∧
    ∃ (e : P ≅ X) (latticeOfPoint : Points P complexAlgebra ≃ Colength m),
      ∀ q,
        windowSchemeSubspace q = latticeSubspace 0 m (latticeOfPoint q).val ∧
        grassmannianSubspace b hd (q ≫ e.hom ≫ j) =
          latticeSubspace (-(m : ℤ)) (2*m) (latticeOfPoint q).val

def SmallSchubertSchemes : Prop :=
  (OrbitBound minusculePair 1 ∧ SchubertRealization 1 minusculePair) ∧
  (OrbitBound twoStepPair 2 ∧ SchubertRealization 2 twoStepPair)

end

end RepTheorySurvey.Geometric.MinusculeAndTwoStepSpecs
