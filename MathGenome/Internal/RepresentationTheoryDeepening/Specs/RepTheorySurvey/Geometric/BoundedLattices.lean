import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Matrix.Normed

namespace RepTheorySurvey.Geometric.BoundedLatticeSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs
open scoped Matrix MatrixGroups Matrix.Norms.Elementwise

def GLTransitive : Prop :=
  ∀ (r : ℕ) (L : Lattice r), ∃ g : GL (Fin r) K, g • standardLattice r = L

def GLStabilizer : Prop :=
  ∀ r : ℕ, MulAction.stabilizer (GL (Fin r) K) (standardLattice r) = PositiveGL r

def GLCosets : Prop :=
  ∀ r : ℕ, ∃ e : Grassmannian (PositiveGL r) ≃ Lattice r,
    ∀ g : GL (Fin r) K, e (coset (PositiveGL r) g) = g • standardLattice r

def TorusTransitive : Prop :=
  ∀ (r : ℕ) (L : TorusLattice r), ∃ g : Fin r → Kˣ,
    g • (fun _ : Fin r ↦ standardLattice 1) = L

def TorusStabilizer : Prop :=
  ∀ r : ℕ, MulAction.stabilizer (Fin r → Kˣ) (fun _ : Fin r ↦ standardLattice 1) =
    PositiveTorus r

def TorusCosets : Prop :=
  ∀ r : ℕ, ∃ e : Grassmannian (PositiveTorus r) ≃ TorusLattice r,
    ∀ g : Fin r → Kˣ, e (coset (PositiveTorus r) g) =
      g • (fun _ : Fin r ↦ standardLattice 1)

def LatticeExhaustion : Prop :=
  (∀ (r : ℕ) (L : Lattice r), ∃ (N : ℕ) (B : BoundedLattice r N), B.val = L) ∧
  (∀ (r : ℕ) (L : TorusLattice r), ∃ (N : ℕ) (B : BoundedTorus r N), ∀ i, (B i).val = L i)

/-- Lattices between the endpoints of the quotient t^a L₀ / t^(a+m) L₀. -/
abbrev WindowLattice (r : ℕ) (a : ℤ) (m : ℕ) :=
  { L : Lattice r // (scalarLattice r (a + (m : ℤ))).val ≤ L.val ∧
    L.val ≤ (scalarLattice r a).val }

abbrev StableSubspaces (r : ℕ) (a : ℤ) (m : ℕ) :=
  { P : Submodule ℂ (Window r a m) // P.map (windowOperator r a m) ≤ P }

def windowStageSubspace {r : ℕ} {a : ℤ} {m : ℕ} (p : WindowStage r a m) :
    Submodule ℂ (Window r a m) :=
  grassmannianSubspace (windowBasis r a m) (windowDimension_le p.1) p.2.val

private def ambientInverseImage {R M V : Type} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module R M] [Module ℂ M] [IsScalarTower ℂ R M]
    [AddCommGroup V] [Module R V] [Module ℂ V] [IsScalarTower ℂ R V]
    (Q : Submodule R M) (f : M →ₗ[R] V) (P : Submodule ℂ (M ⧸ Q)) :
    Submodule ℂ V :=
  (P.comap (Q.mkQ.restrictScalars ℂ)).map (f.restrictScalars ℂ)

/-- The inverse image in the upper lattice, viewed inside K^r. -/
def windowInverseImage {r : ℕ} {a : ℤ} {m : ℕ} (P : Submodule ℂ (Window r a m)) :
    Submodule ℂ (Coordinates r) :=
  @ambientInverseImage O ((scalarLattice r a).val : Type) (Coordinates r)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (windowLower r a m) (scalarLattice r a).val.subtype P

def WindowLatticeComparison : Prop :=
  ∀ (r : ℕ) (a : ℤ) (m : ℕ),
    ∃ e : WindowLattice r a m ≃ StableSubspaces r a m,
      (∀ L, (e L).val = latticeSubspace a m L.val) ∧
      (∀ P, (e.symm P).val.val.restrictScalars ℂ = windowInverseImage P.val)

def WindowStageComparison : Prop :=
  ∀ (r : ℕ) (a : ℤ) (m : ℕ),
    Function.Bijective (fun L : WindowLattice r a m ↦ windowStagePoint a m L.val) ∧
    ∀ L : WindowLattice r a m,
      windowStageSubspace (windowStagePoint a m L.val) = latticeSubspace a m L.val

def BoundedStageComparison : Prop :=
  ∀ r N : ℕ,
    Function.Bijective (boundedPoint (r := r) (N := N)) ∧
    ∀ L : BoundedLattice r N, windowStageSubspace (boundedPoint L) = boundedSubspace L

def windowSchemeInGrassmannian (r : ℕ) (a : ℤ) (m : ℕ) (d : WindowDimension r a m) :
    windowStableScheme r a m d ⟶
      (grassmannianCharts (windowBasis r a m) (windowDimension_le d)).scheme :=
  reducedClosureInclusion _
    {p | StablePlane (windowBasis r a m) (windowDimension_le d) (windowOperator r a m) p}

def windowSchemeSubspace {r : ℕ} {a : ℤ} {m : ℕ} {d : WindowDimension r a m}
    (q : Points (windowStableScheme r a m d) complexAlgebra) : Submodule ℂ (Window r a m) :=
  grassmannianSubspace (windowBasis r a m) (windowDimension_le d)
    (q ≫ windowSchemeInGrassmannian r a m d)

def WindowSchemeComparison : Prop :=
  ∀ (r : ℕ) (a : ℤ) (m : ℕ) (d : WindowDimension r a m),
    IsReduced (windowStableScheme r a m d).left ∧
    IsClosedImmersion (windowSchemeInGrassmannian r a m d).left ∧
    ∃ e : Points (windowStableScheme r a m d) complexAlgebra ≃
      {L : WindowLattice r a m // Module.finrank ℂ (latticeSubspace a m L.val) = d.val},
      ∀ q, windowSchemeSubspace q = latticeSubspace a m (e q).val.val

/-- A smaller interval embeds by taking the same lattice in the larger interval. -/
def WindowInclusions : Prop :=
  ∀ (r : ℕ) (a b : ℤ) (m k : ℕ), b ≤ a → a + (m : ℤ) ≤ b + (k : ℤ) →
    ∀ d : WindowDimension r a m, ∃ d' : WindowDimension r b k,
      d'.val = d.val + r * ((b + (k : ℤ)) - (a + (m : ℤ))).toNat ∧
      ∃ j : windowStableScheme r a m d ⟶ windowStableScheme r b k d',
        IsClosedImmersion j.left ∧
        ∀ (L : WindowLattice r a m) (q : Points (windowStableScheme r a m d) complexAlgebra),
          windowSchemeSubspace q = latticeSubspace a m L.val →
          windowSchemeSubspace (q ≫ j) = latticeSubspace b k L.val

def BoundedInclusionTopology : Prop :=
  ∀ (r N M : ℕ) (h : N ≤ M), Topology.IsClosedEmbedding (boundedInclusion (r := r) h)

def WindowPositiveStable : Prop :=
  ∀ (r : ℕ) (a : ℤ) (m : ℕ) (g : GL (Fin r) O) (L : WindowLattice r a m),
    (scalarLattice r (a + (m : ℤ))).val ≤ (positiveGLMap r g • L.val).val ∧
    (positiveGLMap r g • L.val).val ≤ (scalarLattice r a).val

/-- The natural truncation from n coefficients to m coefficients, including m = 0. -/
def truncateJet {m n : ℕ} (hmn : m ≤ n) : JetRing n →+* JetRing m :=
  Ideal.Quotient.factor (by
    rw [jetIdeal, jetIdeal, Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow t hmn)

def windowJetLinear {r n : ℕ} (a : ℤ) {m : ℕ} (hmn : m ≤ n)
    (g : Matrix (Fin r) (Fin r) (JetRing n)) : Window r a m →ₗ[ℂ] Window r a m :=
  let e := (windowJets r a m).restrictScalars ℂ
  e.symm.toLinearMap.comp (((g.map (truncateJet hmn)).mulVecLin.restrictScalars ℂ).comp e.toLinearMap)

def GLJetAction : Prop :=
  ∀ (r : ℕ) (a : ℤ) (m n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n),
    ∃ ρ : MulAction (GLJets r n hn) (WindowStage r a m),
      (∀ (g : GLJets r n hn) (p : WindowStage r a m),
        windowStageSubspace (ρ.smul g p) =
          (windowStageSubspace p).map (windowJetLinear a hmn g.val)) ∧
      (∀ (g : GL (Fin r) O) (L : Lattice r),
        ρ.smul (reduceGL r n hn g) (windowStagePoint a m L) =
          windowStagePoint a m (positiveGLMap r g • L)) ∧
      Continuous (fun x : GLJets r n hn × WindowStage r a m ↦ ρ.smul x.1 x.2)

abbrev WindowIndex (r m : ℕ) := Fin r × Fin m

abbrev JetMatrixCoefficients (r n : ℕ) := Matrix (Fin r) (Fin r) (Fin n → ℂ)

def jetMatrixCoefficients {r n : ℕ} (g : Matrix (Fin r) (Fin r) (JetRing n)) :
    JetMatrixCoefficients r n :=
  g.map (jetCoefficients n)

/-- Joint analyticity in jet and graph coordinates, expressed by local holomorphic
extensions in the ordinary Grassmannian charts. It applies also on singular stable loci. -/
def GLJetChartAnalytic : Prop :=
  ∀ (r : ℕ) (a : ℤ) (m n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (d : WindowDimension r a m) (I : Pivot (WindowIndex r m) d.val)
    (g : GLJets r n hn) (A : Matrix (Outside I) (Inside I) ℂ),
    let B := jetMatrixCoefficients g.val
    ∃ (J : Pivot (WindowIndex r m) d.val)
      (U : Set (JetMatrixCoefficients r n × Matrix (Outside I) (Inside I) ℂ))
      (F : JetMatrixCoefficients r n × Matrix (Outside I) (Inside I) ℂ →
        Matrix (Outside J) (Inside J) ℂ),
      (B, A) ∈ U ∧ IsOpen U ∧ AnalyticOnNhd ℂ F U ∧
      ∀ (h : GLJets r n hn) (C : Matrix (Outside I) (Inside I) ℂ),
        (jetMatrixCoefficients h.val, C) ∈ U →
        let b := windowBasis r a m
        let hd := windowDimension_le d
        (grassmannianSubspace b hd (grassmannianChartPoint b hd I C)).map
            (windowJetLinear a hmn h.val) =
          grassmannianSubspace b hd
            (grassmannianChartPoint b hd J (F (jetMatrixCoefficients h.val, C)))

def TorusJetAction : Prop :=
  ∀ (r N n : ℕ) (hn : 1 ≤ n) (hmn : 2 * N ≤ n),
    ∃ ρ : MulAction (TorusJets r n hn) (Fin r → BoundedStage 1 N),
      (∀ (g : TorusJets r n hn) (p : Fin r → BoundedStage 1 N) (i : Fin r),
        windowStageSubspace (ρ.smul g p i) = (windowStageSubspace (p i)).map
          (windowJetLinear (-(N : ℤ)) hmn (Matrix.diagonal fun _ : Fin 1 ↦ (g i).val))) ∧
      (∀ (g : Fin r → Oˣ) (L : TorusLattice r),
        ρ.smul (reduceTorus r n hn g) (fun i ↦ windowStagePoint (-(N : ℤ)) (2 * N) (L i)) =
          fun i ↦ windowStagePoint (-(N : ℤ)) (2 * N) ((positiveTorusMap r g • L) i)) ∧
      Continuous (fun x : TorusJets r n hn × (Fin r → BoundedStage 1 N) ↦ ρ.smul x.1 x.2)

end

end RepTheorySurvey.Geometric.BoundedLatticeSpecs
