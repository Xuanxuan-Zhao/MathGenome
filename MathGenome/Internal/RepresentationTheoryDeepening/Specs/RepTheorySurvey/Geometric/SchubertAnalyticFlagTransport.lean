import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

namespace RepTheorySurvey.Geometric.SchubertAnalyticFlagTransportSpecs

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs
open scoped Matrix.Norms.Elementwise

noncomputable section

section Charts

def GraphChartOpenEmbeddings : Prop :=
  ∀ {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d),
    Topology.IsOpenEmbedding (grassmannianChartPoint b hd I)

/-- The graph-coordinate changes are holomorphic on their actual overlaps. -/
def GraphChartAnalyticTransitions : Prop :=
  ∀ {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (I J : Pivot ι d),
    let U := grassmannianChartPoint b hd I ⁻¹' Set.range (grassmannianChartPoint b hd J)
    IsOpen U ∧
      ∃ F : Matrix (Outside I) (Inside I) ℂ → Matrix (Outside J) (Inside J) ℂ,
        AnalyticOnNhd ℂ F U ∧
        ∀ A ∈ U, grassmannianChartPoint b hd J (F A) = grassmannianChartPoint b hd I A

end Charts

section Flags

/-- In the subquotient `B/A`, the denominator is pulled back along the inclusion of `B`. -/
abbrev FlagQuotient {V : Type} [AddCommGroup V] [Module ℂ V]
    (A B : Submodule ℂ V) := B ⧸ A.comap B.subtype

def GrassmannianFlagIncidence : Prop :=
  ∀ {V ι κ : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A B : Submodule ℂ V), A ≤ B →
    ∀ (b : Module.Basis ι ℂ V) (bQ : Module.Basis κ ℂ (FlagQuotient A B))
      (d : ℕ) (hd : d ≤ Module.finrank ℂ (FlagQuotient A B)),
    ∃ (hD : d + Module.finrank ℂ A ≤ Module.finrank ℂ V)
      (f : GrassmannianPoints bQ hd → GrassmannianPoints b hD),
      Topology.IsClosedEmbedding f ∧
      (∀ p v, v ∈ grassmannianSubspace b hD (f p) ↔
        ∃ x : B, (x : V) = v ∧
          (A.comap B.subtype).mkQ x ∈ grassmannianSubspace bQ hd p) ∧
      Set.range f = {p | A ≤ grassmannianSubspace b hD p ∧ grassmannianSubspace b hD p ≤ B}

/-- Both incidence conditions are affine equations in each ordinary graph chart. -/
def GrassmannianFlagChartEquations : Prop :=
  ∀ {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (A B : Submodule ℂ V), A ≤ B →
    ∀ (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d),
    ∃ (n : ℕ) (F : AffineMap ℂ (Matrix (Outside I) (Inside I) ℂ) (Fin n → ℂ)),
      ∀ M,
        let P := grassmannianSubspace b hd (grassmannianChartPoint b hd I M)
        (A ≤ P ∧ P ≤ B) ↔ F M = 0

/-- The interval `[t^(a+m)L₀,t^a L₀]` sits in `[t^(b+k)L₀,t^b L₀]`.
Taking inverse images adds the tail of length `b+k-(a+m)` and forces the
coefficients at exponents below `a` to vanish. -/
def WindowFlagIncidence : Prop :=
  ∀ (r : ℕ) (a b : ℤ) (m k : ℕ), b ≤ a → a + (m : ℤ) ≤ b + (k : ℤ) →
    let α := (a - b).toNat
    let β := (b + (k : ℤ) - (a + (m : ℤ))).toNat
    let A := latticeSubspace b k (scalarLattice r (a + (m : ℤ)))
    let B := latticeSubspace b k (scalarLattice r a)
    ∃ h : α + m ≤ k,
      A ≤ B ∧ Module.finrank ℂ A = r * β ∧
      Module.finrank ℂ (Window r b k ⧸ B) = r * α ∧
      ∀ d : WindowDimension r a m,
      ∃ (D : WindowDimension r b k) (f : WindowPoints r a m d → WindowPoints r b k D),
        D.val = d.val + r * β ∧ Topology.IsClosedEmbedding f ∧
        Set.range f = {p |
          let P := grassmannianSubspace (windowBasis r b k) (windowDimension_le D) p
          A ≤ P ∧ P ≤ B} ∧
        (∀ p w,
          w ∈ grassmannianSubspace (windowBasis r b k) (windowDimension_le D) (f p) ↔
            (∀ (i : Fin r) (j : Fin k), j.val < α → windowCoordinates r b k w (i, j) = 0) ∧
            (windowCoordinates r a m).symm
                (fun ij ↦ windowCoordinates r b k w
                  (ij.1, ⟨α + ij.2.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left ij.2.isLt α) h⟩)) ∈
              grassmannianSubspace (windowBasis r a m) (windowDimension_le d) p) ∧
        ∀ (L : Lattice r) (p : WindowPoints r a m d),
          (scalarLattice r (a + (m : ℤ))).val ≤ L.val → L.val ≤ (scalarLattice r a).val →
          grassmannianSubspace (windowBasis r a m) (windowDimension_le d) p =
            latticeSubspace a m L →
          grassmannianSubspace (windowBasis r b k) (windowDimension_le D) (f p) =
            latticeSubspace b k L

end Flags

section Transport

abbrev BoundedDimension (N : ℕ) := WindowDimension 2 (-(N : ℤ)) (2 * N)

abbrev BoundedGrassmannian (N : ℕ) (d : BoundedDimension N) : SchemeOver ℂ :=
  (grassmannianCharts (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d)).scheme

/-- The topology on complex points induced by their map to the ordinary Grassmannian. -/
@[instance_reducible] def pointTopology {N : ℕ} {d : BoundedDimension N} {X : SchemeOver ℂ}
    (j : X ⟶ BoundedGrassmannian N d) : TopologicalSpace (Points X complexAlgebra) :=
  TopologicalSpace.induced (fun p ↦ p ≫ j)
    (grassmannianAnalyticTopology (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d))

def pointSubspace {N : ℕ} {d : BoundedDimension N} {X : SchemeOver ℂ}
    (j : X ⟶ BoundedGrassmannian N d) (p : Points X complexAlgebra) :
    Submodule ℂ (BoundedWindow 2 N) :=
  grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d) (p ≫ j)

abbrev PointHomeomorph {N : ℕ} {d : BoundedDimension N} {X : SchemeOver ℂ}
    (j : X ⟶ BoundedGrassmannian N d) (S : Set (BoundedLattice 2 N)) :=
  @Homeomorph (Points X complexAlgebra) S (pointTopology j) inferInstance

def BoundedPointTransport : Prop :=
  ∀ (N : ℕ) (d : BoundedDimension N) (S : Set (BoundedLattice 2 N))
    (X : SchemeOver ℂ) (j : X ⟶ BoundedGrassmannian N d),
    IsImmersion j.left → Function.Injective (boundedPoint (r := 2) (N := N)) →
    (∀ L ∈ S, (boundedPoint L).1 = d) →
    Set.range (fun p : Points X complexAlgebra ↦ p ≫ j) =
      {p : WindowPoints 2 (-(N : ℤ)) (2 * N) d |
        ∃ L ∈ S, grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
          (windowDimension_le d) p = boundedSubspace L} →
    ∃ e : PointHomeomorph j S, ∀ p, pointSubspace j p = boundedSubspace (e p).val

/-- Applies to restriction immersions and to composites over the Grassmannian.
The comparison commutes with the inclusion of the represented lattice subsets,
even when their dimension indices are given by different equal expressions. -/
def BoundedPointTransportCompatibility : Prop :=
  ∀ (N : ℕ) (d e : BoundedDimension N) (h : d = e)
    (S T : Set (BoundedLattice 2 N)) (X Y : SchemeOver ℂ)
    (jX : X ⟶ BoundedGrassmannian N d) (jY : Y ⟶ BoundedGrassmannian N e) (i : X ⟶ Y),
    i ≫ jY = jX ≫ eqToHom (congrArg (BoundedGrassmannian N) h) →
    Function.Injective (boundedPoint (r := 2) (N := N)) →
    ∀ (eX : PointHomeomorph jX S) (eY : PointHomeomorph jY T),
      (∀ p, pointSubspace jX p = boundedSubspace (eX p).val) →
      (∀ q, pointSubspace jY q = boundedSubspace (eY q).val) →
      S ⊆ T ∧
      (∀ p : Points X complexAlgebra, (eY (p ≫ i)).val = (eX p).val) ∧
      @Topology.IsEmbedding _ _ (pointTopology jX) (pointTopology jY)
        (fun p : Points X complexAlgebra ↦ p ≫ i) ∧
      Set.range (fun p : Points X complexAlgebra ↦ eY (p ≫ i)) = {L : T | L.val ∈ S}

end Transport

end
end RepTheorySurvey.Geometric.SchubertAnalyticFlagTransportSpecs
