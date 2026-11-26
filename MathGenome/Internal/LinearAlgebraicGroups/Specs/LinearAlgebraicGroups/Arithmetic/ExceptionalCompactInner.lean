import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ComplexExceptionalDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineCorootStabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLieAutomorphismTransport
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Covering.Basic

noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open scoped Matrix unitInterval

namespace LinearAlgebraicGroups.Specs.ExceptionalCompactInner

open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open IntegralModels (MatrixRealization)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open LieAlgebrasAndRepresentations.RealForms (Conjugation)

/-- The exceptional types in scope, attached to a Borel pair on the
geometric scalar extension of the given group. -/
abbrev HasExceptionalType := ComplexExceptionalDatum.HasExceptionalType

/-- Conjugation from the ground field ℝ, on the functor of points of the given group. -/
abbrev realConjugation (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G) :
    PointsIn i ℂ →* PointsIn i ℂ :=
  ExceptionalLieAutomorphismTransport.realConjugation G

/-- The inclusion on the actual points given by ℝ → ℂ. -/
def realToComplex (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G) :
    PointsIn i ℝ →* PointsIn i ℂ :=
  (((groupPointsFunctor ℝ).obj G.val).map (CommAlgCat.ofHom (Algebra.ofId ℝ ℂ))).hom

/-- A complex algebraic action on points is induced by an automorphism
of the scalar-extended group scheme. -/
abbrev ActsOnComplexPoints {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    (a : Aut ((groupBaseChange ℝ ℂ).obj G.val))
    (f : PointsIn i ℂ → PointsIn i ℂ) : Prop :=
  ExceptionalLieAutomorphismTransport.ActsOnComplexPoints G a f

def IsAlgebraicOnComplexPoints {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    (f : PointsIn i ℂ → PointsIn i ℂ) : Prop :=
  ∃ a, ActsOnComplexPoints a f

/-- The differential of the antiholomorphic action (a \sigma) on
the identity tangent of the actual complex group is a compact conjugation.
The scalar-extension comparison and coefficient conjugation use dual-number
points. -/
def HasCompactDifferential {G : AffineAlgebraicGroup ℝ}
    (a : Aut ((groupBaseChange ℝ ℂ).obj G.val)) : Prop :=
  let H := (groupBaseChange ℝ ℂ).obj G.val
  ∃ s : IdentityLieStructure H,
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ τ : Conjugation (Lie ℂ H),
      _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures.IsCompact τ ∧
      let onDual := ExceptionalLieAutomorphismTransport.onDual G
      let conjugate := ExceptionalLieAutomorphismTransport.dualConjugation
      ∀ x : Lie ℂ H, ∃ y : Lie ℂ H,
        onDual y.toMul.val = mapPoints conjugate (onDual x.toMul.val) ∧
        τ.map x = mapPointKernel a.asIso.hom y

/-- The subgroup fixed by an automorphism of the point group. -/
def fixedSubgroup {H : Type*} [Group H] (f : MulAut H) : Subgroup H where
  carrier := {x | f x = x}
  one_mem' := map_one f
  mul_mem' := fun {x y} hx hy =>
    (map_mul f x y).trans (congrArg₂ (· * ·) hx hy)
  inv_mem' := fun {x} hx => (map_inv f x).trans (congrArg Inv.inv hx)

/-- An equivariant strong deformation onto the compact fixed group.
Both endpoint conditions are with respect to the subspace topology. -/
structure CompactRetraction {H : Type*} [Group H] [TopologicalSpace H]
    (ω θ : MulAut H) where
  homotopy : C(unitInterval × H, H)
  start (x : H) : homotopy (0, x) = x
  endpoint (x : H) : homotopy (1, x) ∈ fixedSubgroup ω
  stationary (t : unitInterval) (x : H) : x ∈ fixedSubgroup ω → homotopy (t, x) = x
  equivariant (t : unitInterval) (x : H) :
    homotopy (t, θ (ω x)) = θ (ω (homotopy (t, x)))

/-- The compact deformation is compatible with a deformation on the actual
finite central adjoint quotient, whose complex points form a covering. -/
def IsLiftFromAdjoint {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
    {ω θ : MulAut (PointsIn i ℂ)} (r : CompactRetraction ω θ) : Prop :=
  ∃ (Q : AffineAlgebraicGroup ℝ) (j : MatrixRealization Q)
    (Z : ClosedSubgroup G.val) (q : G.val ⟶ Q.val),
    AdjointCocharacters.IsAdjointQuotient Z q ∧ CentralIsogenies.IsCentralIsogeny q ∧
    let p : PointsIn i ℂ →* PointsIn j ℂ :=
      (((groupPointsFunctor ℝ).map q).app (CommAlgCat.of ℝ ℂ)).hom
    IsCoveringMap p ∧ Function.Surjective p ∧
    ∃ (ω' θ' : MulAut (PointsIn j ℂ)) (r' : CompactRetraction ω' θ'),
      (∀ x, p (ω x) = ω' (p x)) ∧ (∀ x, p (θ x) = θ' (p x)) ∧
      (∀ x, p x ∈ fixedSubgroup ω' ↔ x ∈ fixedSubgroup ω) ∧
      ConnectedSpace (fixedSubgroup ω') ∧
      ∀ t x, p (r.homotopy (t, x)) = r'.homotopy (t, p x)

/-- The compact model and inner-case connectedness for the original real
algebraic group. The reference real structure comes from base-field
conjugation and its fixed points are the actual real points. -/
def CompactInnerStatement : Prop :=
  ∀ (G : AffineAlgebraicGroup ℝ) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → HasExceptionalType G →
    ∃ (ω θ c : MulAut (PointsIn i ℂ)),
      Continuous ω ∧ Continuous θ ∧ Continuous c ∧ Continuous c.symm ∧
      (∃ a, ActsOnComplexPoints a (fun x => ω (realConjugation G i x)) ∧
        HasCompactDifferential a) ∧
      IsAlgebraicOnComplexPoints (fun x => θ x) ∧
      IsAlgebraicOnComplexPoints (fun x => c x) ∧
      Function.Involutive ω ∧ Function.Involutive θ ∧ Function.Commute θ ω ∧
      (∀ x, c (realConjugation G i x) = θ (ω (c x))) ∧
      IsEmbedding (realToComplex G i) ∧
      Set.range (realToComplex G i) = {x | realConjugation G i x = x} ∧
      CompactSpace (fixedSubgroup ω) ∧ ConnectedSpace (fixedSubgroup ω) ∧
      (∃ r : CompactRetraction ω θ, IsLiftFromAdjoint r) ∧
      ((∃ t : PointsIn i ℂ, θ = MulAut.conj t) →
        (∃ t : fixedSubgroup ω, θ = MulAut.conj t.val) ∧
        ConnectedSpace ({x : fixedSubgroup ω | θ x.val = x.val} : Set (fixedSubgroup ω)) ∧
        ConnectedSpace (PointsIn i ℝ))

/-- The three highest-root coefficient vectors in Bourbaki numbering,
with zero-based indices. In these simply laced types the highest coroot
has these same coefficients in the simple-coroot basis. -/
def e6Highest : Fin 6 → ℤ := ![1, 2, 2, 3, 2, 1]
def e7Highest : Fin 7 → ℤ := ![2, 2, 3, 4, 3, 2, 1]
def e8Highest : Fin 8 → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

/-- The vertex opposite the i-th simple wall satisfies the simple-root
values δᵢⱼ/mᵢ, with x written in the simple-coroot basis. -/
def IsNonzeroAlcoveVertex {n : ℕ} (m : Fin n → ℤ) (i : Fin n) (x : Fin n → ℝ) : Prop :=
  ∀ j, (m i : ℝ) * (∑ k, x k * (CartanMatrix.E n k j : ℝ)) = (Pi.single i 1 : Fin n → ℝ) j

/-- Computations in the E-type coroot coordinates used by the affine
Weyl argument. The bound on all roots identifies the stated vector
as the highest root. The last clause excludes every nonzero vertex
from the full simple-coroot lattice. -/
abbrev HighestRootAndVertices {n : ℕ} (m : Fin n → ℤ) : Prop :=
  ExceptionalAffineCorootStabilizers.HighestRootAndVertices m

def ExceptionalAlcoveStatement : Prop :=
  HighestRootAndVertices e6Highest ∧
  HighestRootAndVertices e7Highest ∧
  HighestRootAndVertices e8Highest ∧
  CartanMatrix.E 6 *ᵥ (![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) = Pi.single 0 3 ∧
  CartanMatrix.E 6 *ᵥ (![2, 3, 4, 6, 5, 4] : Fin 6 → ℤ) = Pi.single 5 3 ∧
  CartanMatrix.E 7 *ᵥ (![2, 3, 4, 6, 5, 4, 3] : Fin 7 → ℤ) = Pi.single 6 2

end LinearAlgebraicGroups.Specs.ExceptionalCompactInner
