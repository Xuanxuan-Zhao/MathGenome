import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.BoundedLattices
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Polynomial.Basic

namespace RepTheorySurvey.Geometric.TorusStageSpecs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open LatticeModelSpecs BoundedLatticeSpecs

noncomputable section

/-- Coweights with every coordinate in the integral interval [-N,N]. -/
abbrev BoundedCoweight (r N : ℕ) :=
  { w : Coweight r // ∀ i, -(N : ℤ) ≤ w i ∧ w i ≤ N }

def enlargeCoweight {r N M : ℕ} (h : N ≤ M) (w : BoundedCoweight r N) :
    BoundedCoweight r M :=
  ⟨w.val, fun i ↦ ⟨(neg_le_neg (Int.ofNat_le.mpr h)).trans (w.property i).1,
    (w.property i).2.trans (Int.ofNat_le.mpr h)⟩⟩

def enlargeTorusLattice {r N M : ℕ} (h : N ≤ M) (L : BoundedTorus r N) :
    BoundedTorus r M :=
  fun i ↦ boundedInclusion h (L i)

def forgetTorusBound {r N : ℕ} (L : BoundedTorus r N) : TorusLattice r :=
  fun i ↦ (L i).val

abbrev PolynomialTruncation (m : ℕ) :=
  Polynomial ℂ ⧸ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ m}

/-- The class of a polynomial in the truncated polynomial ring. -/
def truncatedPolynomial {m : ℕ} (f : Polynomial ℂ) : PolynomialTruncation m :=
  Ideal.Quotient.mk _ f

/-- A cyclic model for the window, taking the class of 1 to the class of t^a. -/
def RankOneCyclicWindow : Prop :=
  ∀ (a : ℤ) (m : ℕ), ∃ e : PolynomialTruncation m ≃ₗ[ℂ] Window 1 a m,
    e 1 = (windowLower 1 a m).mkQ (shiftedCoordinates 1 a (fun _ ↦ 1)) ∧
    ∀ x : PolynomialTruncation m,
      e (truncatedPolynomial Polynomial.X * x) = windowOperator 1 a m (e x)

/-- The stable subspaces are the images of the powers t^(a+d)O, including the
zero subspace at d = m. The image at d has dimension m-d. -/
def RankOneStableSubspaces : Prop :=
  ∀ (a : ℤ) (m : ℕ),
    (∀ P : StableSubspaces 1 a m, ∃! d : Fin (m + 1),
      P.val = latticeSubspace a m (scalarLattice 1 (a + (d.val : ℤ)))) ∧
    (∀ d : Fin (m + 1),
      Module.finrank ℂ (latticeSubspace a m (scalarLattice 1 (a + (d.val : ℤ)))) =
        m - d.val)

/-- Bound-preserving lattice labels and the natural inclusions between stages. -/
def BoundedTorusPoints : Prop :=
  ∀ r : ℕ, ∃ e : ∀ N : ℕ, BoundedCoweight r N ≃ BoundedTorus r N,
    (∀ (N : ℕ) (w : BoundedCoweight r N),
      forgetTorusBound (e N w) = torusLatticeAt r w.val) ∧
    (∀ N : ℕ, Finite (BoundedCoweight r N) ∧ DiscreteTopology (BoundedTorus r N)) ∧
    (∀ {N M : ℕ} (h : N ≤ M) (w : BoundedCoweight r N),
      enlargeTorusLattice h (e N w) = e M (enlargeCoweight h w))

/-- All coweights occur, the analytic topology on the union is discrete, and
the identification with the loop quotient respects the monomial representatives
and the positive-loop action. -/
def TorusPoints : Prop :=
  ∀ r : ℕ,
    ∃ (e : Coweight r ≃ TorusLattice r) (q : Grassmannian (PositiveTorus r) ≃ TorusLattice r),
      (∀ w, e w = torusLatticeAt r w) ∧
      (∀ g : Fin r → Kˣ, q (coset (PositiveTorus r) g) =
        g • (fun _ : Fin r ↦ standardLattice 1)) ∧
      (∀ w, q (coset (PositiveTorus r) (torusMonomial r w)) = e w) ∧
      (∀ L : TorusLattice r, ∃ (N : ℕ) (B : BoundedTorus r N), forgetTorusBound B = L) ∧
      @DiscreteTopology (TorusLattice r) (torusAnalyticTopology r) ∧
      (∀ (u : PositiveTorus r) (x : Grassmannian (PositiveTorus r)),
        (u : Fin r → Kˣ) • x = x) ∧
      (∀ (u : PositiveTorus r) (L : TorusLattice r), (u : Fin r → Kˣ) • L = L)

abbrev TorusStageDimensions (r N : ℕ) :=
  Fin r → WindowDimension 1 (-(N : ℤ)) (2 * N)

/-- The whole reduced stage, with all dimension components of the product model. -/
def boundedTorusScheme (r N : ℕ) : SchemeOver ℂ :=
  ∐ fun d : TorusStageDimensions r N ↦ torusStageScheme r N d

/-- The complex point as a scheme over ℂ. -/
abbrev complexPointScheme : SchemeOver ℂ :=
  (testSpec ℂ).obj (op complexAlgebra)

/-- The constant point scheme indexed by the bounded coweights. -/
def labelledPointScheme (r N : ℕ) : SchemeOver ℂ :=
  ∐ fun _ : BoundedCoweight r N ↦ complexPointScheme

/-- The complex point of the stage attached to a coweight by a stage isomorphism
has the given lattice, measured in the original stable Grassmannian model. -/
def HasStageLattice {r N : ℕ} (q : Points (boundedTorusScheme r N) complexAlgebra)
    (L : TorusLattice r) : Prop :=
  ∃ (d : TorusStageDimensions r N) (p : Points (torusStageScheme r N d) complexAlgebra),
    q = p ≫ Sigma.ι (fun d ↦ torusStageScheme r N d) d ∧
    ∀ i : Fin r,
      windowSchemeSubspace
        (p ≫ Pi.π (fun i ↦ windowStableScheme 1 (-(N : ℤ)) (2 * N) (d i)) i) =
          latticeSubspace (-(N : ℤ)) (2 * N) (L i)

def labelledPoint {r N : ℕ} (w : BoundedCoweight r N) :
    Points (labelledPointScheme r N) complexAlgebra :=
  Sigma.ι (fun _ ↦ complexPointScheme) w

def labelledInclusion {r N M : ℕ} (h : N ≤ M) :
    labelledPointScheme r N ⟶ labelledPointScheme r M :=
  Sigma.desc fun w ↦ labelledPoint (enlargeCoweight h w)

/-- An isomorphism of the stages over ℂ, compatible with their lattice points and
with the closed inclusions arising from enlarging the bound. -/
def ReducedTorusStages : Prop :=
  ∀ r : ℕ,
    ∃ (e : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
      (j : ∀ {N M : ℕ}, N ≤ M → (boundedTorusScheme r N ⟶ boundedTorusScheme r M)),
      (∀ (N : ℕ) (w : BoundedCoweight r N),
        HasStageLattice (labelledPoint w ≫ (e N).hom) (torusLatticeAt r w.val)) ∧
      (∀ {N M : ℕ} (h : N ≤ M),
        IsClosedImmersion (j h).left ∧
          (e N).hom ≫ j h = labelledInclusion h ≫ (e M).hom) ∧
      (∀ N : ℕ, j (le_refl N) = 𝟙 (boundedTorusScheme r N)) ∧
      (∀ {N M P : ℕ} (h : N ≤ M) (k : M ≤ P), j h ≫ j k = j (h.trans k))

end

end RepTheorySurvey.Geometric.TorusStageSpecs
