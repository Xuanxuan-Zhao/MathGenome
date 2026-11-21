import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.JacobianPresentation
import Mathlib.RingTheory.AdjoinRoot

/-! KD-21, paper.tex 419–428 and the following paragraph. All quotients and
scalar actions below are the specified ones; no regularity of f is required. -/
namespace Specs.AdvCommAlg.Differentials
universe u
noncomputable section

abbrev Hypersurface (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A) :=
  JacobianQuotient A n 1 (fun _ => f)

def hypersurfaceVariable (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A) (i : Fin n) : Hypersurface A n f :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

def hypersurfaceGradient (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A) : Fin n → Hypersurface A n f :=
  fun i => Ideal.Quotient.mk _ (MvPolynomial.pderiv i f)

def hypersurfaceDifferential (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A) :
    (Fin n → Hypersurface A n f) →ₗ[Hypersurface A n f]
      KaehlerDifferential A (Hypersurface A n f) :=
  (Pi.basisFun (Hypersurface A n f) (Fin n)).constr (Hypersurface A n f)
    (fun i => KaehlerDifferential.D A (Hypersurface A n f)
      (hypersurfaceVariable A n f i))

/-- Generators and *all* relations, including zero-variable and zero-polynomial cases. -/
def hypersurfacePresentation : Prop := ∀ (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A),
  ∃ e : ((Fin n → Hypersurface A n f) ⧸
      Submodule.span (Hypersurface A n f) {hypersurfaceGradient A n f}) ≃ₗ[Hypersurface A n f]
      KaehlerDifferential A (Hypersurface A n f),
    ∀ x, e ((Submodule.span (Hypersurface A n f) {hypersurfaceGradient A n f}).mkQ x) =
      hypersurfaceDifferential A n f x

def hypersurfaceRelation : Prop := ∀ (A : Type u) [CommRing A] (n : ℕ)
    (f : MvPolynomial (Fin n) A),
  ∑ i : Fin n, hypersurfaceGradient A n f i •
    KaehlerDifferential.D A (Hypersurface A n f) (hypersurfaceVariable A n f i) = 0

/-- AdjoinRoot f is literally A[X]/(f), with the canonical quotient algebra. -/
def univariateHypersurface : Prop := ∀ (A : Type u) [CommRing A] (f : Polynomial A),
  ∃ e : (AdjoinRoot f ⧸ Ideal.span {AdjoinRoot.mk f f.derivative}) ≃ₗ[AdjoinRoot f]
      KaehlerDifferential A (AdjoinRoot f),
    ∀ b, e (Ideal.Quotient.mk _ b) = b •
      KaehlerDifferential.D A (AdjoinRoot f) (AdjoinRoot.root f)

abbrev Node (A : Type u) [CommRing A] :=
  Hypersurface A 2 (MvPolynomial.X 0 * MvPolynomial.X 1)
abbrev nodeX (A : Type u) [CommRing A] : Node A :=
  hypersurfaceVariable A 2 (MvPolynomial.X 0 * MvPolynomial.X 1) 0
abbrev nodeY (A : Type u) [CommRing A] : Node A :=
  hypersurfaceVariable A 2 (MvPolynomial.X 0 * MvPolynomial.X 1) 1

/-- The crossing has exactly the relation y dx + x dy. -/
def nodePresentation : Prop := ∀ (A : Type u) [CommRing A],
  ∃ e : ((Fin 2 → Node A) ⧸ Submodule.span (Node A) {![nodeY A, nodeX A]}) ≃ₗ[Node A]
      KaehlerDifferential A (Node A),
    (e ((Submodule.span (Node A) {![nodeY A, nodeX A]}).mkQ (Pi.single 0 1)) =
      KaehlerDifferential.D A (Node A) (nodeX A)) ∧
    (e ((Submodule.span (Node A) {![nodeY A, nodeX A]}).mkQ (Pi.single 1 1)) =
      KaehlerDifferential.D A (Node A) (nodeY A)) ∧
    nodeY A • KaehlerDifferential.D A (Node A) (nodeX A) +
      nodeX A • KaehlerDifferential.D A (Node A) (nodeY A) = 0

abbrev DualQuotient (A : Type u) [CommRing A] := AdjoinRoot (Polynomial.X ^ 2 : Polynomial A)
abbrev epsilon (A : Type u) [CommRing A] : DualQuotient A :=
  AdjoinRoot.root (Polynomial.X ^ 2 : Polynomial A)

def dualNumberPresentation : Prop := ∀ (A : Type u) [CommRing A],
  ∃ e : (DualQuotient A ⧸ Ideal.span {(2 : DualQuotient A) * epsilon A}) ≃ₗ[DualQuotient A]
      KaehlerDifferential A (DualQuotient A),
    (∀ b, e (Ideal.Quotient.mk _ b) = b •
      KaehlerDifferential.D A (DualQuotient A) (epsilon A)) ∧
    ((2 : DualQuotient A) * epsilon A) •
      KaehlerDifferential.D A (DualQuotient A) (epsilon A) = 0

def dualNumberNilpotent : Prop := ∀ (K : Type u) [Field K],
  epsilon K ≠ 0 ∧ (epsilon K) ^ 2 = 0

def dualNumberCharTwo : Prop := ∀ (K : Type u) [Field K] [CharP K 2],
  ∃ b : Module.Basis Unit (DualQuotient K) (KaehlerDifferential K (DualQuotient K)),
    b () = KaehlerDifferential.D K (DualQuotient K) (epsilon K)

/-- The copy of k dε and its specified ε-action, in every characteristic other than two. -/
def dualNumberCharNeTwo : Prop := ∀ (K : Type u) [Field K], (2 : K) ≠ 0 →
  ∃ e : K ≃ₗ[K] KaehlerDifferential K (DualQuotient K),
    e 1 = KaehlerDifferential.D K (DualQuotient K) (epsilon K) ∧
    ∀ ω : KaehlerDifferential K (DualQuotient K), epsilon K • ω = 0

end
end Specs.AdvCommAlg.Differentials
