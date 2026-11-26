import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.IdentityTangent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs

noncomputable section

/-- The differential on identity tangents detects smoothness of the scheme kernel. -/
def SmoothKernelIffLieSurjective : Prop :=
  ∀ (k : Type u) [Field k] (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val)
    (N : ClosedSubgroup G.val), IsSchemeKernel f N →
    Smooth G.val.X.hom → Smooth H.val.X.hom →
    Flat f.hom.hom.left → Surjective f.hom.hom.left →
    (Smooth N.group.X.hom ↔ Function.Surjective (mapPointKernel f))

open RelativeFrobenius in
/-- The relative Frobenius on a polynomial coordinate algebra is faithfully flat
of rank `p` and has zero differential. The kernel is the actual scheme kernel,
with coordinates `k[X]/(X^p)`, and is not smooth. -/
def AdditiveFrobeniusBoundaryAt (k : Type u) [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] (A : HopfAlgebraCategory k) (e : A ≃ₐ[k] Polynomial k)
    (a : twistCoordinates k p A ⟶ A) : Prop :=
  let F := specGroupMap a
  letI : Algebra (twistCoordinates k p A) A := a.hom.toAlgHom.toRingHom.toAlgebra
  Smooth (specGroup A).X.hom ∧ Smooth (specGroup (twistCoordinates k p A)).X.hom ∧
  Flat F.hom.hom.left ∧ Surjective F.hom.hom.left ∧
  Nonempty (Module.Basis (Fin p) (twistCoordinates k p A) A) ∧
  (∀ x : Lie k (specGroup A), mapPointKernel F x = 0) ∧
  PresentsSchemeKernel k a e (alphaIdeal k p) ∧
  ∃ N : ClosedSubgroup (specGroup A), IsSchemeKernel F N ∧ ¬ Smooth N.group.X.hom

open RelativeFrobenius in
def AdditiveFrobeniusBoundary : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : HopfAlgebraCategory k) (e : A ≃ₐ[k] Polynomial k),
    Bialgebra.counitAlgHom k A (e.symm Polynomial.X) = 0 →
    ∀ (a : twistCoordinates k p A ⟶ A), PullbackFormula k p A a →
      AdditiveFrobeniusBoundaryAt k p A e a

open RelativeFrobenius StandardGroups in
/-- The boundary case on the additive group with its primitive coordinate
and its usual addition on points over every test algebra. -/
def AdditiveFrobeniusExample : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    ∃ h : HopfOperations k (Polynomial k),
      letI := h.hopf
      let A := CommHopfAlgCat.of k (Polynomial k)
      h.delta (Polynomial.X : Polynomial k) = Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X ∧
      h.epsilon (Polynomial.X : Polynomial k) = 0 ∧
      h.inverse (Polynomial.X : Polynomial k) = -Polynomial.X ∧
      Represents (Polynomial k) (additivePoints k)
        (fun _ f x => Multiplicative.toAdd x = f Polynomial.X) ∧
      ∃ a : twistCoordinates k p A ⟶ A, PullbackFormula k p A a ∧
        AdditiveFrobeniusBoundaryAt k p A AlgEquiv.refl a

end

end LinearAlgebraicGroups.Specs
