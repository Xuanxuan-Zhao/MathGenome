import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

open CategoryTheory
open scoped TensorProduct

namespace CommutativeAlgebraNotes.CochainTensorHom

universe u

abbrev Complex (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ

namespace Spec

open CochainComplex (linearHomComplex)
open CochainComplex.HomComplex (Cochain)
open HomologicalComplex (tensorObj tensorHom ιTensorObj)

variable {R : Type u} [CommRing R]

abbrev HomMapFamily (R : Type u) [CommRing R] :=
  ∀ {A A' B B' : Complex R}, (A' ⟶ A) → (B ⟶ B') →
    (linearHomComplex R A B ⟶ linearHomComplex R A' B')

abbrev CurryingFamily (R : Type u) [CommRing R] :=
  ∀ (P Q J : Complex R),
    linearHomComplex R (tensorObj P Q) J ≅ linearHomComplex R P (linearHomComplex R Q J)

/-- The linear cochain Hom uses ordinary precomposition and postcomposition
in each component. In particular, precomposition gives the quotient action. -/
def IsHomMapFamily (map : HomMapFamily R) : Prop :=
  ∀ {A A' B B' : Complex R} (g : A' ⟶ A) (h : B ⟶ B')
    {n i v : ℤ} (hi : i + n = v) (f : Cochain A B n) (x : A'.X i),
    ((map g h).f n f).v i v hi x = h.f v (f.v i v hi (g.f i x))

/-- The tensor is the direct-sum total complex, and the Hom terms are
products. The chain isomorphism is determined on pure tensors. -/
def IsCurryingFamily (e : CurryingFamily R) : Prop :=
  ∀ (P Q J : Complex R) {n i j u' v : ℤ}
    (hi : i + n = u') (hj : j + u' = v) (f : Cochain (tensorObj P Q) J n)
    (x : P.X i) (y : Q.X j),
    (((e P Q J).hom.f n f).v i u' hi x).v j v hj y =
      f.v (i + j) v (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))

/-- Tensor–Hom currying as a chain isomorphism, natural in all three complexes.
The naturality square applies to multiplication on a quotient placed in
degree zero as well as any other action by chain endomorphisms. -/
def TensorHomAdjunction : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (map : HomMapFamily R) (e : CurryingFamily R),
      IsHomMapFamily map ∧ IsCurryingFamily e ∧
        ∀ {P P' Q Q' J J' : Complex R} (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J'),
          map (tensorHom a b) c ≫ (e P' Q' J').hom =
            (e P Q J).hom ≫ map a (map b c)

end Spec
end CommutativeAlgebraNotes.CochainTensorHom
