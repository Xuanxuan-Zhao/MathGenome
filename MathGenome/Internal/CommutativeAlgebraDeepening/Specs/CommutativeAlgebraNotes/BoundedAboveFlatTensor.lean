import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.RingTheory.Flat.CategoryTheory

open CategoryTheory HomologicalComplex

universe u

namespace CommutativeAlgebraNotes.Specs

/-- A bounded-above cochain complex of flat modules tensors any acyclic complex
to an acyclic complex, using direct-sum totalization. -/
def boundedAboveFlatTensorAcyclicType : Prop :=
  ∀ (R : Type u) [CommRing R] (F : CochainComplex (ModuleCat.{u} R) ℤ),
    (∀ p, Module.Flat R (F.X p)) →
    (∃ N : ℤ, F.IsStrictlyLE N) →
    ∀ (A : CochainComplex (ModuleCat.{u} R) ℤ), A.Acyclic →
      (tensorObj F A).Acyclic

/-- Tensoring a quasi-isomorphism with a bounded-above flat cochain complex
preserves the quasi-isomorphism. The comparison complexes are arbitrary. -/
def boundedAboveFlatTensorQuasiIsoType : Prop :=
  ∀ (R : Type u) [CommRing R] (F : CochainComplex (ModuleCat.{u} R) ℤ),
    (∀ p, Module.Flat R (F.X p)) →
    (∃ N : ℤ, F.IsStrictlyLE N) →
    ∀ {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B), QuasiIso f →
      QuasiIso (tensorHom (𝟙 F) f)

end CommutativeAlgebraNotes.Specs
