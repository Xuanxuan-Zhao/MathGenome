import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Canonical coefficient quotients and independent statements for the reduction
and extension assertions of paper.tex, RK-12. The complex shape is arbitrary;
there are no finiteness, nonzero, Noetherian or local hypotheses. -/

universe u v w
open scoped Pointwise
open CategoryTheory

namespace AdvCommAlg.RegularSequence

variable {R : Type u} [CommRing R]

/-- The natural map on coefficient quotients: the class of m maps to the class of f m. -/
def coefficientReductionMap {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (x : List R) (f : M →ₗ[R] N) :
    (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) →ₗ[R]
      (N ⧸ (Ideal.ofList x • ⊤ : Submodule R N)) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)

@[simp] theorem coefficientReductionMap_mk {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : List R) (f : M →ₗ[R] N) (m : M) :
    coefficientReductionMap x f (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (f m) := rfl

@[simp] theorem coefficientReductionMap_zero {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (x : List R) :
    coefficientReductionMap x (0 : M →ₗ[R] N) = 0 :=
  Submodule.mapQ_zero _ _

theorem coefficientReductionMap_comp {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (x : List R) (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    coefficientReductionMap x (g.comp f) =
      (coefficientReductionMap x g).comp (coefficientReductionMap x f) :=
  Submodule.mapQ_comp _ _ _ _ _ _ _

/-- Termwise quotient by (x), with the induced original differentials. -/
def coefficientReduction {ι : Type w} {c : ComplexShape ι} (x : List R)
    (K : HomologicalComplex (ModuleCat.{v} R) c) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R ((K.X i) ⧸ (Ideal.ofList x • ⊤ : Submodule R (K.X i)))
  d i j := ModuleCat.ofHom (coefficientReductionMap x (K.d i j).hom)
  shape i j hij := by
    apply ModuleCat.hom_ext
    change coefficientReductionMap x (K.d i j).hom = 0
    rw [K.shape i j hij]
    exact coefficientReductionMap_zero x
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    change (coefficientReductionMap x (K.d j k).hom).comp
      (coefficientReductionMap x (K.d i j).hom) = 0
    rw [← coefficientReductionMap_comp]
    have h : (K.d j k).hom.comp (K.d i j).hom = 0 :=
      congrArg ModuleCat.Hom.hom (K.d_comp_d i j k)
    rw [h, coefficientReductionMap_zero]

namespace Specs

/-- Every exact complex remains exact after reducing by a list weakly regular
on all its terms. Acyclic means exact in every degree, including endpoints. -/
def exact_reductionType : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type w} {c : ComplexShape ι}
    (x : List R) (K : HomologicalComplex (ModuleCat.{v} R) c),
    K.Acyclic → (∀ i, RingTheory.Sequence.IsWeaklyRegular (K.X i) x) →
    (coefficientReduction x K).Acyclic

/-- Weak regularity is closed under extensions of arbitrary coefficient modules. -/
def weaklyRegular_extensionType : Prop :=
  ∀ {R : Type u} [CommRing R] {L M N : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (x : List R) (f : L →ₗ[R] M) (g : M →ₗ[R] N),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    RingTheory.Sequence.IsWeaklyRegular L x → RingTheory.Sequence.IsWeaklyRegular N x →
    RingTheory.Sequence.IsWeaklyRegular M x

end Specs
end AdvCommAlg.RegularSequence
