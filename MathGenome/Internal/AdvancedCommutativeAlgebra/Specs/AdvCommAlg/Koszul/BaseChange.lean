import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Functoriality
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.Flat.Basic

/-! RK-04, scalar comparison (paper.tex 2186–2202).
The coefficient functors below use the canonical complexes and their actual homology.
Only the homology comparisons impose flatness. -/

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v w
namespace AdvCommAlg.Koszul

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- Scalar extension with the specified algebra structure on S. -/
def scalarExtension : ModuleCat.{w} R ⥤ ModuleCat.{max v w} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange S)
  map_id _ := ModuleCat.hom_ext LinearMap.baseChange_id
  map_comp f g := ModuleCat.hom_ext (LinearMap.baseChange_comp f.hom g.hom)

instance : (scalarExtension R S : ModuleCat.{w} R ⥤ _).Additive where
  map_add {_X _Y f g} := ModuleCat.hom_ext (LinearMap.baseChange_add f.hom g.hom)

variable {R}
/-- The scalar extended functional sends s tensor e to s times u(e). -/
def scalarExtensionForm {E : Type w} [AddCommGroup E] [Module R E]
    (a : E →ₗ[R] R) : S ⊗[R] E →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp (a.baseChange S)

/-- Scalar extension applied termwise to the canonical nonnegative complex. -/
def scalarExtensionComplex {E : Type w} [AddCommGroup E] [Module R E]
    (a : E →ₗ[R] R) : ChainComplex (ModuleCat S) ℕ :=
  ((scalarExtension R S).mapHomologicalComplex _).obj (complex a)

section Coefficients
variable {R : Type u} [CommRing R]

/-- The canonical map on coefficient complexes is identity tensor the coefficient map. -/
def coefficientMap (x : List R) {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    coefficientComplex M x ⟶ coefficientComplex N x :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (TensorProduct.map (LinearMap.id : (⋀[R]^n (Fin x.length → R)) →ₗ[R] _) f.hom))
    (fun n => by
      simp only [coefficientComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      change (coefficientDifferential N x n).comp (TensorProduct.map LinearMap.id f.hom) =
        (TensorProduct.map LinearMap.id f.hom).comp (coefficientDifferential M x n)
      simp only [coefficientDifferential, ← TensorProduct.map_comp,
        LinearMap.comp_id, LinearMap.id_comp])

/-- The Koszul complex as a functor in the coefficient module. -/
def coefficientFunctor (x : List R) : ModuleCat.{max u v} R ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ where
  obj M := coefficientComplex M x
  map f := coefficientMap x f
  map_id M := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change TensorProduct.map LinearMap.id LinearMap.id = LinearMap.id
    exact TensorProduct.map_id
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change TensorProduct.map LinearMap.id (g.hom.comp f.hom) =
      (TensorProduct.map LinearMap.id g.hom).comp (TensorProduct.map LinearMap.id f.hom)
    rw [← TensorProduct.map_comp, LinearMap.id_comp]

/-- Homology with its actual functorial maps on coefficient modules. -/
def coefficientHomologyFunctor (x : List R) (q : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  coefficientFunctor x ⋙ HomologicalComplex.homologyFunctor _ _ q

end Coefficients

end AdvCommAlg.Koszul

namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

/-- This formula characterizes the canonical comparison, including degree zero. -/
def IsScalarComparison {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra R S] {E : Type v} [AddCommGroup E] [Module R E]
    (a : E →ₗ[R] R) (i : scalarExtensionComplex S a ≅ complex (scalarExtensionForm S a)) : Prop :=
  ∀ (n : ℕ) (s : S) (e : Fin n → E),
    (i.hom.f n).hom (s ⊗ₜ[R] exteriorPower.ιMulti R n e) =
      s • exteriorPower.ιMulti S n (fun j => (1 : S) ⊗ₜ[R] e j)

def scalarComparison : Prop := ∀ {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    {E : Type v} [AddCommGroup E] [Module R E] (a : E →ₗ[R] R),
  ∃ i : scalarExtensionComplex S a ≅ complex (scalarExtensionForm S a),
    IsScalarComparison a i

/-- Naturality for every map of linear forms; the maps are specified by their components. -/
def scalarComparisonNaturality : Prop := ∀ {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S]
    {E F : Type v} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (a : E →ₗ[R] R) (b : F →ₗ[R] R) (φ : E →ₗ[R] F)
    (f : complex a ⟶ complex b)
    (g : complex (scalarExtensionForm S a) ⟶ complex (scalarExtensionForm S b))
    (i : scalarExtensionComplex S a ≅ complex (scalarExtensionForm S a))
    (j : scalarExtensionComplex S b ≅ complex (scalarExtensionForm S b)),
  b.comp φ = a → IsExteriorMap φ f → IsExteriorMap (φ.baseChange S) g →
  IsScalarComparison a i → IsScalarComparison b j →
    ((scalarExtension R S).mapHomologicalComplex _).map f ≫ j.hom = i.hom ≫ g

/-- Flat base change for the actual coefficient Koszul homology, for every degree. -/
def flatHomologyComparison : Prop := ∀ {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]
    (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ),
  Nonempty ((S ⊗[R] homology M x q) ≃ₗ[S]
    homology (S ⊗[R] M) (x.map (algebraMap R S)) q)

/-- The coefficient comparison is natural, without a flatness assumption. -/
def coefficientScalarComparison : Prop := ∀ {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] (x : List R),
  Nonempty ((coefficientFunctor.{u,v} x ⋙ (scalarExtension R S).mapHomologicalComplex _) ≅
    (scalarExtension R S ⋙ coefficientFunctor (x.map (algebraMap R S))))

/-- Flat homology comparison as a natural isomorphism in the coefficient module. -/
def flatHomologyNaturalComparison : Prop := ∀ {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S] (x : List R) (q : ℕ),
  Nonempty ((coefficientHomologyFunctor.{u,v} x q ⋙ scalarExtension R S) ≅
    (scalarExtension R S ⋙ coefficientHomologyFunctor (x.map (algebraMap R S)) q))

end Specs.AdvCommAlg.Koszul
