import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! RK-12, coefficient sequences (paper.tex 2468–2481).
The chain model is the RK-03 model. The cochain model is Hom of that
same exterior complex, with differential f ↦ f ∘ d, as in RK-10.
The other two assertions of RK-12 belong to ExactReduction.
The coefficient-sequence helpers have a dedicated namespace so that they can
coexist with the coordinate-change maps of Functoriality. -/

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v

namespace AdvCommAlg.Koszul.CoefficientSequences
variable {R : Type u} [CommRing R]

/-- Tensoring the canonical Koszul complex with a coefficient morphism. -/
def coefficientChainMap (x : List R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    coefficientComplex M x ⟶ coefficientComplex N x :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (f.hom.lTensor (⋀[R]^n (Fin x.length → R)))) (by
      intro n
      simp only [coefficientComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext a m
      rfl)

/-- The coefficient chain-complex functor, with the literal RK-03 objects. -/
def coefficientChainFunctor (x : List R) :
    ModuleCat.{v} R ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ where
  obj M := coefficientComplex M x
  map f := coefficientChainMap x f
  map_id M := by
    ext n : 2
    apply TensorProduct.ext
    ext a m
    rfl
  map_comp f g := by
    ext n : 2
    apply TensorProduct.ext
    ext a m
    rfl

instance (x : List R) : (coefficientChainFunctor.{u,v} x).PreservesZeroMorphisms where
  map_zero M N := by
    ext n : 2
    apply TensorProduct.ext
    ext a m
    exact TensorProduct.tmul_zero _ _

/-- Precomposition with the degree-lowering differential. -/
def coefficientCochainDifferential (M : ModuleCat.{v} R) (x : List R) (n : ℕ) :
    ((⋀[R]^n (Fin x.length → R)) →ₗ[R] M) →ₗ[R]
      ((⋀[R]^(n+1) (Fin x.length → R)) →ₗ[R] M) where
  toFun f := f.comp (differential (listForm x) n)
  map_add' f g := rfl
  map_smul' r f := rfl

theorem coefficientCochainDifferential_comp (M : ModuleCat.{v} R) (x : List R) (n : ℕ) :
    (coefficientCochainDifferential M x (n+1)).comp
      (coefficientCochainDifferential M x n) = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro a
  change f (differential (listForm x) n (differential (listForm x) (n+1) a)) = 0
  have hd := LinearMap.congr_fun (differential_comp (listForm x) n) a
  change differential (listForm x) n (differential (listForm x) (n+1) a) = 0 at hd
  rw [hd, map_zero]

/-- The coefficient cochain complex Hom_R(K(x), M), including degree zero. -/
def coefficientCochainComplex (M : ModuleCat.{v} R) (x : List R) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R ((⋀[R]^n (Fin x.length → R)) →ₗ[R] M))
    (fun n => ModuleCat.ofHom (coefficientCochainDifferential M x n))
    (fun n => ModuleCat.hom_ext (coefficientCochainDifferential_comp M x n))

/-- Postcomposition in each degree. -/
def coefficientCochainMap (x : List R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    coefficientCochainComplex M x ⟶ coefficientCochainComplex N x :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (LinearMap.compRight R f.hom)) (by
    intro n
    simp only [coefficientCochainComplex, CochainComplex.of_d]
    rfl)

/-- The covariant coefficient functor Hom_R(K(x), -). -/
def coefficientCochainFunctor (x : List R) :
    ModuleCat.{v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ where
  obj M := coefficientCochainComplex M x
  map f := coefficientCochainMap x f
  map_id M := by ext n f a; rfl
  map_comp f g := by ext n h a; rfl

instance (x : List R) : (coefficientCochainFunctor.{u,v} x).PreservesZeroMorphisms where
  map_zero M N := by ext n f a; rfl

end AdvCommAlg.Koszul.CoefficientSequences

namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul.CoefficientSequences

/-- Finite freeness of the actual terms, without a nonzero-ring assumption. -/
def exteriorTermsFiniteFree : Prop := ∀ {R : Type u} [CommRing R] (x : List R) (q : ℕ),
  Module.Free R ((listComplex x).X q) ∧ Module.Finite R ((listComplex x).X q)

def chainCoefficientShortExact : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (S : ShortComplex (ModuleCat.{v} R)), S.ShortExact →
    (S.map (coefficientChainFunctor x)).ShortExact

def cochainCoefficientShortExact : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (S : ShortComplex (ModuleCat.{v} R)), S.ShortExact →
    (S.map (coefficientCochainFunctor x)).ShortExact

/-- Every overlapping six-term segment is exact; the sequence ends in H₀(N) → 0.
The middle map is the canonical connecting map obtained from the short exact
sequence of the actual RK-03 complexes, not an arbitrarily chosen morphism. -/
def chainCoefficientLongExact : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (S : ShortComplex (ModuleCat.{v} R)), S.ShortExact →
    ∃ h : (S.map (coefficientChainFunctor x)).ShortExact,
      (∀ n : ℕ, (HomologicalComplex.HomologySequence.composableArrows₅ h
        (n+1) n rfl).Exact) ∧
      Epi (HomologicalComplex.homologyMap (S.map (coefficientChainFunctor x)).g 0)

/-- Cohomology has the increasing-degree sequence, beginning in 0 → H⁰(L). -/
def cochainCoefficientLongExact : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (S : ShortComplex (ModuleCat.{v} R)), S.ShortExact →
    ∃ h : (S.map (coefficientCochainFunctor x)).ShortExact,
      (∀ n : ℕ, (HomologicalComplex.HomologySequence.composableArrows₅ h
        n (n+1) rfl).Exact) ∧
      Mono (HomologicalComplex.homologyMap (S.map (coefficientCochainFunctor x)).f 0)

/-- Naturality of the connecting map for every commutative coefficient diagram.
The other four squares of each segment follow from the homology functor. -/
def chainConnectingNatural : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (S T : ShortComplex (ModuleCat.{v} R))
  (hS : (S.map (coefficientChainFunctor x)).ShortExact)
  (hT : (T.map (coefficientChainFunctor x)).ShortExact) (φ : S ⟶ T) (n : ℕ),
    hS.δ (n+1) n rfl ≫
        HomologicalComplex.homologyMap ((coefficientChainFunctor x).map φ.τ₁) n =
      HomologicalComplex.homologyMap ((coefficientChainFunctor x).map φ.τ₃) (n+1) ≫
        hT.δ (n+1) n rfl

def cochainConnectingNatural : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (S T : ShortComplex (ModuleCat.{v} R))
  (hS : (S.map (coefficientCochainFunctor x)).ShortExact)
  (hT : (T.map (coefficientCochainFunctor x)).ShortExact) (φ : S ⟶ T) (n : ℕ),
    hS.δ n (n+1) rfl ≫
        HomologicalComplex.homologyMap ((coefficientCochainFunctor x).map φ.τ₁) (n+1) =
      HomologicalComplex.homologyMap ((coefficientCochainFunctor x).map φ.τ₃) n ≫
        hT.δ n (n+1) rfl

def chainCoefficientFunctorType := ∀ {R : Type u} [CommRing R] (x : List R),
  ModuleCat.{v} R ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ
def chainCoefficientFunctorValue : chainCoefficientFunctorType.{u,v} := @coefficientChainFunctor

def cochainCoefficientFunctorType := ∀ {R : Type u} [CommRing R] (x : List R),
  ModuleCat.{v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℕ
def cochainCoefficientFunctorValue : cochainCoefficientFunctorType.{u,v} := @coefficientCochainFunctor

end Specs.AdvCommAlg.Koszul
