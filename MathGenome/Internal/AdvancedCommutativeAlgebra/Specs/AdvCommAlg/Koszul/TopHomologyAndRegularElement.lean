import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.SelfDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.CoefficientExactness

/-! RK-14: top homology, degree-zero cohomology, and reduction by one
injective element of the generated ideal. The iterated assertion is RK-14-iterated.
All coefficients are arbitrary modules; the zero ring and empty list are allowed.
The degree-zero reduction is stated as an isomorphism (the missing H₋₁ is zero).
-/
open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul.TopHomology
variable {R : Type u} [CommRing R]

/-- The submodule 0 :_M I. -/
def idealAnnihilator (M : Type v) [AddCommGroup M] [Module R M] (I : Ideal R) :
    Submodule R M where
  carrier := {m | ∀ a ∈ I, a • m = 0}
  zero_mem' := by simp
  add_mem' := by intro m n hm hn a ha; simp [smul_add, hm a ha, hn a ha]
  smul_mem' := by intro r m hm a ha; rw [smul_comm, hm a ha, smul_zero]

/-- The class of a concrete cycle in the canonical homology object. -/
def cycleClass {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (q : ι) :
    LinearMap.ker (C.sc q).g.hom →ₗ[R] C.homology q :=
  (C.sc q).moduleCatHomologyIso.inv.hom.comp
    (LinearMap.range (C.sc q).moduleCatToCycles).mkQ

/-- Reading the coefficient of the ordered top exterior basis vector. -/
def topCoefficientEquiv (M : Type v) [AddCommGroup M] [Module R M] (x : List R) :
    (coefficientComplex M x).X x.length ≃ₗ[R] M :=
  (TensorProduct.congr (SelfDuality.orientation x) (LinearEquiv.refl R M)).trans
    (TensorProduct.lid R M)

/-- Evaluation of a degree-zero cochain on the scalar 1. -/
def zeroCochainValue (M : Type v) [AddCommGroup M] [Module R M] (x : List R) :
    ((⋀[R]^0 (Fin x.length → R)) →ₗ[R] M) →ₗ[R] M where
  toFun f := f ((exteriorPower.zeroEquiv R (Fin x.length → R)).symm 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The literal submodule yM, the range of multiplication by y. -/
def scalarRange (M : Type v) [AddCommGroup M] [Module R M] (y : R) : Submodule R M :=
  LinearMap.range (y • (LinearMap.id : M →ₗ[R] M))

/-- M →ʸ M → M/yM, before imposing injectivity. -/
def scalarCoefficientSequence (M : Type v) [AddCommGroup M] [Module R M] (y : R) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.moduleCatMk (y • LinearMap.id) (scalarRange M y).mkQ (by
    ext m
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩)

/-- The positive-degree sequence with the canonical quotient map and connecting map. -/
def reductionHomologySequence (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (y : R)
    (h : ((scalarCoefficientSequence M y).map
      (CoefficientSequences.coefficientChainFunctor x)).ShortExact) (n : ℕ) :
    ShortComplex (ModuleCat.{max u v} R) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap
      ((CoefficientSequences.coefficientChainFunctor x).map (scalarCoefficientSequence M y).g)
      (n+1))
    (h.δ (n+1) n rfl) (h.comp_δ (n+1) n rfl)

/-- The coefficient map induced on M/yM by an R-linear map. -/
def quotientScalarMap {M N : ModuleCat.{v} R} (y : R) (f : M ⟶ N) :
    ModuleCat.of R (M ⧸ scalarRange M y) ⟶ ModuleCat.of R (N ⧸ scalarRange N y) :=
  ModuleCat.ofHom ((scalarRange M y).mapQ (scalarRange N y) f.hom (by
    rintro _ ⟨m, rfl⟩
    exact ⟨f m, by simp⟩))

/-- The canonical diagram between the multiplication-and-quotient sequences. -/
def scalarSequenceMap {M N : ModuleCat.{v} R} (y : R) (f : M ⟶ N) :
    scalarCoefficientSequence M y ⟶ scalarCoefficientSequence N y :=
  ShortComplex.homMk f f (quotientScalarMap y f) (by
      apply ModuleCat.hom_ext
      ext m
      exact (map_smul f.hom y m).symm)
    (by ext m; rfl)

end AdvCommAlg.Koszul.TopHomology

namespace Specs.AdvCommAlg.Koszul.TopHomology
open _root_.AdvCommAlg.Koszul _root_.AdvCommAlg.Koszul.TopHomology

def topHomology : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  ∃ e : homology M x x.length ≃ₗ[R] idealAnnihilator M (listIdeal x),
    ∀ z : LinearMap.ker ((coefficientComplex M x).sc x.length).g.hom,
      (e (cycleClass (coefficientComplex M x) x.length z) : M) = topCoefficientEquiv M x z.val

def zeroCohomology : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  ∃ e : SelfDuality.cohomology M x 0 ≃ₗ[R] ((R ⧸ listIdeal x) →ₗ[R] M),
    ∀ z : LinearMap.ker ((SelfDuality.cochainComplex M x).sc 0).g.hom,
      e (cycleClass (SelfDuality.cochainComplex M x) 0 z) (Ideal.Quotient.mk _ 1) =
        zeroCochainValue M x z.val

def regularElementShortExact : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (y : R),
  y ∈ listIdeal x → Function.Injective (fun m : M => y • m) →
  ∃ h : ((scalarCoefficientSequence M y).map
      (CoefficientSequences.coefficientChainFunctor x)).ShortExact,
    (∀ n : ℕ, (reductionHomologySequence M x y h n).ShortExact) ∧
    IsIso (HomologicalComplex.homologyMap
      ((CoefficientSequences.coefficientChainFunctor x).map (scalarCoefficientSequence M y).g) 0)

/-- Both squares of the short exact sequence commute for every coefficient morphism. -/
def reductionNaturality : Prop := ∀ {R : Type u} [CommRing R]
  (M N : ModuleCat.{v} R) (x : List R) (y : R) (f : M ⟶ N)
  (hM : ((scalarCoefficientSequence M y).map
    (CoefficientSequences.coefficientChainFunctor x)).ShortExact)
  (hN : ((scalarCoefficientSequence N y).map
    (CoefficientSequences.coefficientChainFunctor x)).ShortExact),
  (∀ q : ℕ,
    HomologicalComplex.homologyMap ((CoefficientSequences.coefficientChainFunctor x).map f) q ≫
      HomologicalComplex.homologyMap ((CoefficientSequences.coefficientChainFunctor x).map
        (scalarCoefficientSequence N y).g) q =
    HomologicalComplex.homologyMap ((CoefficientSequences.coefficientChainFunctor x).map
        (scalarCoefficientSequence M y).g) q ≫
      HomologicalComplex.homologyMap ((CoefficientSequences.coefficientChainFunctor x).map
        (quotientScalarMap y f)) q) ∧
  (∀ n : ℕ, hM.δ (n+1) n rfl ≫ HomologicalComplex.homologyMap
      ((CoefficientSequences.coefficientChainFunctor x).map f) n =
    HomologicalComplex.homologyMap
      ((CoefficientSequences.coefficientChainFunctor x).map (quotientScalarMap y f)) (n+1) ≫
      hN.δ (n+1) n rfl)

def homologyBounded : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (q : ℕ),
  x.length < q → Subsingleton (homology M x q)

end Specs.AdvCommAlg.Koszul.TopHomology
