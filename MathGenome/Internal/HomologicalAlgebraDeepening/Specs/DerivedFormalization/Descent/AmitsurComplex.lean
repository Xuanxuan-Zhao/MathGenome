import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurAlgebras
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! The integer-graded augmented Amitsur complex with module coefficients. -/

open CategoryTheory
open scoped BigOperators TensorProduct ZeroObject

namespace AmitsurComplexSpec

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (M : ModuleCat.{max u v w} A)

abbrev degree (p : ℕ) : ModuleCat.{max u v w} A :=
  ModuleCat.of A (AmitsurAlgebrasSpec.degree A B p ⊗[A] M)

/-- The map on coefficients induced by an algebra map on the left tensor factor. -/
noncomputable def tensorCoefficients : CommAlgCat.{max u v} A ⥤ ModuleCat.{max u v w} A where
  obj S := ModuleCat.of A (S ⊗[A] M)
  map f := ModuleCat.ofHom (TensorProduct.map f.hom.toLinearMap LinearMap.id)
  map_id S := ModuleCat.hom_ext TensorProduct.map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s m
    change TensorProduct.map (g.hom.comp f.hom).toLinearMap LinearMap.id (s ⊗ₜ[A] m) =
      TensorProduct.map g.hom.toLinearMap LinearMap.id
        (TensorProduct.map f.hom.toLinearMap LinearMap.id (s ⊗ₜ[A] m))
    simp

noncomputable def coface {p : ℕ} (i : Fin (p + 2)) : degree A B M p ⟶ degree A B M (p + 1) :=
  ModuleCat.ofHom (TensorProduct.map
    (AmitsurAlgebrasSpec.coface (A := A) (B := B) i).toLinearMap LinearMap.id)

/-- Tensor the algebra unit with the identity, using the canonical identification
`M ≃ₗ[A] A ⊗[A] M`. -/
noncomputable def augmentation : M ⟶ degree A B M 0 :=
  ModuleCat.ofHom ((TensorProduct.map (AmitsurAlgebrasSpec.augmentation A B).toLinearMap
    LinearMap.id).comp (TensorProduct.lid A M).symm.toLinearMap)

noncomputable def differential (p : ℕ) : degree A B M p ⟶ degree A B M (p + 1) :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • coface A B M i

noncomputable def term : ℤ → ModuleCat.{max u v w} A
  | .ofNat p => degree A B M p
  | .negSucc 0 => M
  | .negSucc (_ + 1) => 0

noncomputable def step : (q : ℤ) → term A B M q ⟶ term A B M (q + 1)
  | .ofNat p => differential A B M p
  | .negSucc 0 => augmentation A B M
  | .negSucc (_ + 1) => 0

private theorem differential_sq (p : ℕ) :
    differential A B M p ≫ differential A B M (p + 1) = 0 :=
  AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
    (AmitsurAlgebrasSpec.diagram A B ⋙ tensorCoefficients A M) p

private theorem augmentation_apply (m : M) :
    augmentation A B M m = 1 ⊗ₜ[A] m := by
  simp [augmentation]

private theorem augmentation_comp_coface (i : Fin 2) :
    augmentation A B M ≫ coface A B M i =
      ModuleCat.ofHom ((TensorProduct.mk A (AmitsurAlgebrasSpec.degree A B 1) M) 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change coface A B M i (augmentation A B M m) = 1 ⊗ₜ[A] m
  rw [augmentation_apply]
  simp [coface]

private theorem augmentation_comp_differential :
    augmentation A B M ≫ differential A B M 0 = 0 := by
  rw [differential, Preadditive.comp_sum, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_zsmul,
    Preadditive.comp_neg, augmentation_comp_coface, add_neg_cancel]

private theorem step_sq (q : ℤ) :
    step A B M q ≫ step A B M (q + 1) = 0 := by
  cases q with
  | ofNat p => exact differential_sq A B M p
  | negSucc n =>
    cases n with
    | zero => exact augmentation_comp_differential A B M
    | succ n =>
      change 0 ≫ step A B M (Int.negSucc (n + 1) + 1) = 0
      rw [Limits.zero_comp]

/-- The augmented complex, with zero terms in degrees below `-1`. -/
noncomputable def complex : CochainComplex (ModuleCat.{max u v w} A) ℤ :=
  CochainComplex.of (term A B M) (step A B M) (step_sq A B M)

variable {M} {N : ModuleCat.{max u v w} A}

noncomputable def degreeMap (f : M ⟶ N) (p : ℕ) : degree A B M p ⟶ degree A B N p :=
  ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom)

noncomputable def component (f : M ⟶ N) : (q : ℤ) → term A B M q ⟶ term A B N q
  | .ofNat p => degreeMap A B f p
  | .negSucc 0 => f
  | .negSucc (_ + 1) => 𝟙 _

private theorem degreeMap_coface (f : M ⟶ N) {p : ℕ} (i : Fin (p + 2)) :
    degreeMap A B f p ≫ coface A B N i = coface A B M i ≫ degreeMap A B f (p + 1) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro b m
  simp [degreeMap, coface]

theorem degreeMap_differential (f : M ⟶ N) (p : ℕ) :
    degreeMap A B f p ≫ differential A B N p =
      differential A B M p ≫ degreeMap A B f (p + 1) := by
  simp only [differential, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, degreeMap_coface]

theorem augmentation_naturality (f : M ⟶ N) :
    f ≫ augmentation A B N = augmentation A B M ≫ degreeMap A B f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change augmentation A B N (f m) = degreeMap A B f 0 (augmentation A B M m)
  rw [augmentation_apply, augmentation_apply]
  change _ = TensorProduct.map LinearMap.id f.hom (1 ⊗ₜ[A] m)
  simp

private theorem component_step (f : M ⟶ N) (q : ℤ) :
    component A B f q ≫ step A B N q = step A B M q ≫ component A B f (q + 1) := by
  cases q with
  | ofNat p => exact degreeMap_differential A B f p
  | negSucc n =>
    cases n with
    | zero => exact augmentation_naturality A B f
    | succ n =>
      change _ ≫ 0 = 0 ≫ _
      simp

noncomputable def map (f : M ⟶ N) : complex A B M ⟶ complex A B N :=
  CochainComplex.ofHom (component A B f) (fun q => by
    simpa only [complex, CochainComplex.of_d] using component_step A B f q)

private theorem component_id (M : ModuleCat.{max u v w} A) (q : ℤ) :
    component A B (𝟙 M) q = 𝟙 (term A B M q) := by
  cases q with
  | ofNat p => exact ModuleCat.hom_ext TensorProduct.map_id
  | negSucc n => cases n <;> rfl

private theorem component_comp {P : ModuleCat.{max u v w} A}
    (f : M ⟶ N) (g : N ⟶ P) (q : ℤ) :
    component A B (f ≫ g) q = component A B f q ≫ component A B g q := by
  cases q with
  | ofNat p =>
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro b m
    change TensorProduct.map LinearMap.id (g.hom.comp f.hom) (b ⊗ₜ[A] m) =
      TensorProduct.map LinearMap.id g.hom (TensorProduct.map LinearMap.id f.hom (b ⊗ₜ[A] m))
    simp
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n => exact (Category.id_comp _).symm

/-- Functoriality in the coefficient module, with tensoring on each nonnegative degree. -/
noncomputable def functor : ModuleCat.{max u v w} A ⥤
    CochainComplex (ModuleCat.{max u v w} A) ℤ where
  obj := complex A B
  map := map A B
  map_id M := HomologicalComplex.hom_ext _ _ (component_id A B M)
  map_comp f g := HomologicalComplex.hom_ext _ _ (component_comp A B f g)

/-- The same construction for coefficients with an independent universe. -/
noncomputable def liftedFunctor : ModuleCat.{w} A ⥤
    CochainComplex (ModuleCat.{max u v w} A) ℤ :=
  ModuleCat.uliftFunctor.{max u v} A ⋙ functor.{u, v, w} A B

def liftedAugmentedTermEquiv (L : ModuleCat.{w} A) :
    ((liftedFunctor A B).obj L).X (-1) ≃ₗ[A] L :=
  ULift.moduleEquiv

noncomputable def liftedDegreeEquiv (L : ModuleCat.{w} A) (p : ℕ) :
    ((liftedFunctor A B).obj L).X (p : ℤ) ≃ₗ[A] (AmitsurAlgebrasSpec.degree A B p ⊗[A] L) :=
  TensorProduct.congr (LinearEquiv.refl A _) ULift.moduleEquiv

section DeclarationTypes

set_option linter.checkUnivs false

private def declarationType {T : Sort*} (_ : T) := T

def DegreeType := declarationType (@degree.{u, v, w})
def CofaceType := declarationType (@coface.{u, v, w})
def AugmentationType := declarationType (@augmentation.{u, v, w})
def DifferentialType := declarationType (@differential.{u, v, w})
def TermType := declarationType (@term.{u, v, w})
def StepType := declarationType (@step.{u, v, w})
def ComplexType := declarationType (@complex.{u, v, w})
def DegreeMapType := declarationType (@degreeMap.{u, v, w})
def MapType := declarationType (@map.{u, v, w})
def FunctorType := declarationType (@functor.{u, v, w})
def LiftedFunctorType := declarationType (@liftedFunctor.{u, v, w})
def LiftedAugmentedTermEquivType := declarationType (@liftedAugmentedTermEquiv.{u, v, w})
def LiftedDegreeEquivType := declarationType (@liftedDegreeEquiv.{u, v, w})

end DeclarationTypes

def AugmentationApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (m : M), augmentation A B M m = 1 ⊗ₜ[A] m

def CofaceTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ {p : ℕ} (i : Fin (p + 2)) (b : AmitsurAlgebrasSpec.degree A B p) (m : M),
    coface A B M i (b ⊗ₜ[A] m) =
      AmitsurAlgebrasSpec.coface i b ⊗ₜ[A] m

def CofaceTprodTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ {p : ℕ} (i : Fin (p + 2)) (b : Fin (p + 1) → B) (m : M),
    coface A B M i (PiTensorProduct.tprod A b ⊗ₜ[A] m) =
      PiTensorProduct.tprod A (i.insertNth 1 b) ⊗ₜ[A] m

def DifferentialSq : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (p : ℕ), differential A B M p ≫ differential A B M (p + 1) = 0

def AugmentationCompDifferential : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  augmentation A B M ≫ differential A B M 0 = 0

def StepSq : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (q : ℤ), step A B M q ≫ step A B M (q + 1) = 0

def ComplexXOfNat : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (p : ℕ), (complex A B M).X (p : ℤ) = degree A B M p

def ComplexXNegOne : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  (complex A B M).X (-1) = M

def ComplexXOfLt : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (q : ℤ), q < -1 → (complex A B M).X q = 0

def ComplexDSucc : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (q : ℤ), (complex A B M).d q (q + 1) = step A B M q

def ComplexDOfNat : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (p : ℕ), (complex A B M).d (p : ℤ) (↑p + 1) = differential A B M p

def ComplexDNegOne : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  (complex A B M).d (-1) 0 = augmentation A B M

def ComplexDOfNe : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A),
  ∀ (q r : ℤ), q + 1 ≠ r → (complex A B M).d q r = 0

def DegreeMapTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) (p : ℕ)
    (b : AmitsurAlgebrasSpec.degree A B p) (m : M), degreeMap A B f p (b ⊗ₜ[A] m) = b ⊗ₜ[A] f m

def MapFOfNat : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) (p : ℕ),
    (map A B f).f (p : ℤ) = degreeMap A B f p

def MapFNegOne : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {M N : ModuleCat.{max u v w} A} (f : M ⟶ N), (map A B f).f (-1) = f

def DegreeMapDifferential : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {M N : ModuleCat.{max u v w} A} (f : M ⟶ N) (p : ℕ),
    degreeMap A B f p ≫ differential A B N p = differential A B M p ≫ degreeMap A B f (p + 1)

def AugmentationNaturality : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {M N : ModuleCat.{max u v w} A} (f : M ⟶ N),
    f ≫ augmentation A B N = augmentation A B M ≫ degreeMap A B f 0

def FunctorObj : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (M : ModuleCat.{max u v w} A), (functor A B).obj M = complex A B M

def FunctorMap : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ {M N : ModuleCat.{max u v w} A} (f : M ⟶ N), (functor A B).map f = map A B f

def LiftedAugmentationApply : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (L : ModuleCat.{w} A) (m : L),
    liftedDegreeEquiv A B L 0
      (((liftedFunctor A B).obj L).d (-1) 0 ((liftedAugmentedTermEquiv A B L).symm m)) =
      1 ⊗ₜ[A] m

def LiftedCofaceTmul : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
  ∀ (L : ModuleCat.{w} A) {p : ℕ} (i : Fin (p + 2)) (b : AmitsurAlgebrasSpec.degree A B p) (m : L),
    liftedDegreeEquiv A B L (p + 1)
      (coface A B ((ModuleCat.uliftFunctor.{max u v} A).obj L) i
        ((liftedDegreeEquiv A B L p).symm (b ⊗ₜ[A] m))) =
      AmitsurAlgebrasSpec.coface i b ⊗ₜ[A] m

end AmitsurComplexSpec
