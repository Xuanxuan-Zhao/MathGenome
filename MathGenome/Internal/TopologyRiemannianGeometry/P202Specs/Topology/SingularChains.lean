import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! Canonical finite singular chains. The singular-set indices are canonically
continuous maps on the ordered barycentric real simplex; `simplexEquiv` removes
Mathlib's universe lift. No condition is placed on the topology of the space. -/
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct

namespace P202Specs.SingularChains
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

abbrev Simplex (X : TopCat.{w}) (n : ℕ) := (TopCat.toSSet.obj X).obj (op ⦋n⦌)

def simplexEquiv (X : TopCat.{w}) (n : ℕ) :
    Simplex X n ≃ C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
  TopCat.toSSetObjEquiv X (op ⦋n⦌)

/-- Finite sums with coefficients in an arbitrary module. In particular `M=R`
gives the free module on the simplex basis, and `R=ℤ` allows any abelian group. -/
abbrev Chains (X : TopCat.{w}) (n : ℕ) := Simplex X n →₀ M

def finsuppFunctor : Type w ⥤ ModuleCat.{max v w} R where
  obj I := ModuleCat.of R (I →₀ M)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain M R f)
  map_id I := by apply ModuleCat.hom_ext; exact Finsupp.lmapDomain_id M R
  map_comp f g := by apply ModuleCat.hom_ext; exact Finsupp.lmapDomain_comp M R f g

def simplicialChains (X : TopCat.{w}) : SimplicialObject (ModuleCat.{max v w} R) :=
  TopCat.toSSet.obj X ⋙ finsuppFunctor R M

def chainFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ :=
  TopCat.toSSet ⋙ (SimplicialObject.whiskering _ _).obj (finsuppFunctor R M) ⋙
    AlgebraicTopology.alternatingFaceMapComplex _

abbrev complex (X : TopCat.{w}) := (chainFunctor R M).obj X
abbrev chainMap {X Y : TopCat.{w}} (f : X ⟶ Y) := (chainFunctor R M).map f
abbrev boundary (X : TopCat.{w}) (n : ℕ) := ((complex R M X).d (n+1) n).hom

/-- The affine face inclusion omits the `i`-th ordered vertex. -/
def faceInclusion {n : ℕ} (i : Fin (n+2)) :
    C(Convexity.StdSimplex ℝ (Fin (n+1)), Convexity.StdSimplex ℝ (Fin (n+2))) :=
  (SimplexCategory.toTop₀.map (SimplexCategory.δ i)).hom

abbrev face {X : TopCat.{w}} {n : ℕ} (i : Fin (n+2)) (s : Simplex X (n+1)) :
    Simplex X n := (TopCat.toSSet.obj X).δ i s

def sumCoefficients (I : Type w) : (I →₀ M) →ₗ[R] M :=
  Finsupp.lsum R (fun _ => LinearMap.id)

abbrev coefficientModule : ModuleCat.{max v w} R := ModuleCat.of R (ULift.{w} M)

abbrev augmentation (X : TopCat.{w}) : (complex R M X).X 0 ⟶ coefficientModule.{u,v,w} R M :=
  ModuleCat.ofHom ((ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{w} M).toLinearMap.comp
    (sumCoefficients R M (Simplex X 0)))

/-- The augmentation as an ordinary linear map, without the categorical universe lift. -/
def augmentationLinear (X : TopCat.{w}) : Chains M X 0 →ₗ[R] M :=
  sumCoefficients R M (Simplex X 0)

lemma augmentation_boundary (X : TopCat.{w}) :
    (complex R M X).d 1 0 ≫ augmentation R M X = 0 := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  change ULift.up ((sumCoefficients R M _) (boundary R M X 0 (Finsupp.single s m))) = 0
  apply ULift.ext
  have hb : boundary R M X 0 (Finsupp.single s m) =
      Finsupp.single (face 0 s) m - Finsupp.single (face 1 s) m := by
    change ((∑ i : Fin 2, (-1 : ℤ) ^ i.val •
      Finsupp.lmapDomain M R ((TopCat.toSSet.obj X).δ i)) (Finsupp.single s m)) = _
    simp [Fin.sum_univ_two, LinearMap.add_apply, LinearMap.neg_apply, sub_eq_add_neg]
  rw [hb, map_sub]
  simp [sumCoefficients]


lemma augmentation_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (chainMap R M f).f 0 ≫ augmentation R M Y = augmentation R M X := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  change ULift.up ((sumCoefficients R M _) (Finsupp.mapDomain
    ((TopCat.toSSet.map f).app (op ⦋0⦌)) (Finsupp.single s m))) =
      ULift.up ((sumCoefficients R M _) (Finsupp.single s m))
  simp [sumCoefficients]

/-- Index `0` represents degree `-1`, and index `n+1` represents degree `n`. -/
def augmentedShifted (X : TopCat.{w}) : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.augment (complex R M X) (augmentation R M X) (augmentation_boundary R M X)

def augmentedShiftedMap {X Y : TopCat.{w}} (f : X ⟶ Y) :
    augmentedShifted R M X ⟶ augmentedShifted R M Y :=
  ChainComplex.ofHom (fun n => match n with
    | 0 => 𝟙 _
    | n+1 => (chainMap R M f).f n) (by
    intro n
    cases n with
    | zero => simpa [augmentedShifted] using augmentation_naturality R M f
    | succ n => simp [augmentedShifted, (chainMap R M f).comm (n+1) n])

def augmentedShiftedFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ where
  obj := augmentedShifted R M
  map := augmentedShiftedMap R M
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      change ((chainFunctor R M).map (𝟙 X)).f n = 𝟙 ((complex R M X).X n)
      rw [(chainFunctor R M).map_id]
      rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      change ((chainFunctor R M).map (f ≫ g)).f n =
        (((chainFunctor R M).map f) ≫ ((chainFunctor R M).map g)).f n
      rw [(chainFunctor R M).map_comp]

/-- Embedding with image the integers ≥ a; it preserves the downward differential. -/
def degreeEmbedding (a : ℤ) : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => a + (n : ℤ))
    (by intros i j h; dsimp at h; omega)
    (by intros i j; change j + 1 = i ↔ a + (j : ℤ) + 1 = a + (i : ℤ); omega)

set_option backward.isDefEq.respectTransparency false in
instance (a : ℤ) : (degreeEmbedding a).IsRelIff := by
  unfold degreeEmbedding
  infer_instance

/-- Ordinary chains are zero in all negative degrees. -/
def ordinaryComplex (X : TopCat.{w}) : ChainComplex (ModuleCat.{max v w} R) ℤ :=
  (complex R M X).extend (degreeEmbedding 0)

/-- The reduced complex has the coefficient module in degree -1, and is zero below -1. -/
def reducedComplex (X : TopCat.{w}) : ChainComplex (ModuleCat.{max v w} R) ℤ :=
  (augmentedShifted R M X).extend (degreeEmbedding (-1))

def ordinaryNonnegativeIso (X : TopCat.{w}) (n : ℕ) :
    (ordinaryComplex R M X).X (n : ℤ) ≅ (complex R M X).X n :=
  (complex R M X).extendXIso (degreeEmbedding 0) (by change (0 : ℤ) + n = n; omega)

def reducedNonnegativeIso (X : TopCat.{w}) (n : ℕ) :
    (reducedComplex R M X).X (n : ℤ) ≅ (complex R M X).X n :=
  (augmentedShifted R M X).extendXIso (degreeEmbedding (-1))
    (i := n+1) (by change (-1 : ℤ) + ((n+1 : ℕ) : ℤ) = n; omega)

def reducedAugmentationIso (X : TopCat.{w}) :
    (reducedComplex R M X).X (-1) ≅ coefficientModule.{u,v,w} R M :=
  (augmentedShifted R M X).extendXIso (degreeEmbedding (-1)) (i := 0) (by rfl)

/-- In particular the coefficient object in degree -1 is linearly equivalent to M itself. -/
def reducedCoefficientEquiv (X : TopCat.{w}) :
    (reducedComplex R M X).X (-1) ≃ₗ[R] M :=
  (reducedAugmentationIso R M X).toLinearEquiv.trans ULift.moduleEquiv

def ordinaryFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  chainFunctor R M ⋙ (degreeEmbedding 0).extendFunctor _

def reducedFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  augmentedShiftedFunctor R M ⋙ (degreeEmbedding (-1)).extendFunctor _

def homologyFunctor (n : ℤ) : TopCat.{w} ⥤ ModuleCat.{max v w} R :=
  ordinaryFunctor R M ⋙ HomologicalComplex.homologyFunctor _ _ n

def reducedHomologyFunctor (n : ℤ) : TopCat.{w} ⥤ ModuleCat.{max v w} R :=
  reducedFunctor R M ⋙ HomologicalComplex.homologyFunctor _ _ n

abbrev homology (X : TopCat.{w}) (n : ℤ) := (ordinaryComplex R M X).homology n
abbrev reducedHomology (X : TopCat.{w}) (n : ℤ) := (reducedComplex R M X).homology n

def tensorEquiv (X : TopCat.{w}) (n : ℕ) :
    (Chains R X n ⊗[R] M) ≃ₗ[R] Chains M X n :=
  by classical exact TensorProduct.finsuppScalarLeft R M (Simplex X n)

/-! Independent full expected types and values, without assumed certificates. -/
def continuousSimplexChains_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ),
    Chains M X n ≃ₗ[R] (C(Convexity.StdSimplex ℝ (Fin (n+1)), X) →₀ M)

def continuousSimplexChains_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ) :
    Chains M X n ≃ₗ[R] (C(Convexity.StdSimplex ℝ (Fin (n+1)), X) →₀ M) :=
  Finsupp.mapDomain.linearEquiv M R (simplexEquiv X n)

def simplexEquiv_face_type : Prop :=
  ∀ {X : TopCat.{w}} {n : ℕ} (i : Fin (n+2))
    (s : Simplex X (n+1)),
    simplexEquiv X n (face i s) = (simplexEquiv X (n+1) s).comp (faceInclusion i)

def faceInclusion_vertex_type : Prop :=
  ∀ {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)),
    faceInclusion i (Convexity.StdSimplex.single j) =
      Convexity.StdSimplex.single (i.succAbove j)

def faceInclusion_weights_type : Prop :=
  ∀ {n : ℕ} (i : Fin (n+2))
    (x : Convexity.StdSimplex ℝ (Fin (n+1))),
    (faceInclusion i x).weights = x.weights.mapDomain (i.succAbove)

def boundary_single_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ) (s : Simplex X (n+1)) (m : M),
    boundary R M X n (Finsupp.single s m) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • Finsupp.single (face i s) m

def boundary_squared_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ),
    (boundary R M X n).comp (boundary R M X (n+1)) = 0

def ordinary_boundary_zero_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℤ),
    (ordinaryComplex R M X).d 0 n = 0

def augmentation_single_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (s : Simplex X 0) (m : M),
    (augmentation R M X).hom (Finsupp.single s m) = ULift.up m

def augmentation_kills_boundaries_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}),
    (complex R M X).d 1 0 ≫ augmentation R M X = 0

def chainMap_single_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (s : Simplex X n) (m : M),
    ((chainMap R M f).f n).hom (Finsupp.single s m) =
      Finsupp.single ((TopCat.toSSet.map f).app (op ⦋n⦌) s) m

def simplexEquiv_postcomp_type : Prop :=
  ∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (s : Simplex X n),
    simplexEquiv Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) =
      f.hom.comp (simplexEquiv X n s)

def chainMap_id_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}),
    chainMap R M (𝟙 X) = 𝟙 _

def chainMap_comp_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z),
    chainMap R M (f ≫ g) = chainMap R M f ≫ chainMap R M g

def chainMap_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ),
    (chainMap R M f).f (n+1) ≫ (complex R M Y).d (n+1) n =
      (complex R M X).d (n+1) n ≫ (chainMap R M f).f n

def augmentation_natural_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] {X Y : TopCat.{w}} (f : X ⟶ Y),
    (chainMap R M f).f 0 ≫ augmentation R M Y = augmentation R M X

def ordinary_negative_chains_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℤ) (hn : n < 0),
    Limits.IsZero ((ordinaryComplex R M X).X n)

def ordinary_negative_homology_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℤ) (hn : n < 0),
    Limits.IsZero (homology R M X n)

def reduced_below_minus_one_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℤ) (hn : n < -1),
    Limits.IsZero ((reducedComplex R M X).X n) ∧
      Limits.IsZero (reducedHomology R M X n)

def reduced_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ),
    (reducedNonnegativeIso R M X (n+1)).inv ≫
      (reducedComplex R M X).d (n+1 : ℕ) n ≫
        (reducedNonnegativeIso R M X n).hom = (complex R M X).d (n+1) n

def reduced_augmentation_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}),
    (reducedNonnegativeIso R M X 0).inv ≫ (reducedComplex R M X).d 0 (-1) ≫
      (reducedAugmentationIso R M X).hom = augmentation R M X

def tensorEquiv_single_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ) (s : Simplex X n) (r : R) (m : M),
    tensorEquiv R M X n (Finsupp.single s r ⊗ₜ[R] m) = Finsupp.single s (r • m)

def tensorEquiv_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ)
    (z : Chains R X (n+1) ⊗[R] M),
    tensorEquiv R M X n ((boundary R R X n).rTensor M z) =
      boundary R M X n (tensorEquiv R M X (n+1) z)

def tensorEquiv_natural_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (z : Chains R X n ⊗[R] M),
    tensorEquiv R M Y n (((chainMap R R f).f n).hom.rTensor M z) =
      ((chainMap R M f).f n).hom (tensorEquiv R M X n z)

def tensorEquiv_augmentation_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w})
    (z : Chains R X 0 ⊗[R] M),
    augmentationLinear R M X (tensorEquiv R M X 0 z) =
      TensorProduct.lid R M ((augmentationLinear R R X).rTensor M z)

def augmentationLinear_single_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (s : Simplex X 0) (m : M),
    augmentationLinear R M X (Finsupp.single s m) = m

def augmentationLinear_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}),
    (augmentationLinear R M X).comp (boundary R M X 0) = 0

def ordinary_boundary_type : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ),
    (ordinaryNonnegativeIso R M X (n+1)).inv ≫
      (ordinaryComplex R M X).d (n+1 : ℕ) n ≫
        (ordinaryNonnegativeIso R M X n).hom = (complex R M X).d (n+1) n

def singularChainFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ

def singularChainFunctor_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ :=
  chainFunctor R M

def ordinarySingularChainFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ

def ordinarySingularChainFunctor_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  ordinaryFunctor R M

def reducedSingularChainFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ

def reducedSingularChainFunctor_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  reducedFunctor R M

def singularHomologyFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ),
    TopCat.{w} ⥤ ModuleCat.{max v w} R

def singularHomologyFunctor_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ) :
    TopCat.{w} ⥤ ModuleCat.{max v w} R :=
  homologyFunctor R M n

def reducedSingularHomologyFunctor_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ),
    TopCat.{w} ⥤ ModuleCat.{max v w} R

def reducedSingularHomologyFunctor_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℤ) :
    TopCat.{w} ⥤ ModuleCat.{max v w} R :=
  reducedHomologyFunctor R M n

def moduleCoefficients_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ),
    (Chains R X n ⊗[R] M) ≃ₗ[R] Chains M X n

def moduleCoefficients_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) (n : ℕ) :
    (Chains R X n ⊗[R] M) ≃ₗ[R] Chains M X n :=
  tensorEquiv R M X n

def augmentationMap_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}),
    Chains M X 0 →ₗ[R] M

def augmentationMap_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) :
    Chains M X 0 →ₗ[R] M :=
  augmentationLinear R M X

def reducedCoefficient_type :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}),
    (reducedComplex R M X).X (-1) ≃ₗ[R] M

def reducedCoefficient_value (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (X : TopCat.{w}) :
    (reducedComplex R M X).X (-1) ≃ₗ[R] M :=
  reducedCoefficientEquiv R M X

def singularBasis_type :=
  ∀ (R : Type u) [CommRing R] (X : TopCat.{w}) (n : ℕ),
    Module.Basis (Simplex X n) R (Chains R X n)

def singularBasis_value (R : Type u) [CommRing R] (X : TopCat.{w}) (n : ℕ) :
    Module.Basis (Simplex X n) R (Chains R X n) :=
  Finsupp.basisSingleOne

def abelianCoefficients_type :=
  ∀ (A : Type v) [AddCommGroup A] (X : TopCat.{w}) (n : ℕ),
    (Chains ℤ X n ⊗[ℤ] A) ≃ₗ[ℤ] Chains A X n

def abelianCoefficients_value (A : Type v) [AddCommGroup A] (X : TopCat.{w}) (n : ℕ) :
    (Chains ℤ X n ⊗[ℤ] A) ≃ₗ[ℤ] Chains A X n :=
  tensorEquiv ℤ A X n

end P202Specs.SingularChains
