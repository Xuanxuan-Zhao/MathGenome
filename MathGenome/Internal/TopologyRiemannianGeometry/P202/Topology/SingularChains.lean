import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct
namespace P202.SingularChains
open P202Specs.SingularChains
universe u v w
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The canonical coordinates on chains really are finitely supported continuous simplices. -/
def continuousSimplexChains (X : TopCat.{w}) (n : ℕ) :
    Chains M X n ≃ₗ[R] (C(Convexity.StdSimplex ℝ (Fin (n+1)), X) →₀ M) :=
  Finsupp.mapDomain.linearEquiv M R (simplexEquiv X n)

theorem simplexEquiv_face {X : TopCat.{w}} {n : ℕ} (i : Fin (n+2))
    (s : Simplex X (n+1)) :
    simplexEquiv X n (face i s) = (simplexEquiv X (n+1) s).comp (faceInclusion i) := by
  ext x
  rfl

theorem faceInclusion_vertex {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
    faceInclusion i (Convexity.StdSimplex.single j) =
      Convexity.StdSimplex.single (i.succAbove j) := by
  change (Convexity.StdSimplex.single j).map (SimplexCategory.δ i) = _
  simp [SimplexCategory.coe_δ]

theorem faceInclusion_weights {n : ℕ} (i : Fin (n+2))
    (x : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (faceInclusion i x).weights = x.weights.mapDomain (i.succAbove) := by
  rfl

theorem boundary_single (X : TopCat.{w}) (n : ℕ) (s : Simplex X (n+1)) (m : M) :
    boundary R M X n (Finsupp.single s m) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • Finsupp.single (face i s) m := by
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj
    (simplicialChains R M X)).d (n+1) n).hom (Finsupp.single s m) = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp [simplicialChains, finsuppFunctor, LinearMap.sum_apply, LinearMap.smul_apply]

theorem boundary_squared (X : TopCat.{w}) (n : ℕ) :
    (boundary R M X n).comp (boundary R M X (n+1)) = 0 := by
  exact congrArg ModuleCat.Hom.hom ((complex R M X).d_comp_d (n+2) (n+1) n)

theorem ordinary_boundary_zero (X : TopCat.{w}) (n : ℤ) :
    (ordinaryComplex R M X).d 0 n = 0 := by
  apply HomologicalComplex.extend_d_from_eq_zero
    (complex R M X) (degreeEmbedding 0) 0 n 0 (by rfl)
  simp [ComplexShape.down_Rel]

theorem augmentation_single (X : TopCat.{w}) (s : Simplex X 0) (m : M) :
    (augmentation R M X).hom (Finsupp.single s m) = ULift.up m := by
  change ULift.up ((sumCoefficients R M _) (Finsupp.single s m)) = _
  simp [sumCoefficients]

theorem augmentation_kills_boundaries (X : TopCat.{w}) :
    (complex R M X).d 1 0 ≫ augmentation R M X = 0 :=
  augmentation_boundary R M X

theorem chainMap_single {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (s : Simplex X n) (m : M) :
    ((chainMap R M f).f n).hom (Finsupp.single s m) =
      Finsupp.single ((TopCat.toSSet.map f).app (op ⦋n⦌) s) m := by
  change Finsupp.mapDomain _ (Finsupp.single s m) = _
  simp

theorem simplexEquiv_postcomp {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (s : Simplex X n) :
    simplexEquiv Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) =
      f.hom.comp (simplexEquiv X n s) := by
  ext x
  rfl

theorem chainMap_id (X : TopCat.{w}) : chainMap R M (𝟙 X) = 𝟙 _ :=
  (chainFunctor R M).map_id X

theorem chainMap_comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chainMap R M (f ≫ g) = chainMap R M f ≫ chainMap R M g :=
  (chainFunctor R M).map_comp f g

theorem chainMap_boundary {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (chainMap R M f).f (n+1) ≫ (complex R M Y).d (n+1) n =
      (complex R M X).d (n+1) n ≫ (chainMap R M f).f n :=
  (chainMap R M f).comm (n+1) n

theorem augmentation_natural {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (chainMap R M f).f 0 ≫ augmentation R M Y = augmentation R M X :=
  augmentation_naturality R M f

theorem ordinary_negative_chains (X : TopCat.{w}) (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((ordinaryComplex R M X).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change (0 : ℤ) + i = n at h
  omega

theorem ordinary_negative_homology (X : TopCat.{w}) (n : ℤ) (hn : n < 0) :
    Limits.IsZero (homology R M X n) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.extend_exactAt
  intro i h
  change (0 : ℤ) + i = n at h
  omega

theorem reduced_below_minus_one (X : TopCat.{w}) (n : ℤ) (hn : n < -1) :
    Limits.IsZero ((reducedComplex R M X).X n) ∧
      Limits.IsZero (reducedHomology R M X n) := by
  have h : ∀ i, (degreeEmbedding (-1)).f i ≠ n := by
    intro i hi
    change (-1 : ℤ) + i = n at hi
    omega
  exact ⟨HomologicalComplex.isZero_extend_X _ _ _ h,
    (HomologicalComplex.extend_exactAt _ _ _ h).isZero_homology⟩

theorem reduced_boundary (X : TopCat.{w}) (n : ℕ) :
    (reducedNonnegativeIso R M X (n+1)).inv ≫
      (reducedComplex R M X).d (n+1 : ℕ) n ≫
        (reducedNonnegativeIso R M X n).hom = (complex R M X).d (n+1) n := by
  unfold reducedComplex
  rw [HomologicalComplex.extend_d_eq (augmentedShifted R M X) (degreeEmbedding (-1))
    (i := n+2) (j := n+1) (by change (-1 : ℤ) + ((n+2 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ); omega)
    (by change (-1 : ℤ) + ((n+1 : ℕ) : ℤ) = n; omega)]
  simp [reducedNonnegativeIso, augmentedShifted]

theorem reduced_augmentation (X : TopCat.{w}) :
    (reducedNonnegativeIso R M X 0).inv ≫ (reducedComplex R M X).d 0 (-1) ≫
      (reducedAugmentationIso R M X).hom = augmentation R M X := by
  unfold reducedComplex
  rw [HomologicalComplex.extend_d_eq (augmentedShifted R M X) (degreeEmbedding (-1))
    (i := 1) (j := 0) (by change (-1 : ℤ) + 1 = 0; omega) (by rfl)]
  simp [reducedNonnegativeIso, reducedAugmentationIso, augmentedShifted]

theorem tensorEquiv_single (X : TopCat.{w}) (n : ℕ) (s : Simplex X n) (r : R) (m : M) :
    tensorEquiv R M X n (Finsupp.single s r ⊗ₜ[R] m) = Finsupp.single s (r • m) := by
  classical
  ext i
  by_cases h : s = i <;> simp [tensorEquiv, h]

theorem tensorEquiv_boundary (X : TopCat.{w}) (n : ℕ)
    (z : Chains R X (n+1) ⊗[R] M) :
    tensorEquiv R M X n ((boundary R R X n).rTensor M z) =
      boundary R M X n (tensorEquiv R M X (n+1) z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz' 
  | tmul p m =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hp hq
    | single s r =>
      simp only [LinearMap.rTensor_tmul, boundary_single, tensorEquiv_single R M,
        TensorProduct.sum_tmul, map_sum, Finsupp.smul_single]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact smul_assoc ((-1 : ℤ) ^ i.val) r m

theorem tensorEquiv_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (z : Chains R X n ⊗[R] M) :
    tensorEquiv R M Y n (((chainMap R R f).f n).hom.rTensor M z) =
      ((chainMap R M f).f n).hom (tensorEquiv R M X n z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz' 
  | tmul p m =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hp hq
    | single s r =>
      simp only [LinearMap.rTensor_tmul, chainMap_single, tensorEquiv_single R M]

theorem tensorEquiv_augmentation (X : TopCat.{w})
    (z : Chains R X 0 ⊗[R] M) :
    augmentationLinear R M X (tensorEquiv R M X 0 z) =
      TensorProduct.lid R M ((augmentationLinear R R X).rTensor M z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul p m =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hp hq
    | single s r =>
      simp [tensorEquiv_single R M, augmentationLinear, sumCoefficients]

theorem augmentationLinear_single (X : TopCat.{w}) (s : Simplex X 0) (m : M) :
    augmentationLinear R M X (Finsupp.single s m) = m := by
  simp [augmentationLinear, sumCoefficients]

theorem augmentationLinear_boundary (X : TopCat.{w}) :
    (augmentationLinear R M X).comp (boundary R M X 0) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (augmentation_boundary R M X)
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun h c
  exact congrArg ULift.down hc

theorem ordinary_boundary (X : TopCat.{w}) (n : ℕ) :
    (ordinaryNonnegativeIso R M X (n+1)).inv ≫
      (ordinaryComplex R M X).d (n+1 : ℕ) n ≫
        (ordinaryNonnegativeIso R M X n).hom = (complex R M X).d (n+1) n := by
  unfold ordinaryComplex
  rw [HomologicalComplex.extend_d_eq (complex R M X) (degreeEmbedding 0)
    (i := n+1) (j := n) (by change (0 : ℤ) + ((n+1 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ); omega)
    (by change (0 : ℤ) + n = n; omega)]
  simp [ordinaryNonnegativeIso]

def singularChainFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℕ :=
  chainFunctor R M

def ordinarySingularChainFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  ordinaryFunctor R M

def reducedSingularChainFunctor : TopCat.{w} ⥤ ChainComplex (ModuleCat.{max v w} R) ℤ :=
  reducedFunctor R M

def singularHomologyFunctor (n : ℤ) : TopCat.{w} ⥤ ModuleCat.{max v w} R :=
  homologyFunctor R M n

def reducedSingularHomologyFunctor (n : ℤ) : TopCat.{w} ⥤ ModuleCat.{max v w} R :=
  reducedHomologyFunctor R M n

def moduleCoefficients (X : TopCat.{w}) (n : ℕ) :
    (Chains R X n ⊗[R] M) ≃ₗ[R] Chains M X n := tensorEquiv R M X n

def augmentationMap (X : TopCat.{w}) : Chains M X 0 →ₗ[R] M :=
  augmentationLinear R M X

def reducedCoefficient (X : TopCat.{w}) : (reducedComplex R M X).X (-1) ≃ₗ[R] M :=
  reducedCoefficientEquiv R M X

/-- An actual basis, including the possibly empty simplex index set. -/
def singularBasis (X : TopCat.{w}) (n : ℕ) : Module.Basis (Simplex X n) R (Chains R X n) :=
  Finsupp.basisSingleOne

/-- Covers arbitrary abelian coefficients with their canonical ℤ-module structure. -/
def abelianCoefficients (A : Type v) [AddCommGroup A] (X : TopCat.{w}) (n : ℕ) :
    (Chains ℤ X n ⊗[ℤ] A) ≃ₗ[ℤ] Chains A X n := tensorEquiv ℤ A X n

end P202.SingularChains
