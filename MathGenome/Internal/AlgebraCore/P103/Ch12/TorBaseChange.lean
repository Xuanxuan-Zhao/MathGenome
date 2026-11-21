import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.TorBaseChange
import MathGenome.Internal.AlgebraCore.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

namespace P103.Ch12.TorBaseChange
open CategoryTheory
open scoped TensorProduct
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch12.TorBaseChange
noncomputable section
set_option maxHeartbeats 1000000
universe u v w
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem cancel_natural {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (f : M →ₗ[R] N) :
    (TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[S] C) f).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S C M).toLinearMap =
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S C N).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[S] C) (f.baseChange S)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  induction x using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem distrib_natural {M N B : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup B] [Module R M] [Module R N] [Module R B] (f : M →ₗ[R] N) :
    (TensorProduct.AlgebraTensorModule.map
      (LinearMap.id : S ⊗[R] B →ₗ[S] S ⊗[R] B) (f.baseChange S)).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S B M).toLinearMap =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S B N).toLinearMap.comp
      ((TensorProduct.AlgebraTensorModule.map (LinearMap.id : B →ₗ[R] B) f).baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Cancellation is S-linear for the action on C. -/
def firstTensorIso (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] :
    coefficientComplex (S := S) (R := S) (extendComplex S K) C ≅
      coefficientComplex (S := S) K C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S C (K.X n)).toModuleIso)
    (by
      intro i j _
      exact ModuleCat.hom_ext (cancel_natural C (K.d i j).hom))

theorem firstTensorIso_formula (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] :
    FirstComparison (S := S) K C (firstTensorIso (S := S) K C) := by
  constructor <;> intros <;> rfl

/-- Scalar extension distributes over the two tensor factors. -/
def secondTensorIso (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :
    extendComplex.{u,max v w} S (coefficientComplex (S := R) K B) ≅
      coefficientComplex (S := S) (R := S) (extendComplex S K) (S ⊗[R] B) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.AlgebraTensorModule.distribBaseChange R S B (K.X n)).toModuleIso)
    (by
      intro i j _
      exact ModuleCat.hom_ext (distrib_natural (S := S) (B := B) (K.d i j).hom))

/-- Tensor extension preserves projective terms with no finite generation. -/
theorem projective_baseChange (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Projective R M] : Module.Projective S (S ⊗[R] M) := by
  infer_instance

/-- Flatness preserves exactness at each term of the augmented resolution. -/
def extendedResolution {A : Type v} [AddCommGroup A] [Module R A]
    [Module.Flat R S] (P : LeftResolution R A) : LeftResolution S (S ⊗[R] A) where
  complex := extendComplex S P.complex
  ε := P.ε.baseChange S
  surjective := by
    exact LinearMap.lTensor_surjective S P.surjective
  exact_zero := by
    have h := Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr P.exact_zero.symm)
    ext x
    exact (h x).symm
  exact_succ n := by
    have h := Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr (P.exact_succ n).symm)
    ext x
    exact (h x).symm

theorem extendedResolution_projective {A : Type v} [AddCommGroup A] [Module R A]
    [Module.Flat R S] (P : LeftResolution R A) (hP : P.IsProjective) :
    (extendedResolution (S := S) P).IsProjective := by
  intro n
  letI := hP n
  exact projective_baseChange (S := S) (P.complex.X n)

def extensionData {A : Type v} [AddCommGroup A] [Module R A]
    [Module.Flat R S] (P : LeftResolution R A) (hP : P.IsProjective) :
    ExtendedResolution (S := S) P where
  resolution := extendedResolution P
  projective := extendedResolution_projective P hP
  complexIso := Iso.refl _
  augmentation := by intros; rfl

/-- The flat base change of the inclusion of cycles. -/
def cyclesExtensionMap (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    S ⊗[R] cycles K n →ₗ[S] cycles (extendComplex S K) n :=
  ((cycles K n).subtype.baseChange S).codRestrict _ (by
    intro x
    change ((K.d n ((ComplexShape.down ℕ).next n)).hom.baseChange S)
      ((cycles K n).subtype.baseChange S x) = 0
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have h : (K.d n ((ComplexShape.down ℕ).next n)).hom.comp (cycles K n).subtype = 0 :=
      LinearMap.comp_ker_subtype _
    rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

def cyclesExtensionEquiv [Module.Flat R S]
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    S ⊗[R] cycles K n ≃ₗ[S] cycles (extendComplex S K) n :=
  LinearEquiv.ofBijective (cyclesExtensionMap (S := S) K n) (by
    constructor
    · intro x y h
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (cycles K n).subtype Subtype.val_injective (congrArg Subtype.val h)
    · intro z
      have h := Module.Flat.lTensor_exact S
        (LinearMap.exact_subtype_ker_map (K.d n ((ComplexShape.down ℕ).next n)).hom)
      obtain ⟨x, hx⟩ := (h z.val).mp z.property
      exact ⟨x, Subtype.ext hx⟩)

/-- The incoming differential with its codomain restricted to cycles. -/
def differentialToCycles (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    K.X ((ComplexShape.down ℕ).prev n) →ₗ[R] cycles K n :=
  (K.d ((ComplexShape.down ℕ).prev n) n).hom.codRestrict _
    (by intro x; exact boundaryInclusion K n ⟨x, rfl⟩)

theorem differentialToCycles_exact (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    Function.Exact (differentialToCycles K n) (homologyClass K n) := by
  intro z
  rw [show homologyClass K n z = 0 ↔ z ∈ cycleBoundaries K n from
    Submodule.Quotient.mk_eq_zero _]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem cyclesExtension_differential (K : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (n : ℕ) (x : S ⊗[R] K.X ((ComplexShape.down ℕ).prev n)) :
    cyclesExtensionMap (S := S) K n ((differentialToCycles K n).baseChange S x) =
      differentialToCycles (extendComplex S K) n x := by
  apply Subtype.ext
  change ((cycles K n).subtype.baseChange S)
    ((differentialToCycles K n).baseChange S x) =
    ((K.d ((ComplexShape.down ℕ).prev n) n).hom.baseChange S) x
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

/-- The common cycle module surjects onto the extended homology. -/
def extendedHomologyProjection (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    S ⊗[R] cycles K n →ₗ[S] Homology (extendComplex S K) n :=
  (homologyClass _ n).comp (cyclesExtensionMap K n)

theorem homology_projection_kernel [Module.Flat R S]
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    LinearMap.ker ((homologyClass K n).baseChange S) =
      LinearMap.ker (extendedHomologyProjection (S := S) K n) := by
  have h := Module.Flat.lTensor_exact S (differentialToCycles_exact K n)
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (h x).mp hx
    change homologyClass _ n (cyclesExtensionMap K n x) = 0
    rw [← hy]
    change homologyClass _ n
      (cyclesExtensionMap K n ((differentialToCycles K n).baseChange S y)) = 0
    rw [cyclesExtension_differential]
    exact (differentialToCycles_exact (extendComplex S K) n _).mpr ⟨y, rfl⟩
  · intro hx
    change homologyClass _ n (cyclesExtensionMap K n x) = 0 at hx
    obtain ⟨y, hy⟩ := (differentialToCycles_exact (extendComplex S K) n _).mp hx
    have he : (differentialToCycles K n).baseChange S y = x := by
      apply (cyclesExtensionEquiv (S := S) K n).injective
      exact (cyclesExtension_differential K n y).trans hy
    exact (h x).mpr ⟨y, he⟩

def homologyExtensionEquiv [Module.Flat R S]
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    S ⊗[R] Homology K n ≃ₗ[S] Homology (extendComplex S K) n :=
  (((homologyClass K n).baseChange S).quotKerEquivOfSurjective
    (LinearMap.lTensor_surjective S (Submodule.mkQ_surjective _))).symm ≪≫ₗ
  Submodule.quotEquivOfEq _ _ (homology_projection_kernel (S := S) K n) ≪≫ₗ
  (extendedHomologyProjection (S := S) K n).quotKerEquivOfSurjective
    ((Submodule.mkQ_surjective (cycleBoundaries (extendComplex S K) n)).comp
      (cyclesExtensionEquiv (S := S) K n).surjective)

theorem homologyExtensionEquiv_projection [Module.Flat R S]
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ)
    (x : S ⊗[R] cycles K n) :
    homologyExtensionEquiv (S := S) K n ((homologyClass K n).baseChange S x) =
      homologyClass _ n (cyclesExtensionMap K n x) := by
  change (homologyExtensionEquiv (S := S) K n).toLinearMap.comp
    ((homologyClass K n).baseChange S) x = extendedHomologyProjection K n x
  simp only [homologyExtensionEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.comp_apply]
  erw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

abbrev extendMap {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) :=
  ((extensionFunctor R S).mapHomologicalComplex (ComplexShape.down ℕ)).map f

theorem cyclesExtension_natural {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ L) (n : ℕ) (x : S ⊗[R] cycles K n) :
    cyclesExtensionMap (S := S) L n ((cyclesMap f n).baseChange S x) =
      cyclesMap (extendMap (S := S) f) n (cyclesExtensionMap K n x) := by
  apply Subtype.ext
  change ((cycles L n).subtype.baseChange S) ((cyclesMap f n).baseChange S x) =
    ((f.f n).hom.baseChange S) ((cycles K n).subtype.baseChange S x)
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  rfl

theorem homologyExtensionEquiv_natural [Module.Flat R S]
    {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) (n : ℕ)
    (x : S ⊗[R] Homology K n) :
    homologyExtensionEquiv (S := S) L n ((homologyMap f n).baseChange S x) =
      homologyMap (extendMap (S := S) f) n (homologyExtensionEquiv K n x) := by
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective S (Submodule.mkQ_surjective _) x
  change homologyExtensionEquiv L n ((homologyMap f n).baseChange S
      ((homologyClass K n).baseChange S y)) =
    homologyMap (extendMap f) n (homologyExtensionEquiv K n
      ((homologyClass K n).baseChange S y))
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  have he : (homologyMap f n).comp (homologyClass K n) =
      (homologyClass L n).comp (cyclesMap f n) := rfl
  rw [he, LinearMap.baseChange_comp, LinearMap.comp_apply,
    homologyExtensionEquiv_projection, homologyExtensionEquiv_projection]
  change homologyClass _ n
    (cyclesExtensionMap L n ((cyclesMap f n).baseChange S y)) =
    homologyClass _ n (cyclesMap (extendMap f) n (cyclesExtensionMap K n y))
  rw [cyclesExtension_natural]

def homologyExtensionData [Module.Flat R S] : HomologyExtension.{u,v} R S where
  equiv := homologyExtensionEquiv
  cycle K n s z := by
    refine ⟨cyclesExtensionMap K n (s ⊗ₜ[R] z), rfl, ?_⟩
    exact homologyExtensionEquiv_projection K n (s ⊗ₜ[R] z)
  natural f n x := homologyExtensionEquiv_natural f n x

/-- A chain isomorphism acts on the explicit quotient homology. -/
def homologyIso {T : Type*} [Ring T]
    {K L : ChainComplex (ModuleCat.{v} T) ℕ} (e : K ≅ L) (n : ℕ) :
    Homology K n ≃ₗ[T] Homology L n :=
  ((quotientHomology (ComplexShape.down ℕ) n).mapIso e).toLinearEquiv

def firstTorEquiv {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (C : Type w) [AddCommGroup C] [Module S C]
    [Module R C] [IsScalarTower R S C] (n : ℕ) :
    Homology (coefficientComplex (R := S) (S := S) (extendComplex S P.complex) C) n ≃ₗ[S]
      restrictedTor (S := S) P C n := homologyIso (firstTensorIso P.complex C) n

def secondTorEquiv [Module.Flat R S] {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    S ⊗[R] commutativeTor P B n ≃ₗ[S]
      Homology (coefficientComplex (R := S) (S := S) (extendComplex S P.complex)
        (S ⊗[R] B)) n :=
  homologyExtensionEquiv.{u,max v w} (coefficientComplex (S := R) P.complex B) n ≪≫ₗ
    homologyIso (secondTensorIso P.complex B) n

theorem cancel_mixed {M N C D : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup C] [AddCommGroup D] [Module R M] [Module R N]
    [Module S C] [Module S D] [Module R C] [Module R D]
    [IsScalarTower R S C] [IsScalarTower R S D] (f : M →ₗ[R] N) (g : C →ₗ[S] D) :
    (TensorProduct.AlgebraTensorModule.map g f).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S C M).toLinearMap =
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S D N).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.map g (f.baseChange S)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  induction x using TensorProduct.inductionOn with
  | tmul s m => exact congrArg (fun d => d ⊗ₜ[R] f m) (g.map_smul s c)
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem distrib_mixed {M N B D : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup B] [AddCommGroup D] [Module R M] [Module R N]
    [Module R B] [Module R D] (f : M →ₗ[R] N) (g : B →ₗ[R] D) :
    (TensorProduct.AlgebraTensorModule.map (g.baseChange S) (f.baseChange S)).comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S B M).toLinearMap =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S D N).toLinearMap.comp
      ((TensorProduct.AlgebraTensorModule.map g f).baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

theorem firstTensorIso_natural {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ L) {C D : Type w} [AddCommGroup C] [AddCommGroup D]
    [Module S C] [Module S D] [Module R C] [Module R D]
    [IsScalarTower R S C] [IsScalarTower R S D] (g : C →ₗ[S] D) :
    coefficientMap (R := S) (S := S) (extensionMap (S := S) f) g ≫
        (firstTensorIso (S := S) L D).hom =
      (firstTensorIso (S := S) K C).hom ≫ coefficientMap (S := S) f g := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ModuleCat.hom_ext (cancel_mixed (f.f n).hom g).symm

theorem secondTensorIso_natural {K L : ChainComplex (ModuleCat.{max u v} R) ℕ}
    (f : K ⟶ L) {B D : Type w} [AddCommGroup B] [AddCommGroup D]
    [Module R B] [Module R D] (g : B →ₗ[R] D) :
    extensionMap.{u,max v w} (S := S) (coefficientMap (S := R) f g) ≫ (secondTensorIso (S := S) L D).hom =
      (secondTensorIso (S := S) K B).hom ≫
        coefficientMap (R := S) (S := S) (extensionMap (S := S) f) (g.baseChange S) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ModuleCat.hom_ext (distrib_mixed (S := S) (f.f n).hom g).symm

theorem firstTorEquiv_natural {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    {C D : Type w} [AddCommGroup C] [AddCommGroup D] [Module S C] [Module S D]
    [Module R C] [Module R D] [IsScalarTower R S C] [IsScalarTower R S D]
    (l : P.complex ⟶ Q.complex) (g : C →ₗ[S] D) (n : ℕ) x :
    firstTorEquiv (S := S) Q D n
        (homologyMap (coefficientMap (R := S) (S := S) (extensionMap (S := S) l) g) n x) =
      homologyMap (coefficientMap (S := S) l g) n (firstTorEquiv (S := S) P C n x) := by
  change (homologyMap (firstTensorIso Q.complex D).hom n)
    (homologyMap (coefficientMap (extensionMap l) g) n x) =
    homologyMap (coefficientMap l g) n (homologyMap (firstTensorIso P.complex C).hom n x)
  rw [← LinearMap.comp_apply, ← P103.Ch10.Complexes.homologyMap_comp,
    ← LinearMap.comp_apply, ← P103.Ch10.Complexes.homologyMap_comp,
    firstTensorIso_natural]

theorem secondTorEquiv_natural [Module.Flat R S]
    {A A' : Type v} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A']
    (P : LeftResolution R A) (Q : LeftResolution R A')
    {B D : Type w} [AddCommGroup B] [AddCommGroup D] [Module R B] [Module R D]
    (l : P.complex ⟶ Q.complex) (g : B →ₗ[R] D) (n : ℕ) x :
    secondTorEquiv (S := S) Q D n
        ((homologyMap (coefficientMap (S := R) l g) n).baseChange S x) =
      homologyMap (coefficientMap (R := S) (S := S) (extensionMap (S := S) l)
        (g.baseChange S)) n (secondTorEquiv (S := S) P B n x) := by
  change (homologyMap (secondTensorIso Q.complex D).hom n)
      (homologyExtensionEquiv (coefficientComplex (S := R) Q.complex D) n
        ((homologyMap (coefficientMap (S := R) l g) n).baseChange S x)) =
    homologyMap (coefficientMap (extensionMap l) (g.baseChange S)) n
      (homologyMap (secondTensorIso P.complex B).hom n
        (homologyExtensionEquiv (coefficientComplex (S := R) P.complex B) n x))
  rw [homologyExtensionEquiv_natural,
    ← LinearMap.comp_apply, ← P103.Ch10.Complexes.homologyMap_comp,
    ← LinearMap.comp_apply, ← P103.Ch10.Complexes.homologyMap_comp,
    secondTensorIso_natural]

theorem coefficient_lift_independent {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    (hP : P.IsProjective) (f : A →ₗ[R] A') (l l' : P.complex ⟶ Q.complex)
    (hl : ChainLift P Q f l) (hl' : ChainLift P Q f l')
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C] n :
    homologyMap (coefficientMap (S := S) l (LinearMap.id : C →ₗ[S] C)) n =
      homologyMap (coefficientMap (S := S) l' (LinearMap.id : C →ₗ[S] C)) n := by
  have h := P103.Ch10.Comparison.chain_homology_independent R S
    (coefficientTensorFunctor R S C) A A' P Q hP f l l' n hl hl'
  exact congrArg ModuleCat.Hom.hom h

section AdditiveHomology
variable {R' T : Type*} [Ring R'] [Ring T]
    {K : ChainComplex (ModuleCat.{v} R') ℕ} {L : ChainComplex (ModuleCat.{w} T) ℕ}
    (e : ∀ n, K.X n ≃+ L.X n)
    (he : ∀ i j x, e j ((K.d i j).hom x) = (L.d i j).hom (e i x))

def additiveCyclesEquiv (n : ℕ) : cycles K n ≃+ cycles L n where
  toFun z := ⟨e n z.val, by
    change (L.d n ((ComplexShape.down ℕ).next n)).hom (e n z.val) = 0
    rw [← he, z.property, map_zero]⟩
  invFun z := ⟨(e n).symm z.val, by
    apply (e ((ComplexShape.down ℕ).next n)).injective
    rw [he, (e n).apply_symm_apply, map_zero]
    exact z.property⟩
  left_inv z := Subtype.ext ((e n).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((e n).apply_symm_apply z.val)
  map_add' x y := Subtype.ext ((e n).map_add x.val y.val)

theorem additiveCyclesEquiv_boundary (n : ℕ) (z : cycles K n) :
    z ∈ cycleBoundaries K n ↔ additiveCyclesEquiv e he n z ∈ cycleBoundaries L n := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e ((ComplexShape.down ℕ).prev n) x, ?_⟩
    exact (he _ _ x).symm.trans (congrArg (e n) hx)
  · rintro ⟨x, hx⟩
    refine ⟨(e ((ComplexShape.down ℕ).prev n)).symm x, ?_⟩
    change (K.d ((ComplexShape.down ℕ).prev n) n).hom
      ((e ((ComplexShape.down ℕ).prev n)).symm x) = z.val
    apply (e n).injective
    rw [he, (e ((ComplexShape.down ℕ).prev n)).apply_symm_apply]
    exact hx

def additiveHomologyEquiv (n : ℕ) : Homology K n ≃+ Homology L n :=
  QuotientAddGroup.congr (cycleBoundaries K n).toAddSubgroup
    (cycleBoundaries L n).toAddSubgroup (additiveCyclesEquiv e he n) (by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (additiveCyclesEquiv_boundary e he n x).mp hx
      · intro hz
        refine ⟨(additiveCyclesEquiv e he n).symm z, ?_,
          (additiveCyclesEquiv e he n).apply_symm_apply z⟩
        exact (additiveCyclesEquiv_boundary e he n _).mpr (by simpa using hz))


end AdditiveHomology

/-- On terms the bridge is precisely the canonical tensor interchange. -/
def tensorBridgeEquiv (A : Type v) (C : Type w) [AddCommGroup A] [AddCommGroup C]
    [Module R A] [Module R C] :
    letI := P103.BalancedTensor.commRightModule R A
    P103.BalancedTensor.Tensor R A C ≃+ C ⊗[R] A := by
  letI := P103.BalancedTensor.commRightModule R A
  letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
  exact (P103.BalancedTensor.commAddEquiv :
    P103.BalancedTensor.Tensor R A C ≃+ A ⊗[R] C).trans
      (TensorProduct.comm R A C).toAddEquiv

theorem tensorBridgeEquiv_formula (A : Type v) (C : Type w)
    [AddCommGroup A] [AddCommGroup C] [Module R A] [Module R C] :
    letI := P103.BalancedTensor.commRightModule R A
    ∀ x, tensorBridgeEquiv (R := R) A C x = balancedToTensor (R := R) A C x := by
  letI := P103.BalancedTensor.commRightModule R A
  intro x
  induction x using P103.BalancedTensor.induction_on with
  | h0 => exact (map_zero _).trans (map_zero _).symm
  | ht a c => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

theorem tensorBridgeEquiv_natural {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N)
    (C : Type w) [AddCommGroup C] [Module R C] :
    letI := P103.BalancedTensor.commRightModule R M
    letI := P103.BalancedTensor.commRightModule R N
    ∀ x, tensorBridgeEquiv (R := R) N C (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
      ({ f.toAddMonoidHom with map_smul' := fun r m => f.map_smul r.unop m } :
        M →ₗ[Rᵐᵒᵖ] N) LinearMap.id x) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : C →ₗ[R] C) f
        (tensorBridgeEquiv (R := R) M C x) := by
  letI := P103.BalancedTensor.commRightModule R M
  letI := P103.BalancedTensor.commRightModule R N
  intro x
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ht m c => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

def torBridgeEquiv {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (C : Type w) [AddCommGroup C] [Module S C]
    [Module R C] [IsScalarTower R S C] (n : ℕ) :
    letI := P103.BalancedTensor.commRightModule R A
    P103.Specs.Ch11.ExtTorDefinitions.TorWith (rightResolution P) C n ≃+
      restrictedTor (S := S) P C n := by
  letI := P103.BalancedTensor.commRightModule R A
  exact additiveHomologyEquiv (fun n => tensorBridgeEquiv (R := R) (P.complex.X n) C)
    (fun i j x => tensorBridgeEquiv_natural (P.complex.d i j).hom C x) n

def torBridgeCycles {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (C : Type w) [AddCommGroup C] [Module S C]
    [Module R C] [IsScalarTower R S C] (n : ℕ) :
    letI := P103.BalancedTensor.commRightModule R A
    cycles (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (rightResolution P).complex C) n ≃+
      cycles (coefficientComplex (S := S) P.complex C) n := by
  letI := P103.BalancedTensor.commRightModule R A
  exact additiveCyclesEquiv (fun n => tensorBridgeEquiv (R := R) (P.complex.X n) C)
    (fun i j x => tensorBridgeEquiv_natural (P.complex.d i j).hom C x) n

theorem torBridgeEquiv_cycle {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (C : Type w) [AddCommGroup C] [Module S C]
    [Module R C] [IsScalarTower R S C] n :
    letI := P103.BalancedTensor.commRightModule R A
    ∀ z : cycles (P103.Specs.Ch11.ExtTorDefinitions.tensorComplex (rightResolution P).complex C) n,
    torBridgeEquiv (S := S) P C n (homologyClass _ n z) =
      homologyClass _ n (torBridgeCycles (S := S) P C n z) := by
  letI := P103.BalancedTensor.commRightModule R A
  intro z
  rfl

theorem tensorBridgeEquiv_scalar (M : Type*) [AddCommGroup M] [Module R M]
    (C : Type w) [AddCommGroup C] [Module S C] [Module R C] [IsScalarTower R S C]
    (s : S) :
    letI := P103.BalancedTensor.commRightModule R M
    ∀ x, tensorBridgeEquiv (R := R) M C
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id
        ((s • (LinearMap.id : C →ₗ[S] C)).restrictScalars R) x) =
      s • tensorBridgeEquiv (R := R) M C x := by
  letI := P103.BalancedTensor.commRightModule R M
  intro x
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero, smul_zero]
  | ht m c => exact TensorProduct.smul_tmul' s c m
  | ha x y hx hy => simp only [map_add, smul_add, hx, hy]

theorem torBridgeEquiv_scalar {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (C : Type w) [AddCommGroup C] [Module S C]
    [Module R C] [IsScalarTower R S C] n (s : S) :
    letI := P103.BalancedTensor.commRightModule R A
    ∀ x, torBridgeEquiv (S := S) P C n
      (homologyMap (P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (rightResolution P).complex
        ((s • (LinearMap.id : C →ₗ[S] C)).restrictScalars R)) n x) =
      s • torBridgeEquiv (S := S) P C n x := by
  letI := P103.BalancedTensor.commRightModule R A
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change torBridgeEquiv P C n (homologyClass _ n (cyclesMap _ n z)) =
    s • torBridgeEquiv P C n (homologyClass _ n z)
  rw [torBridgeEquiv_cycle, torBridgeEquiv_cycle, ← map_smul]
  apply congrArg (homologyClass _ n)
  apply Subtype.ext
  exact tensorBridgeEquiv_scalar (P.complex.X n) C s z.val

theorem rightResolution_projective {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (hP : P.IsProjective) :
    letI := P103.BalancedTensor.commRightModule R A
    (rightResolution P).IsProjective := by
  letI := P103.BalancedTensor.commRightModule R A
  intro n
  letI := hP n
  letI := P103.BalancedTensor.commRightModule R (P.complex.X n)
  letI := RingHomInvPair.of_ringEquiv (RingEquiv.toOpposite R)
  letI := RingHomInvPair.of_ringEquiv_symm (RingEquiv.toOpposite R)
  let e : P.complex.X n ≃ₛₗ[(RingEquiv.toOpposite R : R →+* Rᵐᵒᵖ)] P.complex.X n :=
    { AddEquiv.refl _ with map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv e

theorem tensorBridgeEquiv_mixed {M N C D : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup C] [AddCommGroup D] [Module R M] [Module R N]
    [Module S C] [Module S D] [Module R C] [Module R D]
    [IsScalarTower R S C] [IsScalarTower R S D] (f : M →ₗ[R] N) (g : C →ₗ[S] D) :
    letI := P103.BalancedTensor.commRightModule R M
    letI := P103.BalancedTensor.commRightModule R N
    ∀ x, tensorBridgeEquiv (R := R) N D
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        ({ f.toAddMonoidHom with map_smul' := fun r m => f.map_smul r.unop m } : M →ₗ[Rᵐᵒᵖ] N)
        (g.restrictScalars R) x) =
      TensorProduct.AlgebraTensorModule.map g f (tensorBridgeEquiv (R := R) M C x) := by
  letI := P103.BalancedTensor.commRightModule R M
  letI := P103.BalancedTensor.commRightModule R N
  intro x
  induction x using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ht m c => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

theorem torBridgeEquiv_natural {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module R A] [Module R A'] (P : LeftResolution R A) (Q : LeftResolution R A')
    {C D : Type w} [AddCommGroup C] [AddCommGroup D] [Module S C] [Module S D]
    [Module R C] [Module R D] [IsScalarTower R S C] [IsScalarTower R S D]
    (l : P.complex ⟶ Q.complex) (g : C →ₗ[S] D) n :
    letI := P103.BalancedTensor.commRightModule R A
    letI := P103.BalancedTensor.commRightModule R A'
    ∀ x, torBridgeEquiv (S := S) Q D n
      (homologyMap (P103.Specs.Ch11.ExtTorDefinitions.tensorFirstMap
          (((P103.Specs.Ch11.TorBalance.commRightFunctor R).mapHomologicalComplex
            (ComplexShape.down ℕ)).map l) C ≫
        P103.Specs.Ch11.ExtTorDefinitions.tensorSecondMap (rightResolution Q).complex
          (g.restrictScalars R)) n x) =
      homologyMap (coefficientMap (S := S) l g) n (torBridgeEquiv (S := S) P C n x) := by
  letI := P103.BalancedTensor.commRightModule R A
  letI := P103.BalancedTensor.commRightModule R A'
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  change torBridgeEquiv Q D n (homologyClass _ n (cyclesMap _ n z)) =
    homologyMap (coefficientMap l g) n (torBridgeEquiv P C n (homologyClass _ n z))
  change homologyClass _ n (torBridgeCycles Q D n (cyclesMap _ n z)) =
    homologyClass _ n (cyclesMap (coefficientMap l g) n (torBridgeCycles P C n z))
  apply congrArg (homologyClass _ n)
  apply Subtype.ext
  letI := P103.BalancedTensor.commRightModule R (P.complex.X n)
  letI := P103.BalancedTensor.commRightModule R (Q.complex.X n)
  have h : ∀ x,
      P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (g.restrictScalars R)
        (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
          ({ (l.f n).hom.toAddMonoidHom with map_smul' := fun r m => (l.f n).hom.map_smul r.unop m } :
            P.complex.X n →ₗ[Rᵐᵒᵖ] Q.complex.X n) LinearMap.id x) =
      P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        ({ (l.f n).hom.toAddMonoidHom with map_smul' := fun r m => (l.f n).hom.map_smul r.unop m } :
          P.complex.X n →ₗ[Rᵐᵒᵖ] Q.complex.X n) (g.restrictScalars R) x := by
    intro x
    induction x using P103.BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht p c => rfl
    | ha x y hx hy => simp only [map_add, hx, hy]
  change tensorBridgeEquiv (R := R) (Q.complex.X n) D
    (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id (g.restrictScalars R)
      (P103.Specs.Ch11.ExtTorDefinitions.tensorMap
        ({ (l.f n).hom.toAddMonoidHom with map_smul' := fun r m => (l.f n).hom.map_smul r.unop m } :
          P.complex.X n →ₗ[Rᵐᵒᵖ] Q.complex.X n) LinearMap.id z.val)) =
    TensorProduct.AlgebraTensorModule.map g (l.f n).hom
      (tensorBridgeEquiv (R := R) (P.complex.X n) C z.val)
  exact (congrArg (tensorBridgeEquiv (R := R) (Q.complex.X n) D) (h z.val)).trans
    (tensorBridgeEquiv_mixed (l.f n).hom g z.val)

def torBridgeData : TorBridge.{u,v,w} R S where
  equiv := torBridgeEquiv
  cycle := by
    intro A _ _ P C _ _ _ _ n
    letI := P103.BalancedTensor.commRightModule R A
    intro z
    refine ⟨torBridgeCycles P C n z, ?_, torBridgeEquiv_cycle P C n z⟩
    exact tensorBridgeEquiv_formula (P.complex.X n) C z.val
  scalar := torBridgeEquiv_scalar
  projective := rightResolution_projective
  natural := torBridgeEquiv_natural

/-- Flat base change for arbitrary modules over a flat map of commutative rings.
The comparisons are natural, carry the indicated scalar actions, and are
independent of the chosen projective resolution. -/
theorem flat_base_change :
    flat_base_changeType.{u,v,w} := by
  intro R S _ _ _ _
  refine ⟨{
    extension := fun P hP => extensionData P hP
    homology := homologyExtensionData
    bridgeR := torBridgeData
    bridgeS := torBridgeData
    bridgeSOriginalCoefficient := torBridgeData
    bridgeRestricted := torBridgeData
    firstChain := firstTensorIso
    first_formula := firstTensorIso_formula
    secondChain := secondTensorIso
    second_formula := ?_
    first := firstTorEquiv
    first_induced := ?_
    second := secondTorEquiv
    second_induced := ?_
    first_natural := firstTorEquiv_natural
    second_natural := secondTorEquiv_natural
    lift_independent := ?_
    original_lift_independent := ?_
  }⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro A A' _ _ _ _ P Q hP f l l' hl hl' C _ _ _ _ n
    exact coefficient_lift_independent P Q hP f l l' hl hl' C n
  · intro A A' _ _ _ _ P Q hP f l l' hl hl' B _ _ n
    exact coefficient_lift_independent (S := R) P Q hP f l l' hl hl' B n

end
end P103.Ch12.TorBaseChange
