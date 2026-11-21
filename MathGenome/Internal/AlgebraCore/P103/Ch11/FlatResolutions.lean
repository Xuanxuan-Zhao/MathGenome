import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.FlatResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexConstruction
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence
import Mathlib.Algebra.FiveLemma
import MathGenome.Internal.AlgebraCore.P103.Ch10.AugmentedAssembly
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Computation from ordinary flat resolutions, paper.tex 2676–2706.
The independent Specs state the complete natural, normalized computation
isomorphisms in all nonnegative degrees over arbitrary unital rings.
-/
namespace P103.Ch11.FlatResolutions
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.FlatResolutions
noncomputable section
universe u v w
universe a b c t
variable {R : Type u} [Ring R]

/-- Transport of the shared balanced tensor along linear equivalences in
its two factors, including factors living in different universes. -/
def tensorLinearEquiv {X X' Y Y' : Type*}
    [AddCommGroup X] [AddCommGroup X'] [AddCommGroup Y] [AddCommGroup Y']
    [Module Rᵐᵒᵖ X] [Module Rᵐᵒᵖ X'] [Module R Y] [Module R Y']
    (e : X ≃ₗ[Rᵐᵒᵖ] X') (f : Y ≃ₗ[R] Y') :
    Tensor R X Y ≃ₗ[ℤ] Tensor R X' Y' where
  toLinearMap := tensorMap e.toLinearMap f.toLinearMap
  invFun := tensorMap e.symm.toLinearMap f.symm.toLinearMap
  left_inv z := by
    have h : (tensorMap e.symm.toLinearMap f.symm.toLinearMap).comp
        (tensorMap e.toLinearMap f.toLinearMap) = LinearMap.id := by
      apply tensor_hom_ext
      intro x y
      change tmul R (e.symm (e x)) (f.symm (f y)) = tmul R x y
      rw [e.symm_apply_apply, f.symm_apply_apply]
    exact LinearMap.congr_fun h z
  right_inv z := by
    have h : (tensorMap e.toLinearMap f.toLinearMap).comp
        (tensorMap e.symm.toLinearMap f.symm.toLinearMap) = LinearMap.id := by
      apply tensor_hom_ext
      intro x y
      change tmul R (e (e.symm x)) (f (f.symm y)) = tmul R x y
      rw [e.apply_symm_apply, f.apply_symm_apply]
    exact LinearMap.congr_fun h z

/-- The enlarged-universe flatness interface applies to exact sequences of
arbitrary smaller sizes, by explicit ULift equivalences. -/
theorem flat_tensor_exact {M : Type v} [AddCommGroup M] [Module R M]
    (hM : P103.Specs.Ch02.FlatnessTests.Flat.{u,v,max a b c} R M)
    {X : Type a} {Y : Type b} {Z : Type c}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module Rᵐᵒᵖ X] [Module Rᵐᵒᵖ Y] [Module Rᵐᵒᵖ Z]
    (f : X →ₗ[Rᵐᵒᵖ] Y) (g : Y →ₗ[Rᵐᵒᵖ] Z) (hex : Function.Exact f g) :
    Function.Exact (tensorMap f (LinearMap.id : M →ₗ[R] M))
      (tensorMap g (LinearMap.id : M →ₗ[R] M)) := by
  let eX : ULift.{max u v b c} X ≃ₗ[Rᵐᵒᵖ] X := ULift.moduleEquiv
  let eY : ULift.{max u v a c} Y ≃ₗ[Rᵐᵒᵖ] Y := ULift.moduleEquiv
  let eZ : ULift.{max u v a b} Z ≃ₗ[Rᵐᵒᵖ] Z := ULift.moduleEquiv
  let f' := eY.symm.toLinearMap.comp (f.comp eX.toLinearMap)
  let g' := eZ.symm.toLinearMap.comp (g.comp eY.toLinearMap)
  have h₁ : f.comp eX.toLinearMap = eY.toLinearMap.comp f' := by
    ext x
    exact (eY.apply_symm_apply _).symm
  have h₂ : g.comp eY.toLinearMap = eZ.toLinearMap.comp g' := by
    ext y
    exact (eZ.apply_symm_apply _).symm
  have hex' : Function.Exact f' g' :=
    (Function.Exact.iff_of_ladder_linearEquiv h₁ h₂).mp hex
  have ht := P103.Ch02.FlatnessTests.flat_preserves_exact R M hM _ _ _ f' g' hex'
    (tensorMap f' LinearMap.id).toAddMonoidHom
    (tensorMap g' LinearMap.id).toAddMonoidHom (fun _ _ => rfl) (fun _ _ => rfl)
  let eTX := tensorLinearEquiv eX (LinearEquiv.refl R M)
  let eTY := tensorLinearEquiv eY (LinearEquiv.refl R M)
  let eTZ := tensorLinearEquiv eZ (LinearEquiv.refl R M)
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := eTX) (e₂ := eTY) (e₃ := eTZ) ?_ ?_).mpr ht
  · apply tensor_hom_ext
    intro x m
    change tmul R (f (eX x)) m = tmul R (eY (f' x)) m
    exact congrArg (fun y => tmul R y m) (LinearMap.congr_fun h₁ x)
  · apply tensor_hom_ext
    intro y m
    change tmul R (g (eY y)) m = tmul R (eZ (g' y)) m
    exact congrArg (fun z => tmul R z m) (LinearMap.congr_fun h₂ y)

open private oppositeFlip from MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests

/-- Exactness on the right in the original M⊗_R− orientation. No
commutativity is used: the flip here also reverses the base ring. -/
theorem rightFlat_tensor_exact {M : Type v} [AddCommGroup M] [Module Rᵐᵒᵖ M]
    (hM : P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,max a b c} R M)
    {X : Type a} {Y : Type b} {Z : Type c}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (hex : Function.Exact f g) :
    Function.Exact (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f)
      (tensorMap (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) g) := by
  letI := P103.Specs.Ch02.FlatnessTests.doubleOppositeModule R X
  letI := P103.Specs.Ch02.FlatnessTests.doubleOppositeModule R Y
  letI := P103.Specs.Ch02.FlatnessTests.doubleOppositeModule R Z
  let fop : X →ₗ[Rᵐᵒᵖᵐᵒᵖ] Y :=
    { f.toAddMonoidHom with map_smul' := fun r x => f.map_smul r.unop.unop x }
  let gop : Y →ₗ[Rᵐᵒᵖᵐᵒᵖ] Z :=
    { g.toAddMonoidHom with map_smul' := fun r y => g.map_smul r.unop.unop y }
  have ht := flat_tensor_exact
    ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R M).mp hM) fop gop hex
  let eX : Tensor R M X ≃ₗ[ℤ] Tensor Rᵐᵒᵖ X M :=
    (oppositeFlip (R := R) (A := M) (B := X)).toIntLinearEquiv
  let eY : Tensor R M Y ≃ₗ[ℤ] Tensor Rᵐᵒᵖ Y M :=
    (oppositeFlip (R := R) (A := M) (B := Y)).toIntLinearEquiv
  let eZ : Tensor R M Z ≃ₗ[ℤ] Tensor Rᵐᵒᵖ Z M :=
    (oppositeFlip (R := R) (A := M) (B := Z)).toIntLinearEquiv
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := eX) (e₂ := eY) (e₃ := eZ) ?_ ?_).mp ht
  · apply tensor_hom_ext
    intro m x
    rfl
  · apply tensor_hom_ext
    intro m y
    rfl

theorem projective_resolution_rightFlat {A : Type v} [AddCommGroup A]
    [Module Rᵐᵒᵖ A] (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective) :
    IsRightFlat.{u,v,w} P := by
  intro p
  exact (P103.Ch02.FlatnessTests.right_tensor_characterizations
    R (P.complex.X p)).2.2.2.1 (hP p)

theorem projective_resolution_leftFlat {B : Type w} [AddCommGroup B]
    [Module R B] (Q : LeftResolution R B) (hQ : Q.IsProjective) :
    IsLeftFlat.{u,v,w} Q := by
  intro q
  exact P103.Ch02.FlatnessTests.projective_flat R (Q.complex.X q) (hQ q)

/-- Interior augmented-row exactness used by the flat-resolution double
complex, with no flatness needed on the resolution itself. -/
theorem tensor_resolution_exact_succ {A : Type v} [AddCommGroup A]
    [Module Rᵐᵒᵖ A] (F : LeftResolution Rᵐᵒᵖ A)
    (B : Type w) [AddCommGroup B] [Module R B]
    (hB : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,max u v} R B) (n : ℕ) :
    Function.Exact ((tensorComplex F.complex B).d (n + 2) (n + 1)).hom
      ((tensorComplex F.complex B).d (n + 1) n).hom :=
  flat_tensor_exact hB (F.complex.d (n + 2) (n + 1)).hom
    (F.complex.d (n + 1) n).hom (LinearMap.exact_iff.mpr (F.exact_succ n).symm)

/-- Interior augmented-column exactness in the original right-left
orientation. The coefficient is right flat, over an arbitrary ring. -/
theorem leftTensor_resolution_exact_succ
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B] (G : LeftResolution R B)
    (hA : P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,max u w} R A) (n : ℕ) :
    Function.Exact ((leftOrdinaryTensorComplex A G.complex).d (n + 2) (n + 1)).hom
      ((leftOrdinaryTensorComplex A G.complex).d (n + 1) n).hom :=
  rightFlat_tensor_exact hA (G.complex.d (n + 2) (n + 1)).hom
    (G.complex.d (n + 1) n).hom (LinearMap.exact_iff.mpr (G.exact_succ n).symm)

private theorem homology_succ_subsingleton_of_exact
    {S : Type*} [Ring S] (C : ChainComplex (ModuleCat.{v} S) ℕ) (n : ℕ)
    (h : Function.Exact (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom) :
    Subsingleton (Homology C (n + 1)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  change ∃ y, (C.d ((ComplexShape.down ℕ).prev (n + 1)) (n + 1)).hom y = z.val
  rw [ChainComplex.prev]
  apply (h z.val).mp
  have hz := z.property
  change (C.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom z.val = 0 at hz
  rwa [ChainComplex.next_nat_succ] at hz

theorem tensor_resolution_homology_succ {A : Type v} [AddCommGroup A]
    [Module Rᵐᵒᵖ A] (F : LeftResolution Rᵐᵒᵖ A)
    (B : Type w) [AddCommGroup B] [Module R B]
    (hB : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,max u v} R B) (n : ℕ) :
    Subsingleton (Homology (tensorComplex F.complex B) (n + 1)) :=
  homology_succ_subsingleton_of_exact _ n (tensor_resolution_exact_succ F B hB n)

theorem leftTensor_resolution_homology_succ
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B] (G : LeftResolution R B)
    (hA : P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,max u w} R A) (n : ℕ) :
    Subsingleton (Homology (leftOrdinaryTensorComplex A G.complex) (n + 1)) :=
  homology_succ_subsingleton_of_exact _ n (leftTensor_resolution_exact_succ A G hA n)

/-- Simultaneous tensoring of a chain map and a coefficient map. -/
abbrev tensorChainMap {C D : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {B B' : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] (l : C ⟶ D) (g : B →ₗ[R] B') :=
  tensorFirstMap l B ≫ tensorSecondMap D g

theorem tensorChainMap_id (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :
    tensorChainMap (𝟙 C) (LinearMap.id : B →ₗ[R] B) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

theorem tensorChainMap_comp {C D E : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {B B' B'' : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] [AddCommGroup B''] [Module R B'']
    (l : C ⟶ D) (k : D ⟶ E) (g : B →ₗ[R] B') (g' : B' →ₗ[R] B'') :
    tensorChainMap l g ≫ tensorChainMap k g' =
      tensorChainMap (l ≫ k) (g'.comp g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

theorem tensorChainMap_identity_coefficient
    {C D : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    (l : C ⟶ D) (B : Type w) [AddCommGroup B] [Module R B] :
    tensorChainMap l (LinearMap.id : B →ₗ[R] B) = tensorFirstMap l B := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

/-- The projective-to-exact comparison exists without any flatness or
projectivity hypothesis on its target. -/
abbrev resolutionComparison {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) : P.complex ⟶ F.complex :=
  P103.Ch10.Comparison.chainMap P F hP LinearMap.id

theorem resolutionComparison_lifts {A : Type v} [AddCommGroup A]
    [Module Rᵐᵒᵖ A] (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) :
    ChainLift P F LinearMap.id (resolutionComparison P hP F) :=
  P103.Ch10.Comparison.chainMap_lifts P F hP LinearMap.id

theorem tensor_lift_independent {A A' : Type v}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (P : LeftResolution Rᵐᵒᵖ A) (F : LeftResolution Rᵐᵒᵖ A')
    (hP : P.IsProjective) (f : A →ₗ[Rᵐᵒᵖ] A')
    (l k : P.complex ⟶ F.complex) (hl : ChainLift P F f l)
    (hk : ChainLift P F f k) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    homologyMap (tensorFirstMap l B) n = homologyMap (tensorFirstMap k B) n := by
  exact congrArg ModuleCat.Hom.hom
    (P103.Ch10.Comparison.chain_homology_independent Rᵐᵒᵖ ℤ
      (tensorFunctor B) A A' P F hP f l k n hl hk)

/-- The homology map induced by a projective comparison into an arbitrary
exact resolution. Flat-target bijectivity is proved below. -/
def comparisonMap {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    TorWith P B n →ₗ[ℤ] Homology (tensorComplex F.complex B) n :=
  homologyMap (tensorFirstMap (resolutionComparison P hP F) B) n

theorem comparisonMap_eq {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B]
    (n : ℕ) (l : P.complex ⟶ F.complex) (hl : ChainLift P F LinearMap.id l) :
    comparisonMap P hP F B n = homologyMap (tensorFirstMap l B) n :=
  tensor_lift_independent P F hP LinearMap.id _ l
    (resolutionComparison_lifts P hP F) hl B n

/-- Naturality of the comparison map before asserting it is invertible.
This works for arbitrary exact targets, and in every degree. -/
theorem comparisonMap_natural {A A' : Type v}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    (hP : P.IsProjective) (hP' : P'.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (F' : LeftResolution Rᵐᵒᵖ A')
    {B B' : Type w} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : F.complex ⟶ F'.complex) (k : P.complex ⟶ P'.complex)
    (hl : ChainLift F F' f l) (hk : ChainLift P P' f k) (n : ℕ) :
    (homologyMap (tensorChainMap l g) n).comp (comparisonMap P hP F B n) =
      (comparisonMap P' hP' F' B' n).comp (homologyMap (tensorChainMap k g) n) := by
  let c := resolutionComparison P hP F
  let c' := resolutionComparison P' hP' F'
  have hcl : ChainLift P F' f (c ≫ l) := by
    simpa only [LinearMap.comp_id] using P103.Ch10.Comparison.chainLift_comp
      (resolutionComparison_lifts P hP F) hl
  have hkc : ChainLift P F' f (k ≫ c') := by
    simpa only [LinearMap.id_comp] using P103.Ch10.Comparison.chainLift_comp hk
      (resolutionComparison_lifts P' hP' F')
  have he := tensor_lift_independent P F' hP f (c ≫ l) (k ≫ c') hcl hkc B n
  have he' : homologyMap (tensorChainMap (c ≫ l) g) n =
      homologyMap (tensorChainMap (k ≫ c') g) n := by
    simpa only [tensorChainMap, P103.Ch10.Complexes.homologyMap_comp] using
      congrArg (fun a => (homologyMap (tensorSecondMap F'.complex g) n).comp a) he
  have h₁ : tensorFirstMap c B ≫ tensorChainMap l g = tensorChainMap (c ≫ l) g := by
    rw [← tensorChainMap_identity_coefficient c B, tensorChainMap_comp, LinearMap.comp_id]
  have h₂ : tensorChainMap k g ≫ tensorFirstMap c' B' = tensorChainMap (k ≫ c') g := by
    rw [← tensorChainMap_identity_coefficient c' B', tensorChainMap_comp, LinearMap.id_comp]
  change (homologyMap (tensorChainMap l g) n).comp
      (homologyMap (tensorFirstMap c B) n) =
    (homologyMap (tensorFirstMap c' B') n).comp (homologyMap (tensorChainMap k g) n)
  rw [← P103.Ch10.Complexes.homologyMap_comp, h₁,
    ← P103.Ch10.Complexes.homologyMap_comp, h₂]
  exact he'

/-- Once the comparison maps are proved bijective for flat targets, all
right-resolution naturality and normalization follow from the preceding
unconditional comparison lemmas. The needed bijectivity is proved below
by coefficient dimension shifting. -/
def rightComputationsOfBijective (n : ℕ)
    (h : ∀ {A : ModuleCat.{v} Rᵐᵒᵖ} (F : LeftResolution Rᵐᵒᵖ A),
      IsRightFlat.{u,v,w} F → ∀ (P : ProjectiveChoice Rᵐᵒᵖ A) (B : ModuleCat.{w} R),
      Function.Bijective (comparisonMap P.val P.property F B n)) :
    RightComputations.{u,v,w} R n where
  iso F hF P B := (LinearEquiv.ofBijective _ (h F hF P B)).symm
  naturality {A} {A'} {B} {B'} F F' hF hF' P P' f g l k hl hk x := by
    let e := LinearEquiv.ofBijective _ (h F hF P B)
    let e' := LinearEquiv.ofBijective _ (h F' hF' P' B')
    change e'.symm _ = _
    apply e'.injective
    rw [e'.apply_symm_apply]
    have hc := LinearMap.congr_fun
      (comparisonMap_natural P.val P'.val P.property P'.property F F'
        f.hom g.hom l k hl hk n) (e.symm x)
    change homologyMap (tensorChainMap l g.hom) n (e (e.symm x)) =
      e' (homologyMap (tensorChainMap k g.hom) n (e.symm x)) at hc
    rw [e.apply_symm_apply] at hc
    exact hc
  normalization F hF P B l hl x := by
    let e := LinearEquiv.ofBijective _ (h F hF P B)
    change e.symm _ = x
    rw [← comparisonMap_eq P.val P.property F B n l hl]
    exact e.symm_apply_apply x

/-- Degree zero needs only right exactness, so this definition applies to
every ordinary exact resolution, even when its terms are not flat. -/
def rightZero {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B] :
    Homology (tensorComplex F.complex B) 0 ≃ₗ[ℤ] TorWith P B 0 :=
  ((P103.Ch11.ExtTorDefinitions.torZero F B).trans
    (P103.Ch11.ExtTorDefinitions.torZero P B).symm).toIntLinearEquiv

theorem rightZero_augmentation {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B]
    (x : Homology (tensorComplex F.complex B) 0) :
    P103.Ch11.ExtTorDefinitions.torZero P B (rightZero F P B x) =
      P103.Ch11.ExtTorDefinitions.torZero F B x :=
  (P103.Ch11.ExtTorDefinitions.torZero P B).apply_symm_apply _

theorem rightZero_natural {A A' : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (F P : LeftResolution Rᵐᵒᵖ A) (F' P' : LeftResolution Rᵐᵒᵖ A')
    {B B' : Type w} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : F.complex ⟶ F'.complex) (k : P.complex ⟶ P'.complex)
    (hl : ChainLift F F' f l) (hk : ChainLift P P' f k)
    (x : Homology (tensorComplex F.complex B) 0) :
    rightZero F' P' B' (homologyMap (tensorChainMap l g) 0 x) =
      homologyMap (tensorChainMap k g) 0 (rightZero F P B x) := by
  apply (P103.Ch11.ExtTorDefinitions.torZero P' B').injective
  rw [rightZero_augmentation]
  rw [P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A' F F' B B' f g l hl
    _ _ (P103.Ch11.ExtTorDefinitions.torZero_class F B)
    (P103.Ch11.ExtTorDefinitions.torZero_class F' B')]
  rw [P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A' P P' B B' f g k hk
    _ _ (P103.Ch11.ExtTorDefinitions.torZero_class P B)
    (P103.Ch11.ExtTorDefinitions.torZero_class P' B')]
  rw [rightZero_augmentation]

theorem rightZero_normalization {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B]
    (l : P.complex ⟶ F.complex) (hl : ChainLift P F LinearMap.id l)
    (x : TorWith P B 0) :
    rightZero F P B (homologyMap (tensorFirstMap l B) 0 x) = x := by
  apply (P103.Ch11.ExtTorDefinitions.torZero P B).injective
  rw [rightZero_augmentation]
  rw [← tensorChainMap_identity_coefficient l B]
  have h := P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A P F B B
    LinearMap.id LinearMap.id l hl _ _
    (P103.Ch11.ExtTorDefinitions.torZero_class P B)
    (P103.Ch11.ExtTorDefinitions.torZero_class F B) x
  have hid : tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
      (LinearMap.id : B →ₗ[R] B) = LinearMap.id := by
    apply tensor_hom_ext
    intro a b
    rfl
  simpa only [hid, LinearMap.id_apply] using h

/-- The full right computation interface is established in degree zero. -/
def rightComputationsZero (R : Type u) [Ring R] : RightComputations.{u,v,w} R 0 where
  iso F _ P B := rightZero F P.val B
  naturality F F' _ _ P P' f g l k hl hk x :=
    rightZero_natural F P.val F' P'.val f.hom g.hom l k hl hk x
  normalization F _ P B l hl x := rightZero_normalization F P.val B l hl x

section LeftZero
variable (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
variable {B : Type w} [AddCommGroup B] [Module R B] (G : LeftResolution R B)

def leftZeroAugmentation : cycles (leftOrdinaryTensorComplex A G.complex) 0 →ₗ[ℤ]
    Tensor R A B :=
  (tensorMap LinearMap.id G.ε).comp
    (cycles (leftOrdinaryTensorComplex A G.complex) 0).subtype

theorem left_tensor_augmentation_exact :
    Function.Exact (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (G.complex.d 1 0).hom)
      (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) G.ε) ∧
    Function.Surjective (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) G.ε) :=
  P103.HomTensorExactness.tensorSecond_rightExact
    (G.complex.d 1 0).hom G.ε (LinearMap.exact_iff.mpr G.exact_zero.symm)
    G.surjective (tensorMap _ _).toAddMonoidHom (tensorMap _ _).toAddMonoidHom
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem leftZeroAugmentation_surjective : Function.Surjective (leftZeroAugmentation A G) := by
  intro z
  obtain ⟨x, hx⟩ := (left_tensor_augmentation_exact A G).2 z
  exact ⟨⟨x, P103.Ch11.ExtTorDefinitions.chain_mem_zero_cycles
    (leftOrdinaryTensorComplex A G.complex) x⟩, hx⟩

theorem leftZeroAugmentation_kernel :
    cycleBoundaries (leftOrdinaryTensorComplex A G.complex) 0 =
      LinearMap.ker (leftZeroAugmentation A G) := by
  ext z
  change (∃ x, ((leftOrdinaryTensorComplex A G.complex).d
      ((ComplexShape.down ℕ).prev 0) 0).hom x = z.val) ↔
    tensorMap LinearMap.id G.ε z.val = 0
  rw [ChainComplex.prev]
  exact ((left_tensor_augmentation_exact A G).1 z.val).symm

/-- The left-variable degree-zero augmentation, for every exact resolution. -/
def leftZeroTensor : Homology (leftOrdinaryTensorComplex A G.complex) 0 ≃ₗ[ℤ] Tensor R A B := by
  let e₁ : Homology (leftOrdinaryTensorComplex A G.complex) 0 ≃ₗ[ℤ]
      (cycles (leftOrdinaryTensorComplex A G.complex) 0 ⧸
        LinearMap.ker (leftZeroAugmentation A G)) :=
    Submodule.quotEquivOfEq _ _ (leftZeroAugmentation_kernel A G)
  exact e₁.trans ((leftZeroAugmentation A G).quotKerEquivOfSurjective
    (leftZeroAugmentation_surjective A G))

theorem leftZeroTensor_class (z : cycles (leftOrdinaryTensorComplex A G.complex) 0) :
    leftZeroTensor A G (homologyClass _ 0 z) = tensorMap LinearMap.id G.ε z.val :=
  LinearMap.quotKerEquivOfSurjective_apply_mk (leftZeroAugmentation A G)
    (leftZeroAugmentation_surjective A G) z

end LeftZero

theorem leftZeroTensor_natural {A A' : Type v}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    {B B' : Type w} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (G : LeftResolution R B) (G' : LeftResolution R B')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : G.complex ⟶ G'.complex) (hl : ChainLift G G' g l)
    (x : Homology (leftOrdinaryTensorComplex A G.complex) 0) :
    leftZeroTensor A' G' (homologyMap (leftTensorMap f l) 0 x) =
      tensorMap f g (leftZeroTensor A G x) := by
  refine Quotient.inductionOn' x ?_
  intro z
  change leftZeroTensor A' G'
      (homologyMap (leftTensorMap f l) 0 (homologyClass _ 0 z)) =
    tensorMap f g (leftZeroTensor A G (homologyClass _ 0 z))
  rw [P103.Ch10.Complexes.homologyMap_apply, leftZeroTensor_class, leftZeroTensor_class]
  have he : (tensorMap (LinearMap.id : A' →ₗ[Rᵐᵒᵖ] A') G'.ε).comp
      ((leftTensorMap f l).f 0).hom =
      (tensorMap f g).comp (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) G.ε) := by
    apply tensor_hom_ext
    intro a b
    change tmul R (f a) (G'.ε ((l.f 0).hom b)) = tmul R (f a) (g (G.ε b))
    exact congrArg (tmul R (f a)) (LinearMap.congr_fun hl b)
  exact LinearMap.congr_fun he z.val

def leftZero {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) :
    Homology (leftOrdinaryTensorComplex A G.complex) 0 ≃ₗ[ℤ] TorWith P B 0 :=
  (leftZeroTensor A G).trans
    (P103.Ch11.ExtTorDefinitions.torZero P B).toIntLinearEquiv.symm

theorem leftZero_augmentation {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) (x : Homology (leftOrdinaryTensorComplex A G.complex) 0) :
    P103.Ch11.ExtTorDefinitions.torZero P B (leftZero P G x) = leftZeroTensor A G x :=
  (P103.Ch11.ExtTorDefinitions.torZero P B).apply_symm_apply _

theorem leftZero_natural {A A' : Type v}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (P : LeftResolution Rᵐᵒᵖ A) (P' : LeftResolution Rᵐᵒᵖ A')
    {B B' : Type w} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (G : LeftResolution R B) (G' : LeftResolution R B')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : G.complex ⟶ G'.complex) (k : P.complex ⟶ P'.complex)
    (hl : ChainLift G G' g l) (hk : ChainLift P P' f k)
    (x : Homology (leftOrdinaryTensorComplex A G.complex) 0) :
    leftZero P' G' (homologyMap (leftTensorMap f l) 0 x) =
      homologyMap (tensorChainMap k g) 0 (leftZero P G x) := by
  apply (P103.Ch11.ExtTorDefinitions.torZero P' B').injective
  rw [leftZero_augmentation, leftZeroTensor_natural G G' f g l hl]
  rw [P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A' P P' B B' f g k hk
    _ _ (P103.Ch11.ExtTorDefinitions.torZero_class P B)
    (P103.Ch11.ExtTorDefinitions.torZero_class P' B')]
  rw [leftZero_augmentation]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Only bidegree (0,0) contributes to the ordinary total in degree zero.
This form works for linear targets of arbitrary size. -/
theorem ordinaryTotal_zero_linearMap_ext
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ)
    {T : Type*} [AddCommGroup T]
    (f g : (ordinaryTotal C D).X 0 →ₗ[ℤ] T)
    (h : ∀ (a : C.X 0) (b : D.X 0),
      f (ordinaryInclusion C D 0 0 0 (by omega) (tmul R a b)) =
      g (ordinaryInclusion C D 0 0 0 (by omega) (tmul R a b))) : f = g := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  have hs (p q : ℤ) (hpq : p + q = 0) (x : (K.X p).X q) :
      f ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q 0 hpq).hom x) =
      g ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q 0 hpq).hom x) := by
    by_cases hp : 0 ≤ p
    · by_cases hq : 0 ≤ q
      · have hp0 : p = 0 := by omega
        have hq0 : q = 0 := by omega
        subst p q
        let eC : (extendNonnegativeChain C).X 0 ≃ₗ[Rᵐᵒᵖ] C.X 0 :=
          (C.extendXIso nonnegativeChainEmbedding (i := 0) rfl).toLinearEquiv
        let eD : (extendNonnegativeChain D).X 0 ≃ₗ[R] D.X 0 :=
          (D.extendXIso nonnegativeChainEmbedding (i := 0) rfl).toLinearEquiv
        have he (a : (extendNonnegativeChain C).X 0)
            (b : (extendNonnegativeChain D).X 0) :
            ordinaryInclusion C D 0 0 0 (by omega) (tmul R (eC a) (eD b)) =
              (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K 0 0 0 hpq).hom
                (tmul R a b) := by
          change (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K 0 0 0 hpq).hom
              (tmul R (eC.symm (eC a)) (eD.symm (eD b))) = _
          rw [eC.symm_apply_apply, eD.symm_apply_apply]
        have hm : f.comp
            (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K 0 0 0 hpq).hom =
            g.comp
            (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K 0 0 0 hpq).hom := by
          apply tensor_hom_ext
          intro a b
          change f ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K 0 0 0 hpq).hom
            (tmul R a b)) = g ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K 0 0 0 hpq).hom
            (tmul R a b))
          rw [← he a b]
          exact h (eC a) (eD b)
        exact LinearMap.congr_fun hm x
      · letI := P103.Ch10.Complexes.extendNonnegativeChain_supported D q (by
          change ¬ 0 ≤ q
          exact hq)
        have hx : x = 0 := by
          change Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q) at x
          haveI : Subsingleton (Tensor R ((extendNonnegativeChain C).X p)
              ((extendNonnegativeChain D).X q)) := by unfold Tensor; infer_instance
          exact @Subsingleton.elim (Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q)) inferInstance x 0
        simp only [hx, map_zero]
    · letI := P103.Ch10.Complexes.extendNonnegativeChain_supported C p (by
        change ¬ 0 ≤ p
        exact hp)
      have hx : x = 0 := by
        change Tensor R ((extendNonnegativeChain C).X p)
          ((extendNonnegativeChain D).X q) at x
        haveI : Subsingleton (Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q)) := by unfold Tensor; infer_instance
        exact @Subsingleton.elim (Tensor R ((extendNonnegativeChain C).X p)
          ((extendNonnegativeChain D).X q)) inferInstance x 0
      simp only [hx, map_zero]
  apply LinearMap.ext
  intro z
  have hre := P103.Ch10.TotalComplexAssembly.total_reconstruction K 0 z
  calc
    f z = f (∑ i ∈ P103.Specs.Ch10.TotalComplexAssembly.totalSupport K 0 z,
      (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K i.val.1 i.val.2 0 i.property).hom
        ((P103.Specs.Ch10.TotalComplexAssembly.totalProjection K i.val.1 i.val.2 0 i.property).hom z)) :=
      congrArg f hre.symm
    _ = g (∑ i ∈ P103.Specs.Ch10.TotalComplexAssembly.totalSupport K 0 z,
      (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K i.val.1 i.val.2 0 i.property).hom
        ((P103.Specs.Ch10.TotalComplexAssembly.totalProjection K i.val.1 i.val.2 0 i.property).hom z)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hs i.val.1 i.val.2 i.property _
    _ = g z := congrArg g hre

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem zero_augmentations_agree {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B) (α : Augmentations P Q) :
    (tensorMap P.ε (LinearMap.id : B →ₗ[R] B)).comp (α.left.f 0).hom =
      (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) Q.ε).comp (α.right.f 0).hom := by
  apply ordinaryTotal_zero_linearMap_ext
  intro a b
  change tensorMap P.ε LinearMap.id ((α.left.f 0).hom
      (ordinaryInclusion P.complex Q.complex 0 0 0 (by omega) (tmul R a b))) =
    tensorMap LinearMap.id Q.ε ((α.right.f 0).hom
      (ordinaryInclusion P.complex Q.complex 0 0 0 (by omega) (tmul R a b)))
  calc
    _ = tensorMap P.ε LinearMap.id (tmul R a (Q.ε b)) :=
      congrArg (tensorMap P.ε LinearMap.id) (α.left_zero 0 a b)
    _ = tmul R (P.ε a) (Q.ε b) := rfl
    _ = tensorMap LinearMap.id Q.ε (tmul R (P.ε a) b) := rfl
    _ = _ := congrArg (tensorMap LinearMap.id Q.ε) (α.right_zero 0 a b).symm

theorem leftZero_normalization {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B) (α : Augmentations P Q)
    (z : Homology (ordinaryTotal P.complex Q.complex) 0) :
    leftZero P Q (homologyMap α.right 0 z) = homologyMap α.left 0 z := by
  apply (P103.Ch11.ExtTorDefinitions.torZero P B).injective
  rw [leftZero_augmentation]
  refine Quotient.inductionOn' z ?_
  intro x
  change leftZeroTensor A Q (homologyMap α.right 0 (homologyClass _ 0 x)) =
    P103.Ch11.ExtTorDefinitions.torZero P B (homologyMap α.left 0 (homologyClass _ 0 x))
  rw [P103.Ch10.Complexes.homologyMap_apply, leftZeroTensor_class,
    P103.Ch10.Complexes.homologyMap_apply, P103.Ch11.ExtTorDefinitions.torZero_class]
  exact (LinearMap.congr_fun (zero_augmentations_agree P Q α) x.val).symm

def leftComputationsZero (R : Type u) [Ring R] : LeftComputations.{u,v,w} R 0 where
  iso {B} G _ {A} P := leftZero P.val G
  naturality G G' _ _ P P' f g l k hl hk x :=
    leftZero_natural P.val P'.val G G' f.hom g.hom l k hl hk x
  normalization P Q _ α z := leftZero_normalization P.val Q.val α z

theorem comparisonMap_zero_bijective {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B] :
    Function.Bijective (comparisonMap P hP F B 0) := by
  let e := rightZero F P B
  have he (x : TorWith P B 0) : e (comparisonMap P hP F B 0 x) = x :=
    rightZero_normalization F P B _ (resolutionComparison_lifts P hP F) x
  constructor
  · intro x y hxy
    simpa only [he] using congrArg e hxy
  · intro y
    refine ⟨e y, e.injective ?_⟩
    exact he (e y)

/-- As an assembly ingredient, a flat coefficient makes every projective
comparison into an arbitrary exact resolution a quasi-isomorphism. The
unrestricted coefficient case is proved below by dimension shifting. -/
theorem comparisonMap_bijective_of_flat_coefficient
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B]
    (hB : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,max u v} R B) (n : ℕ) :
    Function.Bijective (comparisonMap P hP F B n) := by
  cases n with
  | zero => exact comparisonMap_zero_bijective P hP F B
  | succ n =>
    letI := tensor_resolution_homology_succ P B hB n
    letI := tensor_resolution_homology_succ F B hB n
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- An actual computation family provides comparisons without a selected
map between the flat resolutions. -/
def flatComparison {n : ℕ} (C : RightComputations.{u,v,w} R n)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (F F' : LeftResolution Rᵐᵒᵖ A)
    (hF : IsRightFlat.{u,v,w} F) (hF' : IsRightFlat.{u,v,w} F')
    (P : ProjectiveChoice Rᵐᵒᵖ A) (B : ModuleCat.{w} R) :
    Homology (tensorComplex F.complex B) n ≃ₗ[ℤ]
      Homology (tensorComplex F'.complex B) n :=
  (C.iso F hF P B).trans (C.iso F' hF' P B).symm

theorem flatComparison_refl {n : ℕ} (C : RightComputations.{u,v,w} R n)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (F : LeftResolution Rᵐᵒᵖ A)
    (hF : IsRightFlat.{u,v,w} F) (P : ProjectiveChoice Rᵐᵒᵖ A) (B : ModuleCat.{w} R) :
    flatComparison C F F hF hF P B = LinearEquiv.refl ℤ _ := by
  ext x
  exact (C.iso F hF P B).symm_apply_apply x

theorem flatComparison_trans {n : ℕ} (C : RightComputations.{u,v,w} R n)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (F F' F'' : LeftResolution Rᵐᵒᵖ A)
    (hF : IsRightFlat.{u,v,w} F) (hF' : IsRightFlat.{u,v,w} F')
    (hF'' : IsRightFlat.{u,v,w} F'')
    (P : ProjectiveChoice Rᵐᵒᵖ A) (B : ModuleCat.{w} R) :
    (flatComparison C F F' hF hF' P B).trans (flatComparison C F' F'' hF' hF'' P B) =
      flatComparison C F F'' hF hF'' P B := by
  ext x
  change (C.iso F'' hF'' P B).symm
      ((C.iso F' hF' P B) ((C.iso F' hF' P B).symm ((C.iso F hF P B) x))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The normalization determines every right-resolution identification
uniquely; a different selection of projective comparison lifts cannot
produce a different identification. -/
theorem rightComputation_unique {n : ℕ}
    (C D : RightComputations.{u,v,w} R n)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (F : LeftResolution Rᵐᵒᵖ A)
    (hF : IsRightFlat.{u,v,w} F) (P : ProjectiveChoice Rᵐᵒᵖ A)
    (B : ModuleCat.{w} R) : C.iso F hF P B = D.iso F hF P B := by
  let l := resolutionComparison P.val P.property F
  have hl := resolutionComparison_lifts P.val P.property F
  ext x
  have hi : homologyMap (tensorFirstMap l B) n ((C.iso F hF P B) x) = x := by
    apply (C.iso F hF P B).injective
    exact C.normalization F hF P B l hl _
  calc
    (C.iso F hF P B) x = (D.iso F hF P B)
        (homologyMap (tensorFirstMap l B) n ((C.iso F hF P B) x)) :=
      (D.normalization F hF P B l hl _).symm
    _ = (D.iso F hF P B) x := congrArg (D.iso F hF P B) hi

/-- Both degree-zero computations follow from the actual augmentations. -/
theorem degreeZero :
    ∀ (R : Type u) [Ring R],
      Nonempty (RightComputations.{u,v,w} R 0) ∧
      Nonempty (LeftComputations.{u,v,w} R 0) := by
  intro R _
  exact ⟨⟨rightComputationsZero R⟩, ⟨leftComputationsZero R⟩⟩

section DimensionShift
open P103.Specs.Ch10.HomologySequence

/-- Tensoring a termwise right-flat complex with a short exact coefficient
sequence gives a degreewise short exact sequence of abelian-group complexes. -/
theorem tensor_degreewise_exact
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (hC : ∀ n, P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,max u v w} R (C.X n))
    {X Y Z : Type (max u v w)}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z]
    (i : X →ₗ[R] Y) (p : Y →ₗ[R] Z)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hp : Function.Surjective p) :
    DegreewiseExact (tensorSecondMap C i) (tensorSecondMap C p) := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · exact hC n X Y i hi (tensorMap LinearMap.id i).toAddMonoidHom (fun _ _ => rfl)
  · exact rightFlat_tensor_exact (hC n) i p he
  · exact P103.HomTensorExactness.tensorSecond_surjective p hp
      (tensorMap (LinearMap.id : C.X n →ₗ[Rᵐᵒᵖ] C.X n) p).toAddMonoidHom
      (fun _ _ => rfl)

/-- The two orders of tensoring a chain map and a coefficient map agree. -/
theorem tensor_coeff_naturality
    {C D : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    (l : C ⟶ D)
    {X Y : Type w} [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (g : X →ₗ[R] Y) :
    tensorSecondMap C g ≫ tensorFirstMap l Y =
      tensorFirstMap l X ≫ tensorSecondMap D g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a x
  rfl

/-- A natural morphism of short exact sequences, acyclic in the middle,
propagates a comparison isomorphism one degree upward. -/
theorem homology_bijective_succ_of_middle_acyclic
    {C₀ C₁ C₂ D₀ D₁ D₂ : ChainComplex (ModuleCat.{t} ℤ) ℕ}
    (i : C₀ ⟶ C₁) (p : C₁ ⟶ C₂) (i' : D₀ ⟶ D₁) (p' : D₁ ⟶ D₂)
    (α : C₀ ⟶ D₀) (β : C₁ ⟶ D₁) (γ : C₂ ⟶ D₂)
    (hi : i ≫ β = α ≫ i') (hp : p ≫ γ = β ≫ p')
    (hs : DegreewiseExact i p) (hs' : DegreewiseExact i' p') (n : ℕ)
    (hC : Subsingleton (Homology C₁ (n+1)))
    (hD : Subsingleton (Homology D₁ (n+1)))
    (hα : Function.Bijective (homologyMap α n))
    (hβ : Function.Injective (homologyMap β n)) :
    Function.Bijective (homologyMap γ (n+1)) := by
  have hn : (ComplexShape.down ℕ).Rel (n+1) n := by simp
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence i p hs (n+1) n hn
  obtain ⟨ε, hε, _⟩ := P103.Ch10.HomologySequence.sequence i' p' hs' (n+1) n hn
  have hnat := P103.Ch10.HomologySequence.naturality i p i' p' α β γ hi hp hs hs'
    (n+1) n hn δ ε hδ.1 hε.1
  have hiδ := (P103.Ch10.HomologySequence.zero_endpoints i p (n+1) n δ hδ.2).2.2.2.1 hC
  have hiε := (P103.Ch10.HomologySequence.zero_endpoints i' p' (n+1) n ε hε.2).2.2.2.1 hD
  exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
    δ.toAddMonoidHom (homologyMap i n).toAddMonoidHom ε.toAddMonoidHom
    (homologyMap i' n).toAddMonoidHom (homologyMap γ (n+1)).toAddMonoidHom
    (homologyMap α n).toAddMonoidHom (homologyMap β n).toAddMonoidHom
    (congrArg LinearMap.toAddMonoidHom hnat.2.2.1.symm)
    (congrArg LinearMap.toAddMonoidHom hnat.2.2.2.1.symm)
    hδ.2.2.2 hε.2.2.2 hα hβ hiδ hiε


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
theorem comparisonMap_bijective_large {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (hF : IsRightFlat.{u,v,w} F) (n : ℕ) :
    ∀ (B : Type (max u v w)) [AddCommGroup B] [Module R B],
      Function.Bijective (comparisonMap P hP F B n) := by
  induction n with
  | zero => intro B _ _; exact comparisonMap_zero_bijective P hP F B
  | succ n ih =>
    intro B _ _
    let E := B →₀ R
    let p : E →ₗ[R] B := Finsupp.linearCombination R id
    let K := LinearMap.ker p
    let i : K →ₗ[R] E := (LinearMap.ker p).subtype
    have hi : Function.Injective i := Subtype.val_injective
    have hp : Function.Surjective p := Finsupp.linearCombination_surjective R Function.surjective_id
    have he : Function.Exact i p := LinearMap.exact_subtype_ker_map p
    let c := resolutionComparison P hP F
    have hPE := tensor_resolution_homology_succ P E
      (P103.Ch02.FlatnessTests.projective_flat R E inferInstance) n
    have hFE := tensor_resolution_homology_succ F E
      (P103.Ch02.FlatnessTests.projective_flat R E inferInstance) n
    have hsP := tensor_degreewise_exact.{u,max u v,w} P.complex (projective_resolution_rightFlat.{u,v,w} P hP) (X := K) (Y := E) (Z := B) i p hi he hp
    have hsF := tensor_degreewise_exact.{u,max u v,w} F.complex hF (X := K) (Y := E) (Z := B) i p hi he hp
    change Function.Bijective (homologyMap (tensorFirstMap c B) (n+1))
    have hci : tensorSecondMap P.complex i ≫ tensorFirstMap c E =
        tensorFirstMap c K ≫ tensorSecondMap F.complex i :=
      by
        apply HomologicalComplex.Hom.ext
        funext k
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a x
        rfl
    have hcp : tensorSecondMap P.complex p ≫ tensorFirstMap c B =
        tensorFirstMap c E ≫ tensorSecondMap F.complex p :=
      by
        apply HomologicalComplex.Hom.ext
        funext k
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a x
        rfl
    exact homology_bijective_succ_of_middle_acyclic.{max u v w}
      (C₀ := tensorComplex P.complex K) (C₁ := tensorComplex P.complex E)
      (C₂ := tensorComplex P.complex B) (D₀ := tensorComplex F.complex K)
      (D₁ := tensorComplex F.complex E) (D₂ := tensorComplex F.complex B)
      (tensorSecondMap P.complex i) (tensorSecondMap P.complex p)
      (tensorSecondMap F.complex i) (tensorSecondMap F.complex p)
      (tensorFirstMap c K) (tensorFirstMap c E) (tensorFirstMap c B)
      hci hcp
      hsP hsF n hPE hFE (ih K) (ih E).1

def tensorULiftIso
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :
    tensorComplex C B ≅ tensorComplex C (ULift.{max u v} B) where
  hom :=
    { f := fun n => ModuleCat.ofHom
        (tensorMap (LinearMap.id : C.X n →ₗ[Rᵐᵒᵖ] C.X n)
          (ULift.moduleEquiv : ULift.{max u v} B ≃ₗ[R] B).symm.toLinearMap)
      comm' := by
        intro i j h
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro x b
        rfl }
  inv :=
    { f := fun n => ModuleCat.ofHom
        (tensorMap (LinearMap.id : C.X n →ₗ[Rᵐᵒᵖ] C.X n)
          (ULift.moduleEquiv : ULift.{max u v} B ≃ₗ[R] B).toLinearMap)
      comm' := by
        intro i j h
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro x b
        rfl }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x b
    rfl
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x b
    rfl

def tensorULiftHomologyEquiv
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    Homology (tensorComplex C B) n ≃ₗ[ℤ]
      Homology (tensorComplex C (ULift.{max u v} B)) n where
  toLinearMap := homologyMap (tensorULiftIso.{u,v,w} C B).hom n
  invFun := homologyMap (tensorULiftIso.{u,v,w} C B).inv n
  left_inv x := by
    change ((homologyMap (tensorULiftIso.{u,v,w} C B).inv n).comp
      (homologyMap (tensorULiftIso.{u,v,w} C B).hom n)) x = x
    rw [← P103.Ch10.Complexes.homologyMap_comp, Iso.hom_inv_id,
      P103.Ch10.Complexes.homologyMap_id]
    rfl
  right_inv x := by
    change ((homologyMap (tensorULiftIso.{u,v,w} C B).hom n).comp
      (homologyMap (tensorULiftIso.{u,v,w} C B).inv n)) x = x
    rw [← P103.Ch10.Complexes.homologyMap_comp, Iso.inv_hom_id,
      P103.Ch10.Complexes.homologyMap_id]
    rfl

theorem tensorULiftIso_natural
    {C D : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ}
    (l : C ⟶ D) (B : Type w) [AddCommGroup B] [Module R B] :
    (tensorULiftIso.{u,v,w} C B).hom ≫ tensorFirstMap l (ULift.{max u v} B) =
      tensorFirstMap l B ≫ (tensorULiftIso.{u,v,w} D B).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro x b
  rfl

theorem tensorULiftHomologyEquiv_natural
    {C D : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ}
    (l : C ⟶ D) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    (tensorULiftHomologyEquiv.{u,v,w} D B n).toLinearMap.comp
      (homologyMap (tensorFirstMap l B) n) =
    (homologyMap (tensorFirstMap l (ULift.{max u v} B)) n).comp
      (tensorULiftHomologyEquiv.{u,v,w} C B n).toLinearMap := by
  change (homologyMap (tensorULiftIso.{u,v,w} D B).hom n).comp
      (homologyMap (tensorFirstMap l B) n) =
    (homologyMap (tensorFirstMap l (ULift.{max u v} B)) n).comp
      (homologyMap (tensorULiftIso.{u,v,w} C B).hom n)
  rw [← P103.Ch10.Complexes.homologyMap_comp,
    ← P103.Ch10.Complexes.homologyMap_comp, tensorULiftIso_natural]

theorem comparisonMap_ulift_natural
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    (tensorULiftHomologyEquiv.{u,v,w} F.complex B n).toLinearMap.comp
      (comparisonMap P hP F B n) =
    (comparisonMap P hP F (ULift.{max u v} B) n).comp
      (tensorULiftHomologyEquiv.{u,v,w} P.complex B n).toLinearMap :=
  tensorULiftHomologyEquiv_natural.{u,v,w} (resolutionComparison P hP F) B n

theorem comparisonMap_bijective_of_ulift
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ)
    (h : Function.Bijective (comparisonMap P hP F (ULift.{max u v} B) n)) :
    Function.Bijective (comparisonMap P hP F B n) := by
  let eP := tensorULiftHomologyEquiv.{u,v,w} P.complex B n
  let eF := tensorULiftHomologyEquiv.{u,v,w} F.complex B n
  have sq (x : TorWith P B n) :
      eF (comparisonMap P hP F B n x) =
        comparisonMap P hP F (ULift.{max u v} B) n (eP x) :=
    LinearMap.congr_fun (comparisonMap_ulift_natural P hP F B n) x
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eP.injective
    apply h.injective
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨x, hx⟩ := h.surjective (eF y)
    refine ⟨eP.symm x, eF.injective ?_⟩
    rw [sq, eP.apply_symm_apply, hx]


theorem comparisonMap_bijective {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    (F : LeftResolution Rᵐᵒᵖ A) (hF : IsRightFlat.{u,v,w} F)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    Function.Bijective (comparisonMap P hP F B n) :=
  comparisonMap_bijective_of_ulift.{u,v,w} P hP F B n
    (comparisonMap_bijective_large.{u,v,w} P hP F hF n (ULift.{max u v} B))

/-- The natural, normalized computation on every ordinary right-flat resolution. -/
def rightComputations (R : Type u) [Ring R] (n : ℕ) : RightComputations.{u,v,w} R n :=
  rightComputationsOfBijective n (fun F hF P B =>
    comparisonMap_bijective P.val P.property F hF B n)

end DimensionShift

/-- Every ordinary right-flat resolution computes Tor, naturally and compatibly
with every projective comparison over the identity. -/
theorem right_flat_computations
    : P103.Specs.Ch11.FlatResolutions.right_flat_computationsType.{u,v,w} := by
  intro R _ n
  exact ⟨rightComputations R n⟩

section TotalAugmentations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every ordinary total term is spanned by its nonnegative pure-tensor summands. -/
theorem ordinaryTotal_linearMap_ext
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ)
    {T : Type*} [AddCommGroup T]
    (f g : (ordinaryTotal C D).X n →ₗ[ℤ] T)
    (h : ∀ (p q : ℕ) (hpq : p + q = n) (a : C.X p) (b : D.X q),
      f (ordinaryInclusion C D p q n hpq (tmul R a b)) =
      g (ordinaryInclusion C D p q n hpq (tmul R a b))) : f = g := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  have hs (p q : ℤ) (hpq : p + q = n) (x : (K.X p).X q) :
      f ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom x) =
      g ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom x) := by
    by_cases hp : 0 ≤ p
    · by_cases hq : 0 ≤ q
      · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
        obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
        have hn : p + q = n := by exact_mod_cast hpq
        let eC : (extendNonnegativeChain C).X (p : ℤ) ≃ₗ[Rᵐᵒᵖ] C.X p :=
          (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).toLinearEquiv
        let eD : (extendNonnegativeChain D).X (q : ℤ) ≃ₗ[R] D.X q :=
          (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).toLinearEquiv
        have he (a : (extendNonnegativeChain C).X (p : ℤ))
            (b : (extendNonnegativeChain D).X (q : ℤ)) :
            ordinaryInclusion C D p q n hn (tmul R (eC a) (eD b)) =
              (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom
                (tmul R a b) := by
          change (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom
              (tmul R (eC.symm (eC a)) (eD.symm (eD b))) = _
          rw [eC.symm_apply_apply, eD.symm_apply_apply]
        have hm : f.comp
            (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom =
            g.comp
            (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom := by
          apply tensor_hom_ext
          intro a b
          change f ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom
            (tmul R a b)) = g ((P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K p q n hpq).hom
            (tmul R a b))
          rw [← he a b]
          exact h p q hn (eC a) (eD b)
        exact LinearMap.congr_fun hm x
      · letI := P103.Ch10.Complexes.extendNonnegativeChain_supported D q (by
          change ¬ 0 ≤ q
          exact hq)
        have hx : x = 0 := by
          change Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q) at x
          haveI : Subsingleton (Tensor R ((extendNonnegativeChain C).X p)
              ((extendNonnegativeChain D).X q)) := by unfold Tensor; infer_instance
          exact @Subsingleton.elim (Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q)) inferInstance x 0
        simp only [hx, map_zero]
    · letI := P103.Ch10.Complexes.extendNonnegativeChain_supported C p (by
        change ¬ 0 ≤ p
        exact hp)
      have hx : x = 0 := by
        change Tensor R ((extendNonnegativeChain C).X p)
          ((extendNonnegativeChain D).X q) at x
        haveI : Subsingleton (Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q)) := by unfold Tensor; infer_instance
        exact @Subsingleton.elim (Tensor R ((extendNonnegativeChain C).X p)
            ((extendNonnegativeChain D).X q)) inferInstance x 0
      simp only [hx, map_zero]
  apply LinearMap.ext
  intro z
  have hre := P103.Ch10.TotalComplexAssembly.total_reconstruction K n z
  calc
    f z = f (∑ i ∈ P103.Specs.Ch10.TotalComplexAssembly.totalSupport K n z,
      (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K i.val.1 i.val.2 n i.property).hom
        ((P103.Specs.Ch10.TotalComplexAssembly.totalProjection K i.val.1 i.val.2 n i.property).hom z)) :=
      congrArg f hre.symm
    _ = g (∑ i ∈ P103.Specs.Ch10.TotalComplexAssembly.totalSupport K n z,
      (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion K i.val.1 i.val.2 n i.property).hom
        ((P103.Specs.Ch10.TotalComplexAssembly.totalProjection K i.val.1 i.val.2 n i.property).hom z)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact hs i.val.1 i.val.2 i.property _
    _ = g z := congrArg g hre

/-- Augmentation maps are fixed by their values on the nonnegative summands. -/
theorem augmentations_unique {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R B)
    (α β : Augmentations P Q) : α.left = β.left ∧ α.right = β.right := by
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply ordinaryTotal_linearMap_ext
    intro p q hpq a b
    by_cases hq : q = 0
    · subst q
      have hn : n = p := by omega
      subst n
      exact (α.left_zero p a b).trans (β.left_zero p a b).symm
    · have hα := LinearMap.congr_fun (α.left_positive p q n hpq hq) (tmul R a b)
      have hβ := LinearMap.congr_fun (β.left_positive p q n hpq hq) (tmul R a b)
      exact hα.trans hβ.symm
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply ordinaryTotal_linearMap_ext
    intro p q hpq a b
    by_cases hp : p = 0
    · subst p
      have hn : n = q := by omega
      cases hn
      exact (α.right_zero _ a b).trans (β.right_zero _ a b).symm
    · have hα := LinearMap.congr_fun (α.right_positive p q n hpq hp) (tmul R a b)
      have hβ := LinearMap.congr_fun (β.right_positive p q n hpq hp) (tmul R a b)
      exact hα.trans hβ.symm

/-- The total map acts by the given two maps on each tensor summand. -/
theorem ordinaryTotalMap_inclusion
    {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ}
    (f : C ⟶ C') (g : D ⟶ D')
    (p q n : ℕ) (h : p + q = n) (a : C.X p) (b : D.X q) :
    ((ordinaryTotalMap f g).f n).hom (ordinaryInclusion C D p q n h (tmul R a b)) =
      ordinaryInclusion C' D' p q n h (tmul R ((f.f p).hom a) ((g.f q).hom b)) := by
  let C₁ := extendNonnegativeChain C
  let D₁ := extendNonnegativeChain D
  let C₂ := extendNonnegativeChain C'
  let D₂ := extendNonnegativeChain D'
  let f₁ := HomologicalComplex.extendMap f nonnegativeChainEmbedding
  let g₁ := HomologicalComplex.extendMap g nonnegativeChainEmbedding
  have hm := HomologicalComplex₂.ιTotal_map
    (tensorBicomplex C₁ D₁) (tensorBicomplex C₂ D₂) (tensorBicomplexMap f₁ g₁) (ComplexShape.down ℤ)
    (p : ℤ) (q : ℤ) (n : ℤ) (by change (p : ℤ) + q = n; exact_mod_cast h)
  have hf := HomologicalComplex.extendMap_f f nonnegativeChainEmbedding
    (i := p) (i' := (p : ℤ)) rfl
  have hg := HomologicalComplex.extendMap_f g nonnegativeChainEmbedding
    (i := q) (i' := (q : ℤ)) rfl
  have hfa : (f₁.f (p : ℤ)).hom
      ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a) =
      (C'.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom ((f.f p).hom a) := by
    change ((HomologicalComplex.extendMap f nonnegativeChainEmbedding).f (p : ℤ)).hom _ = _
    rw [hf]
    exact congrArg (fun x =>
      (C'.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom ((f.f p).hom x))
      ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).toLinearEquiv.apply_symm_apply a)
  have hgb : (g₁.f (q : ℤ)).hom
      ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b) =
      (D'.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom ((g.f q).hom b) := by
    change ((HomologicalComplex.extendMap g nonnegativeChainEmbedding).f (q : ℤ)).hom _ = _
    rw [hg]
    exact congrArg (fun x =>
      (D'.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom ((g.f q).hom x))
      ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).toLinearEquiv.apply_symm_apply b)
  have he := congrArg (fun k => k.hom
    (tmul R ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
      ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b))) hm
  refine he.trans ?_
  exact congrArg
    (P103.Specs.Ch10.TotalComplexAssembly.totalInclusion
      (tensorBicomplex C₂ D₂) p q n (by exact_mod_cast h)).hom
    (congrArg₂ (tmul R) hfa hgb)

/-- Both augmentation squares commute for arbitrary maps of exact
resolutions; projectivity and flatness are unnecessary for these squares. -/
theorem augmentations_natural : augmentation_naturalType.{u,v,w} := by
  intro R _ A A' B B' _ _ _ _ _ _ _ _ P P' Q Q' f g l m hl hm α β
  constructor
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply ordinaryTotal_linearMap_ext
    intro p q hpq a b
    change (β.left.f n).hom (((ordinaryTotalMap l m).f n).hom
      (ordinaryInclusion P.complex Q.complex p q n hpq (tmul R a b))) =
      tensorMap LinearMap.id g (tensorMap (l.f n).hom LinearMap.id ((α.left.f n).hom
        (ordinaryInclusion P.complex Q.complex p q n hpq (tmul R a b))))
    rw [ordinaryTotalMap_inclusion]
    by_cases hq : q = 0
    · subst q
      have hn : n = p := by omega
      cases hn
      erw [β.left_zero, α.left_zero]
      change tmul R ((l.f n).hom a) (Q'.ε ((m.f 0).hom b)) =
        tmul R ((l.f n).hom a) (g (Q.ε b))
      exact congrArg (tmul R ((l.f n).hom a)) (LinearMap.congr_fun hm b)
    · have hα := LinearMap.congr_fun (α.left_positive p q n hpq hq) (tmul R a b)
      have hβ := LinearMap.congr_fun (β.left_positive p q n hpq hq)
        (tmul R ((l.f p).hom a) ((m.f q).hom b))
      change (β.left.f n).hom _ = 0 at hβ
      change (α.left.f n).hom _ = 0 at hα
      rw [hβ, hα, map_zero, map_zero]
  · apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply ordinaryTotal_linearMap_ext
    intro p q hpq a b
    change (β.right.f n).hom (((ordinaryTotalMap l m).f n).hom
      (ordinaryInclusion P.complex Q.complex p q n hpq (tmul R a b))) =
      tensorMap LinearMap.id (m.f n).hom (tensorMap f LinearMap.id ((α.right.f n).hom
        (ordinaryInclusion P.complex Q.complex p q n hpq (tmul R a b))))
    rw [ordinaryTotalMap_inclusion]
    by_cases hp : p = 0
    · subst p
      have hn : n = q := by omega
      cases hn
      erw [β.right_zero, α.right_zero]
      change tmul R (P'.ε ((l.f 0).hom a)) ((m.f n).hom b) =
        tmul R (f (P.ε a)) ((m.f n).hom b)
      exact congrArg (fun x => tmul R x ((m.f n).hom b)) (LinearMap.congr_fun hl a)
    · have hα := LinearMap.congr_fun (α.right_positive p q n hpq hp) (tmul R a b)
      have hβ := LinearMap.congr_fun (β.right_positive p q n hpq hp)
        (tmul R ((l.f p).hom a) ((m.f q).hom b))
      change (β.right.f n).hom _ = 0 at hβ
      change (α.right.f n).hom _ = 0 at hα
      rw [hβ, hα, map_zero, map_zero]

/-- The homology identification determined by a pair of actual augmentation
maps which are bijective in the degree under consideration. -/
def leftAugmentationEquiv {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    {P : LeftResolution Rᵐᵒᵖ A} {G : LeftResolution R B}
    (α : Augmentations P G) (n : ℕ)
    (hα : Function.Bijective (homologyMap α.left n))
    (hβ : Function.Bijective (homologyMap α.right n)) :
    Homology (leftOrdinaryTensorComplex A G.complex) n ≃ₗ[ℤ] TorWith P B n :=
  (LinearEquiv.ofBijective (homologyMap α.right n) hβ).symm.trans
    (LinearEquiv.ofBijective (homologyMap α.left n) hα)

theorem leftAugmentationEquiv_right {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    {P : LeftResolution Rᵐᵒᵖ A} {G : LeftResolution R B}
    (α : Augmentations P G) (n : ℕ)
    (hα : Function.Bijective (homologyMap α.left n))
    (hβ : Function.Bijective (homologyMap α.right n))
    (z : Homology (ordinaryTotal P.complex G.complex) n) :
    leftAugmentationEquiv α n hα hβ (homologyMap α.right n z) = homologyMap α.left n z := by
  exact congrArg (homologyMap α.left n)
    ((LinearEquiv.ofBijective (homologyMap α.right n) hβ).symm_apply_apply z)

/-- Once the flat augmented total maps are established, their explicit
summand formulas give the full left computation interface. -/
def leftComputationsOfAugmentations (n : ℕ)
    (h : ∀ {B : ModuleCat.{w} R} (G : LeftResolution R B), IsLeftFlat.{u,v,w} G →
      ∀ {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A),
      ∃ α : Augmentations P.val G, Function.Bijective (homologyMap α.left n) ∧
        Function.Bijective (homologyMap α.right n)) : LeftComputations.{u,v,w} R n := by
  classical
  let a {B : ModuleCat.{w} R} (G : LeftResolution R B) (hG : IsLeftFlat.{u,v,w} G)
      {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A) :=
    Classical.choose (h G hG P)
  have ha {B : ModuleCat.{w} R} (G : LeftResolution R B) (hG : IsLeftFlat.{u,v,w} G)
      {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A) :
      Function.Bijective (homologyMap (a G hG P).left n) ∧
      Function.Bijective (homologyMap (a G hG P).right n) :=
    Classical.choose_spec (h G hG P)
  refine { iso := (fun {B} G hG {A} P => leftAugmentationEquiv (a G hG P) n
        (ha G hG P).1 (ha G hG P).2), naturality := ?_, normalization := ?_ }
  · intro A A' B B' G G' hG hG' P P' f g l k hl hk x
    obtain ⟨z, rfl⟩ := (ha G hG P).2.2 x
    have hn := augmentations_natural R A A' B B' P.val P'.val G G'
      f.hom g.hom k l hk hl (a G hG P) (a G' hG' P')
    have hr := congrArg (fun t => homologyMap t n) hn.2
    have hleft := congrArg (fun t => homologyMap t n) hn.1
    have hc₁ := P103.Ch10.Complexes.homologyMap_comp (ordinaryTotalMap k l) (a G' hG' P').right n
    have hc₂ := P103.Ch10.Complexes.homologyMap_comp (a G hG P).right (leftTensorMap f.hom l) n
    dsimp only [P103.Ch10.Complexes.homologyMap] at hc₁ hc₂
    rw [hc₁, hc₂] at hr
    have hrz := congrArg (fun t => t z) hr
    dsimp only [LinearMap.comp_apply] at hrz
    have hc₃ := P103.Ch10.Complexes.homologyMap_comp (ordinaryTotalMap k l) (a G' hG' P').left n
    have hc₄ := P103.Ch10.Complexes.homologyMap_comp (a G hG P).left
      (tensorFirstMap k B ≫ tensorSecondMap P'.val.complex g.hom) n
    dsimp only [P103.Ch10.Complexes.homologyMap] at hc₃ hc₄
    rw [hc₃, hc₄] at hleft
    have hlz := congrArg (fun t => t z) hleft
    dsimp only [LinearMap.comp_apply] at hlz
    calc
      _ = leftAugmentationEquiv (a G' hG' P') n (ha G' hG' P').1 (ha G' hG' P').2
          (homologyMap (a G' hG' P').right n (homologyMap (ordinaryTotalMap k l) n z)) :=
        congrArg (leftAugmentationEquiv (a G' hG' P') n (ha G' hG' P').1 (ha G' hG' P').2) hrz.symm
      _ = homologyMap (a G' hG' P').left n (homologyMap (ordinaryTotalMap k l) n z) :=
        leftAugmentationEquiv_right _ _ _ _ _
      _ = homologyMap (tensorFirstMap k B ≫ tensorSecondMap P'.val.complex g.hom) n
          (homologyMap (a G hG P).left n z) := hlz
      _ = _ := congrArg (homologyMap (tensorFirstMap k B ≫ tensorSecondMap P'.val.complex g.hom) n)
        (leftAugmentationEquiv_right (a G hG P) n (ha G hG P).1 (ha G hG P).2 z).symm

  · intro A B P Q hQ α z
    have hu := augmentations_unique P.val Q.val α (a Q.val hQ P)
    change leftAugmentationEquiv (a Q.val hQ P) n _ _ (homologyMap α.right n z) =
      homologyMap α.left n z
    rw [hu.1, hu.2]
    exact leftAugmentationEquiv_right _ _ _ _ z
end TotalAugmentations

section LeftComparison
open P103.Specs.Ch10.HomologySequence

abbrev leftTensorSecondMap (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {C D : ChainComplex (ModuleCat.{w} R) ℕ} (l : C ⟶ D) :
    leftOrdinaryTensorComplex A C ⟶ leftOrdinaryTensorComplex A D :=
  ((leftTensorFunctor A).mapHomologicalComplex (ComplexShape.down ℕ)).map l

theorem leftTensorMap_identity_coefficient
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {C D : ChainComplex (ModuleCat.{w} R) ℕ} (l : C ⟶ D) :
    leftTensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) l = leftTensorSecondMap A l := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

theorem leftTensor_degreewise_exact
    (C : ChainComplex (ModuleCat.{w} R) ℕ)
    (hC : ∀ n, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,max u v w} R (C.X n))
    {X Y Z : Type (max u v w)}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module Rᵐᵒᵖ X] [Module Rᵐᵒᵖ Y] [Module Rᵐᵒᵖ Z]
    (i : X →ₗ[Rᵐᵒᵖ] Y) (p : Y →ₗ[Rᵐᵒᵖ] Z)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hp : Function.Surjective p) :
    DegreewiseExact (leftTensorFirstMap i C) (leftTensorFirstMap p C) := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · exact hC n X Y i hi (tensorMap i LinearMap.id).toAddMonoidHom (fun _ _ => rfl)
  · exact flat_tensor_exact (hC n) i p he
  · exact (P103.HomTensorExactness.tensor_first_rightExact i p he hp
      (tensorMap i (LinearMap.id : C.X n →ₗ[R] C.X n)).toAddMonoidHom
      (fun _ _ => rfl)
      (tensorMap p (LinearMap.id : C.X n →ₗ[R] C.X n)).toAddMonoidHom
      (fun _ _ => rfl)).2

theorem leftTensor_coeff_naturality
    {C D : ChainComplex (ModuleCat.{w} R) ℕ}
    (l : C ⟶ D)
    {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
    [Module Rᵐᵒᵖ X] [Module Rᵐᵒᵖ Y] (f : X →ₗ[Rᵐᵒᵖ] Y) :
    leftTensorFirstMap f C ≫ leftTensorSecondMap Y l =
      leftTensorSecondMap X l ≫ leftTensorFirstMap f D := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a x
  rfl

abbrev leftResolutionComparison {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) : Q.complex ⟶ G.complex :=
  P103.Ch10.Comparison.chainMap Q G hQ LinearMap.id

theorem leftResolutionComparison_lifts {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) :
    ChainLift Q G LinearMap.id (leftResolutionComparison Q hQ G) :=
  P103.Ch10.Comparison.chainMap_lifts Q G hQ LinearMap.id

def leftComparisonMap
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) (n : ℕ) :
    Homology (leftOrdinaryTensorComplex A Q.complex) n →ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex A G.complex) n :=
  homologyMap (leftTensorSecondMap A (leftResolutionComparison Q hQ G)) n

theorem left_tensor_lift_independent
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B B' : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B']
    (Q : LeftResolution R B) (G : LeftResolution R B') (hQ : Q.IsProjective)
    (g : B →ₗ[R] B') (l k : Q.complex ⟶ G.complex)
    (hl : ChainLift Q G g l) (hk : ChainLift Q G g k) (n : ℕ) :
    homologyMap (leftTensorSecondMap A l) n =
      homologyMap (leftTensorSecondMap A k) n :=
  congrArg ModuleCat.Hom.hom
    (P103.Ch10.Comparison.chain_homology_independent R ℤ
      (leftTensorFunctor A) B B' Q G hQ g l k n hl hk)

theorem leftComparisonMap_eq
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) (n : ℕ) (l : Q.complex ⟶ G.complex)
    (hl : ChainLift Q G LinearMap.id l) :
    leftComparisonMap A Q hQ G n = homologyMap (leftTensorSecondMap A l) n :=
  left_tensor_lift_independent A Q G hQ LinearMap.id _ l
    (leftResolutionComparison_lifts Q hQ G) hl n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem leftComparisonMap_bijective_zero
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective) (G : LeftResolution R B) :
    Function.Bijective (leftComparisonMap A Q hQ G 0) := by
  have hn (x) : leftZeroTensor A G (leftComparisonMap A Q hQ G 0 x) =
      leftZeroTensor A Q x := by
    have h := leftZeroTensor_natural Q G
      (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) LinearMap.id
      (leftResolutionComparison Q hQ G) (leftResolutionComparison_lifts Q hQ G) x
    rw [leftTensorMap_identity_coefficient] at h
    have hid : tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
        (LinearMap.id : B →ₗ[R] B) = LinearMap.id := by
      apply tensor_hom_ext
      intro a b
      rfl
    simpa only [hid, LinearMap.id_apply, leftComparisonMap] using h
  constructor
  · intro x y h
    apply (leftZeroTensor A Q).injective
    rw [← hn x, ← hn y, h]
  · intro y
    refine ⟨(leftZeroTensor A Q).symm (leftZeroTensor A G y), ?_⟩
    apply (leftZeroTensor A G).injective
    rw [hn, LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
theorem leftComparisonMap_bijective_large
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) (hG : IsLeftFlat.{u,v,w} G) (n : ℕ) :
    ∀ (A : Type (max u v w)) [AddCommGroup A] [Module Rᵐᵒᵖ A],
      Function.Bijective (leftComparisonMap A Q hQ G n) := by
  induction n with
  | zero => intro A _ _; exact leftComparisonMap_bijective_zero A Q hQ G
  | succ n ih =>
    intro A _ _
    let E := A →₀ Rᵐᵒᵖ
    let p : E →ₗ[Rᵐᵒᵖ] A := Finsupp.linearCombination Rᵐᵒᵖ id
    let K := LinearMap.ker p
    let i : K →ₗ[Rᵐᵒᵖ] E := (LinearMap.ker p).subtype
    have hi : Function.Injective i := Subtype.val_injective
    have hp : Function.Surjective p :=
      Finsupp.linearCombination_surjective Rᵐᵒᵖ Function.surjective_id
    have he : Function.Exact i p := LinearMap.exact_subtype_ker_map p
    let c := leftResolutionComparison Q hQ G
    have hQE := leftTensor_resolution_homology_succ E Q
      ((P103.Ch02.FlatnessTests.right_tensor_characterizations
        R E).2.2.2.1 inferInstance) n
    have hGE := leftTensor_resolution_homology_succ E G
      ((P103.Ch02.FlatnessTests.right_tensor_characterizations
        R E).2.2.2.1 inferInstance) n
    have hsQ := leftTensor_degreewise_exact.{u,v,max u w} Q.complex
      (projective_resolution_leftFlat.{u,v,w} Q hQ)
      (X := K) (Y := E) (Z := A) i p hi he hp
    have hsG := leftTensor_degreewise_exact.{u,v,max u w} G.complex hG
      (X := K) (Y := E) (Z := A) i p hi he hp
    change Function.Bijective (homologyMap (leftTensorSecondMap.{u,max u v w,max u w} A c) (n+1))
    have hci : leftTensorFirstMap.{u,max u v w,max u w} i Q.complex ≫ leftTensorSecondMap.{u,max u v w,max u w} E c =
        leftTensorSecondMap.{u,max u v w,max u w} K c ≫ leftTensorFirstMap.{u,max u v w,max u w} i G.complex := by
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro a x
      rfl
    have hcp : leftTensorFirstMap.{u,max u v w,max u w} p Q.complex ≫ leftTensorSecondMap.{u,max u v w,max u w} A c =
        leftTensorSecondMap.{u,max u v w,max u w} E c ≫ leftTensorFirstMap.{u,max u v w,max u w} p G.complex := by
      apply HomologicalComplex.Hom.ext
      funext j
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro a x
      rfl
    have ihK : Function.Bijective (homologyMap (leftTensorSecondMap.{u,max u v w,max u w} K c) n) := ih K
    have ihE : Function.Injective (homologyMap (leftTensorSecondMap.{u,max u v w,max u w} E c) n) := (ih E).1
    refine homology_bijective_succ_of_middle_acyclic.{max u v w}
      (C₀ := leftOrdinaryTensorComplex.{u,max u v w,max u w} K Q.complex)
      (C₁ := leftOrdinaryTensorComplex.{u,max u v w,max u w} E Q.complex)
      (C₂ := leftOrdinaryTensorComplex.{u,max u v w,max u w} A Q.complex)
      (D₀ := leftOrdinaryTensorComplex.{u,max u v w,max u w} K G.complex)
      (D₁ := leftOrdinaryTensorComplex.{u,max u v w,max u w} E G.complex)
      (D₂ := leftOrdinaryTensorComplex.{u,max u v w,max u w} A G.complex)
      (leftTensorFirstMap.{u,max u v w,max u w} i Q.complex) (leftTensorFirstMap.{u,max u v w,max u w} p Q.complex)
      (leftTensorFirstMap.{u,max u v w,max u w} i G.complex) (leftTensorFirstMap.{u,max u v w,max u w} p G.complex)
      (leftTensorSecondMap.{u,max u v w,max u w} K c) (leftTensorSecondMap.{u,max u v w,max u w} E c) (leftTensorSecondMap.{u,max u v w,max u w} A c)
      ?_ ?_ ?_ ?_ n ?_ ?_ ?_ ?_
    · exact hci
    · exact hcp
    · exact hsQ
    · exact hsG
    · exact hQE
    · exact hGE
    · exact ihK
    · exact ihE

/-- Raising only the right coefficient changes the left tensor complex by
an explicit chain isomorphism. -/
def leftTensorULiftIso
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (C : ChainComplex (ModuleCat.{max u w} R) ℕ) :
    leftOrdinaryTensorComplex A C ≅
      leftOrdinaryTensorComplex (ULift.{max u w} A) C where
  hom :=
    { f := fun n => ModuleCat.ofHom
        (tensorMap (ULift.moduleEquiv : ULift.{max u w} A ≃ₗ[Rᵐᵒᵖ] A).symm.toLinearMap
          (LinearMap.id : C.X n →ₗ[R] C.X n))
      comm' := by
        intro i j h
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a x
        rfl }
  inv :=
    { f := fun n => ModuleCat.ofHom
        (tensorMap (ULift.moduleEquiv : ULift.{max u w} A ≃ₗ[Rᵐᵒᵖ] A).toLinearMap
          (LinearMap.id : C.X n →ₗ[R] C.X n))
      comm' := by
        intro i j h
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro a x
        rfl }
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a x
    rfl
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a x
    rfl

def leftTensorULiftHomologyEquiv
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (C : ChainComplex (ModuleCat.{max u w} R) ℕ) (n : ℕ) :
    Homology (leftOrdinaryTensorComplex A C) n ≃ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex (ULift.{max u w} A) C) n where
  toLinearMap := homologyMap (leftTensorULiftIso.{u,v,w} A C).hom n
  invFun := homologyMap (leftTensorULiftIso.{u,v,w} A C).inv n
  left_inv x := by
    change ((homologyMap (leftTensorULiftIso.{u,v,w} A C).inv n).comp
      (homologyMap (leftTensorULiftIso.{u,v,w} A C).hom n)) x = x
    rw [← P103.Ch10.Complexes.homologyMap_comp, Iso.hom_inv_id,
      P103.Ch10.Complexes.homologyMap_id]
    rfl
  right_inv x := by
    change ((homologyMap (leftTensorULiftIso.{u,v,w} A C).hom n).comp
      (homologyMap (leftTensorULiftIso.{u,v,w} A C).inv n)) x = x
    rw [← P103.Ch10.Complexes.homologyMap_comp, Iso.inv_hom_id,
      P103.Ch10.Complexes.homologyMap_id]
    rfl

theorem leftTensorULiftIso_natural
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {C D : ChainComplex (ModuleCat.{max u w} R) ℕ} (l : C ⟶ D) :
    (leftTensorULiftIso.{u,v,w} A C).hom ≫
        leftTensorSecondMap (ULift.{max u w} A) l =
      leftTensorSecondMap A l ≫ (leftTensorULiftIso.{u,v,w} A D).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a x
  rfl

theorem leftTensorULiftHomologyEquiv_natural
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {C D : ChainComplex (ModuleCat.{max u w} R) ℕ} (l : C ⟶ D) (n : ℕ) :
    (leftTensorULiftHomologyEquiv.{u,v,w} A D n).toLinearMap.comp
      (homologyMap (leftTensorSecondMap A l) n) =
    (homologyMap (leftTensorSecondMap (ULift.{max u w} A) l) n).comp
      (leftTensorULiftHomologyEquiv.{u,v,w} A C n).toLinearMap := by
  change (homologyMap (leftTensorULiftIso.{u,v,w} A D).hom n).comp
      (homologyMap (leftTensorSecondMap A l) n) =
    (homologyMap (leftTensorSecondMap (ULift.{max u w} A) l) n).comp
      (homologyMap (leftTensorULiftIso.{u,v,w} A C).hom n)
  rw [← P103.Ch10.Complexes.homologyMap_comp,
    ← P103.Ch10.Complexes.homologyMap_comp, leftTensorULiftIso_natural]

theorem leftComparisonMap_ulift_natural
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) (n : ℕ) :
    (leftTensorULiftHomologyEquiv.{u,v,w} A G.complex n).toLinearMap.comp
      (leftComparisonMap A Q hQ G n) =
    (leftComparisonMap (ULift.{max u w} A) Q hQ G n).comp
      (leftTensorULiftHomologyEquiv.{u,v,w} A Q.complex n).toLinearMap :=
  leftTensorULiftHomologyEquiv_natural.{u,v,w} A (leftResolutionComparison Q hQ G) n

theorem leftComparisonMap_bijective_of_ulift
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) (n : ℕ)
    (h : Function.Bijective (leftComparisonMap (ULift.{max u w} A) Q hQ G n)) :
    Function.Bijective (leftComparisonMap A Q hQ G n) := by
  let eQ := leftTensorULiftHomologyEquiv.{u,v,w} A Q.complex n
  let eG := leftTensorULiftHomologyEquiv.{u,v,w} A G.complex n
  have sq (x : Homology (leftOrdinaryTensorComplex A Q.complex) n) :
      eG (leftComparisonMap A Q hQ G n x) =
        leftComparisonMap (ULift.{max u w} A) Q hQ G n (eQ x) :=
    LinearMap.congr_fun (leftComparisonMap_ulift_natural A Q hQ G n) x
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eQ.injective
    apply h.injective
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨x, hx⟩ := h.surjective (eG y)
    refine ⟨eQ.symm x, eG.injective ?_⟩
    rw [sq, eQ.apply_symm_apply, hx]

theorem leftComparisonMap_bijective
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (G : LeftResolution R B) (hG : IsLeftFlat.{u,v,w} G) (n : ℕ) :
    Function.Bijective (leftComparisonMap A Q hQ G n) :=
  leftComparisonMap_bijective_of_ulift A Q hQ G n
    (leftComparisonMap_bijective_large.{u,v,w} Q hQ G hG n (ULift.{max u w} A))

/-- Naturality before inversion of the projective-to-flat comparison,
simultaneously in the augmented resolution and the right coefficient. -/
theorem leftComparisonMap_natural
    {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A']
    {B B' : Type w} [AddCommGroup B] [AddCommGroup B'] [Module R B] [Module R B']
    (Q : LeftResolution R B) (Q' : LeftResolution R B')
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (G : LeftResolution R B) (G' : LeftResolution R B')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B')
    (l : G.complex ⟶ G'.complex) (k : Q.complex ⟶ Q'.complex)
    (hl : ChainLift G G' g l) (hk : ChainLift Q Q' g k) (n : ℕ) :
    (homologyMap (leftTensorMap f l) n).comp (leftComparisonMap A Q hQ G n) =
      (leftComparisonMap A' Q' hQ' G' n).comp
        (homologyMap (leftTensorMap f k) n) := by
  let c := leftResolutionComparison Q hQ G
  let c' := leftResolutionComparison Q' hQ' G'
  have hcl : ChainLift Q G' g (c ≫ l) := by
    simpa only [LinearMap.comp_id] using P103.Ch10.Comparison.chainLift_comp
      (leftResolutionComparison_lifts Q hQ G) hl
  have hkc : ChainLift Q G' g (k ≫ c') := by
    simpa only [LinearMap.id_comp] using P103.Ch10.Comparison.chainLift_comp hk
      (leftResolutionComparison_lifts Q' hQ' G')
  have he := left_tensor_lift_independent A' Q G' hQ g
    (c ≫ l) (k ≫ c') hcl hkc n
  have he' : homologyMap (leftTensorMap f (c ≫ l)) n =
      homologyMap (leftTensorMap f (k ≫ c')) n := by
    simpa only [leftTensorMap, leftTensorSecondMap,
      P103.Ch10.Complexes.homologyMap_comp] using
      congrArg (fun a => a.comp (homologyMap (leftTensorFirstMap f Q.complex) n)) he
  have h₁ : leftTensorSecondMap A c ≫ leftTensorMap f l =
      leftTensorMap f (c ≫ l) := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  have h₂ : leftTensorMap f k ≫ leftTensorSecondMap A' c' =
      leftTensorMap f (k ≫ c') := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  change (homologyMap (leftTensorMap f l) n).comp
      (homologyMap (leftTensorSecondMap A c) n) =
    (homologyMap (leftTensorSecondMap A' c') n).comp
      (homologyMap (leftTensorMap f k) n)
  rw [← P103.Ch10.Complexes.homologyMap_comp, h₁,
    ← P103.Ch10.Complexes.homologyMap_comp, h₂]
  exact he'

end LeftComparison

section Restriction
universe sres tres
variable {S : Type sres} [Ring S]

theorem restriction_cycles_succ (C : ChainComplex (ModuleCat.{tres} S) ℤ) (n : ℕ) :
    cycles (C.restriction nonnegativeChainEmbedding) (n+1) =
      cycles C ((n+1 : ℕ) : ℤ) := by
  unfold cycles
  rw [ChainComplex.next_nat_succ]
  change LinearMap.ker (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = _
  rw [ChainComplex.next]
  have hn : ((n+1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [hn]

theorem restriction_boundaries (C : ChainComplex (ModuleCat.{tres} S) ℤ) (n : ℕ) :
    boundaries (C.restriction nonnegativeChainEmbedding) n =
      boundaries C (n : ℤ) := by
  unfold boundaries
  rw [ChainComplex.prev, ChainComplex.prev]
  change LinearMap.range (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom = _
  congr 2
/-- The quotient homology in a positive degree is unchanged by retaining
only the nonnegative part of an integer chain complex. -/
def restrictionHomologySuccEquiv
    (C : ChainComplex (ModuleCat.{tres} S) ℤ) (n : ℕ) :
    Homology (C.restriction nonnegativeChainEmbedding) (n+1) ≃ₗ[S]
      Homology C ((n+1 : ℕ) : ℤ) := by
  let e : cycles (C.restriction nonnegativeChainEmbedding) (n+1) ≃ₗ[S]
      cycles C ((n+1 : ℕ) : ℤ) :=
    LinearEquiv.ofEq _ _ (restriction_cycles_succ C n)
  apply Submodule.Quotient.equiv _ _ e
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x.val ∈ boundaries C ((n+1 : ℕ) : ℤ)
    rw [← restriction_boundaries C (n+1)]
    exact hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    change z.val ∈ boundaries (C.restriction nonnegativeChainEmbedding) (n+1)
    rw [restriction_boundaries]
    exact hz

theorem restrictionHomologySuccEquiv_class
    (C : ChainComplex (ModuleCat.{tres} S) ℤ) (n : ℕ)
    (z : cycles (C.restriction nonnegativeChainEmbedding) (n+1)) :
    restrictionHomologySuccEquiv C n (homologyClass _ _ z) =
      homologyClass C ((n+1 : ℕ) : ℤ)
        (LinearEquiv.ofEq _ _ (restriction_cycles_succ C n) z) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem restrictionHomologySuccEquiv_natural
    {C D : ChainComplex (ModuleCat.{tres} S) ℤ} (f : C ⟶ D) (n : ℕ)
    (x : Homology (C.restriction nonnegativeChainEmbedding) (n+1)) :
    restrictionHomologySuccEquiv D n
      (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1) x) =
      homologyMap f ((n+1 : ℕ) : ℤ) (restrictionHomologySuccEquiv C n x) := by
  refine Quotient.inductionOn' x ?_
  intro z
  change restrictionHomologySuccEquiv D n
      (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1)
        (homologyClass _ _ z)) =
    homologyMap f ((n+1 : ℕ) : ℤ)
      (restrictionHomologySuccEquiv C n (homologyClass _ _ z))
  rw [P103.Ch10.Complexes.homologyMap_apply, restrictionHomologySuccEquiv_class,
    restrictionHomologySuccEquiv_class, P103.Ch10.Complexes.homologyMap_apply]
  congr 1

theorem restriction_homologyMap_bijective_succ
    {C D : ChainComplex (ModuleCat.{tres} S) ℤ} (f : C ⟶ D) (n : ℕ)
    (hf : Function.Bijective (homologyMap f ((n+1 : ℕ) : ℤ))) :
    Function.Bijective
      (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1)) := by
  let eC := restrictionHomologySuccEquiv C n
  let eD := restrictionHomologySuccEquiv D n
  have sq (x) : eD
      (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1) x) =
      homologyMap f ((n+1 : ℕ) : ℤ) (eC x) :=
    restrictionHomologySuccEquiv_natural f n x
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply eC.injective
    apply hf.injective
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hf.surjective (eD y)
    refine ⟨eC.symm x, eD.injective ?_⟩
    rw [sq, eC.apply_symm_apply, hx]

theorem restriction_quasiIsomorphism_succ
    {C D : ChainComplex (ModuleCat.{tres} S) ℤ} (f : C ⟶ D)
    (hf : QuasiIsomorphism f) (n : ℕ) :
    Function.Bijective
      (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1)) :=
  restriction_homologyMap_bijective_succ f n (hf _)

end Restriction

section CanonicalAugmentations
open P103.Specs.Ch10.TotalComplexAssembly
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def ordinaryProjection (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    (ordinaryTotal C D).X n →ₗ[ℤ] Tensor R (C.X p) (D.X q) :=
  (tensorMap (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom
    (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom.hom).comp
      (totalProjection (tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D))
        p q n (by exact_mod_cast h)).hom

theorem ordinaryProjection_inclusion (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (z : Tensor R (C.X p) (D.X q)) :
    ordinaryProjection C D p q n h (ordinaryInclusion C D p q n h z) = z := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let eC : (extendNonnegativeChain C).X p ≃ₗ[Rᵐᵒᵖ] C.X p :=
    (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).toLinearEquiv
  let eD : (extendNonnegativeChain D).X q ≃ₗ[R] D.X q :=
    (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).toLinearEquiv
  change tensorMap eC.toLinearMap eD.toLinearMap
    ((totalProjection K p q n _).hom ((totalInclusion K p q n _).hom
      (tensorMap eC.symm.toLinearMap eD.symm.toLinearMap z))) = z
  have hc := congrArg (fun f => f.hom (tensorMap eC.symm.toLinearMap eD.symm.toLinearMap z))
    (P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self K p q n (by exact_mod_cast h))
  change (totalProjection K p q n _).hom ((totalInclusion K p q n _).hom _) = _ at hc
  rw [hc]
  exact (tensorLinearEquiv eC eD).apply_symm_apply z

theorem ordinaryProjection_inclusion_ne (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q p' q' n : ℕ)
    (h : p+q=n) (h' : p'+q'=n) (hne : p≠p' ∨ q≠q')
    (z : Tensor R (C.X p) (D.X q)) :
    ordinaryProjection C D p' q' n h' (ordinaryInclusion C D p q n h z) = 0 := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let eC : (extendNonnegativeChain C).X p ≃ₗ[Rᵐᵒᵖ] C.X p :=
    (C.extendXIso nonnegativeChainEmbedding (i := p) rfl).toLinearEquiv
  let eD : (extendNonnegativeChain D).X q ≃ₗ[R] D.X q :=
    (D.extendXIso nonnegativeChainEmbedding (i := q) rfl).toLinearEquiv
  have hne' : (p:ℤ) ≠ p' ∨ (q:ℤ) ≠ q' := by exact_mod_cast hne
  have hc := congrArg (fun f => f.hom (tensorMap eC.symm.toLinearMap eD.symm.toLinearMap z))
    (P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne K p q p' q' n
      (by exact_mod_cast h) (by exact_mod_cast h') hne')
  change (totalProjection K p' q' n _).hom ((totalInclusion K p q n _).hom _) = 0 at hc
  change tensorMap _ _ ((totalProjection K p' q' n _).hom ((totalInclusion K p q n _).hom _)) = 0
  erw [hc, map_zero]


theorem extendNonnegative_d_apply {S : Type*} [Ring S]
    (C : ChainComplex (ModuleCat.{v} S) ℕ) (i j : ℕ)
    (x : (extendNonnegativeChain C).X i) :
    (C.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom.hom
      (((extendNonnegativeChain C).d i j).hom x) =
    (C.d i j).hom ((C.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom.hom x) := by
  have h : (extendNonnegativeChain C).d i j ≫
      (C.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom =
      (C.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom ≫ C.d i j := by
    erw [C.extend_d_eq nonnegativeChainEmbedding (i := i) (j := j) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun f => f.hom x) h

private theorem projection_d_endpoint_congr (K : ChainBicomplex.{0,v} ℤ)
    (p q n m m' : ℤ) (h : p+q=m) (h' : p+q=m') (hm : m=m') :
    (totalProjection K p q m h).hom.comp ((total K).d n m).hom =
      (totalProjection K p q m' h').hom.comp ((total K).d n m').hom := by
  cases hm
  rfl

theorem ordinaryProjection_d (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    (ordinaryProjection C D p q n h).comp ((ordinaryTotal C D).d (n+1) n).hom =
      (tensorMap (C.d (p+1) p).hom (LinearMap.id : D.X q →ₗ[R] D.X q)).comp
        (ordinaryProjection C D (p+1) q (n+1) (by omega)) +
      (p:ℤ).negOnePow • (tensorMap (LinearMap.id : C.X p →ₗ[Rᵐᵒᵖ] C.X p)
        (D.d (q+1) q).hom).comp (ordinaryProjection C D p (q+1) (n+1) (by omega)) := by
  let K := tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D)
  let eC (i : ℕ) : (extendNonnegativeChain C).X i ≃ₗ[Rᵐᵒᵖ] C.X i :=
    (C.extendXIso nonnegativeChainEmbedding (i := i) rfl).toLinearEquiv
  let eD (j : ℕ) : (extendNonnegativeChain D).X j ≃ₗ[R] D.X j :=
    (D.extendXIso nonnegativeChainEmbedding (i := j) rfl).toLinearEquiv
  have hraw : (p:ℤ)+q=(n:ℤ)+1-1 := by
    have hh : (p:ℤ)+q=(n:ℤ) := by exact_mod_cast h
    omega
  have hd := congrArg ModuleCat.Hom.hom
    (P103.Ch10.TotalComplexAssembly.chain_totalProjection_d K p q (n+1) hraw)
  dsimp only [P103.Ch10.TotalComplexAssembly.total, P103.Ch10.TotalComplexAssembly.totalProjection] at hd
  have hn : (n:ℤ)+1-1=n := by omega
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul] at hd
  have hd' : (totalProjection K p q n (by exact_mod_cast h)).hom.comp
      ((total K).d (n+1) n).hom =
      ((K.d (p+1) p).f q).hom.comp
        (totalProjection K (p+1) q (n+1) (by exact_mod_cast (show p+1+q=n+1 by omega))).hom +
      (p:ℤ).negOnePow • ((K.X p).d (q+1) q).hom.comp
        (totalProjection K p (q+1) (n+1) (by exact_mod_cast (show p+(q+1)=n+1 by omega))).hom := by
    exact (projection_d_endpoint_congr K p q (n+1) n (n+1-1)
      (by exact_mod_cast h) hraw hn.symm).trans hd
  have hh : (tensorMap (eC p).toLinearMap (eD q).toLinearMap).comp ((K.d (p+1) p).f q).hom =
      (tensorMap (C.d (p+1) p).hom (LinearMap.id : D.X q →ₗ[R] D.X q)).comp
        (tensorMap (eC (p+1)).toLinearMap (eD q).toLinearMap) := by
    apply tensor_hom_ext
    intro a b
    exact congrArg (fun x => tmul R x ((eD q) b))
      (extendNonnegative_d_apply C (p+1) p a)
  have hv : (tensorMap (eC p).toLinearMap (eD q).toLinearMap).comp ((K.X p).d (q+1) q).hom =
      (tensorMap (LinearMap.id : C.X p →ₗ[Rᵐᵒᵖ] C.X p) (D.d (q+1) q).hom).comp
        (tensorMap (eC p).toLinearMap (eD (q+1)).toLinearMap) := by
    apply tensor_hom_ext
    intro a b
    exact congrArg (tmul R ((eC p) a))
      (extendNonnegative_d_apply D (q+1) q b)
  change ((tensorMap (eC p).toLinearMap (eD q).toLinearMap).comp
      (totalProjection K p q n _).hom).comp ((total K).d (n+1) n).hom = _
  rw [LinearMap.comp_assoc, hd', LinearMap.comp_add, LinearMap.comp_smul,
    ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, hh, hv,
    LinearMap.comp_assoc, LinearMap.comp_assoc]
  rfl


section AugmentationMaps
variable {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
variable {B : Type w} [AddCommGroup B] [Module R B]
variable (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)

def augmentationLeftComponent (n : ℕ) :
    (ordinaryTotal F.complex G.complex).X n →ₗ[ℤ] (tensorComplex F.complex B).X n :=
  (tensorMap (LinearMap.id : F.complex.X n →ₗ[Rᵐᵒᵖ] F.complex.X n) G.ε).comp
    (ordinaryProjection F.complex G.complex n 0 n (by omega))

def augmentationRightComponent (n : ℕ) :
    (ordinaryTotal F.complex G.complex).X n →ₗ[ℤ] (leftOrdinaryTensorComplex A G.complex).X n :=
  (tensorMap F.ε (LinearMap.id : G.complex.X n →ₗ[R] G.complex.X n)).comp
    (ordinaryProjection F.complex G.complex 0 n n (by omega))

private theorem resolution_ε_d {S : Type*} [Ring S] {M : Type*}
    [AddCommGroup M] [Module S M] (F : LeftResolution S M) (x : F.complex.X 1) :
    F.ε ((F.complex.d 1 0).hom x) = 0 := by
  have hx : (F.complex.d 1 0).hom x ∈ LinearMap.ker F.ε :=
    F.exact_zero ▸ ⟨x, rfl⟩
  exact hx

theorem augmentationLeftComponent_comm (n : ℕ) :
    ((tensorComplex F.complex B).d (n+1) n).hom.comp (augmentationLeftComponent F G (n+1)) =
      (augmentationLeftComponent F G n).comp ((ordinaryTotal F.complex G.complex).d (n+1) n).hom := by
  have hd := ordinaryProjection_d F.complex G.complex n 0 n (by omega)
  have hh : (tensorMap (LinearMap.id : F.complex.X n →ₗ[Rᵐᵒᵖ] F.complex.X n) G.ε).comp
      (tensorMap (F.complex.d (n+1) n).hom (LinearMap.id : G.complex.X 0 →ₗ[R] G.complex.X 0)) =
    (tensorMap (F.complex.d (n+1) n).hom (LinearMap.id : B →ₗ[R] B)).comp
      (tensorMap (LinearMap.id : F.complex.X (n+1) →ₗ[Rᵐᵒᵖ] F.complex.X (n+1)) G.ε) := by
    apply tensor_hom_ext; intro a b; rfl
  have hv : (tensorMap (LinearMap.id : F.complex.X n →ₗ[Rᵐᵒᵖ] F.complex.X n) G.ε).comp
      (tensorMap (LinearMap.id : F.complex.X n →ₗ[Rᵐᵒᵖ] F.complex.X n) (G.complex.d 1 0).hom) = 0 := by
    apply tensor_hom_ext
    intro a b
    change tmul R a (G.ε ((G.complex.d 1 0).hom b)) = 0
    rw [resolution_ε_d]
    simp [tmul]
  change (tensorMap (F.complex.d (n+1) n).hom (LinearMap.id : B →ₗ[R] B)).comp
      ((tensorMap (LinearMap.id : F.complex.X (n+1) →ₗ[Rᵐᵒᵖ] F.complex.X (n+1)) G.ε).comp _) =
    ((tensorMap (LinearMap.id : F.complex.X n →ₗ[Rᵐᵒᵖ] F.complex.X n) G.ε).comp _).comp _
  rw [LinearMap.comp_assoc, hd, LinearMap.comp_add, LinearMap.comp_smul]
  simp only [← LinearMap.comp_assoc]
  rw [hh, hv]
  simp only [LinearMap.zero_comp, smul_zero, add_zero, LinearMap.comp_assoc]

theorem augmentationRightComponent_comm (n : ℕ) :
    ((leftOrdinaryTensorComplex A G.complex).d (n+1) n).hom.comp (augmentationRightComponent F G (n+1)) =
      (augmentationRightComponent F G n).comp ((ordinaryTotal F.complex G.complex).d (n+1) n).hom := by
  have hd := ordinaryProjection_d F.complex G.complex 0 n n (by omega)
  have hh : (tensorMap F.ε (LinearMap.id : G.complex.X n →ₗ[R] G.complex.X n)).comp
      (tensorMap (F.complex.d 1 0).hom (LinearMap.id : G.complex.X n →ₗ[R] G.complex.X n)) = 0 := by
    apply tensor_hom_ext
    intro a b
    change tmul R (F.ε ((F.complex.d 1 0).hom a)) b = 0
    rw [resolution_ε_d]
    simp [tmul]
  have hv : (tensorMap F.ε (LinearMap.id : G.complex.X n →ₗ[R] G.complex.X n)).comp
      (tensorMap (LinearMap.id : F.complex.X 0 →ₗ[Rᵐᵒᵖ] F.complex.X 0) (G.complex.d (n+1) n).hom) =
    (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (G.complex.d (n+1) n).hom).comp
      (tensorMap F.ε (LinearMap.id : G.complex.X (n+1) →ₗ[R] G.complex.X (n+1))) := by
    apply tensor_hom_ext; intro a b; rfl
  change (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) (G.complex.d (n+1) n).hom).comp
      ((tensorMap F.ε (LinearMap.id : G.complex.X (n+1) →ₗ[R] G.complex.X (n+1))).comp _) =
    ((tensorMap F.ε (LinearMap.id : G.complex.X n →ₗ[R] G.complex.X n)).comp _).comp _
  rw [LinearMap.comp_assoc, hd, LinearMap.comp_add, LinearMap.comp_smul]
  simp only [← LinearMap.comp_assoc]
  rw [hh, hv]
  simp only [Int.natCast_zero, Int.negOnePow_zero, one_smul, LinearMap.zero_comp,
    zero_add, LinearMap.comp_assoc]

def augmentationLeft : ordinaryTotal F.complex G.complex ⟶ tensorComplex F.complex B where
  f n := ModuleCat.ofHom (augmentationLeftComponent F G n)
  comm' i j hij := by
    have hi : i = j+1 := hij.symm
    subst i
    apply ModuleCat.hom_ext
    exact augmentationLeftComponent_comm F G j

def augmentationRight : ordinaryTotal F.complex G.complex ⟶ leftOrdinaryTensorComplex A G.complex where
  f n := ModuleCat.ofHom (augmentationRightComponent F G n)
  comm' i j hij := by
    have hi : i = j+1 := hij.symm
    subst i
    apply ModuleCat.hom_ext
    exact augmentationRightComponent_comm F G j


def canonicalAugmentations : Augmentations F G where
  left := augmentationLeft F G
  right := augmentationRight F G
  left_zero p a b := by
    change tensorMap (LinearMap.id : F.complex.X p →ₗ[Rᵐᵒᵖ] F.complex.X p) G.ε
      (ordinaryProjection F.complex G.complex p 0 p (by omega)
        (ordinaryInclusion F.complex G.complex p 0 p (by omega) (tmul R a b))) = _
    rw [ordinaryProjection_inclusion]
    rfl
  left_positive p q n h hq := by
    apply LinearMap.ext
    intro z
    change tensorMap (LinearMap.id : F.complex.X n →ₗ[Rᵐᵒᵖ] F.complex.X n) G.ε
      (ordinaryProjection F.complex G.complex n 0 n (by omega)
        (ordinaryInclusion F.complex G.complex p q n h z)) = 0
    rw [ordinaryProjection_inclusion_ne F.complex G.complex p q n 0 n h (by omega) (Or.inr hq)]
    exact map_zero _
  right_zero q a b := by
    change tensorMap F.ε (LinearMap.id : G.complex.X q →ₗ[R] G.complex.X q)
      (ordinaryProjection F.complex G.complex 0 q q (by omega)
        (ordinaryInclusion F.complex G.complex 0 q q (by omega) (tmul R a b))) = _
    rw [ordinaryProjection_inclusion]
    rfl
  right_positive p q n h hp := by
    apply LinearMap.ext
    intro z
    change tensorMap F.ε (LinearMap.id : G.complex.X n →ₗ[R] G.complex.X n)
      (ordinaryProjection F.complex G.complex 0 n n (by omega)
        (ordinaryInclusion F.complex G.complex p q n h z)) = 0
    rw [ordinaryProjection_inclusion_ne F.complex G.complex p q 0 n n h (by omega) (Or.inl hp)]
    exact map_zero _

end AugmentationMaps

end CanonicalAugmentations

section AugmentedTensorAssembly
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def minusOneChainEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) where
  f i := (i : ℤ) - 1
  injective_f := by
    intro i j h
    change (i : ℤ) - 1 = (j : ℤ) - 1 at h
    exact_mod_cast (by omega : (i : ℤ) = j)
  rel := by intro i j h; change (j : ℤ) - 1 + 1 = (i : ℤ) - 1; change j + 1 = i at h; omega

theorem acyclic_iff_exactAt {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} S) c) :
    Acyclic C ↔ ∀ i, C.ExactAt i := by
  constructor
  · intro h i
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact (P103.Ch10.Complexes.acyclic_iff C).mp h i
  · intro h
    apply (P103.Ch10.Complexes.acyclic_iff C).mpr
    intro i
    exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (h i)

theorem acyclic_extend {S : Type*} [Ring S] {ι ι' : Type*}
    {c : ComplexShape ι} {c' : ComplexShape ι'}
    (C : HomologicalComplex (ModuleCat.{t} S) c) (e : c.Embedding c')
    (hC : Acyclic C) : Acyclic (C.extend e) := by
  apply (acyclic_iff_exactAt _).mpr
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    exact (HomologicalComplex.extend_exactAt_iff C e hi).mpr ((acyclic_iff_exactAt C).mp hC i)
  · exact C.extend_exactAt e j (by simpa using hj)

section TensorAugment
variable {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
variable (F : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B]

def augmentedResolutionNat {S : Type u} [Ring S] {M : Type v} [AddCommGroup M] [Module S M]
    (F : LeftResolution S M) : ChainComplex (ModuleCat.{max u v} S) ℕ :=
  ChainComplex.augment F.complex
    (ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} M ≃ₗ[S] M).symm.toLinearMap.comp F.ε)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change (ULift.moduleEquiv : ULift.{u} M ≃ₗ[S] M).symm
        (F.ε ((F.complex.d 1 0).hom a)) = 0
      have ha : F.ε ((F.complex.d 1 0).hom a) = 0 :=
        (show (F.complex.d 1 0).hom a ∈ LinearMap.ker F.ε from
          F.exact_zero ▸ ⟨a, rfl⟩)
      rw [ha, map_zero])

def tensorAugmentedNat : ChainComplex (ModuleCat.{max u v w} ℤ) ℕ :=
  tensorComplex (augmentedResolutionNat F) B

def tensorAugmentedResolution := (tensorAugmentedNat F B).extend minusOneChainEmbedding

theorem tensorAugmentedResolution_supported :
    SupportedIn (tensorAugmentedResolution F B) (Set.Ici (-1 : ℤ)) := by
  intro i hi
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply (tensorAugmentedNat F B).isZero_extend_X minusOneChainEmbedding i
  intro n hn
  change (n : ℤ) - 1 = i at hn
  simp only [Set.mem_Ici, not_le] at hi
  omega

theorem tensorAugmentedNat_acyclic
    (hB : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,max u v} R B) :
    Acyclic (tensorAugmentedNat F B) := by
  apply (acyclic_iff_exactAt _).mpr
  intro n
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((tensorAugmentedNat F B).d ((ComplexShape.down ℕ).prev n) n).hom =
    LinearMap.ker ((tensorAugmentedNat F B).d n ((ComplexShape.down ℕ).next n)).hom
  cases n with
  | zero =>
      rw [ChainComplex.prev, ChainComplex.next_nat_zero]
      change LinearMap.range (tensorMap
          ((ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A).symm.toLinearMap.comp F.ε)
          (LinearMap.id : B →ₗ[R] B)) = LinearMap.ker
        (tensorMap ((augmentedResolutionNat F).d 0 0).hom (LinearMap.id : B →ₗ[R] B))
      rw [(augmentedResolutionNat F).shape 0 0 (by decide)]
      have hz : tensorMap (0 : ULift.{u} A →ₗ[Rᵐᵒᵖ] ULift.{u} A)
          (LinearMap.id : B →ₗ[R] B) = 0 := by
        apply tensor_hom_ext
        intro a b
        change tmul R (0 : ULift.{u} A) b = 0
        simp [tmul]
      rw [show ModuleCat.Hom.hom (0 : (augmentedResolutionNat F).X 0 ⟶ _) = 0 from rfl, hz,
        LinearMap.ker_zero, LinearMap.range_eq_top]
      let e := tensorLinearEquiv (ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A).symm
        (LinearEquiv.refl R B)
      have he : tensorMap
          ((ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A).symm.toLinearMap.comp F.ε)
          (LinearMap.id : B →ₗ[R] B) =
          e.toLinearMap.comp (tensorMap F.ε LinearMap.id) := by
        apply tensor_hom_ext; intro a b; rfl
      rw [he]
      exact e.surjective.comp (P103.Ch11.ExtTorDefinitions.tensor_augmentation_exact F B).2
  | succ n =>
      rw [ChainComplex.prev, ChainComplex.next_nat_succ]
      cases n with
      | zero =>
          change LinearMap.range (tensorMap (F.complex.d 1 0).hom (LinearMap.id : B →ₗ[R] B)) =
            LinearMap.ker (tensorMap
              ((ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A).symm.toLinearMap.comp F.ε)
              (LinearMap.id : B →ₗ[R] B))
          let e := tensorLinearEquiv (ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A).symm
            (LinearEquiv.refl R B)
          have he : tensorMap
              ((ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A).symm.toLinearMap.comp F.ε)
              (LinearMap.id : B →ₗ[R] B) =
              e.toLinearMap.comp (tensorMap F.ε LinearMap.id) := by
            apply tensor_hom_ext; intro a b; rfl
          rw [he, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr e.injective)]
          exact (LinearMap.exact_iff.mp (P103.Ch11.ExtTorDefinitions.tensor_augmentation_exact F B).1).symm
      | succ n =>
          change LinearMap.range ((tensorComplex F.complex B).d (n + 2) (n + 1)).hom =
            LinearMap.ker ((tensorComplex F.complex B).d (n + 1) n).hom
          exact (LinearMap.exact_iff.mp (tensor_resolution_exact_succ F B hB n)).symm

theorem tensorAugmentedResolution_acyclic
    (hB : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,max u v} R B) :
    Acyclic (tensorAugmentedResolution F B) :=
  acyclic_extend _ _ (tensorAugmentedNat_acyclic F B hB)

end TensorAugment

open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.AugmentedAssembly
open CategoryTheory.Limits

def augmentedResolution {S : Type u} [Ring S] {A : Type v} [AddCommGroup A] [Module S A]
    (F : LeftResolution S A) :=
  (augmentedResolutionNat F).extend minusOneChainEmbedding

theorem augmentedResolutionNat_acyclic {S : Type u} [Ring S] {A : Type v}
    [AddCommGroup A] [Module S A] (F : LeftResolution S A) :
    Acyclic (augmentedResolutionNat F) := by
  apply (acyclic_iff_exactAt _).mpr
  intro n
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((augmentedResolutionNat F).d ((ComplexShape.down ℕ).prev n) n).hom =
    LinearMap.ker ((augmentedResolutionNat F).d n ((ComplexShape.down ℕ).next n)).hom
  cases n with
  | zero =>
      rw [ChainComplex.prev, ChainComplex.next_nat_zero,
        (augmentedResolutionNat F).shape 0 0 (by decide)]
      change LinearMap.range
          ((ULift.moduleEquiv : ULift.{u} A ≃ₗ[S] A).symm.toLinearMap.comp F.ε) =
        LinearMap.ker (0 : ULift.{u} A →ₗ[S] ULift.{u} A)
      rw [LinearMap.ker_zero, LinearMap.range_eq_top]
      exact (ULift.moduleEquiv : ULift.{u} A ≃ₗ[S] A).symm.surjective.comp F.surjective
  | succ n =>
      rw [ChainComplex.prev, ChainComplex.next_nat_succ]
      cases n with
      | zero =>
          change LinearMap.range (F.complex.d 1 0).hom =
            LinearMap.ker ((ULift.moduleEquiv : ULift.{u} A ≃ₗ[S] A).symm.toLinearMap.comp F.ε)
          rw [LinearMap.ker_comp_of_ker_eq_bot _
            (LinearMap.ker_eq_bot.mpr (ULift.moduleEquiv : ULift.{u} A ≃ₗ[S] A).symm.injective)]
          exact F.exact_zero
      | succ n =>
          change LinearMap.range (F.complex.d (n + 2) (n + 1)).hom =
            LinearMap.ker (F.complex.d (n + 1) n).hom
          exact F.exact_succ n

theorem augmentedResolution_acyclic {S : Type u} [Ring S] {A : Type v}
    [AddCommGroup A] [Module S A] (F : LeftResolution S A) :
    Acyclic (augmentedResolution F) :=
  acyclic_extend _ _ (augmentedResolutionNat_acyclic F)

theorem augmentedResolution_supported {S : Type u} [Ring S] {A : Type v}
    [AddCommGroup A] [Module S A] (F : LeftResolution S A) :
    SupportedIn (augmentedResolution F) (Set.Ici (-1 : ℤ)) := by
  intro i hi
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply (augmentedResolutionNat F).isZero_extend_X minusOneChainEmbedding i
  intro n hn
  change (n : ℤ) - 1 = i at hn
  simp only [Set.mem_Ici, not_le] at hi
  omega

theorem tensorBicomplex_rowsAcyclic
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ)
    (hC : Acyclic C)
    (hD : ∀ q, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (D.X q)) :
    RowsAcyclic (tensorBicomplex C D) := by
  intro q
  apply (acyclic_iff_exactAt _).mpr
  intro p
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range (tensorMap (C.d ((ComplexShape.down ℤ).prev p) p).hom
      (LinearMap.id : D.X q →ₗ[R] D.X q)) =
    LinearMap.ker (tensorMap (C.d p ((ComplexShape.down ℤ).next p)).hom
      (LinearMap.id : D.X q →ₗ[R] D.X q))
  have he := (P103.Ch10.Complexes.acyclic_iff C).mp hC p
  exact (LinearMap.exact_iff.mp
    (flat_tensor_exact (hD q) _ _ (LinearMap.exact_iff.mpr he.symm))).symm


def augmentedRetainedTermIso {S : Type u} [Ring S] {A : Type v} [AddCommGroup A] [Module S A]
    (F : LeftResolution S A) (p : ℤ) (hp : 0 ≤ p) :
    (augmentedResolution F).X p ≅ (extendNonnegativeChain F.complex).X p :=
  (augmentedResolutionNat F).extendXIso minusOneChainEmbedding
      (i := p.toNat + 1) (by dsimp [minusOneChainEmbedding]; omega) ≪≫
    (F.complex.extendXIso nonnegativeChainEmbedding (i := p.toNat)
      (by exact Int.toNat_of_nonneg hp)).symm

theorem augmentedRetainedTermIso_comm {S : Type u} [Ring S] {A : Type v}
    [AddCommGroup A] [Module S A] (F : LeftResolution S A)
    (p p' : ℤ) (hp : 0 ≤ p) (hp' : 0 ≤ p') :
    (augmentedRetainedTermIso F p hp).hom ≫ (extendNonnegativeChain F.complex).d p p' =
      (augmentedResolution F).d p p' ≫ (augmentedRetainedTermIso F p' hp').hom := by
  let ha : minusOneChainEmbedding.f (p.toNat + 1) = p := by
    dsimp [minusOneChainEmbedding]; omega
  let hb : minusOneChainEmbedding.f (p'.toNat + 1) = p' := by
    dsimp [minusOneChainEmbedding]; omega
  rw [show (extendNonnegativeChain F.complex).d p p' =
      (F.complex.extendXIso nonnegativeChainEmbedding (Int.toNat_of_nonneg hp)).hom ≫
        F.complex.d p.toNat p'.toNat ≫
          (F.complex.extendXIso nonnegativeChainEmbedding (Int.toNat_of_nonneg hp')).inv from
    F.complex.extend_d_eq nonnegativeChainEmbedding _ _]
  rw [show (augmentedResolution F).d p p' =
      ((augmentedResolutionNat F).extendXIso minusOneChainEmbedding ha).hom ≫
        (augmentedResolutionNat F).d (p.toNat + 1) (p'.toNat + 1) ≫
          ((augmentedResolutionNat F).extendXIso minusOneChainEmbedding hb).inv from
    (augmentedResolutionNat F).extend_d_eq minusOneChainEmbedding ha hb]
  simp only [augmentedRetainedTermIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [show (augmentedResolutionNat F).d (p.toNat + 1) (p'.toNat + 1) =
      F.complex.d p.toNat p'.toNat from
    ChainComplex.augment_d_succ_succ _ _ _ _ _]

def tensorFirstTermIso {X Y : ModuleCat.{v} Rᵐᵒᵖ} (e : X ≅ Y)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) :
    leftTensorComplex X D ≅ leftTensorComplex Y D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (tensorLinearEquiv e.toLinearEquiv (LinearEquiv.refl R (D.X q))).toModuleIso)
    (by
      intro q q' _
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro x y
      rfl)

theorem complex_isZero_of_subsingleton {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} S) c) (h : ∀ i, Subsingleton (C.X i)) : IsZero C := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

theorem tensorFirstComplex_isZero {X : ModuleCat.{v} Rᵐᵒᵖ} (hX : IsZero X)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) : IsZero (leftTensorComplex X D) := by
  apply complex_isZero_of_subsingleton
  intro q
  letI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp hX
  exact ⟨fun x y => (eq_zero_of_subsingleton_left x).trans (eq_zero_of_subsingleton_left y).symm⟩

def tensorAugmentedRetainedColumnIso {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : LeftResolution Rᵐᵒᵖ A) (D : ChainComplex (ModuleCat.{w} R) ℤ) (p : ℤ) :
    (unaugmented (tensorBicomplex (augmentedResolution F) D)).X p ≅
      (tensorBicomplex (extendNonnegativeChain F.complex) D).X p := by
  by_cases hp : 0 ≤ p
  · exact retainedColumnIso _ p hp ≪≫ tensorFirstTermIso (augmentedRetainedTermIso F p hp) D
  · apply IsZero.iso
    · apply complex_isZero_of_subsingleton
      intro q
      exact P103.Ch10.AugmentedAssembly.unaugmented_negative _ p q (by omega)
    · apply tensorFirstComplex_isZero
      apply F.complex.isZero_extend_X nonnegativeChainEmbedding p
      intro i hi
      change (i : ℤ) = p at hi
      omega

def tensorAugmentedRetainedIso {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : LeftResolution Rᵐᵒᵖ A) (D : ChainComplex (ModuleCat.{w} R) ℤ) :
    unaugmented (tensorBicomplex (augmentedResolution F) D) ≅
      tensorBicomplex (extendNonnegativeChain F.complex) D :=
  HomologicalComplex.Hom.isoOfComponents (tensorAugmentedRetainedColumnIso F D) (by
    intro p p' _
    by_cases hp : 0 ≤ p
    · by_cases hp' : 0 ≤ p'
      · simp only [tensorAugmentedRetainedColumnIso, dif_pos hp, dif_pos hp', Iso.trans_hom]
        rw [P103.Ch10.AugmentedAssembly.retained_d _ p p' hp hp']
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        congr 1
        apply HomologicalComplex.Hom.ext
        funext q
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro x y
        change tmul R
            (((extendNonnegativeChain F.complex).d p p').hom
              ((augmentedRetainedTermIso F p hp).hom.hom x)) y =
          tmul R ((augmentedRetainedTermIso F p' hp').hom.hom
            (((augmentedResolution F).d p p').hom x)) y
        exact congrArg (fun z => tmul R z y)
          (congrArg (fun f => f.hom x) (augmentedRetainedTermIso_comm F p p' hp hp'))

      · apply (tensorFirstComplex_isZero (D := D) ?_).eq_of_tgt
        apply F.complex.isZero_extend_X nonnegativeChainEmbedding p'
        intro i hi
        change (i : ℤ) = p' at hi
        omega
    · apply (complex_isZero_of_subsingleton _ (fun q =>
        P103.Ch10.AugmentedAssembly.unaugmented_negative _ p q (by omega))).eq_of_src)

theorem flat_of_linearEquiv {X : Type v} {Y : Type w} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y)
    (hY : P103.Specs.Ch02.FlatnessTests.Flat.{u,w,t} R Y) :
    P103.Specs.Ch02.FlatnessTests.Flat.{u,v,t} R X := by
  apply (P103.Ch02.FlatnessTests.flat_iff_finiteRelations R X).mpr
  intro n k x r hx
  have hy : ∀ j, ∑ i, r j i • e (x i) = 0 := by
    intro j
    simpa only [map_sum, map_smul, map_zero] using congrArg e (hx j)
  obtain ⟨l, y, s, hs, hr⟩ :=
    (P103.Ch02.FlatnessTests.flat_iff_finiteRelations R Y).mp hY n k (fun i => e (x i)) r hy
  refine ⟨l, fun a => e.symm (y a), s, ?_, hr⟩
  intro i
  apply e.injective
  simpa only [map_sum, map_smul, e.apply_symm_apply] using hs i

theorem flat_of_subsingleton (X : Type v) [AddCommGroup X] [Module R X] [Subsingleton X] :
    P103.Specs.Ch02.FlatnessTests.Flat.{u,v,t} R X := by
  intro A B _ _ _ _ f hf F hF x y h
  exact (eq_zero_of_subsingleton_right x).trans (eq_zero_of_subsingleton_right y).symm

theorem extendedResolution_leftFlat {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) (hG : IsLeftFlat.{u,v,w} G) (q : ℤ) :
    P103.Specs.Ch02.FlatnessTests.Flat.{u,max u w,max u v} R
      ((extendNonnegativeChain G.complex).X q) := by
  by_cases hq : 0 ≤ q
  · exact flat_of_linearEquiv
      (G.complex.extendXIso nonnegativeChainEmbedding (i := q.toNat)
        (Int.toNat_of_nonneg hq)).toLinearEquiv (hG q.toNat)
  · letI : Subsingleton ((extendNonnegativeChain G.complex).X q) :=
      P103.Ch10.Complexes.extendNonnegativeChain_supported G.complex q (by simpa using hq)
    exact flat_of_subsingleton _

def augmentedMinusOneEquiv {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : LeftResolution Rᵐᵒᵖ A) : (augmentedResolution F).X (-1) ≃ₗ[Rᵐᵒᵖ] A :=
  ((augmentedResolutionNat F).extendXIso minusOneChainEmbedding (i := 0) (by rfl)).toLinearEquiv.trans
    (ULift.moduleEquiv : ULift.{u} A ≃ₗ[Rᵐᵒᵖ] A)

def augmentedTensorColumnIso {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B) :
    (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)).X (-1) ≅
      leftTensorComplex A (extendNonnegativeChain G.complex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (tensorLinearEquiv (augmentedMinusOneEquiv F)
      (LinearEquiv.refl R ((extendNonnegativeChain G.complex).X q))).toModuleIso)
    (by
      intro q q' _
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro x y
      rfl)

theorem tensorBicomplex_supported
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (hC : SupportedIn C (Set.Ici a)) (hD : SupportedIn D (Set.Ici b)) :
    SupportedQuadrant (tensorBicomplex C D) a b := by
  intro p q hpq
  rcases hpq with hp | hq
  · letI : Subsingleton (C.X p) := hC p (by simpa using hp)
    exact ⟨fun x y => (eq_zero_of_subsingleton_left x).trans (eq_zero_of_subsingleton_left y).symm⟩
  · letI : Subsingleton (D.X q) := hD q (by simpa using hq)
    exact ⟨fun x y => (eq_zero_of_subsingleton_right x).trans (eq_zero_of_subsingleton_right y).symm⟩

theorem horizontalTensorAssembly {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B) (hG : IsLeftFlat.{u,v,w} G) :
    ∃ (f : ordinaryTensorTotal F.complex G.complex ⟶
        leftTensorComplex A (extendNonnegativeChain G.complex)),
      QuasiIsomorphism f ∧
      ∃ (k : total (unaugmented (tensorBicomplex (augmentedResolution F)
          (extendNonnegativeChain G.complex))) ⟶
            (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)).X (-1)),
        (∀ n, k.f n = chainAugmentationComponent
          (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)) n) ∧
        f = (HomologicalComplex₂.total.mapIso (tensorAugmentedRetainedIso F
          (extendNonnegativeChain G.complex)) (ComplexShape.down ℤ)).inv ≫ k ≫
          (augmentedTensorColumnIso F G).hom := by
  let K := tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)
  have hs : SupportedQuadrant K (-1) 0 :=
    tensorBicomplex_supported _ _ (-1) 0 (augmentedResolution_supported F)
      (P103.Ch10.Complexes.extendNonnegativeChain_supported G.complex)
  have hr : RowsAcyclic K := tensorBicomplex_rowsAcyclic _ _
    (augmentedResolution_acyclic F) (extendedResolution_leftFlat G hG)
  obtain ⟨k, hk⟩ := P103.Ch10.AugmentedAssembly.chain_rows_quasiIsomorphism K 0 hs hr
  let e := HomologicalComplex₂.total.mapIso (tensorAugmentedRetainedIso F
    (extendNonnegativeChain G.complex)) (ComplexShape.down ℤ)
  refine ⟨e.inv ≫ k ≫ (augmentedTensorColumnIso F G).hom, ?_, k, hk.1, rfl⟩
  apply P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp
  · exact P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso e.symm
  · apply P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp hk.2.1
    exact P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso (augmentedTensorColumnIso F G)

def transportedHorizontalAugmentation {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (augmentedResolution F)
      (extendNonnegativeChain G.complex))) ⟶
        (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)).X (-1)) :
    ordinaryTensorTotal F.complex G.complex ⟶
      leftTensorComplex A (extendNonnegativeChain G.complex) :=
  (HomologicalComplex₂.total.mapIso (tensorAugmentedRetainedIso F
    (extendNonnegativeChain G.complex)) (ComplexShape.down ℤ)).inv ≫ k ≫
      (augmentedTensorColumnIso F G).hom

theorem transportedHorizontalAugmentation_positive {A : Type v} [AddCommGroup A]
    [Module Rᵐᵒᵖ A] {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (augmentedResolution F)
      (extendNonnegativeChain G.complex))) ⟶
        (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)).X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)) n)
    (p q n : ℤ) (h : p + q = n) (hp : p ≠ 0) :
    totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)) p q n h ≫
        (transportedHorizontalAugmentation F G k).f n = 0 := by
  simp only [transportedHorizontalAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_inv, Category.assoc, hk,
    chainAugmentationComponent]
  have hi :
      totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
        (extendNonnegativeChain G.complex)) p q n h ≫
          (HomologicalComplex₂.total.map
            (tensorAugmentedRetainedIso F (extendNonnegativeChain G.complex)).inv
            (ComplexShape.down ℤ)).f n =
        ((tensorAugmentedRetainedIso F (extendNonnegativeChain G.complex)).inv.f p).f q ≫
          totalInclusion (unaugmented (tensorBicomplex (augmentedResolution F)
            (extendNonnegativeChain G.complex))) p q n h :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ p q n h
  rw [← Category.assoc _ ((HomologicalComplex₂.total.map
    (tensorAugmentedRetainedIso F (extendNonnegativeChain G.complex)).inv
    (ComplexShape.down ℤ)).f n), hi]
  simp only [Category.assoc]
  rw [← Category.assoc (totalInclusion _ p q n h) (totalProjection _ 0 n n _)]
  rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne _ p q 0 n n h (by omega)
    (Or.inl hp)]
  simp

theorem augmentedRetained_augmentation {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : LeftResolution Rᵐᵒᵖ A) (x : (extendNonnegativeChain F.complex).X 0) :
    augmentedMinusOneEquiv F (((augmentedResolution F).d 0 (-1)).hom
      ((augmentedRetainedTermIso F 0 (by omega)).inv.hom x)) =
      F.ε ((F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom x) := by
  have hd := (augmentedResolutionNat F).extend_d_eq minusOneChainEmbedding
    (i := 1) (j := 0) (i' := 0) (j' := -1) (by rfl) (by rfl)
  change augmentedMinusOneEquiv F ((((augmentedResolutionNat F).extend minusOneChainEmbedding).d 0 (-1)).hom
    ((augmentedRetainedTermIso F 0 (by omega)).inv.hom x)) = _
  rw [hd]
  let e0 := (augmentedResolutionNat F).extendXIso minusOneChainEmbedding
    (i := 1) (i' := 0) (by rfl)
  let eM := (augmentedResolutionNat F).extendXIso minusOneChainEmbedding
    (i := 0) (i' := -1) (by rfl)
  have he0 (z : (augmentedResolutionNat F).X 1) : e0.hom.hom (e0.inv.hom z) = z :=
    congrArg (fun f => f.hom z) e0.inv_hom_id
  have heM (z : (augmentedResolutionNat F).X 0) : eM.hom.hom (eM.inv.hom z) = z :=
    congrArg (fun f => f.hom z) eM.inv_hom_id
  change ULift.down (eM.hom.hom (eM.inv.hom
    (((augmentedResolutionNat F).d 1 0).hom
      (e0.hom.hom (e0.inv.hom
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom x)))))) = _
  rw [he0, heM]
  rfl

theorem transportedHorizontalAugmentation_zero_component {A : Type v} [AddCommGroup A]
    [Module Rᵐᵒᵖ A] {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (augmentedResolution F)
      (extendNonnegativeChain G.complex))) ⟶
        (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)).X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)) n)
    (n : ℤ) :
    totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)) 0 n n (by omega) ≫
        (transportedHorizontalAugmentation F G k).f n =
      ModuleCat.ofHom (tensorMap
        (F.ε.comp (F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom)
        (LinearMap.id : (extendNonnegativeChain G.complex).X n →ₗ[R] _)) := by
  let K := tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)
  have hi :
      totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
        (extendNonnegativeChain G.complex)) 0 n n (by omega) ≫
          (HomologicalComplex₂.total.map
            (tensorAugmentedRetainedIso F (extendNonnegativeChain G.complex)).inv
            (ComplexShape.down ℤ)).f n =
        ((tensorAugmentedRetainedIso F (extendNonnegativeChain G.complex)).inv.f 0).f n ≫
          totalInclusion (unaugmented K) 0 n n (by omega) :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ 0 n n (by change (0 : ℤ) + n = n; omega)
  simp only [transportedHorizontalAugmentation, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_inv, Category.assoc, hk, chainAugmentationComponent]
  rw [← Category.assoc _ ((HomologicalComplex₂.total.map
    (tensorAugmentedRetainedIso F (extendNonnegativeChain G.complex)).inv
    (ComplexShape.down ℤ)).f n), hi]
  simp only [Category.assoc]
  rw [← Category.assoc (totalInclusion _ 0 n n _) (totalProjection _ 0 n n _),
    P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self]
  simp only [Category.id_comp]
  change (tensorAugmentedRetainedColumnIso F (extendNonnegativeChain G.complex) 0).inv.f n ≫
    (columnToAugmented K 0).f n ≫ (K.d 0 (-1)).f n ≫ (augmentedTensorColumnIso F G).hom.f n = _
  simp only [tensorAugmentedRetainedColumnIso, dite_eq_left (show (0 : ℤ) ≤ 0 by omega),
    Iso.trans_inv, HomologicalComplex.comp_f, columnToAugmented,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hc : (retainedColumnIso K 0 (by omega)).inv.f n ≫
      (retainedColumnIso K 0 (by omega)).hom.f n = 𝟙 _ :=
    congrArg (fun f => f.f n) (retainedColumnIso K 0 (by omega)).inv_hom_id
  rw [← Category.assoc ((retainedColumnIso K 0 (by omega)).inv.f n)
    ((retainedColumnIso K 0 (by omega)).hom.f n), hc, Category.id_comp]
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro x y
  change tmul R (augmentedMinusOneEquiv F (((augmentedResolution F).d 0 (-1)).hom
    ((augmentedRetainedTermIso F 0 (by omega)).inv.hom x))) y = _
  rw [augmentedRetained_augmentation]
  rfl

end AugmentedTensorAssembly

section VerticalTensorAssembly
open CategoryTheory.Limits
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.AugmentedAssembly
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev rightTensorComplexInt
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (B : Type w) [AddCommGroup B] [Module R B] :=
  ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℤ)).obj C

theorem tensorBicomplex_columnsAcyclic
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{w} R) ℤ)
    (hD : Acyclic D)
    (hC : ∀ p, P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,w} R (C.X p)) :
    ColumnsAcyclic (tensorBicomplex C D) := by
  intro p
  apply (acyclic_iff_exactAt _).mpr
  intro q
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range (tensorMap (LinearMap.id : C.X p →ₗ[Rᵐᵒᵖ] C.X p)
      (D.d ((ComplexShape.down ℤ).prev q) q).hom) =
    LinearMap.ker (tensorMap (LinearMap.id : C.X p →ₗ[Rᵐᵒᵖ] C.X p)
      (D.d q ((ComplexShape.down ℤ).next q)).hom)
  have he := (P103.Ch10.Complexes.acyclic_iff D).mp hD q
  exact (LinearMap.exact_iff.mp
    (rightFlat_tensor_exact (hC p) _ _ (LinearMap.exact_iff.mpr he.symm))).symm

def tensorSecondTermIso (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {X Y : ModuleCat.{w} R} (e : X ≅ Y) :
    rightTensorComplexInt C X ≅ rightTensorComplexInt C Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (tensorLinearEquiv (LinearEquiv.refl Rᵐᵒᵖ (C.X p)) e.toLinearEquiv).toModuleIso)
    (by
      intro p p' _
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro x y
      rfl)

theorem tensorSecondComplex_isZero
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) {X : ModuleCat.{w} R} (hX : IsZero X) :
    IsZero (rightTensorComplexInt C X) := by
  apply complex_isZero_of_subsingleton
  intro p
  letI : Subsingleton X := ModuleCat.isZero_iff_subsingleton.mp hX
  exact ⟨fun x y => (eq_zero_of_subsingleton_right x).trans (eq_zero_of_subsingleton_right y).symm⟩

def tensorAugmentedRetainedFlipColumnIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) (q : ℤ) :
    (unaugmented (tensorBicomplex C (augmentedResolution G)).flip).X q ≅
      (tensorBicomplex C (extendNonnegativeChain G.complex)).flip.X q := by
  by_cases hq : 0 ≤ q
  · exact retainedColumnIso _ q hq ≪≫ tensorSecondTermIso C (augmentedRetainedTermIso G q hq)
  · apply IsZero.iso
    · apply complex_isZero_of_subsingleton
      intro p
      exact P103.Ch10.AugmentedAssembly.unaugmented_negative _ q p (by omega)
    · apply tensorSecondComplex_isZero C
      apply G.complex.isZero_extend_X nonnegativeChainEmbedding q
      intro i hi
      change (i : ℤ) = q at hi
      omega

def tensorAugmentedRetainedFlipIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {B : Type w} [AddCommGroup B] [Module R B] (G : LeftResolution R B) :
    unaugmented (tensorBicomplex C (augmentedResolution G)).flip ≅
      (tensorBicomplex C (extendNonnegativeChain G.complex)).flip :=
  HomologicalComplex.Hom.isoOfComponents (tensorAugmentedRetainedFlipColumnIso C G) (by
    intro q q' _
    by_cases hq : 0 ≤ q
    · by_cases hq' : 0 ≤ q'
      · simp only [tensorAugmentedRetainedFlipColumnIso, dif_pos hq, dif_pos hq', Iso.trans_hom]
        rw [P103.Ch10.AugmentedAssembly.retained_d _ q q' hq hq']
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        congr 1
        apply HomologicalComplex.Hom.ext
        funext p
        apply ModuleCat.hom_ext
        apply tensor_hom_ext
        intro x y
        change tmul R x
            (((extendNonnegativeChain G.complex).d q q').hom
              ((augmentedRetainedTermIso G q hq).hom.hom y)) =
          tmul R x ((augmentedRetainedTermIso G q' hq').hom.hom
            (((augmentedResolution G).d q q').hom y))
        exact congrArg (fun z => tmul R x z)
          (congrArg (fun f => f.hom y) (augmentedRetainedTermIso_comm G q q' hq hq'))
      · apply (tensorSecondComplex_isZero (C := C) ?_).eq_of_tgt
        apply G.complex.isZero_extend_X nonnegativeChainEmbedding q'
        intro i hi
        change (i : ℤ) = q' at hi
        omega
    · apply (complex_isZero_of_subsingleton _ (fun p =>
        P103.Ch10.AugmentedAssembly.unaugmented_negative _ q p (by omega))).eq_of_src)

theorem rightFlat_of_linearEquiv
    {X : Type v} {Y : Type w} [AddCommGroup X] [Module Rᵐᵒᵖ X]
    [AddCommGroup Y] [Module Rᵐᵒᵖ Y] (e : X ≃ₗ[Rᵐᵒᵖ] Y)
    (hY : P103.Specs.Ch02.FlatnessTests.RightFlat.{u,w,t} R Y) :
    P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,t} R X :=
  (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R X).mpr
    (flat_of_linearEquiv e ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R Y).mp hY))

theorem rightFlat_of_subsingleton
    (X : Type v) [AddCommGroup X] [Module Rᵐᵒᵖ X] [Subsingleton X] :
    P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,t} R X := by
  intro A B _ _ _ _ f hf F hF x y h
  exact (eq_zero_of_subsingleton_left x).trans (eq_zero_of_subsingleton_left y).symm

theorem extendedResolution_rightFlat
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (F : LeftResolution Rᵐᵒᵖ A) (hF : IsRightFlat.{u,v,w} F) (p : ℤ) :
    P103.Specs.Ch02.FlatnessTests.RightFlat.{u,max u v,max u w} R
      ((extendNonnegativeChain F.complex).X p) := by
  by_cases hp : 0 ≤ p
  · exact rightFlat_of_linearEquiv
      (F.complex.extendXIso nonnegativeChainEmbedding (i := p.toNat)
        (Int.toNat_of_nonneg hp)).toLinearEquiv (hF p.toNat)
  · letI : Subsingleton ((extendNonnegativeChain F.complex).X p) :=
      P103.Ch10.Complexes.extendNonnegativeChain_supported F.complex p (by simpa using hp)
    exact rightFlat_of_subsingleton _

def augmentedMinusOneLeftEquiv
    {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) : (augmentedResolution G).X (-1) ≃ₗ[R] B :=
  ((augmentedResolutionNat G).extendXIso minusOneChainEmbedding (i := 0) (by rfl)).toLinearEquiv.trans
    (ULift.moduleEquiv : ULift.{u} B ≃ₗ[R] B)

def augmentedTensorRowIso
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B) :
    (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1) ≅
      rightTensorComplexInt (extendNonnegativeChain F.complex) B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (tensorLinearEquiv
      (LinearEquiv.refl Rᵐᵒᵖ ((extendNonnegativeChain F.complex).X p))
      (augmentedMinusOneLeftEquiv G)).toModuleIso)
    (by
      intro p p' _
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro x y
      rfl)

def transportedVerticalAugmentation
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1)) :
    ordinaryTensorTotal F.complex G.complex ⟶
      rightTensorComplexInt (extendNonnegativeChain F.complex) B :=
  (signedInterchange (tensorBicomplex (extendNonnegativeChain F.complex)
    (extendNonnegativeChain G.complex))).inv ≫
  (HomologicalComplex₂.total.mapIso (tensorAugmentedRetainedFlipIso
    (extendNonnegativeChain F.complex) G) (ComplexShape.down ℤ)).inv ≫ k ≫
    (augmentedTensorRowIso F G).hom

theorem verticalTensorAssembly
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B) (hF : IsRightFlat.{u,v,w} F) :
    ∃ (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
        (augmentedResolution G)).flip) ⟶
          (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1)),
      (∀ n, k.f n = chainAugmentationComponent
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip n) ∧
      QuasiIsomorphism (transportedVerticalAugmentation F G k) := by
  let K := tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)
  have hs : SupportedQuadrant K 0 (-1) :=
    tensorBicomplex_supported _ _ 0 (-1)
      (P103.Ch10.Complexes.extendNonnegativeChain_supported F.complex)
      (augmentedResolution_supported G)
  have hc : ColumnsAcyclic K := tensorBicomplex_columnsAcyclic _ _
    (augmentedResolution_acyclic G) (extendedResolution_rightFlat F hF)
  obtain ⟨k, hk⟩ := P103.Ch10.AugmentedAssembly.chain_columns_quasiIsomorphism K 0 hs hc
  refine ⟨k, hk.1.1, ?_⟩
  apply P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp
  · exact P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso
      (signedInterchange (tensorBicomplex (extendNonnegativeChain F.complex)
        (extendNonnegativeChain G.complex))).symm
  · apply P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp
    · exact P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso
        (HomologicalComplex₂.total.mapIso (tensorAugmentedRetainedFlipIso
          (extendNonnegativeChain F.complex) G) (ComplexShape.down ℤ)).symm
    · apply P103.Ch10.AugmentedAssembly.quasiIsomorphism_comp hk.1.2.1
      exact P103.Ch10.AugmentedAssembly.quasiIsomorphism_of_iso (augmentedTensorRowIso F G)

def verticalAugmentationFromFlip
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1)) :
    total (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)).flip ⟶
      rightTensorComplexInt (extendNonnegativeChain F.complex) B :=
  (HomologicalComplex₂.total.mapIso (tensorAugmentedRetainedFlipIso
    (extendNonnegativeChain F.complex) G) (ComplexShape.down ℤ)).inv ≫ k ≫
    (augmentedTensorRowIso F G).hom

theorem verticalAugmentationFromFlip_positive
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip n)
    (p q n : ℤ) (h : q + p = n) (hq : q ≠ 0) :
    totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)).flip q p n h ≫
        (verticalAugmentationFromFlip F G k).f n = 0 := by
  simp only [verticalAugmentationFromFlip, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_inv, Category.assoc, hk,
    chainAugmentationComponent]
  have hi :
      totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
        (extendNonnegativeChain G.complex)).flip q p n h ≫
          (HomologicalComplex₂.total.map
            (tensorAugmentedRetainedFlipIso (extendNonnegativeChain F.complex) G).inv
            (ComplexShape.down ℤ)).f n =
        ((tensorAugmentedRetainedFlipIso (extendNonnegativeChain F.complex) G).inv.f q).f p ≫
          totalInclusion (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
            (augmentedResolution G)).flip) q p n h :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ q p n h
  rw [← Category.assoc _ ((HomologicalComplex₂.total.map
    (tensorAugmentedRetainedFlipIso (extendNonnegativeChain F.complex) G).inv
    (ComplexShape.down ℤ)).f n), hi]
  simp only [Category.assoc]
  rw [← Category.assoc (totalInclusion _ q p n h) (totalProjection _ 0 n n _)]
  rw [P103.Ch10.TotalComplexAssembly.totalInclusion_projection_ne _ q p 0 n n h (by omega)
    (Or.inl hq)]
  simp

theorem transportedVerticalAugmentation_positive
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip n)
    (p q n : ℤ) (h : p + q = n) (hq : q ≠ 0) :
    totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)) p q n h ≫
        (transportedVerticalAugmentation F G k).f n = 0 := by
  let L := tensorBicomplex (extendNonnegativeChain F.complex)
    (extendNonnegativeChain G.complex)
  have hi : totalInclusion L p q n h ≫ (signedInterchange L).inv.f n =
      (p*q).negOnePow • totalInclusion L.flip q p n (by omega) :=
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv L _ p q n h
  change totalInclusion L p q n h ≫
    ((signedInterchange L).inv.f n ≫ (verticalAugmentationFromFlip F G k).f n) = 0
  rw [← Category.assoc, hi, Linear.units_smul_comp,
    verticalAugmentationFromFlip_positive F G k hk p q n (by omega) hq, smul_zero]

theorem augmentedRetained_leftAugmentation
    {B : Type w} [AddCommGroup B] [Module R B]
    (G : LeftResolution R B) (x : (extendNonnegativeChain G.complex).X 0) :
    augmentedMinusOneLeftEquiv G (((augmentedResolution G).d 0 (-1)).hom
      ((augmentedRetainedTermIso G 0 (by omega)).inv.hom x)) =
      G.ε ((G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom x) := by
  have hd := (augmentedResolutionNat G).extend_d_eq minusOneChainEmbedding
    (i := 1) (j := 0) (i' := 0) (j' := -1) (by rfl) (by rfl)
  change augmentedMinusOneLeftEquiv G ((((augmentedResolutionNat G).extend minusOneChainEmbedding).d 0 (-1)).hom
    ((augmentedRetainedTermIso G 0 (by omega)).inv.hom x)) = _
  rw [hd]
  let e0 := (augmentedResolutionNat G).extendXIso minusOneChainEmbedding
    (i := 1) (i' := 0) (by rfl)
  let eM := (augmentedResolutionNat G).extendXIso minusOneChainEmbedding
    (i := 0) (i' := -1) (by rfl)
  have he0 (z : (augmentedResolutionNat G).X 1) : e0.hom.hom (e0.inv.hom z) = z :=
    congrArg (fun f => f.hom z) e0.inv_hom_id
  have heM (z : (augmentedResolutionNat G).X 0) : eM.hom.hom (eM.inv.hom z) = z :=
    congrArg (fun f => f.hom z) eM.inv_hom_id
  change ULift.down (eM.hom.hom (eM.inv.hom
    (((augmentedResolutionNat G).d 1 0).hom
      (e0.hom.hom (e0.inv.hom
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom x)))))) = _
  rw [he0, heM]
  rfl

theorem verticalAugmentationFromFlip_zero_component
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip n)
    (n : ℤ) :
    totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)).flip 0 n n (by omega) ≫
        (verticalAugmentationFromFlip F G k).f n =
      ModuleCat.ofHom (tensorMap
        (LinearMap.id : (extendNonnegativeChain F.complex).X n →ₗ[Rᵐᵒᵖ] _)
        (G.ε.comp (G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom)) := by
  let K := (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip
  have hi :
      totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
        (extendNonnegativeChain G.complex)).flip 0 n n (by omega) ≫
          (HomologicalComplex₂.total.map
            (tensorAugmentedRetainedFlipIso (extendNonnegativeChain F.complex) G).inv
            (ComplexShape.down ℤ)).f n =
        ((tensorAugmentedRetainedFlipIso (extendNonnegativeChain F.complex) G).inv.f 0).f n ≫
          totalInclusion (unaugmented K) 0 n n (by omega) :=
    HomologicalComplex₂.ιTotal_map _ _ _ _ 0 n n (by change (0 : ℤ) + n = n; omega)
  simp only [verticalAugmentationFromFlip, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_inv, Category.assoc, hk, chainAugmentationComponent]
  rw [← Category.assoc _ ((HomologicalComplex₂.total.map
    (tensorAugmentedRetainedFlipIso (extendNonnegativeChain F.complex) G).inv
    (ComplexShape.down ℤ)).f n), hi]
  simp only [Category.assoc]
  rw [← Category.assoc (totalInclusion _ 0 n n _) (totalProjection _ 0 n n _),
    P103.Ch10.TotalComplexAssembly.totalInclusion_projection_self]
  simp only [Category.id_comp]
  change (tensorAugmentedRetainedFlipColumnIso (extendNonnegativeChain F.complex) G 0).inv.f n ≫
    (columnToAugmented K 0).f n ≫ (K.d 0 (-1)).f n ≫ (augmentedTensorRowIso F G).hom.f n = _
  simp only [tensorAugmentedRetainedFlipColumnIso, dite_eq_left (show (0 : ℤ) ≤ 0 by omega),
    Iso.trans_inv, HomologicalComplex.comp_f, columnToAugmented,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hc : (retainedColumnIso K 0 (by omega)).inv.f n ≫
      (retainedColumnIso K 0 (by omega)).hom.f n = 𝟙 _ :=
    congrArg (fun f => f.f n) (retainedColumnIso K 0 (by omega)).inv_hom_id
  rw [← Category.assoc ((retainedColumnIso K 0 (by omega)).inv.f n)
    ((retainedColumnIso K 0 (by omega)).hom.f n), hc, Category.id_comp]
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro x y
  change tmul R x (augmentedMinusOneLeftEquiv G (((augmentedResolution G).d 0 (-1)).hom
    ((augmentedRetainedTermIso G 0 (by omega)).inv.hom y))) = _
  rw [augmentedRetained_leftAugmentation]
  rfl

theorem transportedVerticalAugmentation_zero_component
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip n)
    (n : ℤ) :
    totalInclusion (tensorBicomplex (extendNonnegativeChain F.complex)
      (extendNonnegativeChain G.complex)) n 0 n (by omega) ≫
        (transportedVerticalAugmentation F G k).f n =
      ModuleCat.ofHom (tensorMap
        (LinearMap.id : (extendNonnegativeChain F.complex).X n →ₗ[Rᵐᵒᵖ] _)
        (G.ε.comp (G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom)) := by
  let L := tensorBicomplex (extendNonnegativeChain F.complex)
    (extendNonnegativeChain G.complex)
  have hs : totalInclusion L n 0 n (by omega) ≫ (signedInterchange L).inv.f n =
      (n*0).negOnePow • totalInclusion L.flip 0 n n (by omega) :=
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv L (ComplexShape.down ℤ) n 0 n (by
      change n + 0 = n; omega)
  have hi : totalInclusion L n 0 n (by omega) ≫ (signedInterchange L).inv.f n =
      totalInclusion L.flip 0 n n (by omega) := by
    simpa only [mul_zero, Int.negOnePow_zero, one_smul] using hs
  change totalInclusion L n 0 n (by omega) ≫
    ((signedInterchange L).inv.f n ≫ (verticalAugmentationFromFlip F G k).f n) = _
  rw [← Category.assoc, hi, verticalAugmentationFromFlip_zero_component F G k hk n]

end VerticalTensorAssembly

section TensorRestriction
set_option backward.isDefEq.respectTransparency false

def nonnegativeExtensionRestrictionIso
    {S : Type*} [Ring S] (C : ChainComplex (ModuleCat.{v} S) ℕ) :
    (extendNonnegativeChain C).restriction nonnegativeChainEmbedding ≅ C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => C.extendXIso nonnegativeChainEmbedding (i := n) rfl) (by
      intro i j hij
      change (C.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom ≫ C.d i j =
        (extendNonnegativeChain C).d (i : ℤ) (j : ℤ) ≫
          (C.extendXIso nonnegativeChainEmbedding (i := j) rfl).hom
      erw [C.extend_d_eq nonnegativeChainEmbedding (i := i) (j := j) rfl rfl]
      simp)

def leftTensorExtensionRestrictionIso (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    (leftTensorComplex A (extendNonnegativeChain D)).restriction nonnegativeChainEmbedding ≅
      leftOrdinaryTensorComplex A D :=
  ((leftTensorFunctor A).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
    (nonnegativeExtensionRestrictionIso D)

theorem leftTensorExtensionRestrictionIso_apply
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ)
    (a : A) (b : D.X q) :
    ((leftTensorExtensionRestrictionIso A D).hom.f q).hom
      (tmul R a ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)) =
      tmul R a b := by
  change tmul R a ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).hom.hom
    ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)) = _
  exact congrArg (tmul R a)
    ((D.extendXIso nonnegativeChainEmbedding (i := q) rfl).toLinearEquiv.apply_symm_apply b)


def rightTensorExtensionRestrictionIso
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :
    (rightTensorComplexInt (extendNonnegativeChain C) B).restriction nonnegativeChainEmbedding ≅
      tensorComplex C B :=
  ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
    (nonnegativeExtensionRestrictionIso C)

theorem rightTensorExtensionRestrictionIso_apply
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] (p : ℕ)
    (a : C.X p) (b : B) :
    ((rightTensorExtensionRestrictionIso C B).hom.f p).hom
      (tmul R ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a) b) =
      tmul R a b := by
  change tmul R ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom.hom
    ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)) b = _
  exact congrArg (fun a => tmul R a b)
    ((C.extendXIso nonnegativeChainEmbedding (i := p) rfl).toLinearEquiv.apply_symm_apply a)

end TensorRestriction

section OrdinaryAugmentationIsomorphisms
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.AugmentedAssembly
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem transportedVerticalAugmentation_restriction
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (extendNonnegativeChain F.complex)
      (augmentedResolution G)).flip) ⟶
        (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip.X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (extendNonnegativeChain F.complex) (augmentedResolution G)).flip n)
    (α : Augmentations F G) :
    HomologicalComplex.restrictionMap (transportedVerticalAugmentation F G k)
      nonnegativeChainEmbedding ≫ (rightTensorExtensionRestrictionIso F.complex B).hom = α.left := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply ordinaryTotal_linearMap_ext
  intro p q h a b
  by_cases hq : q=0
  · subst q
    have hn : n=p := by omega
    cases hn
    have hz := congrArg (fun f => f.hom (tmul R
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a)
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b)))
      (transportedVerticalAugmentation_zero_component F G k hk n)
    have he : (G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b) = b :=
      (G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).toLinearEquiv.apply_symm_apply b
    change ((transportedVerticalAugmentation F G k).f n).hom
        (ordinaryInclusion F.complex G.complex n 0 n (by omega) (tmul R a b)) =
      tmul R ((F.complex.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom a)
        (G.ε ((G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
          ((G.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom b))) at hz
    erw [he] at hz
    change ((rightTensorExtensionRestrictionIso F.complex B).hom.f n).hom
      (((transportedVerticalAugmentation F G k).f n).hom
        (ordinaryInclusion F.complex G.complex n 0 n (by omega) (tmul R a b))) = _
    rw [hz, rightTensorExtensionRestrictionIso_apply, α.left_zero]
  · have hq' : (q:ℤ) ≠ 0 := by exact_mod_cast hq
    have hz := congrArg (fun f => f.hom (tmul R
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))
      (transportedVerticalAugmentation_positive F G k hk p q n (by exact_mod_cast h) hq')
    change ((transportedVerticalAugmentation F G k).f n).hom
      (ordinaryInclusion F.complex G.complex p q n h (tmul R a b)) = 0 at hz
    have ha := congrArg (fun f => f (tmul R a b)) (α.left_positive p q n h hq)
    change ((rightTensorExtensionRestrictionIso F.complex B).hom.f n).hom
      (((transportedVerticalAugmentation F G k).f n).hom
        (ordinaryInclusion F.complex G.complex p q n h (tmul R a b))) = _
    rw [hz, map_zero]
    exact ha.symm

universe siso tiso

theorem restriction_homology_bijective_succ_of_iso
    {S : Type siso} [Ring S]
    {C D : ChainComplex (ModuleCat.{tiso} S) ℤ}
    {E : ChainComplex (ModuleCat.{tiso} S) ℕ}
    (f : C ⟶ D) (hf : QuasiIsomorphism f)
    (e : D.restriction nonnegativeChainEmbedding ≅ E) (n : ℕ) :
    Function.Bijective (homologyMap
      (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding ≫ e.hom) (n+1)) := by
  have hc := P103.Ch10.Complexes.homologyMap_comp
    (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) e.hom (n+1)
  dsimp only [P103.Ch10.Complexes.homologyMap] at hc
  rw [hc]
  have hiso : Function.Bijective (homologyMap e.hom (n+1)) :=
    ((quotientHomology (ComplexShape.down ℕ) (n+1)).mapIso e).toLinearEquiv.bijective
  have hres : Function.Bijective (homologyMap
      (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1)) :=
    restriction_quasiIsomorphism_succ.{siso,tiso} (S := S) (C := C) (D := D) f hf n
  exact hiso.comp hres

theorem augmentation_left_homology_bijective_succ
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (hF : IsRightFlat.{u,v,w} F) (α : Augmentations F G) (n : ℕ) :
    Function.Bijective (homologyMap α.left (n+1)) := by
  obtain ⟨k, hk, htrans⟩ := verticalTensorAssembly F G hF
  have hb := restriction_homology_bijective_succ_of_iso.{0,max u v w}
    (transportedVerticalAugmentation F G k) htrans
    (rightTensorExtensionRestrictionIso.{u,max u v,w} F.complex B) n
  rw [transportedVerticalAugmentation_restriction F G k hk α] at hb
  exact hb

theorem transportedHorizontalAugmentation_restriction
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (k : total (unaugmented (tensorBicomplex (augmentedResolution F)
      (extendNonnegativeChain G.complex))) ⟶
        (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)).X (-1))
    (hk : ∀ n, k.f n = chainAugmentationComponent
      (tensorBicomplex (augmentedResolution F) (extendNonnegativeChain G.complex)) n)
    (α : Augmentations F G) :
    HomologicalComplex.restrictionMap (transportedHorizontalAugmentation F G k)
      nonnegativeChainEmbedding ≫ (leftTensorExtensionRestrictionIso A G.complex).hom = α.right := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply ordinaryTotal_linearMap_ext
  intro p q h a b
  by_cases hp : p=0
  · subst p
    have hn : n=q := by omega
    cases hn
    have hz := congrArg (fun f => f.hom (tmul R
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b)))
      (transportedHorizontalAugmentation_zero_component F G k hk n)
    have he : (F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a) = a :=
      (F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).toLinearEquiv.apply_symm_apply a
    change ((transportedHorizontalAugmentation F G k).f n).hom
        (ordinaryInclusion F.complex G.complex 0 n n (by omega) (tmul R a b)) =
      tmul R (F.ε ((F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).inv.hom a)))
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := n) rfl).inv.hom b) at hz
    erw [he] at hz
    change ((leftTensorExtensionRestrictionIso A G.complex).hom.f n).hom
      (((transportedHorizontalAugmentation F G k).f n).hom
        (ordinaryInclusion F.complex G.complex 0 n n (by omega) (tmul R a b))) = _
    rw [hz, leftTensorExtensionRestrictionIso_apply, α.right_zero]
  · have hp' : (p:ℤ) ≠ 0 := by exact_mod_cast hp
    have hz := congrArg (fun f => f.hom (tmul R
        ((F.complex.extendXIso nonnegativeChainEmbedding (i := p) rfl).inv.hom a)
        ((G.complex.extendXIso nonnegativeChainEmbedding (i := q) rfl).inv.hom b)))
      (transportedHorizontalAugmentation_positive F G k hk p q n (by exact_mod_cast h) hp')
    change ((transportedHorizontalAugmentation F G k).f n).hom
      (ordinaryInclusion F.complex G.complex p q n h (tmul R a b)) = 0 at hz
    have ha := congrArg (fun f => f (tmul R a b)) (α.right_positive p q n h hp)
    change ((leftTensorExtensionRestrictionIso A G.complex).hom.f n).hom
      (((transportedHorizontalAugmentation F G k).f n).hom
        (ordinaryInclusion F.complex G.complex p q n h (tmul R a b))) = _
    rw [hz, map_zero]
    exact ha.symm


set_option maxHeartbeats 200000 in
theorem augmentation_right_homology_bijective_succ
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B : Type w} [AddCommGroup B] [Module R B]
    (F : LeftResolution Rᵐᵒᵖ A) (G : LeftResolution R B)
    (hG : IsLeftFlat.{u,v,w} G) (α : Augmentations F G) (n : ℕ) :
    Function.Bijective (homologyMap α.right (n+1)) := by
  obtain ⟨f, hf, k, hk, hdef⟩ := horizontalTensorAssembly.{u,v,w} F G hG
  change f = transportedHorizontalAugmentation F G k at hdef
  let e := leftTensorExtensionRestrictionIso.{u,v,max u w} A G.complex
  have hres : Function.Bijective (homologyMap
      (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) (n+1)) :=
    restriction_quasiIsomorphism_succ.{0,max u v w} f hf n
  rw [hdef] at hres
  have hiso : Function.Bijective (homologyMap e.hom (n+1)) :=
    ((quotientHomology (ComplexShape.down ℕ) (n+1)).mapIso e).toLinearEquiv.bijective
  have hc := P103.Ch10.Complexes.homologyMap_comp
    (HomologicalComplex.restrictionMap (transportedHorizontalAugmentation F G k)
      nonnegativeChainEmbedding) e.hom (n+1)
  dsimp only [P103.Ch10.Complexes.homologyMap] at hc
  have hcomp : Function.Bijective (homologyMap
      (HomologicalComplex.restrictionMap (transportedHorizontalAugmentation F G k)
        nonnegativeChainEmbedding ≫ e.hom) (n+1)) := by
    rw [hc]
    exact hiso.comp hres
  rw [transportedHorizontalAugmentation_restriction.{u,v,w} F G k hk α] at hcomp
  exact hcomp

end OrdinaryAugmentationIsomorphisms

/-- The natural, normalized computation on every ordinary left-flat resolution. -/
def leftComputations (R : Type u) [Ring R] (n : ℕ) : LeftComputations.{u,v,w} R n := by
  cases n with
  | zero => exact leftComputationsZero R
  | succ n =>
    apply leftComputationsOfAugmentations (n+1)
    intro B G hG A P
    let α := canonicalAugmentations P.val G
    exact ⟨α,
      augmentation_left_homology_bijective_succ P.val G
        (projective_resolution_rightFlat P.val P.property) α n,
      augmentation_right_homology_bijective_succ P.val G hG α n⟩

/-- Every ordinary left-flat resolution computes Tor, naturally and with the
canonical normalization supplied by the two tensor augmentation maps. -/
theorem left_flat_computations
    : P103.Specs.Ch11.FlatResolutions.left_flat_computationsType.{u,v,w} := by
  intro R _ n
  exact ⟨leftComputations R n⟩

end
end P103.Ch11.FlatResolutions
