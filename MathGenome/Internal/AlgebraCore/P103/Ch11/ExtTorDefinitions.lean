import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.P103.Ch10.ProjectiveResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch01.HomTensorExactness

namespace P103.Ch11.ExtTorDefinitions
open CategoryTheory Opposite
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u v w
variable {R : Type u} [Ring R]

/-- The specified cochain differential has exactly the source's sign and order. -/
theorem hom_differential (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ)
    (h : C.X n →ₗ[R] B) :
    ((homComplex C B).d n (n + 1)).hom h = h.comp (C.d (n + 1) n).hom := rfl

/-- The tensor differential is the differential on the right resolution tensor identity. -/
theorem tensor_differential (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :
    ((tensorComplex C B).d (n + 1) n).hom =
      tensorMap (C.d (n + 1) n).hom LinearMap.id := rfl

/-- This is the already established balanced tensor arrow, not a different tensor theory. -/
theorem tensorMap_eq {A A' B B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R B] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') :
    (tensorMap f g).toAddMonoidHom = P103.BalancedTensor.map f g := by
  apply P103.BalancedTensor.hom_ext
  intro a b
  rfl

/-- Includes independence of lifts, additivity, naturality, inverses and the
cocycle law for comparisons between every pair of projective resolutions. -/
theorem ext_coherent :
  ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice.{u,v} R) (projectiveComplex R)
      projectiveOver (appliedContravariantHomology (homFunctor B) (ComplexShape.down ℕ) n).rightOp) := by
  intro R _ B _ _ n
  exact P103.Ch10.Comparison.chain_contravariant_functorial R ℤ (homFunctor B) n

theorem tor_coherent :
  ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice.{u,v} Rᵐᵒᵖ) (projectiveComplex Rᵐᵒᵖ)
      projectiveOver (appliedHomology (tensorFunctor B) (ComplexShape.down ℕ) n)) := by
  intro R _ B _ _ n
  exact P103.Ch10.Comparison.chain_homology_functorial Rᵐᵒᵖ ℤ (tensorFunctor B) n

/-- A nonnegative cochain complex has no incoming differential at zero. -/
theorem cochain_zero_boundaries (C : CochainComplex (ModuleCat.{v} R) ℕ) :
    cycleBoundaries C 0 = ⊥ := by
  have hd : C.d 0 0 = 0 := C.shape 0 0 (by decide)
  ext z
  change (∃ x, (C.d ((ComplexShape.up ℕ).prev 0) 0).hom x = z.val) ↔ z = 0
  rw [CochainComplex.prev_nat_zero]
  constructor
  · rintro ⟨x, hx⟩
    apply Subtype.ext
    rw [hd] at hx
    exact hx.symm
  · rintro rfl
    exact ⟨0, map_zero _⟩

variable {A : Type v} [AddCommGroup A] [Module R A]

/-- Pull back a map on A along the augmentation; exactness makes it a cocycle. -/
def homToZeroCycles (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B] :
    (A →ₗ[R] B) →ₗ[ℤ] cycles (homComplex P.complex B) 0 :=
  (P103.HomTensorExactness.pre P.ε).toIntLinearMap.codRestrict _ (by
    intro h
    change ((homComplex P.complex B).d 0 ((ComplexShape.up ℕ).next 0)).hom _ = 0
    rw [CochainComplex.next]
    change (h.comp P.ε).comp (P.complex.d 1 0).hom = 0
    rw [LinearMap.comp_assoc, P103.Ch10.Comparison.augmentation_square,
      LinearMap.comp_zero])

theorem homToZeroCycles_bijective (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B] :
    Function.Bijective (homToZeroCycles P B) := by
  constructor
  · intro h k he
    ext a
    obtain ⟨x, rfl⟩ := P.surjective a
    exact LinearMap.congr_fun (congrArg Subtype.val he) x
  · intro z
    have hk : LinearMap.ker P.ε ≤ LinearMap.ker z.val := by
      intro x hx
      rw [← P.exact_zero] at hx
      obtain ⟨y, rfl⟩ := hx
      have hz := z.property
      change ((homComplex P.complex B).d 0 ((ComplexShape.up ℕ).next 0)).hom z.val = 0 at hz
      rw [CochainComplex.next] at hz
      change z.val.comp (P.complex.d 1 0).hom = 0 at hz
      exact LinearMap.congr_fun hz y
    let h := P.ε.liftOfSurjective P.surjective ⟨z.val, hk⟩
    refine ⟨h, Subtype.ext ?_⟩
    change h.comp P.ε = z.val
    ext x
    exact LinearMap.equivOfSurjective_apply P.surjective hk

/-- Canonical descent of degree-zero cocycles to the augmented module. -/
def extZero (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] :
    ExtWith P B 0 ≃+ (A →ₗ[R] B) :=
  ((cycleBoundaries (homComplex P.complex B) 0).quotEquivOfEqBot
      (cochain_zero_boundaries _)).toAddEquiv.trans
    (LinearEquiv.ofBijective (homToZeroCycles P B) (homToZeroCycles_bijective P B)).symm.toAddEquiv

theorem extZero_class (P : LeftResolution R A)
    (B : Type w) [AddCommGroup B] [Module R B]
    (z : cycles (homComplex P.complex B) 0) :
    (extZero P B (homologyClass _ 0 z)).comp P.ε = z.val := by
  have h := (LinearEquiv.ofBijective (homToZeroCycles P B)
    (homToZeroCycles_bijective P B)).apply_symm_apply z
  exact congrArg Subtype.val h

theorem ext_zero : ext_zeroType.{u,v,w} := by
  intro R _ A _ _ P B _ _
  exact ⟨extZero P B, extZero_class P B⟩

/-- Every element of the zeroth term of a nonnegative chain complex is a cycle. -/
theorem chain_mem_zero_cycles (C : ChainComplex (ModuleCat.{v} R) ℕ) (x : C.X 0) :
    x ∈ cycles C 0 := by
  change (C.d 0 ((ComplexShape.down ℕ).next 0)).hom x = 0
  rw [ChainComplex.next_nat_zero, C.shape 0 0 (by decide)]
  rfl

section TorZero
variable {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
variable (P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B]

/-- Right exactness identifies the kernel after tensoring the augmentation. -/
theorem tensor_augmentation_exact :
    Function.Exact (tensorMap (P.complex.d 1 0).hom (LinearMap.id : B →ₗ[R] B))
      (tensorMap P.ε (LinearMap.id : B →ₗ[R] B)) ∧
    Function.Surjective (tensorMap P.ε (LinearMap.id : B →ₗ[R] B)) := by
  exact P103.HomTensorExactness.tensor_first_rightExact
    (P.complex.d 1 0).hom P.ε (LinearMap.exact_iff.mpr P.exact_zero.symm)
    P.surjective (tensorMap _ _).toAddMonoidHom (fun _ _ => rfl)
    (tensorMap _ _).toAddMonoidHom (fun _ _ => rfl)

def tensorZeroAugmentation : cycles (tensorComplex P.complex B) 0 →ₗ[ℤ]
    P103.BalancedTensor.Tensor R A B :=
  (tensorMap P.ε LinearMap.id).comp (cycles (tensorComplex P.complex B) 0).subtype

theorem tensorZeroAugmentation_surjective : Function.Surjective (tensorZeroAugmentation P B) := by
  intro z
  obtain ⟨x, hx⟩ := (tensor_augmentation_exact P B).2 z
  exact ⟨⟨x, chain_mem_zero_cycles (tensorComplex P.complex B) x⟩, hx⟩

theorem tensorZeroAugmentation_kernel :
    cycleBoundaries (tensorComplex P.complex B) 0 = LinearMap.ker (tensorZeroAugmentation P B) := by
  ext z
  change z.val ∈ LinearMap.range
      ((tensorComplex P.complex B).d ((ComplexShape.down ℕ).prev 0) 0).hom ↔
    tensorMap P.ε LinearMap.id z.val = 0
  rw [ChainComplex.prev]
  exact ((tensor_augmentation_exact P B).1 z.val).symm

/-- The degree-zero Tor isomorphism is induced by ε tensor identity. -/
def torZero : TorWith P B 0 ≃+ P103.BalancedTensor.Tensor R A B := by
  let g : cycles (tensorComplex P.complex B) 0 →ₗ[ℤ] P103.BalancedTensor.Tensor R A B :=
    tensorZeroAugmentation P B
  have hg : Function.Surjective g := tensorZeroAugmentation_surjective P B
  have hk : cycleBoundaries (tensorComplex P.complex B) 0 = LinearMap.ker g :=
    tensorZeroAugmentation_kernel P B
  let e₁ : TorWith P B 0 ≃ₗ[ℤ]
      (cycles (tensorComplex P.complex B) 0 ⧸ LinearMap.ker g) :=
    Submodule.quotEquivOfEq _ _ hk
  let e₂ := g.quotKerEquivOfSurjective hg
  exact (e₁.trans e₂).toAddEquiv

theorem torZero_class (z : cycles (tensorComplex P.complex B) 0) :
    torZero P B (homologyClass _ 0 z) = tensorMap P.ε LinearMap.id z.val :=
  LinearMap.quotKerEquivOfSurjective_apply_mk (tensorZeroAugmentation P B)
    (tensorZeroAugmentation_surjective P B) z

end TorZero

theorem tor_zero : tor_zeroType.{u,v,w} := by
  intro R _ A _ _ P B _ _
  exact ⟨torZero P B, torZero_class P B⟩

/-- Uniqueness of descent proves all degree-zero Ext naturality diagrams. -/
theorem ext_zero_natural : ext_zero_naturalType.{u,v,w} := by
  intro R _ A A' _ _ _ _ P Q B B' _ _ _ _ f g l hl eP eQ hP hQ x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    apply LinearMap.ext
    intro a
    obtain ⟨y, rfl⟩ := Q.surjective a
    let φ : P.complex.X 0 →ₗ[R] B := z.val
    have hq := LinearMap.congr_fun
      (hQ (cyclesMap (homPreMap l B ≫ homPostMap Q.complex g) 0 z)) y
    have hp := LinearMap.congr_fun (hP z) ((l.f 0).hom y)
    have he := LinearMap.congr_fun hl y
    change eQ (homologyMap (homPreMap l B ≫ homPostMap Q.complex g) 0
      (homologyClass _ 0 z)) (Q.ε y) = g (eP (homologyClass _ 0 z) (f (Q.ε y)))
    change eQ (homologyMap (homPreMap l B ≫ homPostMap Q.complex g) 0
      (homologyClass _ 0 z)) (Q.ε y) = g (φ ((l.f 0).hom y)) at hq
    calc
      _ = g (φ ((l.f 0).hom y)) := hq
      _ = g (eP (homologyClass _ 0 z) (P.ε ((l.f 0).hom y))) := congrArg g hp.symm
      _ = _ := congrArg (fun a => g (eP (homologyClass _ 0 z) a)) he

/-- The tensor naturality diagram follows on elementary tensors and descends
through the degree-zero homology quotient. -/
theorem tor_zero_natural : tor_zero_naturalType.{u,v,w} := by
  intro R _ A A' _ _ _ _ P Q B B' _ _ _ _ f g l hl eP eQ hP hQ x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    change eQ (homologyClass _ 0
      (cyclesMap (tensorFirstMap l B ≫ tensorSecondMap Q.complex g) 0 z)) =
        tensorMap f g (eP (homologyClass _ 0 z))
    rw [hQ, hP]
    have he : (tensorMap Q.ε (LinearMap.id : B' →ₗ[R] B')).comp
          (((tensorFirstMap l B ≫ tensorSecondMap Q.complex g).f 0).hom) =
        (tensorMap f g).comp (tensorMap P.ε (LinearMap.id : B →ₗ[R] B)) := by
      apply tensor_hom_ext
      intro a b
      change P103.BalancedTensor.tmul R (Q.ε ((l.f 0).hom a)) (g b) =
        P103.BalancedTensor.tmul R (f (P.ε a)) (g b)
      exact congrArg (fun a => P103.BalancedTensor.tmul R a (g b))
        (LinearMap.congr_fun hl a)
    exact LinearMap.congr_fun he z.val


section Bifunctors
open P103.Ch10.Comparison
open P103.Ch10.Complexes (homologyMap_id homologyMap_comp homologyMap_add)

abbrev extChainMap {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (l : D ⟶ C) {B B' : ModuleCat.{w} R} (g : B ⟶ B') :=
  homPreMap l B ≫ homPostMap D g.hom

abbrev torChainMap {C D : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    (l : C ⟶ D) {B B' : ModuleCat.{w} R} (g : B ⟶ B') :=
  tensorFirstMap l B ≫ tensorSecondMap D g.hom

/-- The second variable can be varied after any lift of the first map. -/
def extMapWith {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') {B B' : ModuleCat.{w} R}
    (f : A' ⟶ A) (g : B ⟶ B') (n : ℕ) :
    ExtWith P.val B n →ₗ[ℤ] ExtWith Q.val B' n :=
  homologyMap (extChainMap (chainMap Q.val P.val Q.property f.hom) g) n

def torMapWith {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{w} R}
    (f : A ⟶ A') (g : B ⟶ B') (n : ℕ) :
    TorWith P.val B n →ₗ[ℤ] TorWith Q.val B' n :=
  homologyMap (torChainMap (chainMap P.val Q.val P.property f.hom) g) n

theorem extMapWith_formula {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') {B B' : ModuleCat.{w} R}
    (f : A' ⟶ A) (g : B ⟶ B') (l : Q.val.complex ⟶ P.val.complex)
    (hl : ChainLift Q.val P.val f.hom l) (n : ℕ) :
    extMapWith P Q f g n = homologyMap (extChainMap l g) n := by
  have e := chain_contravariant_independent R ℤ (homFunctor B) A' A
    Q.val P.val Q.property f.hom (chainMap Q.val P.val Q.property f.hom) l n
    (chainMap_lifts Q.val P.val Q.property f.hom) hl
  have e' : homologyMap (homPreMap (chainMap Q.val P.val Q.property f.hom) B) n =
      homologyMap (homPreMap l B) n := congrArg (fun k => k.unop.hom) e
  simp only [extMapWith, extChainMap, homologyMap_comp, e']
  rfl

theorem torMapWith_formula {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{w} R}
    (f : A ⟶ A') (g : B ⟶ B') (l : P.val.complex ⟶ Q.val.complex)
    (hl : ChainLift P.val Q.val f.hom l) (n : ℕ) :
    torMapWith P Q f g n = homologyMap (torChainMap l g) n := by
  have e := chain_homology_independent Rᵐᵒᵖ ℤ (tensorFunctor B) A A'
    P.val Q.val P.property f.hom (chainMap P.val Q.val P.property f.hom) l n
    (chainMap_lifts P.val Q.val P.property f.hom) hl
  have e' : homologyMap (tensorFirstMap (chainMap P.val Q.val P.property f.hom) B) n =
      homologyMap (tensorFirstMap l B) n := congrArg ModuleCat.Hom.hom e
  simp only [torMapWith, torChainMap, homologyMap_comp, e']
  rfl

/-- Full higher-degree Ext bifunctor laws, with all resolutions retained. -/
def extMaps (n : ℕ) : ExtMaps.{u,v,w} R n where
  map {A A'} P Q {B B'} f g := extMapWith P Q f g n
  formula {A A'} P Q {B B'} f g l hl := extMapWith_formula P Q f g l hl n
  id P B := by
    erw [extMapWith_formula P P (𝟙 _) (𝟙 B) (𝟙 _) (chainLift_id P.val) n]
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ z => rfl
  comp {A A' A''} P Q T {B B' B''} f f' g g' := by
    let l := chainMap Q.val P.val Q.property f.hom
    let l' := chainMap T.val Q.val T.property f'.hom
    have hl := chainMap_lifts Q.val P.val Q.property f.hom
    have hl' := chainMap_lifts T.val Q.val T.property f'.hom
    erw [extMapWith_formula P T (f' ≫ f) (g ≫ g') (l' ≫ l)
      (chainLift_comp hl' hl) n,
      extMapWith_formula P Q f g l hl n,
      extMapWith_formula Q T f' g' l' hl' n, ← homologyMap_comp]
    congr 1
  add_first {A A'} P Q {B B'} f f' g := by
    let l := chainMap Q.val P.val Q.property f.hom
    let l' := chainMap Q.val P.val Q.property f'.hom
    have hl := chainMap_lifts Q.val P.val Q.property f.hom
    have hl' := chainMap_lifts Q.val P.val Q.property f'.hom
    erw [extMapWith_formula P Q (f + f') g (l + l') (chainLift_add hl hl') n,
      extMapWith_formula P Q f g l hl n,
      extMapWith_formula P Q f' g l' hl' n, ← homologyMap_add]
    congr 1
    ext k : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change P.val.complex.X k →ₗ[R] B at φ
    apply LinearMap.ext
    intro a
    change g.hom (φ ((l.f k).hom a + (l'.f k).hom a)) =
      g.hom (φ ((l.f k).hom a)) + g.hom (φ ((l'.f k).hom a))
    rw [map_add, map_add]
  add_second {A A'} P Q {B B'} f g g' := by
    simp only [extMapWith]
    erw [← homologyMap_add]
    congr 1

/-- Full higher-degree Tor bifunctor laws, including mixed composition. -/
def torMaps (n : ℕ) : TorMaps.{u,v,w} R n where
  map {A A'} P Q {B B'} f g := torMapWith P Q f g n
  formula {A A'} P Q {B B'} f g l hl := torMapWith_formula P Q f g l hl n
  id P B := by
    erw [torMapWith_formula P P (𝟙 _) (𝟙 B) (𝟙 _) (chainLift_id P.val) n]
    have h : torChainMap (𝟙 P.val.complex) (𝟙 B) = 𝟙 _ := by
      ext k : 1
      apply ModuleCat.hom_ext
      apply tensor_hom_ext
      intro a b
      rfl
    rw [h]
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ z => rfl
  comp {A A' A''} P Q T {B B' B''} f f' g g' := by
    let l := chainMap P.val Q.val P.property f.hom
    let l' := chainMap Q.val T.val Q.property f'.hom
    have hl := chainMap_lifts P.val Q.val P.property f.hom
    have hl' := chainMap_lifts Q.val T.val Q.property f'.hom
    erw [torMapWith_formula P T (f ≫ f') (g ≫ g') (l ≫ l')
      (chainLift_comp hl hl') n,
      torMapWith_formula P Q f g l hl n,
      torMapWith_formula Q T f' g' l' hl' n, ← homologyMap_comp]
    congr 1
    ext k : 1
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  add_first {A A'} P Q {B B'} f f' g := by
    let l := chainMap P.val Q.val P.property f.hom
    let l' := chainMap P.val Q.val P.property f'.hom
    have hl := chainMap_lifts P.val Q.val P.property f.hom
    have hl' := chainMap_lifts P.val Q.val P.property f'.hom
    erw [torMapWith_formula P Q (f + f') g (l + l') (chainLift_add hl hl') n,
      torMapWith_formula P Q f g l hl n,
      torMapWith_formula P Q f' g l' hl' n, ← homologyMap_add]
    congr 1
    ext k : 1
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change P103.BalancedTensor.tmul R (((l.f k).hom + (l'.f k).hom) a) (g.hom b) = _
    erw [LinearMap.add_apply, P103.BalancedTensor.add_tmul]
    rfl
  add_second {A A'} P Q {B B'} f g g' := by
    simp only [torMapWith]
    erw [← homologyMap_add]
    congr 1
    ext k : 1
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change P103.BalancedTensor.tmul R _ ((g.hom + g'.hom) b) = _
    erw [LinearMap.add_apply, P103.BalancedTensor.tmul_add]
    rfl

theorem ext_bifunctorial : ext_bifunctorialType.{u,v,w} := by
  intro R _ n
  exact ⟨extMaps n⟩

theorem tor_bifunctorial : tor_bifunctorialType.{u,v,w} := by
  intro R _ n
  exact ⟨torMaps n⟩
end Bifunctors


/-- A fixed, global projective family for all later uses of the resolution formulas. -/
def resolutionFamily (S : Type u) [Ring S] : ResolutionFamily.{u,v} S := fun A =>
  ⟨Classical.choose (P103.Ch10.ProjectiveResolutions.exists_projective_resolution S A),
    Classical.choose_spec (P103.Ch10.ProjectiveResolutions.exists_projective_resolution S A)⟩

def theory (S : Type u) [Ring S] : CanonicalTheory.{u,v,w} S where
  leftResolutions := resolutionFamily S
  rightResolutions := resolutionFamily Sᵐᵒᵖ
  extMaps := extMaps
  torMaps := torMaps

/-- The canonical family is the same explicit quotient theory in every degree. -/
abbrev Ext (S : Type u) [Ring S] (A : ModuleCat.{v} S) (B : ModuleCat.{w} S) (n : ℕ) :=
  (theory S).Ext A B n
abbrev Tor (S : Type u) [Ring S] (A : ModuleCat.{v} Sᵐᵒᵖ) (B : ModuleCat.{w} S) (n : ℕ) :=
  (theory S).Tor A B n

/-- Right-module Ext uses exactly the left-module construction over the opposite. -/
abbrev RightExt (S : Type u) [Ring S]
    (A : ModuleCat.{v} Sᵐᵒᵖ) (B : ModuleCat.{w} Sᵐᵒᵖ) (n : ℕ) := Ext Sᵐᵒᵖ A B n

theorem canonical_theory : canonical_theoryType.{u,v,w} := by
  intro S _
  exact ⟨theory S⟩

theorem ext_linear : ext_linearType.{u,v,w} := by
  intro K _ n E A A' P Q B B' f g r x
  change E.map P Q f g (E.map P P (𝟙 _) (scalarMap B r) x) =
    E.map Q Q (𝟙 _) (scalarMap B' r) (E.map P Q f g x)
  have h₁ := E.comp P P Q (𝟙 _) f (scalarMap B r) g
  have h₂ := E.comp P Q Q f (𝟙 _) g (scalarMap B' r)
  have h : (E.map P Q f g).comp (E.map P P (𝟙 _) (scalarMap B r)) =
      (E.map Q Q (𝟙 _) (scalarMap B' r)).comp (E.map P Q f g) := by
    rw [← h₁, ← h₂]
    simp only [Category.id_comp, Category.comp_id, scalarMap_naturality]
  exact LinearMap.congr_fun h x

theorem tor_linear : tor_linearType.{u,v,w} := by
  intro K _ n E A A' P Q B B' f g r x
  change E.map P Q f g (E.map P P (𝟙 _) (scalarMap B r) x) =
    E.map Q Q (𝟙 _) (scalarMap B' r) (E.map P Q f g x)
  have h₁ := E.comp P P Q (𝟙 _) f (scalarMap B r) g
  have h₂ := E.comp P Q Q f (𝟙 _) g (scalarMap B' r)
  have h : (E.map P Q f g).comp (E.map P P (𝟙 _) (scalarMap B r)) =
      (E.map Q Q (𝟙 _) (scalarMap B' r)).comp (E.map P Q f g) := by
    rw [← h₁, ← h₂]
    simp only [Category.id_comp, Category.comp_id, scalarMap_naturality]
  exact LinearMap.congr_fun h x

theorem ext_zero_linear : ext_zero_linearType.{u,v,w} := by
  intro K _ E A P B e he r x
  change e (E.map P P (𝟙 _) (scalarMap B r) x) = r • e x
  rw [E.formula P P (𝟙 _) (scalarMap B r) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  have h := ext_zero_natural K A A P.val P.val B B LinearMap.id
    (scalarMap B r).hom (𝟙 _) (P103.Ch10.Comparison.chainLift_id P.val) e e he he x
  refine h.trans ?_
  ext a
  rfl

theorem tor_zero_linear : tor_zero_linearType.{u,v,w} := by
  intro K _ E A P B
  letI := P103.BalancedTensor.rightModule (R := K) (A := A) (B := B) (S := K)
  refine ⟨inferInstance, (fun r a b => rfl), ?_⟩
  intro e he r x
  change e (E.map P P (𝟙 _) (scalarMap B r) x) =
    P103.BalancedTensor.rightScale r (e x)
  rw [E.formula P P (𝟙 _) (scalarMap B r) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  have h := tor_zero_natural K A A P.val P.val B B LinearMap.id
    (scalarMap B r).hom (𝟙 _) (P103.Ch10.Comparison.chainLift_id P.val) e e he he x
  refine h.trans ?_
  have hmap : (tensorMap (LinearMap.id : A →ₗ[Kᵐᵒᵖ] A) (scalarMap B r).hom).toAddMonoidHom =
      P103.BalancedTensor.rightScale r := by
    apply P103.BalancedTensor.hom_ext
    intro a b
    rfl
  exact DFunLike.congr_fun hmap (e x)

section ScalarRepresentatives
variable {K : Type u} [CommRing K]

/-- The coefficient-functor action is the usual scalar action on cocycles. -/
theorem extModule_smul_class {n : ℕ} (E : ExtMaps.{u,v,w} K n)
    {A : ModuleCat.{v} K} (P : ProjectiveChoice K A) (B : ModuleCat.{w} K)
    (r : K) (z : cycles (homComplex P.val.complex B) n) :
    letI := extModule E P B
    r • homologyClass _ n z = homologyClass _ n
      (cyclesMap (homPostMap P.val.complex (scalarMap B r).hom) n z) := by
  change E.map P P (𝟙 _) (scalarMap B r) (homologyClass _ n z) = _
  rw [E.formula P P (𝟙 _) (scalarMap B r) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  rfl

/-- On representatives the action multiplies the target of the cocycle. -/
theorem extModule_smul_class_val {n : ℕ}
    {A : ModuleCat.{v} K} (P : ProjectiveChoice K A) (B : ModuleCat.{w} K)
    (r : K) (z : cycles (homComplex P.val.complex B) n) :
    ((cyclesMap (homPostMap P.val.complex (scalarMap B r).hom) n z).val : P.val.complex.X n →ₗ[K] B) = @SMul.smul K (P.val.complex.X n →ₗ[K] B) inferInstance r z.val := by
  rfl

end ScalarRepresentatives

/-- Coefficient scalar multiplication acts on a quotient representative by the
ordinary tensor map on the left coefficient. -/
theorem torModule_smul_class (K : Type u) [CommRing K] (n : ℕ)
    (E : TorMaps.{u,v,w} K n) {A : ModuleCat.{v} Kᵐᵒᵖ}
    (P : ProjectiveChoice Kᵐᵒᵖ A) (B : ModuleCat.{w} K)
    (r : K) (z : cycles (tensorComplex P.val.complex B) n) :
    letI := torModule E P B
    r • homologyClass _ n z = homologyClass _ n
      (cyclesMap (tensorSecondMap P.val.complex (scalarMap B r).hom) n z) := by
  change E.map P P (𝟙 _) (scalarMap B r) (homologyClass _ n z) = _
  rw [E.formula P P (𝟙 _) (scalarMap B r) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  have h : tensorFirstMap (𝟙 P.val.complex) B = 𝟙 _ := by
    exact CategoryTheory.Functor.map_id
      ((tensorFunctor (R := K) B).mapHomologicalComplex (ComplexShape.down ℕ)) _
  rw [h, Category.id_comp]
  rfl

/-- On a cycle's underlying tensor the representative is precisely the standard
balanced tensor scalar action. -/
theorem torScalarCycle_val (K : Type u) [CommRing K]
    (C : ChainComplex (ModuleCat.{v} Kᵐᵒᵖ) ℕ) (B : ModuleCat.{w} K)
    (n : ℕ) (r : K) (z : cycles (tensorComplex C B) n) :
    (cyclesMap (tensorSecondMap C (scalarMap B r).hom) n z).val =
      P103.BalancedTensor.rightScale r z.val := by
  change tensorMap (LinearMap.id : C.X n →ₗ[Kᵐᵒᵖ] C.X n)
    (scalarMap B r).hom z.val = _
  have h : (tensorMap (LinearMap.id : C.X n →ₗ[Kᵐᵒᵖ] C.X n)
      (scalarMap B r).hom).toAddMonoidHom = P103.BalancedTensor.rightScale r := by
    apply P103.BalancedTensor.hom_ext
    intro a b
    rfl
  exact DFunLike.congr_fun h z.val

/-- Degree-zero Tor with its usual tensor module structure, as a bundled linear
isomorphism rather than only a scalar-preservation proposition. -/
def torZeroLinear (K : Type u) [CommRing K] (E : TorMaps.{u,v,w} K 0)
    {A : ModuleCat.{v} Kᵐᵒᵖ} (P : ProjectiveChoice Kᵐᵒᵖ A) (B : ModuleCat.{w} K) :
    letI := torModule E P B
    letI := P103.BalancedTensor.rightModule (R := K) (A := A) (B := B) (S := K)
    TorWith P.val B 0 ≃ₗ[K] P103.BalancedTensor.Tensor K A B := by
  letI := torModule E P B
  letI := P103.BalancedTensor.rightModule (R := K) (A := A) (B := B) (S := K)
  refine { P103.Ch11.ExtTorDefinitions.torZero P.val B with map_smul' := ?_ }
  intro r x
  change P103.Ch11.ExtTorDefinitions.torZero P.val B
    (E.map P P (𝟙 _) (scalarMap B r) x) =
    P103.BalancedTensor.rightScale r (P103.Ch11.ExtTorDefinitions.torZero P.val B x)
  rw [E.formula P P (𝟙 _) (scalarMap B r) (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  have h := P103.Ch11.ExtTorDefinitions.tor_zero_natural K A A P.val P.val B B
    LinearMap.id (scalarMap B r).hom (𝟙 _) (P103.Ch10.Comparison.chainLift_id P.val)
    (P103.Ch11.ExtTorDefinitions.torZero P.val B)
    (P103.Ch11.ExtTorDefinitions.torZero P.val B)
    (P103.Ch11.ExtTorDefinitions.torZero_class P.val B)
    (P103.Ch11.ExtTorDefinitions.torZero_class P.val B) x
  refine h.trans ?_
  have hmap : (tensorMap (LinearMap.id : A →ₗ[Kᵐᵒᵖ] A) (scalarMap B r).hom).toAddMonoidHom =
      P103.BalancedTensor.rightScale r := by
    apply P103.BalancedTensor.hom_ext
    intro a b
    rfl
  exact DFunLike.congr_fun hmap _


/-- Coefficient maps for the globally fixed family of projective resolutions. -/
abbrev extMap (R : Type u) [Ring R] (n : ℕ)
    {A A' : ModuleCat.{v} R} {B B' : ModuleCat.{w} R} (f : A' ⟶ A) (g : B ⟶ B') :=
  (theory R).extMap n f g
abbrev torMap (R : Type u) [Ring R] (n : ℕ)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} {B B' : ModuleCat.{w} R} (f : A ⟶ A') (g : B ⟶ B') :=
  (theory R).torMap n f g

instance canonicalExtModule (K : Type u) [CommRing K]
    (A : ModuleCat.{v} K) (B : ModuleCat.{w} K) (n : ℕ) : Module K (Ext K A B n) :=
  extModule (extMaps n) (resolutionFamily K A) B
instance canonicalTorModule (K : Type u) [CommRing K]
    (A : ModuleCat.{v} Kᵐᵒᵖ) (B : ModuleCat.{w} K) (n : ℕ) : Module K (Tor K A B n) :=
  torModule (torMaps n) (resolutionFamily Kᵐᵒᵖ A) B

/-- Over a commutative ring all simultaneous coefficient maps are linear. -/
def extMapLinear (K : Type u) [CommRing K] (n : ℕ)
    {A A' : ModuleCat.{v} K} {B B' : ModuleCat.{w} K} (f : A' ⟶ A) (g : B ⟶ B') :
    Ext K A B n →ₗ[K] Ext K A' B' n where
  toAddHom := (extMap K n f g).toAddMonoidHom
  map_smul' r x := ext_linear K n (extMaps n) (resolutionFamily K A)
    (resolutionFamily K A') f g r x

def torMapLinear (K : Type u) [CommRing K] (n : ℕ)
    {A A' : ModuleCat.{v} Kᵐᵒᵖ} {B B' : ModuleCat.{w} K} (f : A ⟶ A') (g : B ⟶ B') :
    Tor K A B n →ₗ[K] Tor K A' B' n where
  toAddHom := (torMap K n f g).toAddMonoidHom
  map_smul' r x := tor_linear K n (torMaps n) (resolutionFamily Kᵐᵒᵖ A)
    (resolutionFamily Kᵐᵒᵖ A') f g r x

def extZeroLinear (K : Type u) [CommRing K]
    (A : ModuleCat.{v} K) (B : ModuleCat.{w} K) :
    Ext K A B 0 ≃ₗ[K] (A →ₗ[K] B) where
  __ := extZero (resolutionFamily K A).val B
  map_smul' r x := ext_zero_linear K (extMaps 0) (resolutionFamily K A) B _
    (extZero_class (resolutionFamily K A).val B) r x

abbrev ExtWith := @P103.Specs.Ch11.ExtTorDefinitions.ExtWith.{u,v,w}
abbrev TorWith := @P103.Specs.Ch11.ExtTorDefinitions.TorWith.{u,v,w}

end
end P103.Ch11.ExtTorDefinitions
