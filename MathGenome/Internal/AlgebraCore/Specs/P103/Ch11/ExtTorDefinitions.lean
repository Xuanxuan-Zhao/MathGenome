import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.HomTensorExactness

/-! Resolution formulas, paper.tex 2577–2617 and 2710–2734.
The coefficient groups are integer modules; no centrality of the base ring
is assumed. The ordinary resolutions already have their augmentations deleted.
This file contains canonical definitions only, independently of the proofs. -/
namespace P103.Specs.Ch11.ExtTorDefinitions
open CategoryTheory Opposite
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch10.Comparison
open P103.BalancedTensor
noncomputable section
universe u v w x
variable {R : Type u} [Ring R]

/-- Hom on arbitrary left modules, with its contravariant action. -/
def homFunctor (B : Type w) [AddCommGroup B] [Module R B] :
    (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{max v w} ℤ where
  obj M := ModuleCat.of ℤ (M.unop →ₗ[R] B)
  map f := ModuleCat.ofHom (P103.HomTensorExactness.pre f.unop.hom).toIntLinearMap
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance homFunctor_additive (B : Type w) [AddCommGroup B] [Module R B] :
    (homFunctor (R := R) B : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{max v w} ℤ).Additive where
  map_add := by
    intros M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change M.unop →ₗ[R] B at h
    change h.comp (f.unop.hom + g.unop.hom) = h.comp f.unop.hom + h.comp g.unop.hom
    exact LinearMap.comp_add _ _ _

/-- The ordinary Hom cochain complex. -/
abbrev homComplex (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :=
  ((homFunctor B).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((HomologicalComplex.opFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).obj (op C))

/-- Ext computed using the explicitly supplied ordinary resolution. -/
abbrev ExtWith {A : Type v} [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (homComplex P.complex B) n

/-- The map on the common balanced tensor, built directly on its defining
integer tensor quotient. -/
def tensorMap {A : Type v} {A' : Type w} {B : Type x} {B' : Type*}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R B] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') :
    Tensor R A B →ₗ[ℤ] Tensor R A' B' :=
  (relations R A B).mapQ (relations R A' B')
    (TensorProduct.map f.toAddMonoidHom.toIntLinearMap g.toAddMonoidHom.toIntLinearMap) (by
      apply Submodule.span_le.mpr
      rintro z ⟨r, a, b, rfl⟩
      change (TensorProduct.map f.toAddMonoidHom.toIntLinearMap
        g.toAddMonoidHom.toIntLinearMap)
        (TensorProduct.tmul ℤ (MulOpposite.op r • a) b -
          TensorProduct.tmul ℤ a (r • b)) ∈ relations R A' B'
      simp only [map_sub, TensorProduct.map_tmul, AddMonoidHom.coe_toIntLinearMap,
        LinearMap.toAddMonoidHom_coe, map_smul]
      exact Submodule.subset_span ⟨r, f a, g b, rfl⟩)

/-- Linear maps from the common tensor are determined on elementary tensors. -/
theorem tensor_hom_ext {A : Type v} {B : Type w} {D : Type x}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module Rᵐᵒᵖ A] [Module R B]
    (f g : Tensor R A B →ₗ[ℤ] D)
    (h : ∀ a b, f (tmul R a b) = g (tmul R a b)) : f = g := by
  apply (relations R A B).quot_hom_ext
  have e : f.comp (relations R A B).mkQ = g.comp (relations R A B).mkQ :=
    TensorProduct.ext' h
  exact LinearMap.congr_fun e

/-- Tensoring right modules with the fixed left coefficient module. -/
def tensorFunctor (B : Type w) [AddCommGroup B] [Module R B] :
    ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ where
  obj M := ModuleCat.of ℤ (Tensor R M B)
  map f := ModuleCat.ofHom (tensorMap f.hom LinearMap.id)
  map_id _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

instance tensorFunctor_additive (B : Type w) [AddCommGroup B] [Module R B] :
    (tensorFunctor (R := R) B : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ).Additive where
  map_add := by
    intros M N f g
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    change (relations R N B).mkQ (TensorProduct.tmul ℤ ((f.hom + g.hom) a) b) = _
    simp only [LinearMap.add_apply, TensorProduct.add_tmul, map_add]
    rfl

/-- The ordinary tensor chain complex. -/
abbrev tensorComplex (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :=
  ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Tor computed using the explicitly supplied ordinary right resolution. -/
abbrev TorWith {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) :=
  Homology (tensorComplex P.complex B) n

/-- Precomposition by a chain map reverses the arrows in Ext. -/
abbrev homPreMap {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : C ⟶ D) (B : Type w) [AddCommGroup B] [Module R B] :
    homComplex D B ⟶ homComplex C B :=
  ((homFunctor B).mapHomologicalComplex (ComplexShape.up ℕ)).map
    ((HomologicalComplex.opFunctor (ModuleCat.{v} R) (ComplexShape.down ℕ)).map f.op)

/-- Postcomposition by a coefficient map is covariant. -/
def homPostMap (C : ChainComplex (ModuleCat.{v} R) ℕ)
    {B B' : Type w} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') : homComplex C B ⟶ homComplex C B' where
  f n := ModuleCat.ofHom (P103.HomTensorExactness.post g).toIntLinearMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    rfl

abbrev tensorFirstMap {C D : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    (f : C ⟶ D) (B : Type w) [AddCommGroup B] [Module R B] :
    tensorComplex C B ⟶ tensorComplex D B :=
  ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℕ)).map f

/-- Tensoring a chain complex with a map in the left coefficient. -/
def tensorSecondMap (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    {B B' : Type w} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (g : B →ₗ[R] B') : tensorComplex C B ⟶ tensorComplex C B' where
  f n := ModuleCat.ofHom (tensorMap LinearMap.id g)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

def ext_coherentType : Prop :=
  ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice.{u,v} R) (projectiveComplex R)
      projectiveOver (appliedContravariantHomology (homFunctor B) (ComplexShape.down ℕ) n).rightOp)

def tor_coherentType : Prop :=
  ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice.{u,v} Rᵐᵒᵖ) (projectiveComplex Rᵐᵒᵖ)
      projectiveOver (appliedHomology (tensorFunctor B) (ComplexShape.down ℕ) n))

def ext_zeroType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B],
    ∃ e : ExtWith P B 0 ≃+ (A →ₗ[R] B),
      ∀ z : cycles (homComplex P.complex B) 0,
        (e (homologyClass _ 0 z)).comp P.ε = z.val

def tor_zeroType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B],
    ∃ e : TorWith P B 0 ≃+ Tensor R A B,
      ∀ z : cycles (tensorComplex P.complex B) 0,
        e (homologyClass _ 0 z) = tensorMap P.ε LinearMap.id z.val

/-- Naturality includes simultaneous changes of coefficients and resolution.
Taking f or g to be identity gives the individual coefficient diagrams. -/
def ext_zero_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v)
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    (P : LeftResolution R A) (Q : LeftResolution R A')
    (B B' : Type w) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (f : A' →ₗ[R] A) (g : B →ₗ[R] B') (l : Q.complex ⟶ P.complex),
    ChainLift Q P f l →
    ∀ (eP : ExtWith P B 0 ≃+ (A →ₗ[R] B)) (eQ : ExtWith Q B' 0 ≃+ (A' →ₗ[R] B')),
    (∀ z, (eP (homologyClass _ 0 z)).comp P.ε = z.val) →
    (∀ z, (eQ (homologyClass _ 0 z)).comp Q.ε = z.val) →
    ∀ x, eQ (homologyMap (homPreMap l B ≫ homPostMap Q.complex g) 0 x) =
      g.comp ((eP x).comp f)

def tor_zero_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution Rᵐᵒᵖ A')
    (B B' : Type w) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B') (l : P.complex ⟶ Q.complex),
    ChainLift P Q f l →
    ∀ (eP : TorWith P B 0 ≃+ Tensor R A B) (eQ : TorWith Q B' 0 ≃+ Tensor R A' B'),
    (∀ z, eP (homologyClass _ 0 z) = tensorMap P.ε LinearMap.id z.val) →
    (∀ z, eQ (homologyClass _ 0 z) = tensorMap Q.ε LinearMap.id z.val) →
    ∀ x, eQ (homologyMap (tensorFirstMap l B ≫ tensorSecondMap Q.complex g) 0 x) =
      tensorMap f g (eP x)

def hom_differentialType : Prop :=
  ∀ {R : Type u} [Ring R] (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ) (h : C.X n →ₗ[R] B),
    ((homComplex C B).d n (n + 1)).hom h = h.comp (C.d (n + 1) n).hom

def tensor_differentialType : Prop :=
  ∀ {R : Type u} [Ring R] (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
    ((tensorComplex C B).d (n + 1) n).hom =
      tensorMap (C.d (n + 1) n).hom LinearMap.id


/-- The full two-variable action, simultaneously on every ordinary projective
resolution. Its composition law includes all mixed naturality diagrams. -/
structure ExtMaps (R : Type u) [Ring R] (n : ℕ) where
  map : ∀ {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') {B B' : ModuleCat.{w} R},
    (A' ⟶ A) → (B ⟶ B') → ExtWith P.val B n →ₗ[ℤ] ExtWith Q.val B' n
  formula : ∀ {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') {B B' : ModuleCat.{w} R}
    (f : A' ⟶ A) (g : B ⟶ B') (l : Q.val.complex ⟶ P.val.complex),
    ChainLift Q.val P.val f.hom l →
    map P Q f g = homologyMap (homPreMap l B ≫ homPostMap Q.val.complex g.hom) n
  id : ∀ {A : ModuleCat.{v} R} (P : ProjectiveChoice R A) (B : ModuleCat.{w} R),
    map P P (𝟙 A) (𝟙 B) = LinearMap.id
  comp : ∀ {A A' A'' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') (T : ProjectiveChoice R A'')
    {B B' B'' : ModuleCat.{w} R} (f : A' ⟶ A) (f' : A'' ⟶ A')
    (g : B ⟶ B') (g' : B' ⟶ B''),
    map P T (f' ≫ f) (g ≫ g') = (map Q T f' g').comp (map P Q f g)
  add_first : ∀ {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') {B B' : ModuleCat.{w} R}
    (f f' : A' ⟶ A) (g : B ⟶ B'), map P Q (f + f') g = map P Q f g + map P Q f' g
  add_second : ∀ {A A' : ModuleCat.{v} R} (P : ProjectiveChoice R A)
    (Q : ProjectiveChoice R A') {B B' : ModuleCat.{w} R}
    (f : A' ⟶ A) (g g' : B ⟶ B'), map P Q f (g + g') = map P Q f g + map P Q f g'

/-- The analogous action for right-left Tor. -/
structure TorMaps (R : Type u) [Ring R] (n : ℕ) where
  map : ∀ {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{w} R},
    (A ⟶ A') → (B ⟶ B') → TorWith P.val B n →ₗ[ℤ] TorWith Q.val B' n
  formula : ∀ {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{w} R}
    (f : A ⟶ A') (g : B ⟶ B') (l : P.val.complex ⟶ Q.val.complex),
    ChainLift P.val Q.val f.hom l →
    map P Q f g = homologyMap (tensorFirstMap l B ≫ tensorSecondMap Q.val.complex g.hom) n
  id : ∀ {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A) (B : ModuleCat.{w} R),
    map P P (𝟙 A) (𝟙 B) = LinearMap.id
  comp : ∀ {A A' A'' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') (T : ProjectiveChoice Rᵐᵒᵖ A'')
    {B B' B'' : ModuleCat.{w} R} (f : A ⟶ A') (f' : A' ⟶ A'')
    (g : B ⟶ B') (g' : B' ⟶ B''),
    map P T (f ≫ f') (g ≫ g') = (map Q T f' g').comp (map P Q f g)
  add_first : ∀ {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{w} R}
    (f f' : A ⟶ A') (g : B ⟶ B'), map P Q (f + f') g = map P Q f g + map P Q f' g
  add_second : ∀ {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{w} R}
    (f : A ⟶ A') (g g' : B ⟶ B'), map P Q f (g + g') = map P Q f g + map P Q f g'

def ext_bifunctorialType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ), Nonempty (ExtMaps.{u,v,w} R n)
def tor_bifunctorialType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ), Nonempty (TorMaps.{u,v,w} R n)


/-- A common choice of ordinary projective resolutions, in every module size. -/
abbrev ResolutionFamily (R : Type u) [Ring R] :=
  ∀ A : ModuleCat.{v} R, ProjectiveChoice R A

/-- One family and one map construction are used for every degree. -/
structure CanonicalTheory (R : Type u) [Ring R] where
  leftResolutions : ResolutionFamily.{u,v} R
  rightResolutions : ResolutionFamily.{u,v} Rᵐᵒᵖ
  extMaps : ∀ n, ExtMaps.{u,v,w} R n
  torMaps : ∀ n, TorMaps.{u,v,w} R n

abbrev CanonicalTheory.Ext (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} R) (B : ModuleCat.{w} R) (n : ℕ) :=
  ExtWith (T.leftResolutions A).val B n
abbrev CanonicalTheory.Tor (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R) (n : ℕ) :=
  TorWith (T.rightResolutions A).val B n

/-- Applying the all-resolution maps to the chosen family gives the usual
coefficient maps; no derived-category identification is being assumed. -/
abbrev CanonicalTheory.extMap (T : CanonicalTheory.{u,v,w} R) (n : ℕ)
    {A A' : ModuleCat.{v} R} {B B' : ModuleCat.{w} R} (f : A' ⟶ A) (g : B ⟶ B') :=
  (T.extMaps n).map (T.leftResolutions A) (T.leftResolutions A') f g
abbrev CanonicalTheory.torMap (T : CanonicalTheory.{u,v,w} R) (n : ℕ)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} {B B' : ModuleCat.{w} R} (f : A ⟶ A') (g : B ⟶ B') :=
  (T.torMaps n).map (T.rightResolutions A) (T.rightResolutions A') f g

def canonical_theoryType : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (CanonicalTheory.{u,v,w} R)

/-- Fixing the first coefficient gives an additive coefficient functor. -/
def ExtMaps.coefficients {n : ℕ} (E : ExtMaps.{u,v,w} R n)
    {A : ModuleCat.{v} R} (P : ProjectiveChoice R A) :
    ModuleCat.{w} R ⥤ ModuleCat.{max u v w} ℤ where
  obj B := ModuleCat.of ℤ (ExtWith P.val B n)
  map g := ModuleCat.ofHom (E.map P P (𝟙 _) g)
  map_id B := ModuleCat.hom_ext (E.id P B)
  map_comp g h := ModuleCat.hom_ext (by simpa using E.comp P P P (𝟙 _) (𝟙 _) g h)

instance {n : ℕ} (E : ExtMaps.{u,v,w} R n) {A : ModuleCat.{v} R}
    (P : ProjectiveChoice R A) : (E.coefficients P).Additive where
  map_add := by
    intro X Y g h
    exact ModuleCat.hom_ext (E.add_second P P (𝟙 _) g h)

def TorMaps.coefficients {n : ℕ} (E : TorMaps.{u,v,w} R n)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A) :
    ModuleCat.{w} R ⥤ ModuleCat.{max u v w} ℤ where
  obj B := ModuleCat.of ℤ (TorWith P.val B n)
  map g := ModuleCat.ofHom (E.map P P (𝟙 _) g)
  map_id B := ModuleCat.hom_ext (E.id P B)
  map_comp g h := ModuleCat.hom_ext (by simpa using E.comp P P P (𝟙 _) (𝟙 _) g h)

instance {n : ℕ} (E : TorMaps.{u,v,w} R n) {A : ModuleCat.{v} Rᵐᵒᵖ}
    (P : ProjectiveChoice Rᵐᵒᵖ A) : (E.coefficients P).Additive where
  map_add := by
    intro X Y g h
    exact ModuleCat.hom_ext (E.add_second P P (𝟙 _) g h)

section Scalars
variable {K : Type u} [CommRing K]

/-- Scalar multiplication is a coefficient endomorphism only when it is linear. -/
def scalarMap (B : ModuleCat.{w} K) (r : K) : B ⟶ B :=
  ModuleCat.ofHom (r • (LinearMap.id : B →ₗ[K] B))

@[simp] theorem scalarMap_one (B : ModuleCat.{w} K) : scalarMap B 1 = 𝟙 B := by
  ext b
  exact one_smul K b
@[simp] theorem scalarMap_zero (B : ModuleCat.{w} K) : scalarMap B 0 = 0 := by
  ext b
  exact zero_smul K b
@[simp] theorem scalarMap_add (B : ModuleCat.{w} K) (r s : K) :
    scalarMap B (r + s) = scalarMap B r + scalarMap B s := by
  ext b
  exact add_smul r s b
@[simp] theorem scalarMap_mul (B : ModuleCat.{w} K) (r s : K) :
    scalarMap B (r * s) = scalarMap B s ≫ scalarMap B r := by
  ext b
  exact mul_smul r s b

theorem scalarMap_naturality {B B' : ModuleCat.{w} K} (g : B ⟶ B') (r : K) :
    scalarMap B r ≫ g = g ≫ scalarMap B' r := by
  ext b
  exact g.hom.map_smul r b

/-- The natural scalar action of an additive coefficient functor. -/
@[instance_reducible] def coefficientModule (F : ModuleCat.{w} K ⥤ ModuleCat.{x} ℤ) [F.Additive]
    (B : ModuleCat.{w} K) : Module K (F.obj B) where
  smul r z := (F.map (scalarMap B r)).hom z
  one_smul z := by
    change (F.map (scalarMap B 1)).hom z = z
    simp only [scalarMap_one, F.map_id]
    rfl
  mul_smul r s z := by
    change (F.map (scalarMap B (r * s))).hom z =
      (F.map (scalarMap B r)).hom ((F.map (scalarMap B s)).hom z)
    rw [scalarMap_mul, F.map_comp]
    rfl
  smul_zero r := map_zero _
  smul_add r z z' := map_add _ _ _
  zero_smul z := by
    change (F.map (scalarMap B 0)).hom z = 0
    simp only [scalarMap_zero, F.map_zero]
    rfl
  add_smul r s z := by
    change (F.map (scalarMap B (r + s))).hom z =
      (F.map (scalarMap B r)).hom z + (F.map (scalarMap B s)).hom z
    rw [scalarMap_add, F.map_add]
    rfl

@[instance_reducible] def extModule {n : ℕ} (E : ExtMaps.{u,v,w} K n) {A : ModuleCat.{v} K}
    (P : ProjectiveChoice K A) (B : ModuleCat.{w} K) : Module K (ExtWith P.val B n) :=
  coefficientModule (E.coefficients P) B

@[instance_reducible] def torModule {n : ℕ} (E : TorMaps.{u,v,w} K n) {A : ModuleCat.{v} Kᵐᵒᵖ}
    (P : ProjectiveChoice Kᵐᵒᵖ A) (B : ModuleCat.{w} K) : Module K (TorWith P.val B n) :=
  coefficientModule (E.coefficients P) B

end Scalars

def ext_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (n : ℕ) (E : ExtMaps.{u,v,w} K n)
    {A A' : ModuleCat.{v} K} (P : ProjectiveChoice K A) (Q : ProjectiveChoice K A')
    {B B' : ModuleCat.{w} K} (f : A' ⟶ A) (g : B ⟶ B'),
    letI := extModule E P B
    letI := extModule E Q B'
    ∀ (r : K) x, E.map P Q f g (r • x) = r • E.map P Q f g x

def tor_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (n : ℕ) (E : TorMaps.{u,v,w} K n)
    {A A' : ModuleCat.{v} Kᵐᵒᵖ} (P : ProjectiveChoice Kᵐᵒᵖ A) (Q : ProjectiveChoice Kᵐᵒᵖ A')
    {B B' : ModuleCat.{w} K} (f : A ⟶ A') (g : B ⟶ B'),
    letI := torModule E P B
    letI := torModule E Q B'
    ∀ (r : K) x, E.map P Q f g (r • x) = r • E.map P Q f g x

def ext_zero_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (E : ExtMaps.{u,v,w} K 0)
    {A : ModuleCat.{v} K} (P : ProjectiveChoice K A) (B : ModuleCat.{w} K)
    (e : ExtWith P.val B 0 ≃+ (A →ₗ[K] B)),
    (∀ z, (e (homologyClass _ 0 z)).comp P.val.ε = z.val) →
    letI := extModule E P B
    ∀ (r : K) x, e (r • x) = r • e x

/-- The tensor scalar action is specified on elementary tensors, so an arbitrary
unrelated module structure cannot satisfy this interface. -/
def tor_zero_linearType : Prop :=
  ∀ (K : Type u) [CommRing K] (E : TorMaps.{u,v,w} K 0)
    {A : ModuleCat.{v} Kᵐᵒᵖ} (P : ProjectiveChoice Kᵐᵒᵖ A) (B : ModuleCat.{w} K),
    ∃ m : Module K (Tensor K A B),
      letI := m
      (∀ (r : K) (a : A) (b : B), r • tmul K a b = tmul K a (r • b)) ∧
      ∀ (e : TorWith P.val B 0 ≃+ Tensor K A B),
        (∀ z, e (homologyClass _ 0 z) = tensorMap P.val.ε LinearMap.id z.val) →
        letI := torModule E P B
        ∀ (r : K) x, e (r • x) = r • e x

-- Definition interfaces and their canonical values.
set_option linter.unusedVariables false
set_option linter.checkUnivs false
def ExtWithType := ∀ {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]
  (P : LeftResolution R A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
  Type (max u v w)
abbrev ExtWithValue := @ExtWith.{u,v,w}

def TorWithType := ∀ {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  (P : LeftResolution Rᵐᵒᵖ A) (B : Type w) [AddCommGroup B] [Module R B] (n : ℕ),
  Type (max u v w)
abbrev TorWithValue := @TorWith.{u,v,w}

end
end P103.Specs.Ch11.ExtTorDefinitions
