import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! HA-B05 and the flat comparison preceding it (source lines 979–1029).
The tensor and resolution homology are the actual P103 noncommutative models.
The flat comparison uses categorical homology of arbitrary short complexes;
applying it to `C.sc n` covers every degree of any unbounded chain complex.
Its two equations identify the comparison through cycles and their quotient.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w x y
namespace AdvancedHomologicalAlgebra.TorBalance

/-- A canonical exact-functor comparison, including its cycle and quotient maps.
Naturality in short complexes includes naturality in chain maps in every degree. -/
structure HomologyComparison
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] where
  equivalence : ∀ S : ShortComplex C, F.obj S.homology ≅ (S.map F).homology
  cyclesEquivalence : ∀ S : ShortComplex C, F.obj S.cycles ≅ (S.map F).cycles
  inclusion : ∀ S, (cyclesEquivalence S).hom ≫ (S.map F).iCycles = F.map S.iCycles
  projection : ∀ S, F.map S.homologyπ ≫ (equivalence S).hom =
    (cyclesEquivalence S).hom ≫ (S.map F).homologyπ
  naturality : ∀ {S T : ShortComplex C} (f : S ⟶ T),
    F.map (ShortComplex.homologyMap f) ≫ (equivalence T).hom =
      (equivalence S).hom ≫ ShortComplex.homologyMap (F.mapShortComplex.map f)

/-- Coefficient maps for the right-module tensor functor. -/
def tensorCoefficientMap {R : Type u} [Ring R] {M N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (g : M →ₗ[R] N) :
    (P103.Specs.Ch11.ExtTorDefinitions.tensorFunctor M :
      ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ) ⟶
      P103.Specs.Ch11.ExtTorDefinitions.tensorFunctor N where
  app X := ModuleCat.ofHom (P103.Specs.Ch11.ExtTorDefinitions.tensorMap LinearMap.id g)
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply P103.Specs.Ch11.ExtTorDefinitions.tensor_hom_ext
    intro a m
    rfl

/-- Coefficient maps for tensoring left modules with a fixed right module. -/
def leftTensorCoefficientMap {R : Type u} [Ring R] {A B : Type w}
    [AddCommGroup A] [AddCommGroup B] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B]
    (f : A →ₗ[Rᵐᵒᵖ] B) :
    (P103.Specs.Ch11.TorBalance.leftTensorFunctor A :
      ModuleCat.{v} R ⥤ ModuleCat.{max v w} ℤ) ⟶
      P103.Specs.Ch11.TorBalance.leftTensorFunctor B where
  app X := ModuleCat.ofHom (P103.Specs.Ch11.ExtTorDefinitions.tensorMap f LinearMap.id)
  naturality := by
    intro X Y g
    apply ModuleCat.hom_ext
    apply P103.Specs.Ch11.ExtTorDefinitions.tensor_hom_ext
    intro a m
    rfl

/-- Compatibility with a change of the exact functor, in addition to chain maps. -/
def ComparisonCompatible
    {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    (a : HomologyComparison F) (b : HomologyComparison G) (τ : F ⟶ G) : Prop :=
  ∀ S, τ.app S.homology ≫ (b.equivalence S).hom =
    (a.equivalence S).hom ≫ ShortComplex.homologyMap (S.mapNatTrans τ)

namespace Specs
open P103.Specs.Ch11.TorBalance P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch02.FlatnessTests

abbrev Balance := balanceType.{u,v,w}
abbrev AugmentationNaturality := augmentation_naturalType.{u,v,w}
abbrev BalanceNaturality := balanceEquiv_naturalType.{u,v,w}
abbrev LiftIndependence := lift_independentType.{u,v,w}
abbrev ResolutionIndependence := tor_coherentType.{u,v,w}

/-- Coherent comparison also applies to resolving the left coefficient. -/
def LeftResolutionIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice.{u,v} R) (projectiveComplex R)
      projectiveOver (appliedHomology (leftTensorFunctor A) (ComplexShape.down ℕ) n))

/-- Both resolution formulas identify with any chosen P103 Tor theory, compatibly
with the total-augmentation comparison. -/
def TorIdentification : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R)
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R M),
    P.IsProjective → Q.IsProjective →
    ∃ (α : Augmentations P Q) (hL : QuasiIsomorphism α.left)
      (hR : QuasiIsomorphism α.right), ∀ n : ℕ,
    ∃ (eP : TorWith P M n ≃ₗ[ℤ] T.Tor A M n)
      (eQ : Homology (leftOrdinaryTensorComplex A Q.complex) n ≃ₗ[ℤ] T.Tor A M n),
      eP = (balanceEquiv α hL hR n).trans eQ

/-- The displayed balance isomorphism is induced by the two total augmentations. -/
def BalancedIdentification : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (M : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module R M]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution R M),
    P.IsProjective → Q.IsProjective →
    ∃ (α : Augmentations P Q) (hL : QuasiIsomorphism α.left)
      (hR : QuasiIsomorphism α.right), ∀ n : ℕ,
      ∃ e : TorWith P M n ≃ₗ[ℤ] Homology (leftOrdinaryTensorComplex A Q.complex) n,
        e = balanceEquiv α hL hR n ∧
        ∀ z, e (homologyMap α.left n z) = homologyMap α.right n z

/-- Tensoring right-module homology with a flat left module, without support bounds. -/
def FlatLeftComparison : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type w) [AddCommGroup M] [Module R M],
    Flat.{u,w,v} R M → Nonempty (HomologyComparison
      (tensorFunctor M : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ))

/-- The dual assertion uses the original orientation A ⊗_R −. -/
def FlatRightComparison : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    RightFlat.{u,w,v} R A → Nonempty (HomologyComparison
      (leftTensorFunctor A : ModuleCat.{v} R ⥤ ModuleCat.{max v w} ℤ))

/-- The left-flat comparisons commute with maps of flat coefficient modules. -/
def FlatLeftNaturality : Prop :=
  ∀ (R : Type u) [Ring R] (M N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N],
    Flat.{u,w,v} R M → Flat.{u,w,v} R N →
    ∀ g : M →ₗ[R] N,
    ∃ (a : HomologyComparison (tensorFunctor M :
        ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ))
      (b : HomologyComparison (tensorFunctor N :
        ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ)),
      ComparisonCompatible a b (tensorCoefficientMap g)

def FlatRightNaturality : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type w)
    [AddCommGroup A] [AddCommGroup B] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B],
    RightFlat.{u,w,v} R A → RightFlat.{u,w,v} R B →
    ∀ f : A →ₗ[Rᵐᵒᵖ] B,
    ∃ (a : HomologyComparison (leftTensorFunctor A :
        ModuleCat.{v} R ⥤ ModuleCat.{max v w} ℤ))
      (b : HomologyComparison (leftTensorFunctor B :
        ModuleCat.{v} R ⥤ ModuleCat.{max v w} ℤ)),
      ComparisonCompatible a b (leftTensorCoefficientMap f)

/-- Degreewise form for genuinely unbounded integer-indexed chain complexes. -/
def FlatLeftChainComparison : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type w) [AddCommGroup M] [Module R M],
    Flat.{u,w,v} R M →
    ∀ (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (n : ℤ),
    let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ := tensorFunctor M
    let T := (F.mapHomologicalComplex (ComplexShape.down ℤ)).obj C
    ∃ (e : ModuleCat.of ℤ (P103.BalancedTensor.Tensor R (C.homology n) M) ≅ T.homology n)
      (k : F.obj (C.cycles n) ≅ T.cycles n),
      k.hom ≫ T.iCycles n = F.map (C.iCycles n) ∧
      F.map (C.homologyπ n) ≫ e.hom = k.hom ≫ T.homologyπ n

def FlatRightChainComparison : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    RightFlat.{u,w,v} R A →
    ∀ (C : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ),
    let F : ModuleCat.{v} R ⥤ ModuleCat.{max v w} ℤ := leftTensorFunctor A
    let T := (F.mapHomologicalComplex (ComplexShape.down ℤ)).obj C
    ∃ (e : ModuleCat.of ℤ (P103.BalancedTensor.Tensor R A (C.homology n)) ≅ T.homology n)
      (k : F.obj (C.cycles n) ≅ T.cycles n),
      k.hom ≫ T.iCycles n = F.map (C.iCycles n) ∧
      F.map (C.homologyπ n) ≫ e.hom = k.hom ≫ T.homologyπ n

end Specs

/-- A chain map of modules whose source and target may have independently
sized carriers. The formula is the ordinary differential-commutation law. -/
structure LinearChainMap {S : Type u} [Ring S] {ι : Type x}
    {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} S) c)
    (L : HomologicalComplex (ModuleCat.{w} S) c) where
  app : ∀ n, K.X n →ₗ[S] L.X n
  comm : ∀ i j, (L.d i j).hom.comp (app i) = (app j).comp (K.d i j).hom

namespace LinearChainMap
open P103.Specs.Ch10.Complexes

def ofHom {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{v} S) c} (f : K ⟶ L) :
    LinearChainMap K L where
  app n := (f.f n).hom
  comm i j := congrArg ModuleCat.Hom.hom (f.comm i j)

/-- Restrict an original chain map to the cycle submodules. -/
def cyclesMap {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c}
    (f : LinearChainMap K L) (n : ι) : cycles K n →ₗ[S] cycles L n :=
  ((f.app n).comp (cycles K n).subtype).codRestrict (cycles L n) (by
    intro z
    change (L.d n (c.next n)).hom (f.app n z.val) = 0
    have h := LinearMap.congr_fun (f.comm n (c.next n)) z.val
    change (L.d n (c.next n)).hom (f.app n z.val) =
      f.app (c.next n) ((K.d n (c.next n)).hom z.val) at h
    rw [h, show (K.d n (c.next n)).hom z.val = 0 from z.property, map_zero])

/-- The actual map of cycle quotients also works across carrier universes. -/
def homologyMap {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c}
    (f : LinearChainMap K L) (n : ι) : Homology K n →ₗ[S] Homology L n :=
  (cycleBoundaries K n).mapQ (cycleBoundaries L n) (f.cyclesMap n) (by
    intro z hz
    obtain ⟨a, ha⟩ := hz
    change (K.d (c.prev n) n).hom a = z.val at ha
    change ∃ b, (L.d (c.prev n) n).hom b = f.app n z.val
    refine ⟨f.app (c.prev n) a, ?_⟩
    simpa only [LinearMap.comp_apply, ha] using
      LinearMap.congr_fun (f.comm (c.prev n) n) a)

/-- A quasi-isomorphism is tested on the original cycle quotients. -/
def IsQuasiIso {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c}
    (f : LinearChainMap K L) : Prop :=
  ∀ n, Function.Bijective (f.homologyMap n)

/-- The equivalence given by the actual quotient map of a quasi-isomorphism. -/
def homologyEquiv {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c}
    (f : LinearChainMap K L) (h : f.IsQuasiIso) (n : ι) :
    Homology K n ≃ₗ[S] Homology L n :=
  LinearEquiv.ofBijective (f.homologyMap n) (h n)

/-- A map on the original quotient must act on every original cycle by the
specified degreewise map, using the actual target's cycle submodule. -/
def InducesHomology {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c}
    (f : LinearChainMap K L)
    (h : ∀ n, Homology K n → Homology L n) : Prop :=
  ∀ n (z : cycles K n), ∃ y : cycles L n,
    y.val = f.app n z.val ∧ h n (homologyClass K n z) = homologyClass L n y

theorem homologyMap_induces {S : Type u} [Ring S] {ι : Type x} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c} (f : LinearChainMap K L) :
    f.InducesHomology (fun n z => f.homologyMap n z) := by
  intro n z
  exact ⟨f.cyclesMap n z, rfl, rfl⟩

end LinearChainMap

section
open P103.Specs.Ch10.Comparison

/-- An augmented projective resolution whose term universe is independent
of the coefficient universe. -/
structure AugmentedResolution (R : Type u) [Ring R]
    (A : Type v) [AddCommGroup A] [Module R A] where
  complex : ChainComplex (ModuleCat.{w} R) ℕ
  ε : complex.X 0 →ₗ[R] A
  surjective : Function.Surjective ε
  exact_zero : LinearMap.range (complex.d 1 0).hom = LinearMap.ker ε
  exact_succ : ∀ n : ℕ, LinearMap.range (complex.d (n + 2) (n + 1)).hom =
    LinearMap.ker (complex.d (n + 1) n).hom
  projective : ∀ n, Module.Projective R (complex.X n)

namespace AugmentedResolution

variable {R : Type u} [Ring R] {A : Type v} {B : Type w}
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

def ofP103 (P : LeftResolution R A) (h : P.IsProjective) :
    AugmentedResolution.{u,v,max u v} R A where
  complex := P.complex
  ε := P.ε
  surjective := P.surjective
  exact_zero := P.exact_zero
  exact_succ := P.exact_succ
  projective := h

/-- The augmented square for arbitrary original linear coefficient maps. -/
def Lifts (P : AugmentedResolution.{u,v,x} R A) (Q : AugmentedResolution.{u,w,y} R B)
    (g : A →ₗ[R] B) (l : LinearChainMap P.complex Q.complex) : Prop :=
  ∀ a, Q.ε (l.app 0 a) = g (P.ε a)

end AugmentedResolution

end

section
open P103.BalancedTensor P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
universe a b
variable {R : Type u} [Ring R] {A : Type v} {M : Type w}
  [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup M] [Module R M]

/-- The two augmentations on the given signed total. Their codomains use
the given coefficients, so each map can cross a universe boundary. -/
structure OriginalAugmentations
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (Q : AugmentedResolution.{u,w,b} R M) where
  left : LinearChainMap (ordinaryTotal P.complex Q.complex) (tensorComplex P.complex M)
  right : LinearChainMap (ordinaryTotal P.complex Q.complex)
    (leftOrdinaryTensorComplex A Q.complex)
  left_zero : ∀ (p : ℕ) (a : P.complex.X p) (m : Q.complex.X 0),
    left.app p (ordinaryInclusion P.complex Q.complex p 0 p (by omega) (tmul R a m)) =
      tmul R a (Q.ε m)
  left_positive : ∀ (p q n : ℕ) (h : p + q = n), q ≠ 0 →
    (left.app n).comp (ordinaryInclusion P.complex Q.complex p q n h) = 0
  right_zero : ∀ (q : ℕ) (a : P.complex.X 0) (m : Q.complex.X q),
    right.app q (ordinaryInclusion P.complex Q.complex 0 q q (by omega) (tmul R a m)) =
      tmul R (P.ε a) m
  right_positive : ∀ (p q n : ℕ) (h : p + q = n), p ≠ 0 →
    (right.app n).comp (ordinaryInclusion P.complex Q.complex p q n h) = 0

def OriginalAugmentations.ofP103
    {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution R M}
    (hP : P.IsProjective) (hQ : Q.IsProjective) (α : Augmentations P Q) :
    OriginalAugmentations (AugmentedResolution.ofP103 P hP)
      (AugmentedResolution.ofP103 Q hQ) where
  left := LinearChainMap.ofHom α.left
  right := LinearChainMap.ofHom α.right
  left_zero := α.left_zero
  left_positive := α.left_positive
  right_zero := α.right_zero
  right_positive := α.right_positive

def OriginalAugmentations.balanceEquiv
    {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {Q : AugmentedResolution.{u,w,b} R M}
    (α : OriginalAugmentations P Q) (hL : α.left.IsQuasiIso) (hR : α.right.IsQuasiIso) (n : ℕ) :
    Homology (tensorComplex P.complex M) n ≃ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex A Q.complex) n :=
  (α.left.homologyEquiv hL n).symm.trans (α.right.homologyEquiv hR n)

end

section
open P103.BalancedTensor P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
universe v' w' a a' b b'
variable {R : Type u} [Ring R]
variable {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v'} Rᵐᵒᵖ}
  {M : ModuleCat.{w} R} {M' : ModuleCat.{w'} R}
  {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A'}
  {Q : AugmentedResolution.{u,w,b} R M} {Q' : AugmentedResolution.{u,w',b'} R M'}

/-- The three original chain maps in the two total-augmentation squares. -/
structure BalanceMaps (f : A →ₗ[Rᵐᵒᵖ] A') (g : M →ₗ[R] M')
    (l : LinearChainMap P.complex P'.complex) (m : LinearChainMap Q.complex Q'.complex)
    (α : OriginalAugmentations P Q) (β : OriginalAugmentations P' Q') where
  total : LinearChainMap (ordinaryTotal P.complex Q.complex) (ordinaryTotal P'.complex Q'.complex)
  left : LinearChainMap (tensorComplex P.complex M) (tensorComplex P'.complex M')
  right : LinearChainMap (leftOrdinaryTensorComplex A Q.complex)
    (leftOrdinaryTensorComplex A' Q'.complex)
  total_formula : ∀ i j n (h : i + j = n),
    (total.app n).comp (ordinaryInclusion P.complex Q.complex i j n h) =
      (ordinaryInclusion P'.complex Q'.complex i j n h).comp (tensorMap (l.app i) (m.app j))
  left_formula : ∀ n, left.app n = tensorMap (l.app n) g
  right_formula : ∀ n, right.app n = tensorMap f (m.app n)
  left_square : ∀ n, (β.left.app n).comp (total.app n) = (left.app n).comp (α.left.app n)
  right_square : ∀ n, (β.right.app n).comp (total.app n) = (right.app n).comp (α.right.app n)

namespace Specs

/-- Both original total augmentations are quasi-isomorphisms, for every
augmented projective resolution with its own term universe. -/
def OriginalBalance : Prop :=
  ∀ (R : Type u) [Ring R] (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R)
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (Q : AugmentedResolution.{u,w,b} R M),
    ∃ α : OriginalAugmentations P Q, α.left.IsQuasiIso ∧ α.right.IsQuasiIso

/-- Naturality on the given complexes and their cycle quotients for
independently sized coefficients and independently sized resolution terms. -/
def HeterogeneousBalanceNaturality : Prop :=
  ∀ (R : Type u) [Ring R] (A : ModuleCat.{v} Rᵐᵒᵖ) (A' : ModuleCat.{v'} Rᵐᵒᵖ)
    (M : ModuleCat.{w} R) (M' : ModuleCat.{w'} R)
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A')
    (Q : AugmentedResolution.{u,w,b} R M) (Q' : AugmentedResolution.{u,w',b'} R M')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : M →ₗ[R] M')
    (l : LinearChainMap P.complex P'.complex) (m : LinearChainMap Q.complex Q'.complex),
    P.Lifts P' f l → Q.Lifts Q' g m →
    ∀ (α : OriginalAugmentations P Q) (β : OriginalAugmentations P' Q')
      (hαL : α.left.IsQuasiIso) (hαR : α.right.IsQuasiIso)
      (hβL : β.left.IsQuasiIso) (hβR : β.right.IsQuasiIso),
    ∃ F : BalanceMaps f g l m α β, ∀ n,
      (β.left.homologyMap n).comp (F.total.homologyMap n) =
        (F.left.homologyMap n).comp (α.left.homologyMap n) ∧
      (β.right.homologyMap n).comp (F.total.homologyMap n) =
        (F.right.homologyMap n).comp (α.right.homologyMap n) ∧
      (β.balanceEquiv hβL hβR n).toLinearMap.comp (F.left.homologyMap n) =
        (F.right.homologyMap n).comp (α.balanceEquiv hαL hαR n).toLinearMap

/-- Arbitrary maps admit augmented comparison lifts between the given
resolutions. All lifts induce the same maps on the two tensor homologies. -/
def HeterogeneousLiftIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (A : ModuleCat.{v} Rᵐᵒᵖ) (A' : ModuleCat.{v'} Rᵐᵒᵖ)
    (M : ModuleCat.{w} R) (M' : ModuleCat.{w'} R)
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A')
    (Q : AugmentedResolution.{u,w,b} R M) (Q' : AugmentedResolution.{u,w',b'} R M')
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : M →ₗ[R] M'),
    (∃ (l : LinearChainMap P.complex P'.complex) (m : LinearChainMap Q.complex Q'.complex),
      P.Lifts P' f l ∧ Q.Lifts Q' g m) ∧
    ∀ (l l' : LinearChainMap P.complex P'.complex) (m m' : LinearChainMap Q.complex Q'.complex),
      P.Lifts P' f l → P.Lifts P' f l' → Q.Lifts Q' g m → Q.Lifts Q' g m' →
    ∀ (α : OriginalAugmentations P Q) (β : OriginalAugmentations P' Q')
      (F : BalanceMaps f g l m α β) (G : BalanceMaps f g l' m' α β) (n : ℕ),
      F.left.homologyMap n = G.left.homologyMap n ∧
      F.right.homologyMap n = G.right.homologyMap n

/-- The canonical P103 Tor value is reached via every augmentation-preserving
comparison with its chosen resolution. The left-resolution formula uses the
same comparison through the inverse of the actual balance isomorphism. -/
def OriginalTorIdentification : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R)
    (P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A) (Q : AugmentedResolution.{u,w,b} R M),
    let P₀ := (T.rightResolutions A).val
    let P₀' := AugmentedResolution.ofP103 P₀ (T.rightResolutions A).property
    ∀ (l : LinearChainMap P.complex P₀.complex), P.Lifts P₀' LinearMap.id l →
    ∀ (α : OriginalAugmentations P Q) (hL : α.left.IsQuasiIso) (hR : α.right.IsQuasiIso),
    ∃ t : LinearChainMap (tensorComplex P.complex M) (tensorComplex P₀.complex M),
      (∀ n, t.app n = tensorMap (l.app n) LinearMap.id) ∧
      ∃ ht : t.IsQuasiIso, ∀ n : ℕ,
        ∃ e : Homology (leftOrdinaryTensorComplex A Q.complex) n ≃ₗ[ℤ] T.Tor A M n,
          (α.balanceEquiv hL hR n).trans e = t.homologyEquiv ht n

end Specs
end

end AdvancedHomologicalAlgebra.TorBalance
