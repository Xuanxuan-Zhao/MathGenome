import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests

/-! HA-B07, source lines 1132–1202.
Independent scalar/tensor, quotient-page, finite-convergence and
resolution-independent naturality contracts for the change-of-rings construction.
No flatness of the ring map is imposed. -/
noncomputable section
universe u v w x a b
namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open P103.BalancedTensor

/-- A type synonym records the particular ring map used for restriction. -/
def Restricted {R : Type u} {S : Type v} [Ring R] [Ring S]
    (_f : R →+* S) (M : Type w) := M

namespace Restricted
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
variable (M : Type w) [AddCommGroup M] [Module S M]
instance : AddCommGroup (Restricted f M) := inferInstanceAs (AddCommGroup M)
instance : Module R (Restricted f M) := Module.compHom M f

def of (m : M) : Restricted f M := m

def val (m : Restricted f M) : M := m

omit [Module S M] in
@[simp] theorem of_add (a b : M) : of f M (a+b) = of f M a + of f M b := rfl
@[simp] theorem of_smul (r : R) (a : M) :
    of f M (f r • a) = r • of f M a := rfl

instance rightRegular : Module Sᵐᵒᵖ (Restricted f S) :=
  inferInstanceAs (Module Sᵐᵒᵖ S)
instance commuting : SMulCommClass Sᵐᵒᵖ R (Restricted f S) where
  smul_comm s r t := by
    change (f r * val f S t) * s.unop = f r * (val f S t * s.unop)
    exact mul_assoc _ _ _

/-- Restriction acts on maps without changing their underlying functions. -/
def map {M N : Type w} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (g : M →ₗ[S] N) :
    Restricted f M →ₗ[R] Restricted f N where
  toFun := g
  map_add' := g.map_add
  map_smul' r m := g.map_smul (f r) m
end Restricted

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
open CategoryTheory
open P103.Specs.Ch10.Comparison

/-- Restriction of scalars, recording the ring map on the underlying type. -/
def restrictionFunctor (f : R →+* S) : ModuleCat.{w} S ⥤ ModuleCat.{w} R where
  obj M := ModuleCat.of R (Restricted f M)
  map g := ModuleCat.ofHom (Restricted.map f g.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

instance restrictionFunctor_additive (f : R →+* S) :
    (restrictionFunctor f : ModuleCat.{w} S ⥤ ModuleCat.{w} R).Additive where
  map_add := rfl

/-- Restriction changes the scalar action, but none of the differentials. -/
abbrev restrictionComplex (f : R →+* S) {ι : Type*} (c : ComplexShape ι)
    (C : HomologicalComplex (ModuleCat.{w} S) c) :=
  ((restrictionFunctor f).mapHomologicalComplex c).obj C

/-- An exact augmented S-complex remains an exact augmented R-complex.
The universe of M is large enough for both ordinary resolution conventions. -/
def restrictionResolution (f : R →+* S) (M : Type (max u v w))
    [AddCommGroup M] [Module S M] (Q : LeftResolution S M) :
    LeftResolution R (Restricted f M) where
  complex := restrictionComplex f (ComplexShape.down ℕ) Q.complex
  ε := Restricted.map f (M := Q.complex.X 0) (N := M) Q.ε
  surjective := Q.surjective
  exact_zero := by
    ext a
    exact Iff.of_eq (congrArg (fun T : Submodule S (Q.complex.X 0) => Restricted.val f (Q.complex.X 0) a ∈ T) Q.exact_zero)
  exact_succ n := by
    ext a
    exact Iff.of_eq (congrArg (fun T : Submodule S (Q.complex.X (n+1)) => Restricted.val f (Q.complex.X (n+1)) a ∈ T)
      (Q.exact_succ n))

variable (f : R →+* S) (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]

/-- The required descended action is specified by right multiplication on S. -/
structure ExtensionAction where
  module : Module Sᵐᵒᵖ (Tensor R A (Restricted f S))
  formula : letI := module
    ∀ (s t : S) (a : A),
      MulOpposite.op t • tmul R a (Restricted.of f S s) =
        tmul R a (Restricted.of f S (s*t))

/-- Extension of a map, including linearity for the unused right S action. -/
def ExtensionMapProperty (a : ExtensionAction f A)
    {B : Type x} [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (b : ExtensionAction f B) (g : A →ₗ[Rᵐᵒᵖ] B) : Prop :=
  letI := a.module
  letI := b.module
  ∃ h : Tensor R A (Restricted f S) →ₗ[Sᵐᵒᵖ] Tensor R B (Restricted f S),
    ∀ x s, h (tmul R x (Restricted.of f S s)) = tmul R (g x) (Restricted.of f S s)

/-- The reassociation has both source formulas, rather than just an unspecified
isomorphism of abelian groups. -/
def ReassociationProperty (a : ExtensionAction f A)
    (M : Type x) [AddCommGroup M] [Module S M] : Prop :=
  letI := a.module
  ∃ e : Tensor S (Tensor R A (Restricted f S)) M ≃+ Tensor R A (Restricted f M),
    (∀ x s y, e (tmul S (tmul R x (Restricted.of f S s)) y) =
      tmul R x (Restricted.of f M (s • y))) ∧
    (∀ x y, e.symm (tmul R x (Restricted.of f M y)) =
      tmul S (tmul R x (Restricted.of f S 1)) y)

/-- An actual complex of right S-modules, with the original balanced tensor
terms and differentials. Its homology therefore carries a right S-action. -/
structure ExtensionComplexData
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) where
  action : ∀ n, ExtensionAction f (C.X n)
  complex : ChainComplex (ModuleCat.{max w v} Sᵐᵒᵖ) ℕ
  termEquiv : ∀ n, complex.X n ≃+ Tensor R (C.X n) (Restricted f S)
  linear : ∀ n, letI := (action n).module
    ∀ (s : Sᵐᵒᵖ) z, termEquiv n (s • z) = s • termEquiv n z
  differential : ∀ m n z,
    termEquiv n ((complex.d m n).hom z) =
      P103.Specs.Ch11.ExtTorDefinitions.tensorMap (C.d m n).hom LinearMap.id (termEquiv m z)

open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions

/-- The original Tor quotient and the homology of the right S-module complex
are identified on representatives, not merely as abstract abelian groups. -/
structure InnerHomologyData (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    extends ExtensionComplexData f C where
  homologyEquiv : ∀ n, Homology complex n ≃ₗ[ℤ]
    Homology (tensorComplex C (Restricted f S)) n
  representative : ∀ n (z : cycles complex n),
    ∃ t : cycles (tensorComplex C (Restricted f S)) n,
      t.val = termEquiv n z.val ∧
      homologyEquiv n (homologyClass complex n z) =
        homologyClass (tensorComplex C (Restricted f S)) n t

/-- Varying the left coefficient of the original right tensor complex. -/
def tensorCoefficientComplex (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) :
    ModuleCat.{x} R ⥤ ChainComplex (ModuleCat.{max w x} ℤ) ℕ where
  obj M := tensorComplex C M
  map g := tensorSecondMap C g.hom
  map_id _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  map_comp _ _ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl

instance tensorCoefficientComplex_additive (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) :
    (tensorCoefficientComplex C : ModuleCat.{x} R ⥤ _).Additive where
  map_add := by
    intro M N g h
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    exact tmul_add _ _ _

/-- Horizontal homology, with the original left-resolution index first.
This is the unsigned first-page complex in the coefficient direction. -/
abbrev rowHomologyComplex (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{max v x} S) ℕ) (q : ℕ) :=
  ((((restrictionFunctor f ⋙ tensorCoefficientComplex C) ⋙
    P103.Specs.Ch10.Comparison.quotientHomology (ComplexShape.down ℕ) q).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj Q)

/-- The first homology computation uses flatness over S. The action on
its first tensor factor is the same action carried by the inner Tor quotient. -/
structure HorizontalHomologyData (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (M : Type (max v x)) [AddCommGroup M] [Module S M] (n : ℕ) where
  inner : InnerHomologyData f C
  module : Module Sᵐᵒᵖ (Homology (tensorComplex C (Restricted f S)) n)
  linear : letI := module
    ∀ (s : Sᵐᵒᵖ) z, inner.homologyEquiv n (s • z) = s • inner.homologyEquiv n z
  equiv : letI := module
    Tensor S (Homology (tensorComplex C (Restricted f S)) n) M ≃ₗ[ℤ]
      Homology (tensorComplex C (Restricted f M)) n

/-- The total augmentation actually computes the original chosen-resolution
Tor, without supposing that the restricted left resolution is projective. -/
structure TargetComparisonData
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (M : Type (max u v x)) [AddCommGroup M] [Module S M]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution S M) where
  augmentation : P103.Specs.Ch11.TorBalance.ordinaryTotal P.complex
    (restrictionResolution f M Q).complex ⟶ tensorComplex P.complex (Restricted f M)
  quasi : QuasiIsomorphism augmentation
  zero : ∀ p (a : P.complex.X p) (b : (restrictionResolution f M Q).complex.X 0),
    (augmentation.f p).hom
      (P103.Specs.Ch11.TorBalance.ordinaryInclusion P.complex
        (restrictionResolution f M Q).complex p 0 p (by omega) (tmul R a b)) =
      tmul R a ((restrictionResolution f M Q).ε b)
  positive : ∀ (p q n : ℕ) (h : p+q=n), q ≠ 0 →
    (augmentation.f n).hom.comp
      (P103.Specs.Ch11.TorBalance.ordinaryInclusion P.complex
        (restrictionResolution f M Q).complex p q n h) = 0

section HomologicalIndexing
variable {V : Type a} [Category.{b} V] [Abelian V]
variable {T : CochainComplex V ℤ} (F : Filtration T) (D : F03Specs.PageData F)

/-- Total chain degree is `n`, and the increasing filtration index is `p`. -/
abbrev chainPage (r p n : ℤ) := PageCohomology.object F D r (-p) (-n)

def chainDifferential (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    chainPage F D r p n ⟶ chainPage F D r (p-r) (n-1) :=
  D.differential r hr (-p) (-n) ≫ eqToHom (by
    congr 1 <;> omega)

/-- The short complex computing the next chain page, centered at `(p,n)`. -/
abbrev chainPageShortComplex (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :=
  PageCohomology.shortComplex F D r hr (-p-r) (-n-1)

/-- The target filtration is increasing after the change of indexing. -/
abbrev chainTargetPiece (p n : ℤ) :=
  FiniteFiltrationConvergence.cohomologyPiece F (-p) (-n)


end HomologicalIndexing

section SpectralPages
open P103.Specs.Ch11.TorBalance
open CategoryTheory.Limits
open FiniteDiagonalFiltrations DoubleTotalization DoubleComplexFirstPages

/-- Reversing integer chain indices, retaining both commuting differentials. -/
def chainToCochainBicomplex {A : Type u} [Category.{v} A] [Preadditive A]
    (K : HomologicalComplex₂ A (ComplexShape.down ℤ) (ComplexShape.down ℤ)) : Bicomplex A :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun i => (K.X (-i.1)).X (-i.2))
    (fun p p' q => (K.d (-p) (-p')).f (-q))
    (fun p q q' => (K.X (-p)).d (-q) (-q'))
    (by intro p p' h q; apply K.shape_f; intro h'; apply h; simp only [ComplexShape.down_Rel, ComplexShape.up_Rel] at *; omega)
    (by intro p q q' h; apply HomologicalComplex.shape; intro h'; apply h; simp only [ComplexShape.down_Rel, ComplexShape.up_Rel] at *; omega)
    (by intros; apply HomologicalComplex₂.d_f_comp_d_f)
    (by intros; apply HomologicalComplex.d_comp_d)
    (by intros; apply HomologicalComplex₂.d_comm)

/-- The tensor bicomplex in the source, now in the negative cochain quadrant. -/
abbrev tensorCochainBicomplex
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{x} R) ℕ) :=
  chainToCochainBicomplex (tensorBicomplex (extendNonnegativeChain C) (extendNonnegativeChain D))


/-- The actual row filtration and its full sequence of quotient pages.
The negative cochain indices give homological chain indices after reversal. -/
structure TensorPagesData
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{x} R) ℕ)
    [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)] where
  filtration : Filtration (sumTotal (tensorCochainBicomplex C Q))
  formula : HasFiltrationFormula (tensorCochainBicomplex C Q) Prod.snd filtration
  pages : F03Specs.PageData filtration
  cohomology : PageCohomology.Data filtration pages
  firstPages : RowData (tensorCochainBicomplex C Q) filtration formula pages
  convergence : DoubleComplexConvergence.Converges filtration

/-- Place chain degree `n` in cochain degree `-n`. -/
def negativeChainEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ) where
  f n := -(n : ℤ)
  injective_f := by
    intro m n h
    change -(m : ℤ) = -(n : ℤ) at h
    omega
  rel {m n} h := by
    change n + 1 = m at h
    change -(m : ℤ) + 1 = -(n : ℤ)
    omega

/-- The categorical homology comparison with the explicit P103 quotient. -/
def quotientHomologyIso {B : Type a} [Ring B] {ι : Type b} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{w} B) c) (n : ι) :
    K.homology n ≅ ModuleCat.of B (Homology K n) := by
  have hr : LinearMap.range (K.sc n).moduleCatToCycles = cycleBoundaries K n := by
    ext z
    change (∃ x, (K.sc n).moduleCatToCycles x = z) ↔
      ∃ x, (K.d (c.prev n) n).hom x = z.val
    exact ⟨fun ⟨x, hx⟩ => ⟨x, congrArg Subtype.val hx⟩,
      fun ⟨x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  exact (K.sc n).moduleCatHomologyIso ≪≫
    eqToIso (congrArg (fun T : Submodule B (cycles K n) =>
      ModuleCat.of B (cycles K n ⧸ T)) hr)

/-- A representative of a categorical homology class, using the actual cycles. -/
def explicitClass {B : Type a} [Ring B] {ι : Type b} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{w} B) c) (n : ι) (z : cycles K n) :
    K.homology n :=
  (K.homologyπ n).hom ((K.sc n).moduleCatCyclesIso.inv.hom z)

/-- At each active bidegree the zero extension identifies the original tensor. -/
def tensorSummand
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{x} R) ℕ) (i j : ℕ) :
    Tensor R (C.X i) (D.X j) →ₗ[ℤ]
      ↥(((tensorCochainBicomplex C D).X (-(i : ℤ))).X (-(j : ℤ))) :=
  tensorMap
    (C.extendXIso nonnegativeChainEmbedding (i := i) (i' := -(-(i : ℤ)))
      (by change (i : ℤ) = -(-(i : ℤ)); omega)).inv.hom
    (D.extendXIso nonnegativeChainEmbedding (i := j) (i' := -(-(j : ℤ)))
      (by change (j : ℤ) = -(-(j : ℤ)); omega)).inv.hom

/-- The signed total of the zero extensions and the original signed total,
with all summand maps specified. -/
structure TotalRegrading
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{x} R) ℕ)
    [(tensorCochainBicomplex C D).HasTotal (ComplexShape.up ℤ)] where
  iso : sumTotal (tensorCochainBicomplex C D) ≅
    (ordinaryTotal C D).extend negativeChainEmbedding
  on_summands : ∀ (i j n : ℕ) (h : i+j=n) (z : Tensor R (C.X i) (D.X j)),
    (iso.hom.f (-(n : ℤ))).hom
      ((sumInjection (tensorCochainBicomplex C D) (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ))
        (by omega)).hom (tensorSummand C D i j z)) =
      ((ordinaryTotal C D).extendXIso negativeChainEmbedding (i := n) rfl).inv.hom
        (ordinaryInclusion C D i j n h z)

/-- The horizontal homology comparison uses tensor reassociation and sends the
tensor of an inner cycle class and a coefficient to the reassociated cycle class.
It is a map of the unsigned row complexes, to be composed with the signed
page comparison. -/
structure RowTensorComparison
    (C : ChainComplex (ModuleCat.{max u w} Rᵐᵒᵖ) ℕ)
    (D : ChainComplex (ModuleCat.{max u v x} S) ℕ)
    (inner : InnerHomologyData f C) (q : ℕ)
    [Module Sᵐᵒᵖ (Homology (tensorComplex C (Restricted f S)) q)] where
  reassociate : ∀ p : ℕ, letI := (inner.action q).module
    Tensor S (Tensor R (C.X q) (Restricted f S)) (D.X p) ≃+
      Tensor R (C.X q) (Restricted f (D.X p))
  on_tensors : ∀ (p : ℕ) (a : C.X q) (s : S) (b : D.X p),
    letI := (inner.action q).module
    reassociate p (tmul S (tmul R a (Restricted.of f S s)) b) =
      tmul R a (Restricted.of f (D.X p) (s • b))
  iso : (leftOrdinaryTensorComplex (Homology (tensorComplex C (Restricted f S)) q) D).extend
      negativeChainEmbedding ≅
    verticalHomology (tensorCochainBicomplex C
      (restrictionComplex f (ComplexShape.down ℕ) D)).flip (-(q : ℤ))
  on_classes : ∀ (p : ℕ) (z : cycles (tensorComplex C (Restricted f S)) q)
      (b : D.X p), letI := (inner.action q).module
    let L := leftOrdinaryTensorComplex (Homology (tensorComplex C (Restricted f S)) q) D
    let D' := restrictionComplex f (ComplexShape.down ℕ) D
    let K := (tensorCochainBicomplex C D').flip.X (-(p : ℤ))
    ∃ t : cycles K (-(q : ℤ)),
      t.val = tensorSummand C D' q p (reassociate p (tmul S z.val b)) ∧
      (iso.hom.f (-(p : ℤ))).hom
          ((L.extendXIso negativeChainEmbedding (i := p) rfl).inv.hom
            (tmul S (homologyClass (tensorComplex C (Restricted f S)) q z) b)) =
        explicitClass K (-(q : ℤ)) t

/-- The change-of-rings sequence with chosen projective resolutions.
The outer Tor is identified with every projective right resolution of the
specified inner Tor module, rather than with an unspecified abelian group. -/
structure ResolvedSequenceData
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (M : Type (max u v x)) [AddCommGroup M] [Module S M]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution S M)
    [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
      (ComplexShape.up ℤ)]
    extends TensorPagesData P.complex (restrictionResolution f M Q).complex where
  inner : InnerHomologyData f P.complex
  innerModule : ∀ q : ℕ, Module Sᵐᵒᵖ (TorWith P (Restricted f S) q)
  innerLinear : ∀ q, letI := innerModule q
    ∀ (s : Sᵐᵒᵖ) z, inner.homologyEquiv q (s • z) = s • inner.homologyEquiv q z
  totalRegrading : TotalRegrading P.complex (restrictionResolution f M Q).complex
  augmentation : TargetComparisonData f A M P Q
  rowTensor : ∀ q : ℕ, letI := innerModule q
    RowTensorComparison f P.complex Q.complex inner q
  balance : ∀ q : ℕ, letI := innerModule q
    ∀ (U : LeftResolution Sᵐᵒᵖ (TorWith P (Restricted f S) q)), U.IsProjective →
      ∃ α : Augmentations U Q, QuasiIsomorphism α.left ∧ QuasiIsomorphism α.right
  firstQuadrant : ∀ r p q : ℤ, 0 ≤ r → p < 0 ∨ q < 0 →
    IsZero (chainPage (V := ModuleCat.{max u v w x} ℤ) filtration pages r p (p+q))

namespace ResolvedSequenceData

variable {A : Type w} [AddCommGroup A] [Module Rᵐᵒᵖ A]
  {M : Type (max u v x)} [AddCommGroup M] [Module S M]
  {P : LeftResolution Rᵐᵒᵖ A} {Q : LeftResolution S M}
  [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
    (ComplexShape.up ℤ)]
  {f} (E : ResolvedSequenceData f A M P Q)

/-- The abutment map is the homology of the summand-preserving regrading
and the actual degree-zero augmentation. -/
def targetIso (n : ℕ) :
    (sumTotal (tensorCochainBicomplex P.complex
      (restrictionResolution f M Q).complex)).homology (-(n : ℤ)) ≅
      ModuleCat.of ℤ (TorWith P (Restricted f M) n) :=
  HomologicalComplex.homologyMapIso E.totalRegrading.iso (-(n : ℤ)) ≪≫
    (ordinaryTotal P.complex (restrictionResolution f M Q).complex).extendHomologyIso
      negativeChainEmbedding (j := n) rfl ≪≫
    quotientHomologyIso _ n ≪≫
    (LinearEquiv.ofBijective (homologyMap E.augmentation.augmentation n)
      (E.augmentation.quasi n)).toModuleIso

/-- The signed row-page comparison, the horizontal flat tensor comparison,
and canonical Tor balance determine the second-page map. -/
def secondIso (p q : ℕ) :
    letI := E.innerModule q
    ∀ (U : LeftResolution Sᵐᵒᵖ (TorWith P (Restricted f S) q)), U.IsProjective →
      (chainPage (V := ModuleCat.{max u v w x} ℤ) E.filtration E.pages 2 p (p+q) ≅
        ModuleCat.of ℤ (TorWith U M p)) := by
  letI := E.innerModule q
  intro U hU
  let α := (E.balance q U hU).choose
  have hL : QuasiIsomorphism α.left := (E.balance q U hU).choose_spec.1
  have hR : QuasiIsomorphism α.right := (E.balance q U hU).choose_spec.2
  let L := leftOrdinaryTensorComplex (TorWith P (Restricted f S) q) Q.complex
  refine eqToIso ?_ ≪≫ E.firstPages.secondIso (-(p : ℤ)) (-(q : ℤ)) ≪≫
    HomologicalComplex.homologyMapIso (E.rowTensor q).iso.symm (-(p : ℤ)) ≪≫
    L.extendHomologyIso negativeChainEmbedding (j := p) rfl ≪≫
    quotientHomologyIso L p ≪≫ (balanceEquiv α hL hR p).symm.toModuleIso
  change PageCohomology.object E.filtration E.pages 2 (-(p : ℤ)) (-(p+q : ℤ)) =
    PageCohomology.object E.filtration E.pages 2 (-(p : ℤ)) (-(p : ℤ) + -(q : ℤ))
  congr 1
  omega

end ResolvedSequenceData

end SpectralPages

namespace Specs

/-- A totalization and its row pages exist without any flatness assumption. -/
def TensorTotalExists : Prop :=
  ∀ (R : Type u) [Ring R]
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{x} R) ℕ),
    (tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)

def TensorPages : Prop :=
  ∀ (R : Type u) [Ring R]
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (Q : ChainComplex (ModuleCat.{x} R) ℕ),
    ∀ [(tensorCochainBicomplex C Q).HasTotal (ComplexShape.up ℤ)],
      Nonempty (TensorPagesData C Q)


/-- The resolved existence and convergence part of HA-B07.
Naturality from E₂ onward is an additional obligation. -/
def ResolvedSequence : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (M : Type (max u v x)) [AddCommGroup M] [Module S M]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution S M),
    P.IsProjective → Q.IsProjective →
    ∀ [(tensorCochainBicomplex P.complex (restrictionResolution f M Q).complex).HasTotal
      (ComplexShape.up ℤ)], Nonempty (ResolvedSequenceData f A M P Q)

def HorizontalHomology : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ)
    (M : Type (max v x)) [AddCommGroup M] [Module S M],
    P103.Specs.Ch02.FlatnessTests.Flat.{v,max v x,max w v} S M →
    ∀ n : ℕ, Nonempty (HorizontalHomologyData f C M n)

def TargetComparison : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (M : Type (max u v x)) [AddCommGroup M] [Module S M]
    (P : LeftResolution Rᵐᵒᵖ A) (Q : LeftResolution S M),
    P.IsProjective → Nonempty (TargetComparisonData f A M P Q)

/-- Compatibility with arbitrary maps of both tensor factors. In particular,
applying this to either differential gives the two required chain squares. -/
def ReassociationNaturality : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A B : Type w) [AddCommGroup A] [AddCommGroup B]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B]
    (M N : Type x) [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    (a : ExtensionAction f A) (b : ExtensionAction f B),
    letI := a.module
    letI := b.module
    ∀ (g : A →ₗ[Rᵐᵒᵖ] B) (h : M →ₗ[S] N)
      (k : Tensor R A (Restricted f S) →ₗ[Sᵐᵒᵖ] Tensor R B (Restricted f S))
      (_hk : ∀ x s, k (tmul R x (Restricted.of f S s)) =
        tmul R (g x) (Restricted.of f S s))
      (e : Tensor S (Tensor R A (Restricted f S)) M ≃+ Tensor R A (Restricted f M))
      (e' : Tensor S (Tensor R B (Restricted f S)) N ≃+ Tensor R B (Restricted f N))
      (_he : ∀ x s y, e (tmul S (tmul R x (Restricted.of f S s)) y) =
        tmul R x (Restricted.of f M (s • y)))
      (_he' : ∀ x s y, e' (tmul S (tmul R x (Restricted.of f S s)) y) =
        tmul R x (Restricted.of f N (s • y))) (z),
      e' (P103.BalancedTensor.map k h z) =
        P103.BalancedTensor.map g (Restricted.map f h) (e z)

/-- The right S-action is on the existing P103 Tor quotient. The equivalence
from the complex of right S-modules is S-linear for this action. -/
def InnerTorAction : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ) (n : ℕ),
    ∃ (D : InnerHomologyData f C)
      (m : Module Sᵐᵒᵖ (Homology (tensorComplex C (Restricted f S)) n)),
      letI := m
      ∀ (s : Sᵐᵒᵖ) z, D.homologyEquiv n (s • z) = s • D.homologyEquiv n z

def InnerHomology : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ), Nonempty (InnerHomologyData f C)

def ExtensionComplex : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (C : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ), Nonempty (ExtensionComplexData f C)

/-- Simultaneous choices of the action, functorial maps, and reassociation,
valid for every unital ring map, without a flatness hypothesis. -/
def TensorAlgebra : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S)
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    ∃ a : ExtensionAction f A,
      (∀ (B : Type w) [AddCommGroup B] [Module Rᵐᵒᵖ B]
        (g : A →ₗ[Rᵐᵒᵖ] B), ∃ b : ExtensionAction f B, ExtensionMapProperty f A a b g) ∧
      ∀ (M : Type x) [AddCommGroup M] [Module S M], ReassociationProperty f A a M
end Specs
end AdvancedHomologicalAlgebra.ChangeOfRingsTor

namespace AdvancedHomologicalAlgebra.ChangeOfRingsTor
open CategoryTheory
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open FiniteDiagonalFiltrations DoubleTotalization

/-- Canonical map for simultaneous reversal of the two chain indices. -/
def chainToCochainBicomplexMap
    {V : Type a} [Category.{b} V] [Preadditive V]
    {K L : HomologicalComplex₂ V (ComplexShape.down ℤ) (ComplexShape.down ℤ)}
    (φ : K ⟶ L) : chainToCochainBicomplex K ⟶ chainToCochainBicomplex L where
  f p :=
    { f q := (φ.f (-p)).f (-q)
      comm' q q' _ := (φ.f (-p)).comm (-q) (-q') }
  comm' p p' _ := by
    ext q
    exact congrArg (fun z => z.f (-q)) (φ.comm (-p) (-p'))

abbrev tensorCochainBicomplexMap
    {R : Type u} [Ring R]
    {C C' : ChainComplex (ModuleCat.{w} Rᵐᵒᵖ) ℕ}
    {Q Q' : ChainComplex (ModuleCat.{x} R) ℕ}
    (l : C ⟶ C') (m : Q ⟶ Q') :
    tensorCochainBicomplex C Q ⟶ tensorCochainBicomplex C' Q' :=
  chainToCochainBicomplexMap (tensorBicomplexMap
    (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
    (HomologicalComplex.extendMap m nonnegativeChainEmbedding))

/-- The projective choices over one pair of original modules. -/
structure ResolutionPair {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (A : ModuleCat.{w} Rᵐᵒᵖ) (M : ModuleCat.{max u v x} S) where
  right : LeftResolution Rᵐᵒᵖ A
  left : LeftResolution S M
  right_projective : right.IsProjective
  left_projective : left.IsProjective
  total : (tensorCochainBicomplex right.complex
    (restrictionResolution f M left).complex).HasTotal (ComplexShape.up ℤ)
attribute [instance] ResolutionPair.total

section FullSystem
variable {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)

abbrev Resolved (A : ModuleCat.{w} Rᵐᵒᵖ) (M : ModuleCat.{max u v x} S)
    (P : ResolutionPair f A M) := ResolvedSequenceData f A M P.right P.left

/-- The target is the original Tor quotient, with the transported finite filtration. -/
def resolvedTargetPiece {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    {P : ResolutionPair f A M} (E : Resolved f A M P) (p : ℤ) (n : ℕ) :
    Subobject (ModuleCat.of ℤ (TorWith P.right (Restricted f M) n)) :=
  Subobject.mapIsoToOrderIso (E.targetIso n) (chainTargetPiece E.filtration p (n : ℤ))

/-- One canonical natural sequence for all projective choices. Laws range over
all choices of the resolutions, so comparisons and their coherence are included. -/
structure NaturalSystem where
  choices : ∀ (A : ModuleCat.{w} Rᵐᵒᵖ) (M : ModuleCat.{max u v x} S),
    Nonempty (ResolutionPair f A M)
  rowSystem : DoubleComplexFirstPages.System (ModuleCat.{max u v w x} ℤ)
  sequence : ∀ {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M), Resolved f A M P
  canonical_row : ∀ {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M)
    (hK : FiniteDiagonals (tensorCochainBicomplex P.right.complex
      (restrictionResolution f M P.left).complex)),
    (sequence P).firstPages = rowSystem.row _ hK
      (sequence P).filtration (sequence P).formula (sequence P).pages
  lifted : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex),
    FilteredMap ⟨_, (sequence P).filtration⟩ ⟨_, (sequence Q).filtration⟩
  lifted_hom : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex),
    (lifted P Q l m).hom = HomologicalComplex₂.total.map
      (tensorCochainBicomplexMap l
        (((restrictionFunctor f).mapHomologicalComplex (ComplexShape.down ℕ)).map m))
      (ComplexShape.up ℤ)
  liftedPages : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex),
    FilteredPageFunctoriality.MapData (lifted P Q l m) (sequence P).pages (sequence Q).pages
  map : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (r p n : ℤ),
    chainPage (sequence P).filtration (sequence P).pages r p n ⟶
      chainPage (sequence Q).filtration (sequence Q).pages r p n
  map_eq : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex),
    ChainLift P.right Q.right a.hom l → ChainLift P.left Q.left b.hom m →
    ∀ r p n, 2 ≤ r → map P Q a b r p n = (liftedPages P Q l m).map r (-p) (-n)
  map_id : ∀ {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) r p n, 2 ≤ r → map P P (𝟙 A) (𝟙 M) r p n = 𝟙 _
  map_comp : ∀ {A B C : ModuleCat.{w} Rᵐᵒᵖ} {M N O : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (T : ResolutionPair f C O)
    (a : A ⟶ B) (a' : B ⟶ C) (b : M ⟶ N) (b' : N ⟶ O) r p n, 2 ≤ r →
    map P T (a ≫ a') (b ≫ b') r p n = map P Q a b r p n ≫ map Q T a' b' r p n
  differential_naturality : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    r (hr : 0 ≤ r) p n, 2 ≤ r →
    map P Q a b r p n ≫ chainDifferential (sequence Q).filtration (sequence Q).pages r hr p n =
      chainDifferential (sequence P).filtration (sequence P).pages r hr p n ≫
        map P Q a b r (p-r) (n-1)
  innerMap : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (q : ℕ),
    letI := (sequence P).innerModule q
    letI := (sequence Q).innerModule q
    TorWith P.right (Restricted f S) q →ₗ[Sᵐᵒᵖ] TorWith Q.right (Restricted f S) q
  innerMap_eq : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (q : ℕ)
    (l : P.right.complex ⟶ Q.right.complex), ChainLift P.right Q.right a.hom l →
    ∀ z, innerMap P Q a q z = homologyMap (tensorFirstMap l (Restricted f S)) q z
  second_naturality : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (p q : ℕ), letI := (sequence P).innerModule q
    letI := (sequence Q).innerModule q
    ∀ (U : LeftResolution Sᵐᵒᵖ (TorWith P.right (Restricted f S) q))
      (V : LeftResolution Sᵐᵒᵖ (TorWith Q.right (Restricted f S) q))
      (hU : U.IsProjective) (hV : V.IsProjective) (k : U.complex ⟶ V.complex),
    ChainLift U V (innerMap P Q a q) k →
    map P Q a b 2 p (p+q) ≫ ((sequence Q).secondIso p q V hV).hom =
      ((sequence P).secondIso p q U hU).hom ≫
        ModuleCat.ofHom (homologyMap (tensorFirstMap k M ≫ tensorSecondMap V.complex b.hom) p)
  targetMap : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N) (n : ℕ),
    ModuleCat.of ℤ (TorWith P.right (Restricted f M) n) ⟶
      ModuleCat.of ℤ (TorWith Q.right (Restricted f N) n)
  targetMap_eq : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N) (n : ℕ)
    (l : P.right.complex ⟶ Q.right.complex), ChainLift P.right Q.right a.hom l →
    targetMap P Q a b n = ModuleCat.ofHom
      (homologyMap (tensorFirstMap l (Restricted f M) ≫
        tensorSecondMap Q.right.complex (Restricted.map f b.hom)) n)
  target_naturality : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (l : P.right.complex ⟶ Q.right.complex) (m : P.left.complex ⟶ Q.left.complex),
    ChainLift P.right Q.right a.hom l → ChainLift P.left Q.left b.hom m → ∀ n : ℕ,
    HomologicalComplex.homologyMap (lifted P Q l m).hom (-(n : ℤ)) ≫
      ((sequence Q).targetIso n).hom = ((sequence P).targetIso n).hom ≫ targetMap P Q a b n
  target_preserves : ∀ {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (Q : ResolutionPair f B N) (a : A ⟶ B) (b : M ⟶ N)
    (p : ℤ) (n : ℕ), ∃ h : (resolvedTargetPiece f (sequence P) p n : ModuleCat ℤ) ⟶
      (resolvedTargetPiece f (sequence Q) p n : ModuleCat ℤ),
    h ≫ (resolvedTargetPiece f (sequence Q) p n).arrow =
      (resolvedTargetPiece f (sequence P) p n).arrow ≫ targetMap P Q a b n
namespace NaturalSystem
variable {f}
variable (T : NaturalSystem f)

/-- Changing either resolution gives a canonical page isomorphism from E2 onward. -/
def comparison {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P Q : ResolutionPair f A M) (r p n : ℤ) (hr : 2 ≤ r) :
    chainPage (T.sequence P).filtration (T.sequence P).pages r p n ≅
      chainPage (T.sequence Q).filtration (T.sequence Q).pages r p n where
  hom := T.map P Q (𝟙 A) (𝟙 M) r p n
  inv := T.map Q P (𝟙 A) (𝟙 M) r p n
  hom_inv_id := by
    rw [← T.map_comp P Q P _ _ _ _ r p n hr]
    simpa only [Category.id_comp] using T.map_id P r p n hr
  inv_hom_id := by
    rw [← T.map_comp Q P Q _ _ _ _ r p n hr]
    simpa only [Category.id_comp] using T.map_id Q r p n hr

@[simp] theorem comparison_refl
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P : ResolutionPair f A M) (r p n : ℤ) (hr : 2 ≤ r) :
    T.comparison P P r p n hr = Iso.refl _ := by
  apply Iso.ext
  exact T.map_id P r p n hr

theorem comparison_trans
    {A : ModuleCat.{w} Rᵐᵒᵖ} {M : ModuleCat.{max u v x} S}
    (P Q U : ResolutionPair f A M) (r p n : ℤ) (hr : 2 ≤ r) :
    T.comparison P Q r p n hr ≪≫ T.comparison Q U r p n hr =
      T.comparison P U r p n hr := by
  apply Iso.ext
  change T.map P Q (𝟙 A) (𝟙 M) r p n ≫ T.map Q U (𝟙 A) (𝟙 M) r p n = _
  rw [← T.map_comp P Q U _ _ _ _ r p n hr]
  simp only [Category.id_comp]
  rfl

theorem comparison_naturality
    {A B : ModuleCat.{w} Rᵐᵒᵖ} {M N : ModuleCat.{max u v x} S}
    (P P' : ResolutionPair f A M) (Q Q' : ResolutionPair f B N)
    (a : A ⟶ B) (b : M ⟶ N) (r p n : ℤ) (hr : 2 ≤ r) :
    T.map P Q a b r p n ≫ (T.comparison Q Q' r p n hr).hom =
      (T.comparison P P' r p n hr).hom ≫ T.map P' Q' a b r p n := by
  change T.map P Q a b r p n ≫ T.map Q Q' (𝟙 B) (𝟙 N) r p n =
    T.map P P' (𝟙 A) (𝟙 M) r p n ≫ T.map P' Q' a b r p n
  rw [← T.map_comp P Q Q' _ _ _ _ r p n hr,
    ← T.map_comp P P' Q' _ _ _ _ r p n hr]
  simp only [Category.comp_id, Category.id_comp]
end NaturalSystem

end FullSystem
namespace Specs
/-- Full naturality with f fixed, including coherent changes of projective choices. -/
def NaturalSequence : Prop := ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (f : R →+* S), Nonempty (NaturalSystem.{u,v,w,x} f)
end Specs
end AdvancedHomologicalAlgebra.ChangeOfRingsTor
