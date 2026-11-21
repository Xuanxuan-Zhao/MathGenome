import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! HA-B06, source lines 1034–1085.
The tensor is the actual noncommutative P103 balanced tensor. The row index
is the resolution index. Negating both integer indices converts increasing
chain filtrations into the existing decreasing cochain filtrations.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Classical
universe u v w
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

/-- Index reversal, expressed at the level of shapes. -/
def reversal : (ComplexShape.up ℤ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => -n) neg_injective (by
    intro i j
    simp only [ComplexShape.up_Rel, ComplexShape.down_Rel]
    omega)

instance : reversal.IsRelIff := inferInstanceAs
  ((ComplexShape.Embedding.mk' (ComplexShape.up ℤ) (ComplexShape.down ℤ)
    (fun n => -n) neg_injective _).IsRelIff)

abbrev reverseChain {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    (P : ChainComplex A ℤ) : CochainComplex A ℤ := P.restriction reversal

/-- Homology under the standard reversal of integer degrees. -/
def reverseHomologyIso {A : Type*} [Category* A] [Abelian A]
    (P : ChainComplex A ℤ) (b : ℤ) : (reverseChain P).homology b ≅ P.homology (-b) :=
  P.restrictionHomologyIso reversal _ b _ rfl rfl
    (i' := -b+1) (k' := -b-1)
    (by
      rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (b-1) b by
        simp only [ComplexShape.up_Rel]; omega)]
      change -(b-1) = -b+1
      omega)
    rfl
    (by
      rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel b (b+1) by
        simp only [ComplexShape.up_Rel])]
      change -(b+1) = -b-1
      omega)
    ((ComplexShape.down ℤ).prev_eq' (by change -b + 1 = -b + 1; rfl))
    ((ComplexShape.down ℤ).next_eq' (by change (-b - 1) + 1 = -b; omega))

variable {R : Type u} [Ring R]

/-- Original chain complex; its lower bound may be any integer. -/
def BoundedBelow (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (L : ℤ) : Prop :=
  ∀ i, i < L → IsZero (P.X i)

/-- Flatness is in the right-module orientation, tested against left modules. -/
def FlatTerms (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) : Prop :=
  ∀ i, P103.Specs.Ch02.FlatnessTests.RightFlat.{u,v,w} R (P.X i)

/-- The unsigned tensor bicomplex after both indices have been negated.
The horizontal index is the P index and the vertical index the Q index. -/
abbrev tensorCochain (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) : Bicomplex (ModuleCat.{max v w} ℤ) :=
  ((reversal.restrictionFunctor (ModuleCat.{max v w} ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj ((tensorBicomplex P Q).restriction reversal)

/-- The simultaneous map in both factors, on the same balanced tensor. -/
def tensorCochainMap
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorCochain P Q ⟶ tensorCochain P' Q' :=
  ((reversal.restrictionFunctor (ModuleCat.{max v w} ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (HomologicalComplex.restrictionMap (tensorBicomplexMap f g) reversal)

abbrev coefficientComplex (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) : ChainComplex (ModuleCat.{max v w} ℤ) ℤ :=
  ((tensorFunctor M).mapHomologicalComplex (ComplexShape.down ℤ)).obj P

def coefficientComplexMap
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ N) :
    coefficientComplex P M ⟶ coefficientComplex P' N where
  f i := ModuleCat.ofHom (tensorMap (f.f i).hom g.hom)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a m
    change _ = _
    have hf := congrArg ModuleCat.Hom.hom (f.comm i j)
    exact congrArg (fun t => P103.BalancedTensor.tmul R t (g.hom m))
      (LinearMap.congr_fun hf a)


/-- One realization of the actual row-filtered spectral sequence, before the
Tor identification and the comparison to the augmented target are supplied. -/
structure TensorPages (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) where
  filtration : Filtration (sumTotal (tensorCochain P Q))
  formula : HasFiltrationFormula (tensorCochain P Q) Prod.snd filtration
  pages : F03Specs.PageData filtration
  next : PageCohomology.Data filtration pages
  convergence : DoubleComplexConvergence.Converges filtration

/-- Homological indices, with the resolution index first. -/
abbrev TensorPages.term {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q) (r p q : ℤ) :=
  PageCohomology.object S.filtration S.pages r (-p) (-(p+q))

/-- Negating the filtration and total degrees gives homological bidegree
`(-r,r-1)` for the canonical page differential. -/
def homologicalPageDifferential {A : Type*} [Category* A] [Abelian A]
    {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    PageCohomology.object F D r (-p) (-(p+q)) ⟶
      PageCohomology.object F D r (-(p-r)) (-((p-r)+(q+r-1))) :=
  D.differential r hr (-p) (-(p+q)) ≫ eqToHom (by
    unfold PageCohomology.object; congr 1 <;> omega)

/-- Reindexing the cochain differential gives bidegree `(-r,r-1)`. -/
def TensorPages.differential {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    S.term r p q ⟶ S.term r (p-r) (q+r-1) :=
  homologicalPageDifferential S.filtration S.pages r hr p q

section Transport
open FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y : A}

def transportedSubobjectIso (e : X ≅ Y) (S : Subobject X) :
    (S : A) ≅ ((Subobject.map e.hom).obj S : A) :=
  (Subobject.isoOfEqMk _ (S.arrow ≫ e.hom) (by
    conv_lhs => rw [← Subobject.mk_arrow S]
    rw [Subobject.map_mk])).symm

@[reassoc (attr := simp)]
theorem transportedSubobjectIso_arrow (e : X ≅ Y) (S : Subobject X) :
    (transportedSubobjectIso e S).hom ≫ ((Subobject.map e.hom).obj S).arrow =
      S.arrow ≫ e.hom := by
  exact Subobject.ofMkLE_arrow _

variable {K : CochainComplex A ℤ} (F : Filtration K) (n : ℤ) (H : A)
  (e : K.homology (-n) ≅ H)

/-- Increasing homological image filtration transported by the target comparison. -/
def transportedPiece (p : ℤ) : Subobject H :=
  (Subobject.map e.hom).obj (cohomologyPiece F (-p) (-n))

theorem transportedPiece_increasing (p : ℤ) :
    transportedPiece F n H e (p-1) ≤ transportedPiece F n H e p := by
  apply (Subobject.map e.hom).monotone
  simpa only [show -(p-1) = -p+1 by omega] using
    cohomologyPiece_decreasing F (-p) (-n)

abbrev transportedGraded (p : ℤ) : A :=
  cokernel (Subobject.ofLE _ _ (transportedPiece_increasing F n H e p))

def transportedGradedIso (p : ℤ) :
    gradedCohomology F (-p) (-n) ≅ transportedGraded F n H e p := by
  have hp : (-p)+1 = -(p-1) := by omega
  let i := Subobject.isoOfEq (cohomologyPiece F ((-p)+1) (-n))
    (cohomologyPiece F (-(p-1)) (-n)) (by rw [hp]) ≪≫
      transportedSubobjectIso e (cohomologyPiece F (-(p-1)) (-n))
  let j := transportedSubobjectIso e (cohomologyPiece F (-p) (-n))
  refine cokernel.mapIso _ _ i j ?_
  apply (cancel_mono (transportedPiece F n H e p).arrow).1
  dsimp only [i, j, transportedPiece, Subobject.mapIsoToOrderIso]
  simp only [Iso.trans_hom, Category.assoc, Subobject.ofLE_arrow,
    Subobject.isoOfEq_hom, transportedSubobjectIso_arrow, Subobject.ofLE_arrow_assoc]

end Transport

/-- Homology of the original coefficient complex, placed in the common
universe needed by ordinary projective resolutions. -/
abbrev targetHomology (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (n : ℤ) : ModuleCat.{max u v w} ℤ :=
  ModuleCat.of ℤ (ULift.{u} (Homology (coefficientComplex P M) n))

/-- The prescribed map on the original coefficient-complex homology. -/
def targetHomologyMap {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ N) (n : ℤ) :
    targetHomology P M n ⟶ targetHomology P' N n :=
  (ModuleCat.uliftFunctor.{u} ℤ).map
    (ModuleCat.ofHom (homologyMap (coefficientComplexMap f g) n))

/-- The left-resolution tensor complex in the cochain row index. -/
abbrev rowTensorComplex (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (b : ℤ) :=
  reverseChain (leftTensorComplex (P.homology (-b)) Q)

/-- The first page comparison before removing the sign of the row differential. -/
def rowTensorHomologyIso (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (e : AdvancedHomologicalAlgebra.TorBalance.HomologyComparison
      (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ)) :
    ((tensorCochain P Q).flip.X a).homology b ≅ (rowTensorComplex P Q b).X a :=
  (e.equivalence ((reverseChain P).sc b)).symm ≪≫
    (tensorFunctor (Q.X (-a))).mapIso (reverseHomologyIso P b)

/-- The first-page isomorphism on the actual row filtration determines the
induced map on second-page homology after removing the row differential sign. -/
structure RowTensorComparison (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (S : TensorPages P Q) where
  row : DoubleComplexFirstPages.RowData (tensorCochain P Q)
    S.filtration S.formula S.pages
  flatComparison : ∀ a : ℤ, AdvancedHomologicalAlgebra.TorBalance.HomologyComparison
    (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ)
  shortIso : ∀ a b : ℤ, PageCohomology.shortComplex S.filtration S.pages
    1 (by omega) (a-1) (a+b-1) ≅ (rowTensorComplex P Q b).sc a
  middle_formula : ∀ a b : ℤ, (shortIso a b).hom.τ₂ =
    (a*b).negOnePow • (eqToHom (by
      change PageCohomology.object S.filtration S.pages 1 (a-1+1) (a+b-1+1) =
        PageCohomology.object S.filtration S.pages 1 a (a+b)
      congr 1 <;> omega) ≫ (row.firstIso a b).hom ≫
      (rowTensorHomologyIso P Q a b (flatComparison a)).hom)

/-- The canonical extension-by-zero comparison and the original P103
quotient model, with their maps fixed on original terms and cycles. -/
structure OrdinaryTensorComparison (A : ModuleCat.{v} Rᵐᵒᵖ)
    (Q : ChainComplex (ModuleCat.{w} R) ℕ) where
  extension : leftTensorComplex A (extendNonnegativeChain Q) ≅
    extendNonnegativeChain (leftOrdinaryTensorComplex A Q)
  extension_formula : ∀ p : ℕ,
    (extension.hom.f p) ≫
      ((leftOrdinaryTensorComplex A Q).extendXIso nonnegativeChainEmbedding (i := p) rfl).hom =
    (leftTensorFunctor A).map (Q.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom
  quotient : ∀ p : ℕ, (leftOrdinaryTensorComplex A Q).homology p ≅
    ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex A Q) p)
  quotient_formula : ∀ (p : ℕ) (x : (leftOrdinaryTensorComplex A Q).cycles p),
    (quotient p).hom ((leftOrdinaryTensorComplex A Q).homologyπ p x) =
      homologyClass (leftOrdinaryTensorComplex A Q) p
        (((leftOrdinaryTensorComplex A Q).sc p).moduleCatCyclesIso.hom x)

/-- The signed row computation gives the original ordinary tensor homology,
before any identification with a chosen Tor model. -/
def RowTensorComparison.ordinaryHomologyIso
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℕ}
    {S : TensorPages P (extendNonnegativeChain Q)}
    (C : RowTensorComparison P (extendNonnegativeChain Q) S)
    (p : ℕ) (q : ℤ) (ord : OrdinaryTensorComparison (P.homology q) Q) :
    S.term 2 p q ≅ ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex (P.homology q) Q) p) := by
  let a : ℤ := -(p : ℤ)
  let b : ℤ := -q
  refine eqToIso ?_ ≪≫ S.next.nextIso 1 (by omega) (a-1) (a+b-1) ≪≫
    ShortComplex.homologyMapIso (C.shortIso a b) ≪≫ ?_
  · unfold TensorPages.term PageCohomology.object a b
    congr 1 <;> omega
  · let eqb : -b = q := neg_neg q
    let e : leftTensorComplex (P.homology (-b)) (extendNonnegativeChain Q) ≅
        extendNonnegativeChain (leftOrdinaryTensorComplex (P.homology q) Q) :=
      eqToIso (by rw [eqb]) ≪≫ ord.extension
    exact reverseHomologyIso _ a ≪≫
      (HomologicalComplex.homologyFunctor _ _ (-a)).mapIso e ≪≫
      (leftOrdinaryTensorComplex (P.homology q) Q).extendHomologyIso
        nonnegativeChainEmbedding (j := p) (neg_neg (p : ℤ)).symm ≪≫ ord.quotient p

/-- The maps constituting the source's signed row-to-Tor comparison.
The last identification is precisely the two-augmentation balance map,
using the actual right resolution defining the chosen P103 Tor. -/
structure ResolutionSecondPageComparison (T : CanonicalTheory.{u,v,w} R)
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (Q : LeftResolution R M) (S : TensorPages P (extendNonnegativeChain Q.complex)) where
  rowComparison : RowTensorComparison P (extendNonnegativeChain Q.complex) S
  ordinary : ∀ q : ℤ, OrdinaryTensorComparison (P.homology q) Q.complex
  balance : ∀ q : ℤ, Augmentations (T.rightResolutions (P.homology q)).val Q
  leftQuasiIso : ∀ q : ℤ, QuasiIsomorphism (balance q).left
  rightQuasiIso : ∀ q : ℤ, QuasiIsomorphism (balance q).right

/-- The prescribed second-page identification as the composition of actual
page cohomology, signed row comparison, reindexing, quotient and balance. -/
def ResolutionSecondPageComparison.iso {T : CanonicalTheory.{u,v,w} R}
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {M : ModuleCat.{w} R}
    {Q : LeftResolution R M} {S : TensorPages P (extendNonnegativeChain Q.complex)}
    (C : ResolutionSecondPageComparison T P M Q S) (p : ℕ) (q : ℤ) :
    S.term 2 p q ≅ ModuleCat.of ℤ (T.Tor (P.homology q) M p) :=
  C.rowComparison.ordinaryHomologyIso p q (C.ordinary q) ≪≫
    (balanceEquiv (C.balance q) (C.leftQuasiIso q) (C.rightQuasiIso q) p).symm.toModuleIso

/-- Lift coefficients to the universe of the chosen projective resolution. -/
abbrev liftedCoefficientComplex (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) : ChainComplex (ModuleCat.{max u v w} ℤ) ℤ :=
  ((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    (coefficientComplex P M)

/-- The unshifted tensor augmentation on the actual sum total.
The indices are cochain indices, so the resolution degree on its
`(i,j)` summand is `-j`. -/
structure TargetAugmentation (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) where
  hom : sumTotal (tensorCochain P (extendNonnegativeChain Q.complex)) ⟶
    reverseChain (liftedCoefficientComplex P M)
  zero_component : ∀ (i : ℤ) (a : P.X (-i)) (b : Q.complex.X 0),
    (hom.f i).hom
      ((sumInjection (tensorCochain P (extendNonnegativeChain Q.complex))
        i 0 i (by omega)).hom
        (P103.BalancedTensor.tmul R a
          ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl).inv.hom b))) =
      ULift.up (P103.BalancedTensor.tmul R a (Q.ε b))
  other_components : ∀ (i j n : ℤ) (h : i + j = n), j ≠ 0 →
    sumInjection (tensorCochain P (extendNonnegativeChain Q.complex)) i j n h ≫ hom.f n = 0

/-- The target comparison sends each class to the class of its augmented
cycle, after index reversal and the prescribed carrier lift. -/
def TargetAugmentation.Induces {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q : LeftResolution R M}
    (a : TargetAugmentation P M Q) (n : ℤ)
    (e : (sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).homology (-n) ≅
      targetHomology P M n) : Prop :=
  let K := sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))
  let C := coefficientComplex P M
  let C' := liftedCoefficientComplex P M
  ∀ z : K.cycles (-n), ∃ w : cycles C n,
    (w : C.X n) =
      ULift.down (((C'.restrictionXIso reversal (by change -(-n) = n; omega)).hom)
        ((a.hom.f (-n)).hom ((K.iCycles (-n)).hom z))) ∧
    (e.hom).hom ((K.homologyπ (-n)).hom z) = ULift.up (homologyClass C n w)


/-- A realization using an arbitrary chosen ordinary projective resolution.
The target filtration is defined below by transporting the actual row image
filtration through `targetIso`. The simultaneous System below supplies naturality. -/
structure Realization (T : CanonicalTheory.{u,v,w} R)
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (Q : LeftResolution R M) (L : ℤ) where
  tensorPages : TensorPages P (extendNonnegativeChain Q.complex)
  support : ∀ r p q : ℤ, p < 0 ∨ q < L → IsZero (tensorPages.term r p q)
  secondComparison : ResolutionSecondPageComparison T P M Q tensorPages
  targetIso : ∀ n : ℤ, (sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))).homology (-n) ≅
    targetHomology P M n
  targetAugmentation : TargetAugmentation P M Q
  targetQuasiIso : QuasiIso targetAugmentation.hom
  targetInduced : ∀ n, targetAugmentation.Induces n (targetIso n)

abbrev Realization.secondIso {T : CanonicalTheory.{u,v,w} R}
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {M : ModuleCat.{w} R}
    {Q : LeftResolution R M} {L : ℤ} (D : Realization T P M Q L) (p : ℕ) (q : ℤ) :=
  D.secondComparison.iso p q

abbrev Realization.targetPiece {T : CanonicalTheory.{u,v,w} R}
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {M : ModuleCat.{w} R}
    {Q : LeftResolution R M} {L : ℤ} (D : Realization T P M Q L) (p n : ℤ) :=
  transportedPiece D.tensorPages.filtration n (targetHomology P M n) (D.targetIso n) p

abbrev Realization.targetGraded {T : CanonicalTheory.{u,v,w} R}
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {M : ModuleCat.{w} R}
    {Q : LeftResolution R M} {L : ℤ} (D : Realization T P M Q L) (p n : ℤ) :=
  transportedGraded D.tensorPages.filtration n (targetHomology P M n) (D.targetIso n) p

namespace Specs
/-- Finite diagonal support, including translated quadrants and empty diagonals. -/
def FiniteTensorDiagonals : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (L J : ℤ),
    BoundedBelow P L → (∀ j, j < J → IsZero (Q.X j)) →
      FiniteDiagonals (tensorCochain P Q)

/-- Construction of the convergent row pages for every lower bounded tensor
bicomplex. No flatness is needed until the homology identifications. -/
def TensorPageConstruction : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (L J : ℤ),
    BoundedBelow P L → (∀ j, j < J → IsZero (Q.X j)) →
      Nonempty (TensorPages P Q)
/-- Every page is supported on the original translated chain quadrant. -/
def TensorPageSupport : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (L J : ℤ),
    BoundedBelow P L → (∀ j, j < J → IsZero (Q.X j)) →
    ∀ (S : TensorPages P Q) (r p q : ℤ), p < J ∨ q < L →
      IsZero (S.term r p q)

/-- Specialization to any ordinary left resolution, without assuming P is
nonnegative or projective. Flatness of P is only used for the target comparison. -/
def ResolutionPageConstruction : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (L : ℤ) (M : ModuleCat.{w} R) (Q : LeftResolution R M),
    BoundedBelow P L →
    ∃ S : TensorPages P (extendNonnegativeChain Q.complex),
      ∀ r p q : ℤ, p < 0 ∨ q < L → IsZero (S.term r p q)

/-- The tensor maps induce the canonical maps of all the actual row pages.
These already commute with differentials by `MapData.differential_comm`.
Lift independence from E₂ onward is a further obligation. -/
def TensorPageMaps : Prop :=
  ∀ (R : Type u) [Ring R]
    (P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q Q' : ChainComplex (ModuleCat.{w} R) ℤ)
    (S : TensorPages P Q) (S' : TensorPages P' Q') (f : P ⟶ P') (g : Q ⟶ Q'),
    ∃ h : FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P' Q'), S'.filtration⟩,
      h.hom = HomologicalComplex₂.total.map (tensorCochainMap f g) (ComplexShape.up ℤ) ∧
      Nonempty (FilteredPageFunctoriality.MapData h S.pages S'.pages)

/-- Equality of maps on a page propagates to every later page. This supplies
choice independence once the two lifts are compared on E₂. -/
def PageMapEqualityPropagation : Prop :=
  ∀ {A : Type u} [Category.{v} A] [Abelian A] {X Y : FilteredComplex A}
    (f g : FilteredMap X Y) (D : F03Specs.PageData X.filtration)
    (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g D E) (r : ℤ),
    0 ≤ r → (∀ p n, M.map r p n = N.map r p n) →
      ∀ s, r ≤ s → ∀ p n, M.map s p n = N.map s p n
/-- Tensoring a quasi-isomorphism in the left variable with a lower bounded
complex of flat right modules preserves the quasi-isomorphism of finite totals.
This is a comparison lemma; applying it to a resolution augmentation still
requires constructing and checking that augmentation. -/
def TensorTotalQuasiIso : Prop :=
  ∀ (R : Type u) [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q Q' : ChainComplex (ModuleCat.{w} R) ℤ) (L J J' : ℤ),
    BoundedBelow P L → FlatTerms.{u,v,w} P →
    (∀ j, j < J → IsZero (Q.X j)) →
    (∀ j, j < J' → IsZero (Q'.X j)) →
    ∀ g : Q ⟶ Q', QuasiIso g →
      QuasiIso (HomologicalComplex₂.total.map (tensorCochainMap (𝟙 P) g)
        (ComplexShape.up ℤ))

/-- Square-zero with the homological bidegree specified in HA-B06. -/
def TensorPageSquareZero : Prop :=
  ∀ {R : Type u} [Ring R] {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ),
    S.differential r hr p q ≫ S.differential r hr (p-r) (q+r-1) = 0

/-- The next page is homology of the actual three-term page complex. -/
def TensorNextPageCohomology : Prop :=
  ∀ {R : Type u} [Ring R] {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ),
    Nonempty (S.term (r+1) p q ≅ (PageCohomology.shortComplex S.filtration S.pages
      r hr (-p-r) (-(p+q)-1)).homology)

/-- The actual second page is the actual P103 Tor object. -/
def ResolutionSecondPage : Prop :=
  ∀ {R : Type u} [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (L : ℤ),
    BoundedBelow P L → Q.IsProjective →
    ∀ (T : CanonicalTheory.{u,v,w} R) (S : TensorPages P (extendNonnegativeChain Q.complex)),
      Nonempty (ResolutionSecondPageComparison T P M Q S)

/-- The given resolution augmentation induces the comparison with the original
coefficient complex on homology in every integer degree. -/
def ResolutionTargetComparison : Prop :=
  ∀ {R : Type u} [Ring R] (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (L : ℤ) (M : ModuleCat.{w} R) (Q : LeftResolution R M),
    BoundedBelow P L → FlatTerms.{u,v,w} P → Q.IsProjective →
    ∃ a : TargetAugmentation P M Q, QuasiIso a.hom ∧ ∀ n, ∃ e, a.Induces n e

/-- Existence and convergence data for any chosen projective left resolution.
This incremental obligation does not include the naturality system. -/
def KunnethConstruction : Prop :=
  ∀ {R : Type u} [Ring R] (T : CanonicalTheory.{u,v,w} R)
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (L : ℤ) (M : ModuleCat.{w} R)
    (Q : LeftResolution R M), BoundedBelow P L → FlatTerms.{u,v,w} P → Q.IsProjective →
      Nonempty (Realization T P M Q L)

/-- Finite increasing target filtration and the stabilized graded identification. -/
def KunnethConvergence : Prop :=
  ∀ {R : Type u} [Ring R] {T : CanonicalTheory.{u,v,w} R}
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {L : ℤ} {M : ModuleCat.{w} R}
    {Q : LeftResolution R M} (D : Realization T P M Q L),
    (∀ p n, D.targetPiece (p-1) n ≤ D.targetPiece p n) ∧
    (∀ n, ∃ a b : ℤ, (∀ p, p ≤ a → D.targetPiece p n = ⊥) ∧
      (∀ p, b ≤ p → D.targetPiece p n = ⊤)) ∧
    (∀ n, ∃ r₀ : ℤ, 0 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∀ p,
      Nonempty (D.tensorPages.term r p (n-p) ≅ D.targetGraded p n))

end Specs
/-- Exactly the hypotheses of HA-B06, plus a freely chosen projective left
resolution; the system below compares all such choices. -/
structure Input (R : Type u) [Ring R] where
  P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ
  L : ℤ
  M : ModuleCat.{w} R
  Q : LeftResolution R M
  bounded : BoundedBelow P L
  flat : FlatTerms.{u,v,w} P
  projective : Q.IsProjective

def Input.changeResolution (X : Input.{u,v,w} R) (Q : LeftResolution R X.M)
    (hQ : Q.IsProjective) : Input.{u,v,w} R :=
  ⟨X.P,X.L,X.M,Q,X.bounded,X.flat,hQ⟩

structure Input.Hom (X Y : Input.{u,v,w} R) where
  right : X.P ⟶ Y.P
  coefficient : X.M ⟶ Y.M
  lift : X.Q.complex ⟶ Y.Q.complex
  lifts : ChainLift X.Q Y.Q coefficient.hom lift

def Input.Hom.id (X : Input.{u,v,w} R) : Input.Hom X X :=
  ⟨𝟙 X.P,𝟙 X.M,𝟙 X.Q.complex,by
    change X.Q.ε.comp LinearMap.id = LinearMap.id.comp X.Q.ε
    simp⟩

def Input.Hom.comp {X Y Z : Input.{u,v,w} R} (f : Input.Hom X Y)
    (g : Input.Hom Y Z) : Input.Hom X Z :=
  ⟨f.right ≫ g.right, f.coefficient ≫ g.coefficient, f.lift ≫ g.lift, by
    change Z.Q.ε.comp ((g.lift.f 0).hom.comp (f.lift.f 0).hom) =
      (g.coefficient.hom.comp f.coefficient.hom).comp X.Q.ε
    rw [← LinearMap.comp_assoc, g.lifts, LinearMap.comp_assoc, f.lifts,
      ← LinearMap.comp_assoc]⟩

/-- The naturality assertions concern the actual tensor map, all its actual
page maps, the specified Tor action, and the original fixed target. -/
structure NaturalMap (T : CanonicalTheory.{u,v,w} R)
    {X Y : Input.{u,v,w} R}
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T Y.P Y.M Y.Q Y.L)
    (f : Input.Hom X Y) where
  filtered : FilteredMap
    ⟨sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex)), D.tensorPages.filtration⟩
    ⟨sumTotal (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex)), E.tensorPages.filtration⟩
  total : filtered.hom = HomologicalComplex₂.total.map
    (tensorCochainMap f.right (HomologicalComplex.extendMap f.lift nonnegativeChainEmbedding))
    (ComplexShape.up ℤ)
  pages : FilteredPageFunctoriality.MapData filtered D.tensorPages.pages E.tensorPages.pages
  second : ∀ (p : ℕ) (q : ℤ),
    pages.map 2 (-p) (-(p+q)) ≫ (E.secondIso p q).hom =
      (D.secondIso p q).hom ≫
        ModuleCat.ofHom (T.torMap p (HomologicalComplex.homologyMap f.right q) f.coefficient)
  target : ∀ n, HomologicalComplex.homologyMap filtered.hom (-n) ≫ (E.targetIso n).hom =
    (D.targetIso n).hom ≫ targetHomologyMap f.right f.coefficient n
  step : ∀ p n, (D.targetPiece p n : ModuleCat.{max u v w} ℤ) ⟶ (E.targetPiece p n : ModuleCat.{max u v w} ℤ)
  step_arrow : ∀ p n, step p n ≫ (E.targetPiece p n).arrow =
    (D.targetPiece p n).arrow ≫ targetHomologyMap f.right f.coefficient n
  graded : ∀ p n, D.targetGraded p n ⟶ E.targetGraded p n
  graded_projection : ∀ p n,
    cokernel.π (Subobject.ofLE _ _
      (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) p)) ≫ graded p n =
      step p n ≫ cokernel.π (Subobject.ofLE _ _
        (transportedPiece_increasing E.tensorPages.filtration n _ (E.targetIso n) p))
  limit_target_natural : ∀ r p n
    (I : LimitIso D.tensorPages.filtration D.tensorPages.pages r (-p) (-n))
    (J : LimitIso E.tensorPages.filtration E.tensorPages.pages r (-p) (-n)),
    Stabilized D.tensorPages.filtration r (-p) (-n) →
    Stabilized E.tensorPages.filtration r (-p) (-n) →
    pages.map r (-p) (-n) ≫ J.iso.hom ≫
        (transportedGradedIso E.tensorPages.filtration n _ (E.targetIso n) p).hom =
      I.iso.hom ≫ (transportedGradedIso D.tensorPages.filtration n _ (D.targetIso n) p).hom ≫ graded p n
  limit_natural : ∀ r p n
    (I : LimitIso D.tensorPages.filtration D.tensorPages.pages r (-p) (-n))
    (J : LimitIso E.tensorPages.filtration E.tensorPages.pages r (-p) (-n)),
    Stabilized D.tensorPages.filtration r (-p) (-n) →
    Stabilized E.tensorPages.filtration r (-p) (-n) →
    pages.map r (-p) (-n) ≫ J.iso.hom =
      I.iso.hom ≫ gradedCohomologyMap filtered (-p) (-n)

abbrev NaturalMap.page {T : CanonicalTheory.{u,v,w} R} {X Y : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    {f : Input.Hom X Y} (m : NaturalMap T D E f) (r p q : ℤ) :=
  m.pages.map r (-p) (-(p+q))

/-- A simultaneous choice of the Künneth sequence for every original input,
with all comparison laws. Every field is output of the existence theorem. -/
structure System (T : CanonicalTheory.{u,v,w} R) where
  resolution_exists : ∀ M : ModuleCat.{w} R, ∃ Q : LeftResolution R M, Q.IsProjective
  realize : ∀ X : Input.{u,v,w} R, Realization T X.P X.M X.Q X.L
  lift_exists : ∀ (X Y : Input.{u,v,w} R) (f : X.P ⟶ Y.P) (g : X.M ⟶ Y.M),
    ∃ l : X.Q.complex ⟶ Y.Q.complex, ChainLift X.Q Y.Q g.hom l
  map : ∀ {X Y : Input.{u,v,w} R} (f : Input.Hom X Y), NaturalMap T (realize X) (realize Y) f
  page_identity : ∀ X (r p q : ℤ), 2 ≤ r → (map (Input.Hom.id X)).page r p q = 𝟙 _
  page_composition : ∀ {X Y Z} (f : Input.Hom X Y) (g : Input.Hom Y Z) (r p q : ℤ),
    2 ≤ r → (map (f.comp g)).page r p q = (map f).page r p q ≫ (map g).page r p q
  lift_independent : ∀ {X Y} (f g : Input.Hom X Y), f.right = g.right →
    f.coefficient = g.coefficient → ∀ r p q, 2 ≤ r → (map f).page r p q = (map g).page r p q
  step_identity : ∀ X p n, (map (Input.Hom.id X)).step p n = 𝟙 _
  step_composition : ∀ {X Y Z} (f : Input.Hom X Y) (g : Input.Hom Y Z) p n,
    (map (f.comp g)).step p n = (map f).step p n ≫ (map g).step p n
  step_lift_independent : ∀ {X Y} (f g : Input.Hom X Y), f.right = g.right →
    f.coefficient = g.coefficient → ∀ p n, (map f).step p n = (map g).step p n
  graded_identity : ∀ X p n, (map (Input.Hom.id X)).graded p n = 𝟙 _
  graded_composition : ∀ {X Y Z} (f : Input.Hom X Y) (g : Input.Hom Y Z) p n,
    (map (f.comp g)).graded p n = (map f).graded p n ≫ (map g).graded p n
  graded_lift_independent : ∀ {X Y} (f g : Input.Hom X Y), f.right = g.right →
    f.coefficient = g.coefficient → ∀ p n, (map f).graded p n = (map g).graded p n
  comparison_isIso : ∀ (X : Input.{u,v,w} R) (Q : LeftResolution R X.M) (hQ : Q.IsProjective)
    (l : X.Q.complex ⟶ Q.complex) (hl : ChainLift X.Q Q (LinearMap.id : X.M →ₗ[R] X.M) l)
    r p q, 2 ≤ r → IsIso ((map (X := X) (Y := X.changeResolution Q hQ)
      ⟨𝟙 X.P, 𝟙 X.M, l, hl⟩).page r p q)
  target_choice : ∀ (X : Input.{u,v,w} R) (Q : LeftResolution R X.M) (hQ : Q.IsProjective) p n,
    (realize X).targetPiece p n = (realize (X.changeResolution Q hQ)).targetPiece p n
  finite : ∀ X n, ∃ a b : ℤ,
    (∀ p, p ≤ a → (realize X).targetPiece p n = ⊥) ∧
    (∀ p, b ≤ p → (realize X).targetPiece p n = ⊤)
  stable : ∀ X n, ∃ r₀ : ℤ, 0 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∀ p,
    Nonempty ((realize X).tensorPages.term r p (n-p) ≅ (realize X).targetGraded p n)

namespace Specs
/-- Complete HA-B06, simultaneous in complexes, coefficients and resolutions.
The Input packaging imposes exactly the original hypotheses; System includes
existence of lifts for every pair map and coherent actual page and target maps. -/
def FullStatement : Prop :=
  ∀ (R : Type u) [Ring R], Nonempty (CanonicalTheory.{u,v,w} R) ∧
    ∀ (T : CanonicalTheory.{u,v,w} R), Nonempty (System T)
end Specs

section OriginalCarriers

open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)
open P103.BalancedTensor (tmul)
universe v' w'

/-- The original maps of the two inputs and an augmented comparison of
their chosen resolutions, with no common carrier size imposed. -/
structure OriginalInputMap (X : Input.{u,v,w} R) (Y : Input.{u,v',w'} R) where
  right : LinearChainMap X.P Y.P
  coefficient : X.M →ₗ[R] Y.M
  lift : LinearChainMap X.Q.complex Y.Q.complex
  lift_augmented : Y.Q.ε.comp (lift.app 0) = coefficient.comp X.Q.ε

/-- The original map on categorical homology is determined by its formula
on actual cycles and their quotient, independently of the carrier sizes. -/
def InducesCategoricalHomology {S : Type u} [Ring S] {ι : Type*}
    {c : ComplexShape ι} {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c} (f : LinearChainMap K L)
    (h : ∀ n, K.homology n →ₗ[S] L.homology n) : Prop :=
  ∀ n (z : K.cycles n), ∃ y : L.cycles n,
    (L.iCycles n).hom y = f.app n ((K.iCycles n).hom z) ∧
    h n ((K.homologyπ n).hom z) = (L.homologyπ n).hom y

/-- The natural maps of the original augmented totals, page quotients,
Tor groups, and target filtrations, all across independent carrier sizes. -/
structure OriginalNaturalMap {T : CanonicalTheory.{u,v,w} R}
    {T' : CanonicalTheory.{u,v',w'} R} {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
    (f : OriginalInputMap X Y) where
  extended : LinearChainMap (extendNonnegativeChain X.Q.complex) (extendNonnegativeChain Y.Q.complex)
  extended_formula : ∀ (j : ℕ) (b : X.Q.complex.X j),
    extended.app j ((X.Q.complex.extendXIso nonnegativeChainEmbedding (i := j) rfl).inv.hom b) =
      (Y.Q.complex.extendXIso nonnegativeChainEmbedding (i := j) rfl).inv.hom (f.lift.app j b)
  total : LinearChainMap
    (sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex)))
    (sumTotal (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex)))
  total_formula : ∀ (i j n : ℤ) (h : i + j = n) (a : X.P.X (-i))
    (b : (extendNonnegativeChain X.Q.complex).X (-j)),
    total.app n ((sumInjection (tensorCochain X.P (extendNonnegativeChain X.Q.complex))
        i j n h).hom (tmul R a b)) =
      (sumInjection (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex))
        i j n h).hom (tmul R (f.right.app (-i) a) (extended.app (-j) b))
  filtered : ∀ p n (z : (D.tensorPages.filtration.piece p n : ModuleCat.{max u v w} ℤ)),
    ∃ y : (E.tensorPages.filtration.piece p n : ModuleCat.{max u v' w'} ℤ),
      (E.tensorPages.filtration.piece p n).arrow.hom y =
        total.app n ((D.tensorPages.filtration.piece p n).arrow.hom z)
  almost : ∀ r p n,
    (FilteredPage.almost D.tensorPages.filtration r p n : ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
      (FilteredPage.almost E.tensorPages.filtration r p n : ModuleCat.{max u v' w'} ℤ)
  almost_formula : ∀ r p n z,
    (FilteredPage.almost E.tensorPages.filtration r p n).arrow.hom (almost r p n z) =
      total.app n ((FilteredPage.almost D.tensorPages.filtration r p n).arrow.hom z)
  page : ∀ r p n,
    (PageCohomology.object D.tensorPages.filtration D.tensorPages.pages r p n :
      ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
    (PageCohomology.object E.tensorPages.filtration E.tensorPages.pages r p n :
      ModuleCat.{max u v' w'} ℤ)
  page_formula : ∀ r p n,
    (page r p n).comp
      (FilteredPage.toPage D.tensorPages.filtration r p n (D.tensorPages.pages.containment r p n)).hom =
    (FilteredPage.toPage E.tensorPages.filtration r p n (E.tensorPages.pages.containment r p n)).hom.comp
      (almost r p n)
  differential : ∀ r (hr : 0 ≤ r) p n,
    (E.tensorPages.pages.differential r hr p n).hom.comp (page r p n) =
      (page r (p+r) (n+1)).comp (D.tensorPages.pages.differential r hr p n).hom
  next_natural : ∀ r (hr : 0 ≤ r) p n,
    let A := PageCohomology.shortComplex D.tensorPages.filtration D.tensorPages.pages r hr p n
    let B := PageCohomology.shortComplex E.tensorPages.filtration E.tensorPages.pages r hr p n
    ∀ z : A.cycles, ∃ y : B.cycles,
      B.iCycles.hom y = page r (p+r) (n+1) (A.iCycles.hom z) ∧
      (E.tensorPages.next.nextIso r hr p n).hom.hom
        (page (r+1) (p+r) (n+1)
          ((D.tensorPages.next.nextIso r hr p n).inv.hom (A.homologyπ.hom z))) =
        B.homologyπ.hom y
  pHomology : ∀ q, X.P.homology q →ₗ[Rᵐᵒᵖ] Y.P.homology q
  pHomology_formula : InducesCategoricalHomology f.right pHomology
  tor : ∀ (q : ℤ) (p : ℕ), T.Tor (X.P.homology q) X.M p →ₗ[ℤ] T'.Tor (Y.P.homology q) Y.M p
  tor_formula : ∀ (q : ℤ),
    let P := (T.rightResolutions (X.P.homology q)).val
    let P' := (T'.rightResolutions (Y.P.homology q)).val
    ∃ l : LinearChainMap P.complex P'.complex,
      P'.ε.comp (l.app 0) = (pHomology q).comp P.ε ∧
      ∃ g : LinearChainMap (tensorComplex P.complex X.M) (tensorComplex P'.complex Y.M),
        (∀ p, g.app p = tensorMap (l.app p) f.coefficient) ∧ g.InducesHomology (fun n z => tor q n z)
  second : ∀ (p : ℕ) (q : ℤ),
    (E.secondIso p q).hom.hom.comp (page 2 (-p) (-(p+q))) =
      (tor q p).comp (D.secondIso p q).hom.hom
  targetChain : LinearChainMap (coefficientComplex X.P X.M) (coefficientComplex Y.P Y.M)
  targetChain_formula : ∀ n, targetChain.app n = tensorMap (f.right.app n) f.coefficient
  augmentation : ∀ i z,
    (E.targetAugmentation.hom.f i).hom (total.app i z) =
      ULift.up (targetChain.app (-i) (ULift.down ((D.targetAugmentation.hom.f i).hom z)))
  totalHomology : ∀ n,
    (sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex))).homology n →ₗ[ℤ]
      (sumTotal (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex))).homology n
  totalHomology_formula : InducesCategoricalHomology total totalHomology
  targetQuotient : ∀ n,
    Homology (coefficientComplex X.P X.M) n →ₗ[ℤ] Homology (coefficientComplex Y.P Y.M) n
  targetQuotient_formula : targetChain.InducesHomology (fun n z => targetQuotient n z)
  target : ∀ n, targetHomology X.P X.M n →ₗ[ℤ] targetHomology Y.P Y.M n
  target_formula : ∀ n z, target n (ULift.up z) = ULift.up (targetQuotient n z)
  target_comparison : ∀ n, (E.targetIso n).hom.hom.comp (totalHomology (-n)) =
    (target n).comp (D.targetIso n).hom.hom
  step : ∀ p n, (D.targetPiece p n : ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
    (E.targetPiece p n : ModuleCat.{max u v' w'} ℤ)
  step_arrow : ∀ p n, (E.targetPiece p n).arrow.hom.comp (step p n) =
    (target n).comp (D.targetPiece p n).arrow.hom
  graded : ∀ p n, (D.targetGraded p n : ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
    (E.targetGraded p n : ModuleCat.{max u v' w'} ℤ)
  graded_projection : ∀ p n,
    (graded p n).comp (cokernel.π (Subobject.ofLE _ _
      (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) p))).hom =
    (cokernel.π (Subobject.ofLE _ _
      (transportedPiece_increasing E.tensorPages.filtration n _ (E.targetIso n) p))).hom.comp
        (step p n)
  limit_target_natural : ∀ r p n
    (I : LimitIso D.tensorPages.filtration D.tensorPages.pages r (-p) (-n))
    (J : LimitIso E.tensorPages.filtration E.tensorPages.pages r (-p) (-n)),
    Stabilized D.tensorPages.filtration r (-p) (-n) →
    Stabilized E.tensorPages.filtration r (-p) (-n) →
    ((J.iso.hom ≫ (transportedGradedIso E.tensorPages.filtration n _ (E.targetIso n) p).hom).hom).comp
      (page r (-p) (-n)) =
    (graded p n).comp
      (I.iso.hom ≫ (transportedGradedIso D.tensorPages.filtration n _ (D.targetIso n) p).hom).hom

namespace Specs

/-- Arbitrary original maps admit an augmented lift and every such lift
induces the natural comparison of the specified original realizations. -/
def OriginalNaturality : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (T' : CanonicalTheory.{u,v',w'} R)
    (X : Input.{u,v,w} R) (Y : Input.{u,v',w'} R)
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
    (f : LinearChainMap X.P Y.P) (g : X.M →ₗ[R] Y.M),
    (∃ l : LinearChainMap X.Q.complex Y.Q.complex, Y.Q.ε.comp (l.app 0) = g.comp X.Q.ε) ∧
    ∀ (l : LinearChainMap X.Q.complex Y.Q.complex) (a : Y.Q.ε.comp (l.app 0) = g.comp X.Q.ε),
      Nonempty (OriginalNaturalMap D E ⟨f,g,l,a⟩)

/-- From the second page on, changing the lift leaves the original page,
filtered target, and graded maps unchanged. -/
def OriginalLiftIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (T' : CanonicalTheory.{u,v',w'} R)
    (X : Input.{u,v,w} R) (Y : Input.{u,v',w'} R)
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
    (f : LinearChainMap X.P Y.P) (g : X.M →ₗ[R] Y.M)
    (l m : LinearChainMap X.Q.complex Y.Q.complex)
    (a : Y.Q.ε.comp (l.app 0) = g.comp X.Q.ε) (b : Y.Q.ε.comp (m.app 0) = g.comp X.Q.ε)
    (L : OriginalNaturalMap D E ⟨f,g,l,a⟩) (M : OriginalNaturalMap D E ⟨f,g,m,b⟩),
    (∀ (r p n : ℤ), 2 ≤ r → L.page r p n = M.page r p n) ∧
    L.target = M.target ∧ L.step = M.step ∧ L.graded = M.graded

end Specs
end OriginalCarriers

namespace IndependentResolution

open AdvancedHomologicalAlgebra.TorBalance
  (AugmentedResolution LinearChainMap OriginalAugmentations)
open P103.BalancedTensor (tmul)
open FilteredPage FiniteFiltrationConvergence

universe t v' w' t'

/-- A chosen resolution of the given left module, with an independent term level. -/
structure Input (R : Type u) [Ring R] where
  P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ
  L : ℤ
  M : ModuleCat.{w} R
  Q : AugmentedResolution.{u,w,t} R M
  bounded : BoundedBelow P L
  flat : FlatTerms.{u,v,max w t} P

abbrev Input.extended (X : Input.{u,v,w,t} R) := extendNonnegativeChain X.Q.complex
abbrev Input.tensor (X : Input.{u,v,w,t} R) := tensorCochain X.P X.extended
abbrev Input.total (X : Input.{u,v,w,t} R) := sumTotal X.tensor
abbrev Input.coefficient (X : Input.{u,v,w,t} R) := coefficientComplex X.P X.M

/-- The actual signed sum total augments to the tensor with the original
coefficient module, without changing the terms of the given resolution. -/
structure Augmentation (X : Input.{u,v,w,t} R) where
  map : LinearChainMap X.total (reverseChain X.coefficient)
  zero_component : ∀ (i : ℤ) (a : X.P.X (-i)) (b : X.Q.complex.X 0),
    map.app i ((sumInjection X.tensor i 0 i (by omega)).hom
      (tmul R a ((X.Q.complex.extendXIso nonnegativeChainEmbedding
        (i := 0) (i' := 0) rfl).inv.hom b))) = tmul R a (X.Q.ε b)
  other_components : ∀ (i j n : ℤ) (h : i + j = n), j ≠ 0 →
    (map.app n).comp (sumInjection X.tensor i j n h).hom = 0

/-- The signed row comparison followed by balance with the chosen Tor model.
Both maps in the balance use the actual projective resolution in that factor. -/
structure SecondPage (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w,t} R)
    (S : TensorPages X.P X.extended) where
  row : RowTensorComparison X.P X.extended S
  ordinary : ∀ q : ℤ, OrdinaryTensorComparison (X.P.homology q) X.Q.complex
  balance : ∀ q : ℤ, OriginalAugmentations
    (AugmentedResolution.ofP103 (T.rightResolutions (X.P.homology q)).val
      (T.rightResolutions (X.P.homology q)).property) X.Q
  leftQuasiIso : ∀ q, (balance q).left.IsQuasiIso
  rightQuasiIso : ∀ q, (balance q).right.IsQuasiIso

def SecondPage.equiv {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w,t} R}
    {S : TensorPages X.P X.extended} (D : SecondPage T X S) (p : ℕ) (q : ℤ) :
    S.term 2 p q ≃ₗ[ℤ] T.Tor (X.P.homology q) X.M p :=
  (D.row.ordinaryHomologyIso p q (D.ordinary q)).toLinearEquiv.trans
    ((D.balance q).balanceEquiv (D.leftQuasiIso q) (D.rightQuasiIso q) p).symm

/-- The target maps the class of a cycle to the class of its augmented cycle. -/
def Augmentation.Induces {X : Input.{u,v,w,t} R} (a : Augmentation X)
    (n : ℤ) (e : X.total.homology (-n) ≃ₗ[ℤ] Homology X.coefficient n) : Prop :=
  ∀ z : X.total.cycles (-n), ∃ y : cycles X.coefficient n,
    y.val = (X.coefficient.restrictionXIso reversal (by change -(-n) = n; omega)).hom
      (a.map.app (-n) ((X.total.iCycles (-n)).hom z)) ∧
    e ((X.total.homologyπ (-n)).hom z) = homologyClass X.coefficient n y

/-- The row pages, second-page coordinates and target comparison are all
attached to the same original tensor bicomplex and its augmentation. -/
structure Realization (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w,t} R) where
  pages : TensorPages X.P X.extended
  support : ∀ r p q : ℤ, p < 0 ∨ q < X.L → IsZero (pages.term r p q)
  second : SecondPage T X pages
  augmentation : Augmentation X
  quasiIso : augmentation.map.IsQuasiIso
  target : ∀ n : ℤ, X.total.homology (-n) ≃ₗ[ℤ] Homology X.coefficient n
  target_formula : ∀ n, augmentation.Induces n (target n)

/-- Transport the actual image filtration to the original quotient homology. -/
def Realization.piece {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w,t} R}
    (D : Realization T X) (p n : ℤ) : Submodule ℤ (Homology X.coefficient n) :=
  ((ModuleCat.subobjectModule _).toFun (cohomologyPiece D.pages.filtration (-p) (-n))).map
    (D.target n).toLinearMap

theorem Realization.piece_increasing {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w,t} R}
    (D : Realization T X) (p n : ℤ) : D.piece (p-1) n ≤ D.piece p n := by
  apply Submodule.map_mono
  apply (ModuleCat.subobjectModule _).monotone
  simpa only [show -(p-1) = -p+1 by omega] using cohomologyPiece_decreasing D.pages.filtration (-p) (-n)

abbrev Realization.gradedSubmodule {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w,t} R}
    (D : Realization T X) (p n : ℤ) := (D.piece (p-1) n).comap (D.piece p n).subtype

abbrev Realization.graded {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w,t} R}
    (D : Realization T X) (p n : ℤ) := (D.piece p n) ⧸ (D.gradedSubmodule p n)

/-- The limiting map sends each closed representative to the class of the
same augmented homology element in the quotient of the actual image step. -/
structure LimitComparison {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w,t} R}
    (D : Realization T X) (r p n : ℤ) where
  equiv : (PageCohomology.object D.pages.filtration D.pages.pages r (-p) (-n) :
      ModuleCat.{max v t} ℤ) ≃ₗ[ℤ] D.graded p n
  closed_formula : ∀ z : (closed D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ),
    ∃ x : D.piece p n,
      x.val = D.target n ((cohomologyPiece D.pages.filtration (-p) (-n)).arrow.hom
        ((closedClass D.pages.filtration (-p) (-n)).hom z)) ∧
      equiv ((closedToPage D.pages.filtration D.pages.pages r (-p) (-n)).hom z) =
        (D.gradedSubmodule p n).mkQ x

/-- Maps between the given inputs use an augmented lift between their actual
resolutions. The three carrier levels can vary independently in each input. -/
structure Input.Hom (X : Input.{u,v,w,t} R) (Y : Input.{u,v',w',t'} R) where
  right : LinearChainMap X.P Y.P
  coefficient : X.M →ₗ[R] Y.M
  lift : LinearChainMap X.Q.complex Y.Q.complex
  augmented : X.Q.Lifts Y.Q coefficient lift

/-- Maps of the actual filtered totals, their page quotients and the
augmentation-induced target filtrations. The formulas determine every map. -/
structure NaturalMap {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
    {X : Input.{u,v,w,t} R} {Y : Input.{u,v',w',t'} R}
    (D : Realization T X) (E : Realization T' Y) (f : Input.Hom X Y) where
  extended : LinearChainMap X.extended Y.extended
  extended_formula : ∀ (j : ℕ) (b : X.Q.complex.X j),
    extended.app j ((X.Q.complex.extendXIso nonnegativeChainEmbedding (i := j) rfl).inv.hom b) =
      (Y.Q.complex.extendXIso nonnegativeChainEmbedding (i := j) rfl).inv.hom (f.lift.app j b)
  total : LinearChainMap X.total Y.total
  total_formula : ∀ (i j n : ℤ) (h : i + j = n) (a : X.P.X (-i)) (b : X.extended.X (-j)),
    total.app n ((sumInjection X.tensor i j n h).hom (tmul R a b)) =
      (sumInjection Y.tensor i j n h).hom (tmul R (f.right.app (-i) a) (extended.app (-j) b))
  preserves_filtration : ∀ p n (z : (D.pages.filtration.piece p n : ModuleCat.{max v t} ℤ)),
    ∃ y : (E.pages.filtration.piece p n : ModuleCat.{max v' t'} ℤ),
      (E.pages.filtration.piece p n).arrow.hom y = total.app n ((D.pages.filtration.piece p n).arrow.hom z)
  almost : ∀ r p n, (FilteredPage.almost D.pages.filtration r p n : ModuleCat.{max v t} ℤ) →ₗ[ℤ]
    (FilteredPage.almost E.pages.filtration r p n : ModuleCat.{max v' t'} ℤ)
  almost_formula : ∀ r p n z,
    (FilteredPage.almost E.pages.filtration r p n).arrow.hom (almost r p n z) =
      total.app n ((FilteredPage.almost D.pages.filtration r p n).arrow.hom z)
  page : ∀ r p n, (PageCohomology.object D.pages.filtration D.pages.pages r p n :
      ModuleCat.{max v t} ℤ) →ₗ[ℤ]
    (PageCohomology.object E.pages.filtration E.pages.pages r p n : ModuleCat.{max v' t'} ℤ)
  page_formula : ∀ r p n,
    (page r p n).comp (FilteredPage.toPage D.pages.filtration r p n (D.pages.pages.containment r p n)).hom =
      (FilteredPage.toPage E.pages.filtration r p n (E.pages.pages.containment r p n)).hom.comp (almost r p n)
  page_differential : ∀ r (hr : 0 ≤ r) p n,
    (E.pages.pages.differential r hr p n).hom.comp (page r p n) =
      (page r (p+r) (n+1)).comp (D.pages.pages.differential r hr p n).hom
  next_natural : ∀ r (hr : 0 ≤ r) p n,
    let A := PageCohomology.shortComplex D.pages.filtration D.pages.pages r hr p n
    let B := PageCohomology.shortComplex E.pages.filtration E.pages.pages r hr p n
    ∀ z : A.cycles, ∃ y : B.cycles,
      B.iCycles.hom y = page r (p+r) (n+1) (A.iCycles.hom z) ∧
      (E.pages.next.nextIso r hr p n).hom.hom
        (page (r+1) (p+r) (n+1) ((D.pages.next.nextIso r hr p n).inv.hom (A.homologyπ.hom z))) =
        B.homologyπ.hom y
  right_homology : ∀ q, X.P.homology q →ₗ[Rᵐᵒᵖ] Y.P.homology q
  right_homology_formula : InducesCategoricalHomology f.right right_homology
  tor : ∀ (q : ℤ) (p : ℕ), T.Tor (X.P.homology q) X.M p →ₗ[ℤ] T'.Tor (Y.P.homology q) Y.M p
  tor_formula : ∀ q : ℤ,
    let P := (T.rightResolutions (X.P.homology q)).val
    let P' := (T'.rightResolutions (Y.P.homology q)).val
    ∃ l : LinearChainMap P.complex P'.complex,
      P'.ε.comp (l.app 0) = (right_homology q).comp P.ε ∧
      ∃ g : LinearChainMap (tensorComplex P.complex X.M) (tensorComplex P'.complex Y.M),
        (∀ p, g.app p = tensorMap (l.app p) f.coefficient) ∧ (∀ p, tor q p = g.homologyMap p)
  second : ∀ (p : ℕ) (q : ℤ),
    (E.second.equiv p q).toLinearMap.comp (page 2 (-p) (-(p+q))) =
      (tor q p).comp (D.second.equiv p q).toLinearMap
  coefficient : LinearChainMap X.coefficient Y.coefficient
  coefficient_formula : ∀ n, coefficient.app n = tensorMap (f.right.app n) f.coefficient
  augmentation : ∀ i,
    (E.augmentation.map.app i).comp (total.app i) =
      (coefficient.app (-i)).comp (D.augmentation.map.app i)
  total_homology : ∀ n, X.total.homology n →ₗ[ℤ] Y.total.homology n
  total_homology_formula : InducesCategoricalHomology total total_homology
  target_comparison : ∀ n, (E.target n).toLinearMap.comp (total_homology (-n)) =
    (coefficient.homologyMap n).comp (D.target n).toLinearMap
  step : ∀ p n, D.piece p n →ₗ[ℤ] E.piece p n
  step_formula : ∀ p n, (E.piece p n).subtype.comp (step p n) =
    (coefficient.homologyMap n).comp (D.piece p n).subtype
  graded : ∀ p n, D.graded p n →ₗ[ℤ] E.graded p n
  graded_formula : ∀ p n,
    (graded p n).comp (D.gradedSubmodule p n).mkQ = (E.gradedSubmodule p n).mkQ.comp (step p n)
  limit_natural : ∀ r p n (I : LimitComparison D r p n) (J : LimitComparison E r p n),
    Stabilized D.pages.filtration r (-p) (-n) → Stabilized E.pages.filtration r (-p) (-n) →
    J.equiv.toLinearMap.comp (page r (-p) (-n)) = (graded p n).comp I.equiv.toLinearMap

namespace Specs

/-- Construction on every original resolution and its actual augmentation. -/
def Construction : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w,t} R),
    Nonempty (Realization T X)

/-- Degreewise finiteness and the representative-normalized limiting maps. -/
def Convergence : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w,t} R)
    (D : Realization T X),
    (∀ n, ∃ a b : ℤ, (∀ p, p ≤ a → D.piece p n = ⊥) ∧ (∀ p, b ≤ p → D.piece p n = ⊤)) ∧
    ∀ n, ∃ r₀ : ℤ, 0 ≤ r₀ ∧ ∀ r, r₀ ≤ r → ∀ p,
      Stabilized D.pages.filtration r (-p) (-n) ∧ Nonempty (LimitComparison D r p n)

/-- Every original map admits an augmented lift, and each such lift gives the
specified map on the filtered total, its pages and the target. -/
def Naturality : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (T' : CanonicalTheory.{u,v',w'} R)
    (X : Input.{u,v,w,t} R) (Y : Input.{u,v',w',t'} R)
    (D : Realization T X) (E : Realization T' Y)
    (f : LinearChainMap X.P Y.P) (g : X.M →ₗ[R] Y.M),
    (∃ l : LinearChainMap X.Q.complex Y.Q.complex, X.Q.Lifts Y.Q g l) ∧
    ∀ (l : LinearChainMap X.Q.complex Y.Q.complex) (h : X.Q.Lifts Y.Q g l),
      Nonempty (NaturalMap D E ⟨f,g,l,h⟩)

/-- The page maps from E₂ onward, along with the filtered-target maps, are
independent of the chosen augmented lift. -/
def LiftIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R) (T' : CanonicalTheory.{u,v',w'} R)
    (X : Input.{u,v,w,t} R) (Y : Input.{u,v',w',t'} R)
    (D : Realization T X) (E : Realization T' Y)
    (f : LinearChainMap X.P Y.P) (g : X.M →ₗ[R] Y.M)
    (l m : LinearChainMap X.Q.complex Y.Q.complex) (h : X.Q.Lifts Y.Q g l) (k : X.Q.Lifts Y.Q g m)
    (F : NaturalMap D E ⟨f,g,l,h⟩) (G : NaturalMap D E ⟨f,g,m,k⟩),
    (∀ r p n : ℤ, 2 ≤ r → F.page r p n = G.page r p n) ∧
    (∀ n, F.coefficient.homologyMap n = G.coefficient.homologyMap n) ∧
    F.step = G.step ∧ F.graded = G.graded

/-- Comparing two independently sized resolutions over the same original
coefficient module gives the identity on the target and isomorphisms from E₂. -/
def ChoiceIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (T : CanonicalTheory.{u,v,w} R)
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (L : ℤ) (M : ModuleCat.{w} R)
    (Q : AugmentedResolution.{u,w,t} R M) (Q' : AugmentedResolution.{u,w,t'} R M)
    (b : BoundedBelow P L) (h : FlatTerms.{u,v,max w t} P) (h' : FlatTerms.{u,v,max w t'} P)
    (D : Realization T ⟨P,L,M,Q,b,h⟩) (E : Realization T ⟨P,L,M,Q',b,h'⟩)
    (l : LinearChainMap Q.complex Q'.complex) (a : Q.Lifts Q' (LinearMap.id : M →ₗ[R] M) l)
    (F : NaturalMap D E ⟨⟨fun _ => LinearMap.id, by intros; rfl⟩,LinearMap.id,l,a⟩),
    (∀ r p n : ℤ, 2 ≤ r → Function.Bijective (F.page r p n)) ∧
    (∀ n, F.coefficient.homologyMap n = LinearMap.id) ∧
    ∀ p n, D.piece p n = E.piece p n ∧ Function.Bijective (F.step p n) ∧ Function.Bijective (F.graded p n)

end Specs

end IndependentResolution

end AdvancedHomologicalAlgebra.KunnethSpectralSequence
