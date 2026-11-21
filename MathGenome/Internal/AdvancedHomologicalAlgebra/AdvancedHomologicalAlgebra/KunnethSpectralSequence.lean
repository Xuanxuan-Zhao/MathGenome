import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.KunnethSpectralSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Batteries.Tactic.OpenPrivate

/-! HA-B06: the Künneth spectral sequence over an arbitrary ring.
The actual row pages of the balanced tensor double complex identify with Tor
on E₂ and converge to the homology of the original coefficient complex.
The construction includes naturality and coherent independence of resolutions,
with integer lower bounds allowed to be negative.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Classical
universe u v w
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteDiagonalFiltrations
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open AugmentedDoubleComplexComparison
variable {R : Type u} [Ring R]

/-- The regrading is definitionally the one already used by HA-B04 assembly. -/
theorem tensorCochain_eq (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) :
    tensorCochain P Q =
      AugmentedDoubleComplexComparison.cochainBicomplex (tensorBicomplex P Q) := rfl

/-- Tensoring a zero factor gives the zero abelian group, in either variable. -/
theorem tensor_isZero (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{w} R)
    (h : IsZero A ∨ IsZero B) :
    IsZero (ModuleCat.of ℤ (P103.BalancedTensor.Tensor R A B)) := by
  rcases h with h | h
  · exact Functor.map_isZero (tensorFunctor B) h
  · exact Functor.map_isZero (leftTensorFunctor A) h

/-- Explicit bounds on every potentially nonzero regraded summand.
In original chain coordinates these are `L ≤ i ≤ n-J` and `J ≤ j ≤ n-L`.
Neither lower bound is required to be nonnegative. -/
theorem tensor_support_bounds
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (L J : ℤ)
    (hP : BoundedBelow P L) (hQ : ∀ j, j < J → IsZero (Q.X j))
    (n : ℤ) (i : Diagonal n)
    (hi : ¬ IsZero (diagonalFamily (tensorCochain P Q) n i)) :
    n + J ≤ i.val.1 ∧ i.val.1 ≤ -L ∧
      n + L ≤ i.val.2 ∧ i.val.2 ≤ -J := by
  have hb : L ≤ -i.val.1 ∧ J ≤ -i.val.2 := by
    by_contra hb
    apply hi
    change IsZero (ModuleCat.of ℤ
      (P103.BalancedTensor.Tensor R (P.X (-i.val.1)) (Q.X (-i.val.2))))
    apply tensor_isZero
    by_cases hp : L ≤ -i.val.1
    · exact Or.inr (hQ _ (by omega))
    · exact Or.inl (hP _ (by omega))
  have he := i.property
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem tensor_finite_diagonals : Specs.FiniteTensorDiagonals.{u,v,w} := by
  intro R _ P Q L J hP hQ n
  let s : Set (Diagonal n) :=
    {i | ¬ IsZero (diagonalFamily (tensorCochain P Q) n i)}
  have ht : Set.Finite ((fun i : Diagonal n => i.val.1) '' s) :=
    (Set.finite_Icc (n+J) (-L)).subset (by
      rintro _ ⟨i, hi, rfl⟩
      have hb := tensor_support_bounds P Q L J hP hQ n i hi
      exact ⟨hb.1, hb.2.1⟩)
  apply Set.Finite.of_finite_image ht
  intro i hi j hj hij
  apply Subtype.ext
  apply Prod.ext hij
  have hi' := i.property
  have hj' := j.property
  dsimp at hij
  omega

/-- The convergent pages come from the Q-degree (row) filtration. -/
theorem tensor_page_construction : Specs.TensorPageConstruction.{u,v,w} := by
  intro R _ P Q L J hP hQ
  have hK := tensor_finite_diagonals R P Q L J hP hQ
  obtain ⟨Fc, Fr, hc, hr, hfc, hfr⟩ :=
    FiniteDiagonalFiltrations.filtrations (tensorCochain P Q) hK
  obtain ⟨D, ⟨C⟩⟩ := filtered_page_cohomology Fr
  exact ⟨⟨Fr, hr, D, C, (DoubleComplexConvergence.double_complex_convergence
    (tensorCochain P Q) hK Fc Fr hc hr).2⟩⟩

/-- Subquotients of a zero graded object are zero, for all page indices. -/
theorem page_isZero_of_graded {A : Type*} [Category* A] [Abelian A]
    {K : CochainComplex A ℤ} (F : Filtration K) (D : F03Specs.PageData F)
    (r p n : ℤ) (h : IsZero ((F.graded p).X n)) :
    IsZero (PageCohomology.object F D r p n) := by
  have hc : IsZero (FilteredPage.cycles F r p n : A) :=
    IsZero.of_mono (FilteredPage.cycles F r p n).arrow h
  exact IsZero.of_epi (cokernel.π (Subobject.ofLE _ _ (D.containment r p n))) hc

theorem tensor_pages_support : Specs.TensorPageSupport.{u,v,w} := by
  intro R _ P Q L J hP hQ S r p q hpq
  apply page_isZero_of_graded
  have e := (DoubleComplexFirstPages.rowData (tensorCochain P Q)
    S.filtration S.formula S.pages).gradedIso (-p) (-q)
  have hz : IsZero (((tensorCochain P Q).X (-q)).X (-p)) := by
    change IsZero (ModuleCat.of ℤ
      (P103.BalancedTensor.Tensor R (P.X (- -q)) (Q.X (- -p))))
    apply tensor_isZero
    rcases hpq with hp | hq
    · exact Or.inr (by simpa only [neg_neg] using hQ p hp)
    · exact Or.inl (by simpa only [neg_neg] using hP q hq)
  have hgraded := IsZero.of_iso hz e
  simpa only [neg_add] using hgraded

/-- Extension of an ordinary chain complex has no negative terms. -/
theorem extended_resolution_isZero (M : ModuleCat.{w} R) (Q : LeftResolution R M)
    (j : ℤ) (hj : j < 0) : IsZero ((extendNonnegativeChain Q.complex).X j) := by
  exact Q.complex.isZero_extend_X nonnegativeChainEmbedding j (by
    intro i hi
    change (i : ℤ) = j at hi
    omega)

theorem resolution_page_construction : Specs.ResolutionPageConstruction.{u,v,w} := by
  intro R _ P L M Q hP
  obtain ⟨S⟩ := tensor_page_construction R P (extendNonnegativeChain Q.complex)
    L 0 hP (extended_resolution_isZero M Q)
  exact ⟨S, tensor_pages_support R P (extendNonnegativeChain Q.complex)
    L 0 hP (extended_resolution_isZero M Q) S⟩

theorem tensor_page_maps : Specs.TensorPageMaps.{u,v,w} := by
  intro R _ P P' Q Q' S S' f g
  obtain ⟨h, hh⟩ := FiniteDiagonalFiltrations.formula_filteredMap
    (tensorCochain P Q) (tensorCochain P' Q') Prod.snd
    S.filtration S'.filtration S.formula S'.formula (tensorCochainMap f g)
  exact ⟨h, hh, ⟨FilteredPageFunctoriality.mapData h S.pages S'.pages⟩⟩

/-- The next-page isomorphisms identify equal maps with equal homology maps. -/
theorem page_maps_equal_next {A : Type*} [Category* A] [Abelian A]
    {X Y : FilteredComplex A} {f g : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g D E) (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, M.map r p n = N.map r p n) (p n : ℤ) :
    M.map (r+1) p n = N.map (r+1) p n := by
  let C := PageCohomology.data X.filtration D
  let C' := PageCohomology.data Y.filtration E
  have he : FilteredPageFunctoriality.shortComplexMap M r hr (p-r) (n-1) =
      FilteredPageFunctoriality.shortComplexMap N r hr (p-r) (n-1) := by
    ext <;> apply h
  have hm := FilteredPageFunctoriality.next_naturality M C C' r hr (p-r) (n-1)
  have hn := FilteredPageFunctoriality.next_naturality N C C' r hr (p-r) (n-1)
  rw [he] at hm
  have hh := hm.trans hn.symm
  have hh' := (cancel_mono (C'.nextIso r hr (p-r) (n-1)).hom).1 hh
  rw [sub_add_cancel, sub_add_cancel] at hh'
  exact hh'

theorem page_maps_equal_later : Specs.PageMapEqualityPropagation.{u,v} := by
  intro A _ _ X Y f g D E M N r hr h s hs
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hs
  clear hs
  induction k with
  | zero =>
    rw [Int.natCast_zero, add_zero]
    exact h
  | succ k ih =>
    rw [show r + (↑(k+1) : ℤ) = r + (k : ℤ) + 1 by omega]
    exact page_maps_equal_next M N (r + (k : ℤ)) (by omega) ih

/-- Flatness of a right term preserves quasi-isomorphisms of left complexes. -/
theorem tensor_column_quasiIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (hP : FlatTerms.{u,v,w} P)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q')
    (hg : QuasiIso g) (i : ℤ) :
    QuasiIso ((tensorBicomplexMap (𝟙 P) g).f i) := by
  have hF := TorBalance.right_flat_tensor_preservesHomology.{u,w,v} (hP i)
  have he : (tensorBicomplexMap (𝟙 P) g).f i =
      ((leftTensorFunctor (P.X i)).mapHomologicalComplex (ComplexShape.down ℤ)).map g := by
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl
  rw [he]
  exact HomologicalComplex.quasiIso_map_of_preservesHomology g
    (leftTensorFunctor (P.X i))

/-- The comparison applies on a translated quadrant, so no sign condition on L
is needed. Both totalizations here are the actual regraded tensor totals. -/
theorem tensor_total_quasiIso : Specs.TensorTotalQuasiIso.{u,v,w} := by
  intro R _ P Q Q' L J J' hP hflat hQ hQ' g hg
  have hK := tensor_finite_diagonals R P Q L J hP hQ
  have hK' := tensor_finite_diagonals R P Q' L J' hP hQ'
  apply DoubleComplexConvergence.double_complex_comparison
    (tensorCochain P Q) (tensorCochain P Q') hK hK'
    (tensorCochainMap (𝟙 P) g)
  left
  intro i
  change QuasiIso (HomologicalComplex.restrictionMap
    ((tensorBicomplexMap (𝟙 P) g).f (-i)) reversal)
  exact (AugmentedDoubleComplexComparison.quasiIso_regrade_iff _).2
    (tensor_column_quasiIso P hflat g hg (-i))

def singleTensorAxisIso (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) :
    tensorBicomplex P ((HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℤ) 0).obj M) ≅
      axisComplex (coefficientComplex P M) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    (HomologicalComplex.singleMapHomologicalComplex (leftTensorFunctor (P.X i))
      (ComplexShape.down ℤ) 0).app M) ?_
  intro i j h
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

/-- Totalization of the tensor with a coefficient placed in degree zero. -/
def singleTensorTotalIso (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) :
    sumTotal (tensorCochain P
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℤ) 0).obj M)) ≅
      reverseChain (coefficientComplex P M) := by
  let e := singleTensorAxisIso P M
  let e' := ((negEmbedding.restrictionFunctor _).mapHomologicalComplex
    (ComplexShape.up ℤ)).mapIso ((negEmbedding.restrictionFunctor _).mapIso e)
  exact HomologicalComplex₂.total.mapIso e' (ComplexShape.up ℤ) ≪≫
    (@asIso _ _ _ _ (regradeTotalMap (axisComplex (coefficientComplex P M)))
      (regradeTotalMap_isIso _)) ≪≫
    (negEmbedding.restrictionFunctor _).mapIso (asIso (axisInclusion (coefficientComplex P M))).symm

/-- The chain augmentation induces this specific map of regraded total complexes. -/
def tensorAugmentationMap
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (M : ModuleCat.{w} R)
    (g : Q ⟶ (HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℤ) 0).obj M) :
    sumTotal (tensorCochain P Q) ⟶ reverseChain (coefficientComplex P M) :=
  HomologicalComplex₂.total.map (tensorCochainMap (𝟙 P) g) (ComplexShape.up ℤ) ≫
    (singleTensorTotalIso P M).hom

theorem singleTensorTotalIso_zero (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (a : ℤ) :
    sumInjection (tensorCochain P
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.down ℤ) 0).obj M))
      a 0 a (add_zero a) ≫ (singleTensorTotalIso P M).hom.f a =
      ModuleCat.ofHom (tensorMap (LinearMap.id : P.X (-a) →ₗ[Rᵐᵒᵖ] P.X (-a))
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 M).hom.hom) := by
  simp only [singleTensorTotalIso, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map]
  simp only [asIso_hom, regradeTotalMap]
  change (((singleTensorAxisIso P M).hom.f (-a)).f (-0) ≫
    sumInjection (cochainBicomplex (axisComplex (coefficientComplex P M))) a 0 a (add_zero a)) ≫
    regradeTotalComponent (axisComplex (coefficientComplex P M)) a ≫
      (inv (axisInclusion (coefficientComplex P M))).f (-a) = _
  rw [Category.assoc, injection_regradeTotalComponent_assoc]
  have haxis : sumInjection (axisComplex (coefficientComplex P M)) (-a) 0 (-a)
      (add_zero (-a)) ≫ (inv (axisInclusion (coefficientComplex P M))).f (-a) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0
        ((coefficientComplex P M).X (-a))).hom := by
    apply (cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0
      ((coefficientComplex P M).X (-a))).inv).1
    simpa only [axisInclusion, HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Category.assoc, Iso.inv_hom_id] using
      congrArg (fun f => f.f (-a)) (IsIso.hom_inv_id (axisInclusion (coefficientComplex P M)))
  change (((HomologicalComplex.singleMapHomologicalComplex (leftTensorFunctor (P.X (-a)))
      (ComplexShape.down ℤ) 0).app M).hom.f 0) ≫
      sumInjection (axisComplex (coefficientComplex P M)) (-a) 0 (-a) (add_zero (-a)) ≫
      (inv (axisInclusion (coefficientComplex P M))).f (-a) = _
  rw [haxis]
  change ((HomologicalComplex.singleMapHomologicalComplex (leftTensorFunctor (P.X (-a)))
    (ComplexShape.down ℤ) 0).hom.app M).f 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0
      ((leftTensorFunctor (P.X (-a))).obj M)).hom = _
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl


theorem cycles_range_eq {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    LinearMap.range (C.sc n).moduleCatToCycles = cycleBoundaries C n := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

def categoricalHomologyIso {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    C.homology n ≅ ModuleCat.of R (Homology C n) :=
  (C.sc n).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (cycles_range_eq C n)).toModuleIso

theorem categoricalHomologyIso_natural {ι : Type*} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{v} R) c} (f : C ⟶ D) (n : ι) :
    HomologicalComplex.homologyMap f n ≫ (categoricalHomologyIso D n).hom =
      (categoricalHomologyIso C n).hom ≫ ModuleCat.ofHom (homologyMap f n) := by
  rw [← cancel_epi (C.homologyπ n), HomologicalComplex.homologyπ_naturality_assoc]
  dsimp only [categoricalHomologyIso, Iso.trans_hom]
  simp only [Category.assoc]
  dsimp only [HomologicalComplex.homologyπ, HomologicalComplex.homology, HomologicalComplex.cycles]
  rw [ShortComplex.π_moduleCatCyclesIso_hom_assoc,
    ShortComplex.π_moduleCatCyclesIso_hom_assoc]
  rw [← cancel_epi (C.sc n).moduleCatCyclesIso.inv]
  simp only [Iso.inv_hom_id_assoc]
  have hc : (C.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap f n ≫
      (D.sc n).moduleCatCyclesIso.hom = ModuleCat.ofHom (cyclesMap f n) := by
    rw [← cancel_mono (D.sc n).moduleCatLeftHomologyData.i]
    dsimp only [HomologicalComplex.cyclesMap, HomologicalComplex.cycles]
    simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i]
    rw [← Category.assoc, ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  have hc' := reassoc_of% hc
  dsimp only [HomologicalComplex.cyclesMap, HomologicalComplex.cycles] at hc' ⊢
  rw [hc']
  apply ModuleCat.hom_ext
  ext z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  simp only [ShortComplex.moduleCatLeftHomologyData_π_hom,
    LinearEquiv.toModuleIso_hom]
  rfl

def reverseHomologyAtNegIso (C : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ) :
    (reverseChain C).homology (-q) ≅ C.homology q :=
  C.restrictionHomologyIso reversal (-q-1) (-q) (-q+1) (by simp) (by simp)
    (show -(-q-1) = q+1 by omega) (show -(-q) = q by omega)
    (show -(-q+1) = q-1 by omega) (by simp) (by simp)

/-- The flat coefficient comparison as a whole complex in the Q direction. -/
private def tensorRowFlatIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j)) (b : ℤ) :
    DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip b ≅
      reverseChain (leftTensorComplex ((reverseChain P).homology b) Q) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p => ?_) ?_
  · have := TorBalance.flat_tensor_preservesHomology (hQ (-p))
    exact ((reverseChain P).sc b).mapHomologyIso (tensorFunctor (Q.X (-p)))
  · intro i j hij
    symm
    have := TorBalance.flat_tensor_preservesHomology (hQ (-i))
    have := TorBalance.flat_tensor_preservesHomology (hQ (-j))
    change HomologicalComplex.homologyMap ((tensorCochain P Q).flip.d i j) b ≫
      (((reverseChain P).sc b).mapHomologyIso (tensorFunctor (Q.X (-j)))).hom =
      (((reverseChain P).sc b).mapHomologyIso (tensorFunctor (Q.X (-i)))).hom ≫
        ModuleCat.ofHom (tensorMap LinearMap.id (Q.d (-i) (-j)).hom)
    change ShortComplex.homologyMap
      (((reverseChain P).sc b).mapNatTrans
        (TorBalance.tensorCoefficientMap (Q.d (-i) (-j)).hom)) ≫ _ = _
    rw [ShortComplex.homologyMap_mapNatTrans]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

def tensorHorizontalHomologyIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j)) (q : ℤ) :
    DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip (-q) ≅
      reverseChain (leftTensorComplex ((reverseChain P).homology (-q)) Q) :=
  tensorRowFlatIso P Q hQ (-q)

def leftTensorComplexFirstIso (A B : ModuleCat.{v} Rᵐᵒᵖ) (e : A ≅ B)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) :
    leftTensorComplex A Q ≅ leftTensorComplex B Q :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (tensorFunctor (Q.X i)).mapIso e) (by
    intro i j hij
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a b
    rfl)

def tensorHorizontalHomologyIso' (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j)) (q : ℤ) :
    DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip (-q) ≅
      reverseChain (leftTensorComplex (P.homology q) Q) :=
  tensorHorizontalHomologyIso P Q hQ q ≪≫
    (reversal.restrictionFunctor _).mapIso
      (leftTensorComplexFirstIso _ _ (reverseHomologyAtNegIso P q) Q)

/-- The signed row identification in the centered index of the page complex. -/
private def rowFirstCenteredShortIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (S : TensorPages P Q)
    (i a b n : ℤ) (hi : i+1 = a) (hn : i+b = n) :
    PageCohomology.shortComplex S.filtration S.pages 1 (by omega) i n ≅
      (DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip b).sc a := by
  subst a n
  let X := DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip b
  exact DoubleComplexFirstPages.rowFirstShortIso (tensorCochain P Q)
    S.filtration S.formula S.pages i b ≪≫
      (X.isoSc' i (i+1) (i+1+1) (by simp) (by simp)).symm

set_option maxHeartbeats 1300000 in
private theorem rowFirstCenteredShortIso_middle
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (S : TensorPages P Q)
    (i a b n : ℤ) (hi : i+1 = a) (hn : i+b = n) :
    (rowFirstCenteredShortIso P Q S i a b n hi hn).hom.τ₂ =
      (a*b).negOnePow •
        (eqToHom (congrArg₂ (PageCohomology.object S.filtration S.pages 1)
          hi (show n+1=a+b by omega)) ≫
          (DoubleComplexFirstPages.rowFirstIso (tensorCochain P Q)
            S.filtration S.formula S.pages a b).hom) := by
  subst a n
  simp only [rowFirstCenteredShortIso, Iso.trans_hom, ShortComplex.comp_τ₂, Iso.symm_hom,
    DoubleComplexFirstPages.rowFirstShortIso, ShortComplex.isoMk_hom_τ₂,
    Preadditive.smul_iso_hom, DoubleComplexFirstPages.rowFirstIsoAt, eqToIso.hom]
  exact Category.comp_id _

private def tensorRowIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (b : ℤ) :
    DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip b ≅
      rowTensorComplex P Q b :=
  tensorRowFlatIso P Q hQ b ≪≫
    (reversal.restrictionFunctor _).mapIso
      (leftTensorComplexFirstIso _ _ (reverseHomologyIso P b) Q)

/-- Construct the comparison of the signed first-page short complexes. -/
def rowTensorComparison
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (S : TensorPages P Q) : RowTensorComparison P Q S := by
  let flat (a : ℤ) := by
    have := TorBalance.flat_tensor_preservesHomology (hQ (-a))
    exact TorBalance.exactHomologyComparison
      (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ)
  refine ⟨DoubleComplexFirstPages.rowData (tensorCochain P Q) S.filtration S.formula S.pages,
    flat, fun a b => rowFirstCenteredShortIso P Q S (a-1) a b (a+b-1)
      (by omega) (by omega) ≪≫ (HomologicalComplex.shortComplexFunctor _ _ a).mapIso (tensorRowIso P Q hQ b),
    ?_⟩
  intro a b
  simp only [Iso.trans_hom, ShortComplex.comp_τ₂, Functor.mapIso_hom,
    HomologicalComplex.shortComplexFunctor_map_τ₂, rowFirstCenteredShortIso_middle,
    Linear.units_smul_comp, Category.assoc]
  rfl

private def tensorExtendIso
    (A : ModuleCat.{v} Rᵐᵒᵖ) (Q : ChainComplex (ModuleCat.{w} R) ℕ) :
    leftTensorComplex A (extendNonnegativeChain Q) ≅
      extendNonnegativeChain (leftOrdinaryTensorComplex A Q) := by
  let F : ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ := leftTensorFunctor A
  let C := leftOrdinaryTensorComplex A Q
  let e := nonnegativeChainEmbedding
  let u (n : ℤ) : (leftTensorComplex A (extendNonnegativeChain Q)).X n ≅
      (extendNonnegativeChain C).X n := by
    by_cases hn : 0 ≤ n
    · exact F.mapIso (Q.extendXIso e (Int.toNat_of_nonneg hn)) ≪≫
        (C.extendXIso e (Int.toNat_of_nonneg hn)).symm
    · exact (F.map_isZero (Q.isZero_extend_X e n
        (fun p hp => hn (by change (p : ℤ) = n at hp; omega)))).iso
        (C.isZero_extend_X e n (fun p hp => hn (by change (p : ℤ) = n at hp; omega)))
  refine HomologicalComplex.Hom.isoOfComponents u ?_
  intro i j hij
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · dsimp only [u]
      rw [dite_eq_left hi, dite_eq_left hj]
      symm
      change F.map ((Q.extend e).d i j) ≫
          ((F.mapIso (Q.extendXIso e (Int.toNat_of_nonneg hj))) ≪≫
            (C.extendXIso e (Int.toNat_of_nonneg hj)).symm).hom =
        ((F.mapIso (Q.extendXIso e (Int.toNat_of_nonneg hi))) ≪≫
            (C.extendXIso e (Int.toNat_of_nonneg hi)).symm).hom ≫ (C.extend e).d i j
      rw [Q.extend_d_eq e (Int.toNat_of_nonneg hi) (Int.toNat_of_nonneg hj),
        C.extend_d_eq e (Int.toNat_of_nonneg hi) (Int.toNat_of_nonneg hj)]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Functor.map_comp_assoc]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
      rfl
    · exact (C.isZero_extend_X e j
        (fun p hp => hj (by change (p : ℤ) = j at hp; omega))).eq_of_tgt _ _
  · exact (F.map_isZero (Q.isZero_extend_X e i
      (fun p hp => hi (by change (p : ℤ) = i at hp; omega)))).eq_of_src _ _

theorem tensorExtendIso_formula
    (A : ModuleCat.{v} Rᵐᵒᵖ) (Q : ChainComplex (ModuleCat.{w} R) ℕ) (p : ℕ) :
    (tensorExtendIso A Q).hom.f p ≫
      ((leftOrdinaryTensorComplex A Q).extendXIso nonnegativeChainEmbedding (i := p) rfl).hom =
    (leftTensorFunctor A).map (Q.extendXIso nonnegativeChainEmbedding (i := p) rfl).hom := by
  simp only [tensorExtendIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    dite_eq_left (Int.natCast_nonneg p), Int.toNat_natCast,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

theorem categoricalHomologyIso_formula {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) (x : C.cycles n) :
    (categoricalHomologyIso C n).hom (C.homologyπ n x) =
      homologyClass C n ((C.sc n).moduleCatCyclesIso.hom x) := by
  have h := congrArg (fun k : C.cycles n ⟶ _ => k.hom x)
    ((C.sc n).π_moduleCatCyclesIso_hom)
  change
    (Submodule.quotEquivOfEq _ _ (cycles_range_eq C n))
      ((C.sc n).moduleCatHomologyIso.hom.hom ((C.sc n).homologyπ.hom x)) =
        homologyClass C n ((C.sc n).moduleCatCyclesIso.hom x)
  change (C.sc n).moduleCatHomologyIso.hom.hom ((C.sc n).homologyπ.hom x) = _ at h
  rw [h]
  rfl

private def ordinaryTensorComparison
    (A : ModuleCat.{v} Rᵐᵒᵖ) (Q : ChainComplex (ModuleCat.{w} R) ℕ) :
    OrdinaryTensorComparison A Q where
  extension := tensorExtendIso A Q
  extension_formula := tensorExtendIso_formula A Q
  quotient := categoricalHomologyIso _
  quotient_formula := categoricalHomologyIso_formula _

def tensorSecondIso (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (S : TensorPages P Q) (p q : ℤ) :
    S.term 2 p q ≅ (leftTensorComplex (P.homology q) Q).homology p := by
  have e := (DoubleComplexFirstPages.rowData (tensorCochain P Q)
    S.filtration S.formula S.pages).secondIso (-p) (-q)
  have e' : S.term 2 p q ≅
      (DoubleComplexFirstPages.verticalHomology (tensorCochain P Q).flip (-q)).homology (-p) := by
    exact eqToIso (show S.term 2 p q = DoubleComplexFirstPages.page S.filtration S.pages 2 (-p) (-q) from by
      unfold TensorPages.term DoubleComplexFirstPages.page
      congr 1 <;> omega) ≪≫ e
  exact e' ≪≫ HomologicalComplex.homologyMapIso (tensorHorizontalHomologyIso' P Q hQ q) (-p) ≪≫
    reverseHomologyAtNegIso (leftTensorComplex (P.homology q) Q) p

def leftTensorExtendedHomologyIso (A : ModuleCat.{v} Rᵐᵒᵖ)
    (Q : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    (leftTensorComplex A (extendNonnegativeChain Q)).homology (n : ℤ) ≅
      ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex A Q) n) := by
  let C := leftTensorComplex A (extendNonnegativeChain Q)
  have hC : SupportedIn C (Set.Ici 0) := by
    intro j hj
    have hj' : j < 0 := by simpa using hj
    have hz : IsZero ((extendNonnegativeChain Q).X j) :=
      Q.isZero_extend_X nonnegativeChainEmbedding j (by intro i hi; change (i : ℤ) = j at hi; omega)
    have hz' := Functor.map_isZero (leftTensorFunctor A) hz
    exact (ModuleCat.isZero_iff_subsingleton).mp hz'
  exact categoricalHomologyIso C n ≪≫
    (P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm.toModuleIso ≪≫
    (quotientHomology (ComplexShape.down ℕ) n).mapIso
      (P103.Ch11.TorBalance.restrictExtendMapIso Q (leftTensorFunctor A))

theorem extendedResolution_flat
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (hQ : Q.IsProjective) (j : ℤ) :
    P103.Specs.Ch02.FlatnessTests.Flat.{u,max u w,v} R ((extendNonnegativeChain Q.complex).X j) := by
  have hp : Module.Projective R ((extendNonnegativeChain Q.complex).X j) := by
    by_cases hj : 0 ≤ j
    · let n := j.toNat
      have hn : (n : ℤ) = j := Int.toNat_of_nonneg hj
      letI := hQ n
      exact Module.Projective.of_equiv'
        (Q.complex.extendXIso nonnegativeChainEmbedding hn).toLinearEquiv.symm
    · have hz : IsZero ((extendNonnegativeChain Q.complex).X j) :=
        Q.complex.isZero_extend_X nonnegativeChainEmbedding j
          (by intro i hi; change (i : ℤ) = j at hi; omega)
      letI := (ModuleCat.isZero_iff_subsingleton).mp hz
      infer_instance
  exact P103.Ch02.FlatnessTests.projective_flat R _ hp

theorem resolution_second_iso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (hQ : Q.IsProjective)
    (T : CanonicalTheory.{u,v,w} R)
    (S : TensorPages P (extendNonnegativeChain Q.complex)) (p : ℕ) (q : ℤ) :
    Nonempty (S.term 2 (p : ℤ) q ≅ ModuleCat.of ℤ (T.Tor (P.homology q) M p)) := by
  obtain ⟨α, hL, hR⟩ := TorBalance.balance R (P.homology q) M
    (T.rightResolutions (P.homology q)).val Q
    (T.rightResolutions (P.homology q)).property hQ
  exact ⟨tensorSecondIso P (extendNonnegativeChain Q.complex)
      (extendedResolution_flat M Q hQ) S p q ≪≫
    leftTensorExtendedHomologyIso (P.homology q) Q.complex p ≪≫
    (balanceEquiv α hL hR p).symm.toModuleIso⟩

def reverseHomotopy {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    {C D : ChainComplex A ℤ} {f g : C ⟶ D} (h : Homotopy f g) :
    Homotopy (HomologicalComplex.restrictionMap f reversal)
      (HomologicalComplex.restrictionMap g reversal) where
  hom i j := h.hom (-i) (-j)
  zero i j hij := by
    apply h.zero
    simp only [ComplexShape.up_Rel, ComplexShape.down_Rel] at hij ⊢
    omega
  comm i := by
    have hi := h.comm (-i)
    rw [dNext_eq h.hom (show (ComplexShape.down ℤ).Rel (-i) (-i-1) by simp),
      prevD_eq h.hom (show (ComplexShape.down ℤ).Rel (-i+1) (-i) by simp)] at hi
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i by simp)]
    change f.f (-i) = C.d (-i) (-(i+1)) ≫ h.hom (-(i+1)) (-i) +
      h.hom (-i) (-(i-1)) ≫ D.d (-(i-1)) (-i) + g.f (-i)
    rw [show -(i+1) = -i-1 by omega, show -(i-1) = -i+1 by omega]
    exact hi

abbrev tensorHorizontalHomologyMap
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') (q : ℤ) :=
  DoubleComplexFirstPages.verticalHomologyMap (tensorCochain P Q).flip
    ((HomologicalComplex₂.flipFunctor (ModuleCat.{max v w} ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map (tensorCochainMap (𝟙 P) g)) (-q)

theorem tensorHorizontalHomologyIso_natural
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (q : ℤ) :
    tensorHorizontalHomologyMap P g q ≫ (tensorHorizontalHomologyIso P Q' hQ' q).hom =
      (tensorHorizontalHomologyIso P Q hQ q).hom ≫
        HomologicalComplex.restrictionMap
          (((leftTensorFunctor ((reverseChain P).homology (-q))).mapHomologicalComplex
            (ComplexShape.down ℤ)).map g) reversal := by
  apply HomologicalComplex.Hom.ext
  funext i
  have := TorBalance.flat_tensor_preservesHomology (hQ (-i))
  have := TorBalance.flat_tensor_preservesHomology (hQ' (-i))
  change HomologicalComplex.homologyMap
    (((HomologicalComplex₂.flipFunctor _ _ _).map (tensorCochainMap (𝟙 P) g)).f i) (-q) ≫
      (((reverseChain P).sc (-q)).mapHomologyIso (tensorFunctor (Q'.X (-i)))).hom =
      (((reverseChain P).sc (-q)).mapHomologyIso (tensorFunctor (Q.X (-i)))).hom ≫
        ModuleCat.ofHom (tensorMap LinearMap.id (g.f (-i)).hom)
  change ShortComplex.homologyMap
    (((reverseChain P).sc (-q)).mapNatTrans
      (TorBalance.tensorCoefficientMap (g.f (-i)).hom)) ≫ _ = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem tensorHorizontalHomologyMap_eq_of_homotopy
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    {g g' : Q ⟶ Q'} (h : Homotopy g g') (p q : ℤ) :
    HomologicalComplex.homologyMap (tensorHorizontalHomologyMap P g q) (-p) =
      HomologicalComplex.homologyMap (tensorHorizontalHomologyMap P g' q) (-p) := by
  let e := tensorHorizontalHomologyIso P Q hQ q
  let e' := tensorHorizontalHomologyIso P Q' hQ' q
  have hn := tensorHorizontalHomologyIso_natural P hQ hQ' g q
  have hn' := tensorHorizontalHomologyIso_natural P hQ hQ' g' q
  have he := congrArg (fun f => HomologicalComplex.homologyMap f (-p)) hn
  have he' := congrArg (fun f => HomologicalComplex.homologyMap f (-p)) hn'
  have hh := (reverseHomotopy ((leftTensorFunctor ((reverseChain P).homology (-q))).mapHomotopy h)).homologyMap_eq (-p)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp, hh] at he
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he'
  exact (cancel_mono (HomologicalComplex.homologyMap e'.hom (-p))).1 (he.trans he'.symm)

theorem tensor_second_page_maps_eq_of_homotopy
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (S : TensorPages P Q) (S' : TensorPages P Q')
    {g g' : Q ⟶ Q'} (ht : Homotopy g g')
    (f f' : FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P Q'), S'.filtration⟩)
    (hf : f.hom = HomologicalComplex₂.total.map (tensorCochainMap (𝟙 P) g) (ComplexShape.up ℤ))
    (hf' : f'.hom = HomologicalComplex₂.total.map (tensorCochainMap (𝟙 P) g') (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData f S.pages S'.pages)
    (N : FilteredPageFunctoriality.MapData f' S.pages S'.pages) (p n : ℤ) :
    M.map 2 p n = N.map 2 p n := by
  have hm := DoubleComplexFirstPages.rowSecondIso_naturality (tensorCochain P Q)
    S.filtration S.formula S'.filtration S'.formula S.pages S'.pages
    (tensorCochainMap (𝟙 P) g) f hf M p (n-p)
  have hn := DoubleComplexFirstPages.rowSecondIso_naturality (tensorCochain P Q)
    S.filtration S.formula S'.filtration S'.formula S.pages S'.pages
    (tensorCochainMap (𝟙 P) g') f' hf' N p (n-p)
  have he := tensorHorizontalHomologyMap_eq_of_homotopy P hQ hQ' ht (-p) (p-n)
  have hnq : -(p-n) = n-p := by omega
  have hnp : -(-p) = p := by omega
  dsimp only [tensorHorizontalHomologyMap] at he
  rw [hnq, hnp] at he
  rw [he] at hm
  have hh := hm.trans hn.symm
  have hpn : p + (n-p) = n := by omega
  have hh' := (cancel_mono _).1 hh
  rw [hpn] at hh'
  exact hh'

theorem balancedTorIso_natural
    (T : CanonicalTheory.{u,v,w} R)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} {M M' : ModuleCat.{w} R}
    (Q : LeftResolution R M) (Q' : LeftResolution R M')
    (f : A ⟶ A') (g : M ⟶ M')
    (l : (T.rightResolutions A).val.complex ⟶ (T.rightResolutions A').val.complex)
    (m : Q.complex ⟶ Q'.complex)
    (hl : ChainLift (T.rightResolutions A).val (T.rightResolutions A').val f.hom l)
    (hm : ChainLift Q Q' g.hom m)
    (α : Augmentations (T.rightResolutions A).val Q)
    (β : Augmentations (T.rightResolutions A').val Q')
    (hαL : QuasiIsomorphism α.left) (hαR : QuasiIsomorphism α.right)
    (hβL : QuasiIsomorphism β.left) (hβR : QuasiIsomorphism β.right) (n : ℕ) :
    ModuleCat.ofHom (homologyMap (leftTensorMap f.hom m) n) ≫
        (balanceEquiv β hβL hβR n).symm.toModuleIso.hom =
      (balanceEquiv α hαL hαR n).symm.toModuleIso.hom ≫
        ModuleCat.ofHom (T.torMap n f g) := by
  have hn := TorBalance.balance_naturality R A A' M M'
    (T.rightResolutions A).val (T.rightResolutions A').val Q Q'
    f.hom g.hom l m hl hm α β hαL hαR hβL hβR n
  have ht := (T.torMaps n).formula (T.rightResolutions A)
    (T.rightResolutions A') f g l hl
  rw [← ht] at hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (balanceEquiv β hβL hβR n).symm (homologyMap (leftTensorMap f.hom m) n z) =
    T.torMap n f g ((balanceEquiv α hαL hαR n).symm z)
  apply (balanceEquiv β hβL hβR n).injective
  rw [LinearEquiv.apply_symm_apply]
  have hz := (LinearMap.congr_fun hn ((balanceEquiv α hαL hαR n).symm z)).symm
  change homologyMap (leftTensorMap f.hom m) n
    ((balanceEquiv α hαL hαR n) ((balanceEquiv α hαL hαR n).symm z)) = _ at hz
  rw [LinearEquiv.apply_symm_apply] at hz
  exact hz

def leftTensorIntegerMap {A A' : ModuleCat.{v} Rᵐᵒᵖ}
    (a : A ⟶ A') {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') :
    leftTensorComplex A Q ⟶ leftTensorComplex A' Q' where
  f i := ModuleCat.ofHom (tensorMap a.hom (g.f i).hom)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x y
    change P103.BalancedTensor.tmul R (a.hom x) ((Q'.d i j).hom ((g.f i).hom y)) =
      P103.BalancedTensor.tmul R (a.hom x) ((g.f j).hom ((Q.d i j).hom y))
    exact congrArg (P103.BalancedTensor.tmul R (a.hom x))
      (congrArg (fun k => k.hom y) (g.comm i j))

private abbrev tensorRowHomologyMap
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') (b : ℤ) :=
  DoubleComplexFirstPages.verticalHomologyMap (tensorCochain P Q).flip
    ((HomologicalComplex₂.flipFunctor (ModuleCat.{max v w} ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map (tensorCochainMap f g)) b

private theorem tensorRowFlatIso_pair_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (b : ℤ) :
    tensorRowHomologyMap f g b ≫ (tensorRowFlatIso P' Q' hQ' b).hom =
      (tensorRowFlatIso P Q hQ b).hom ≫
        HomologicalComplex.restrictionMap
          (leftTensorIntegerMap
            (HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f reversal) b) g) reversal := by
  apply HomologicalComplex.Hom.ext
  funext i
  have := TorBalance.flat_tensor_preservesHomology (hQ (-i))
  have := TorBalance.flat_tensor_preservesHomology (hQ' (-i))
  let ff := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) b).map
    (HomologicalComplex.restrictionMap f reversal)
  let F : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ := tensorFunctor (Q.X (-i))
  let G : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ := tensorFunctor (Q'.X (-i))
  let τ : F ⟶ G := TorBalance.tensorCoefficientMap (g.f (-i)).hom
  have hf : (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) b).map
      (((HomologicalComplex₂.flipFunctor _ _ _).map (tensorCochainMap f g)).f i) =
      F.mapShortComplex.map ff ≫ ((reverseChain P').sc b).mapNatTrans τ := by
    apply ShortComplex.hom_ext <;> apply ModuleCat.hom_ext <;> apply tensor_hom_ext <;> intros <;> rfl
  change ShortComplex.homologyMap _ ≫ _ = _
  rw [hf, ShortComplex.homologyMap_comp]
  dsimp only [tensorRowFlatIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [Category.assoc, ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ShortComplex.mapHomologyIso_hom_naturality]
  dsimp only [G, F, τ, ff, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f, HomologicalComplex.restrictionMap_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply congrArg (fun k => (((reverseChain P).sc b).mapHomologyIso
    (tensorFunctor (Q.X (-i)))).hom ≫ k)
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

abbrev tensorHorizontalPairHomologyMap
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') (q : ℤ)  :=
  tensorRowHomologyMap f g (-q)

theorem tensorHorizontalHomologyIso_pair_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (q : ℤ) :
    tensorHorizontalPairHomologyMap f g q ≫ (tensorHorizontalHomologyIso P' Q' hQ' q).hom =
      (tensorHorizontalHomologyIso P Q hQ q).hom ≫
        HomologicalComplex.restrictionMap
          (leftTensorIntegerMap
            (HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f reversal) (-q)) g) reversal :=
  tensorRowFlatIso_pair_natural f hQ hQ' g (-q)

theorem reverseHomologyIso_natural
    {C D : ChainComplex (ModuleCat.{v} R) ℤ} (f : C ⟶ D) (q : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f reversal) (-q) ≫
        (reverseHomologyAtNegIso D q).hom =
      (reverseHomologyAtNegIso C q).hom ≫ HomologicalComplex.homologyMap f q := by
  rw [← cancel_epi ((reverseChain C).homologyπ (-q)),
    HomologicalComplex.homologyπ_naturality_assoc]
  dsimp only [reverseHomologyAtNegIso]
  rw [HomologicalComplex.homologyπ_restrictionHomologyIso_hom,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom_assoc]
  rw [HomologicalComplex.homologyπ_naturality]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (D.iCycles q)]
  simp only [Category.assoc, HomologicalComplex.restrictionCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i]
  dsimp only [HomologicalComplex.restrictionMap_f, HomologicalComplex.restrictionXIso]
  rw [HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.restrictionCyclesIso_hom_iCycles_assoc]
  dsimp only [HomologicalComplex.restrictionMap_f, HomologicalComplex.restrictionXIso]
  congr 1
  exact HomologicalComplex.XIsoOfEq_hom_naturality f (show -(-q) = q by omega)

theorem leftTensorComplexFirstIso_natural
    {A A' B B' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A') (b : B ⟶ B')
    (e : A ≅ B) (e' : A' ≅ B') (h : a ≫ e'.hom = e.hom ≫ b)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q') :
    leftTensorIntegerMap a g ≫ (leftTensorComplexFirstIso A' B' e' Q').hom =
      (leftTensorComplexFirstIso A B e Q).hom ≫ leftTensorIntegerMap b g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro x y
  change P103.BalancedTensor.tmul R (e'.hom.hom (a.hom x)) ((g.f i).hom y) =
    P103.BalancedTensor.tmul R (b.hom (e.hom.hom x)) ((g.f i).hom y)
  exact congrArg (fun z => P103.BalancedTensor.tmul R z ((g.f i).hom y))
    (congrArg (fun k => k.hom x) h)

theorem tensorHorizontalHomologyIso'_pair_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (q : ℤ) :
    tensorHorizontalPairHomologyMap f g q ≫ (tensorHorizontalHomologyIso' P' Q' hQ' q).hom =
      (tensorHorizontalHomologyIso' P Q hQ q).hom ≫
        HomologicalComplex.restrictionMap
          (leftTensorIntegerMap (HomologicalComplex.homologyMap f q) g) reversal := by
  dsimp only [tensorHorizontalHomologyIso', Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, tensorHorizontalHomologyIso_pair_natural f hQ hQ' g q]
  have hn := leftTensorComplexFirstIso_natural
    (HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f reversal) (-q))
    (HomologicalComplex.homologyMap f q) (reverseHomologyAtNegIso P q) (reverseHomologyAtNegIso P' q)
    (reverseHomologyIso_natural f q) g
  have hn' := congrArg ((reversal.restrictionFunctor (ModuleCat.{max v w} ℤ)).map) hn
  rw [Functor.map_comp, Functor.map_comp] at hn'
  have hn'' := congrArg (fun k => (tensorHorizontalHomologyIso P Q hQ q).hom ≫ k) hn'
  dsimp only [ComplexShape.Embedding.restrictionFunctor, reverseChain] at hn'' ⊢
  simpa only [Category.assoc] using hn''

set_option maxHeartbeats 3000000 in
theorem tensorSecondIso_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (S : TensorPages P Q) (S' : TensorPages P' Q')
    (h : FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P' Q'), S'.filtration⟩)
    (hh : h.hom = HomologicalComplex₂.total.map (tensorCochainMap f g) (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages) (p q : ℤ) :
    M.map 2 (-p) (-(p+q)) ≫ (tensorSecondIso P' Q' hQ' S' p q).hom =
      (tensorSecondIso P Q hQ S p q).hom ≫
        HomologicalComplex.homologyMap
          (leftTensorIntegerMap (HomologicalComplex.homologyMap f q) g) p := by
  have hr := DoubleComplexFirstPages.rowSecondIso_naturality (tensorCochain P Q)
    S.filtration S.formula S'.filtration S'.formula S.pages S'.pages
    (tensorCochainMap f g) h hh M (-p) (-q)
  have hn := congrArg (fun k => HomologicalComplex.homologyMap k (-p))
    (tensorHorizontalHomologyIso'_pair_natural f hQ hQ' g q)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hn
  have hv := reverseHomologyIso_natural
    (leftTensorIntegerMap (HomologicalComplex.homologyMap f q) g) p
  dsimp only [tensorSecondIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  dsimp only [DoubleComplexFirstPages.rowData, eqToIso.hom]
  have ht := DoubleComplexFirstPages.rowPageMap_transport (tensorCochain P Q)
    S.filtration S'.filtration S.pages S'.pages
    (tensorCochainMap f g) h hh M 2 (-p) (-p) (-(p+q)) (-p + -q) rfl (by omega)
  simp only [Category.assoc]
  rw [reassoc_of% ht, reassoc_of% hr, reassoc_of% hn, hv]


structure BalanceData (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R) (Q : LeftResolution R M) where
  augmentation : Augmentations (T.rightResolutions A).val Q
  left_quasiIso : QuasiIsomorphism augmentation.left
  right_quasiIso : QuasiIsomorphism augmentation.right

def balanceData (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R) (Q : LeftResolution R M)
    (hQ : Q.IsProjective) : BalanceData T A M Q := by
  have h := TorBalance.balance R A M (T.rightResolutions A).val Q
    (T.rightResolutions A).property hQ
  exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

def leftResolutionTorIso (T : CanonicalTheory.{u,v,w} R)
    (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R) (Q : LeftResolution R M)
    (hQ : Q.IsProjective) (n : ℕ) :
    ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex A Q.complex) n) ≅
      ModuleCat.of ℤ (T.Tor A M n) :=
  (balanceEquiv (balanceData T A M Q hQ).augmentation
    (balanceData T A M Q hQ).left_quasiIso
    (balanceData T A M Q hQ).right_quasiIso n).symm.toModuleIso

theorem leftResolutionTorIso_natural
    (T : CanonicalTheory.{u,v,w} R)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} {M M' : ModuleCat.{w} R}
    (Q : LeftResolution R M) (Q' : LeftResolution R M')
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (f : A ⟶ A') (g : M ⟶ M') (m : Q.complex ⟶ Q'.complex)
    (hm : ChainLift Q Q' g.hom m) (n : ℕ) :
    ModuleCat.ofHom (homologyMap (leftTensorMap f.hom m) n) ≫
        (leftResolutionTorIso T A' M' Q' hQ' n).hom =
      (leftResolutionTorIso T A M Q hQ n).hom ≫
        ModuleCat.ofHom (T.torMap n f g) := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists Rᵐᵒᵖ A A'
    (T.rightResolutions A).val (T.rightResolutions A').val
    (T.rightResolutions A).property f.hom
  exact balancedTorIso_natural T Q Q' f g l m hl hm
    (balanceData T A M Q hQ).augmentation (balanceData T A' M' Q' hQ').augmentation
    (balanceData T A M Q hQ).left_quasiIso (balanceData T A M Q hQ).right_quasiIso
    (balanceData T A' M' Q' hQ').left_quasiIso (balanceData T A' M' Q' hQ').right_quasiIso n

/-- The actual signed row, ordinary quotient, and augmentation comparisons. -/
def resolutionSecondPageComparison
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (hQ : Q.IsProjective)
    (T : CanonicalTheory.{u,v,w} R)
    (S : TensorPages P (extendNonnegativeChain Q.complex)) :
    ResolutionSecondPageComparison T P M Q S where
  rowComparison := rowTensorComparison P _ (extendedResolution_flat M Q hQ) S
  ordinary q := ordinaryTensorComparison (P.homology q) Q.complex
  balance q := (balanceData T (P.homology q) M Q hQ).augmentation
  leftQuasiIso q := (balanceData T (P.homology q) M Q hQ).left_quasiIso
  rightQuasiIso q := (balanceData T (P.homology q) M Q hQ).right_quasiIso

def resolutionSecondIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (hQ : Q.IsProjective)
    (T : CanonicalTheory.{u,v,w} R)
    (S : TensorPages P (extendNonnegativeChain Q.complex)) (p : ℕ) (q : ℤ) :
    S.term 2 (p : ℤ) q ≅ ModuleCat.of ℤ (T.Tor (P.homology q) M p) :=
  (resolutionSecondPageComparison P M Q hQ T S).iso p q

theorem tensorRestrictExtendIso_natural
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℕ} (g : Q ⟶ Q') :
    HomologicalComplex.restrictionMap
        (leftTensorIntegerMap a (HomologicalComplex.extendMap g nonnegativeChainEmbedding))
        nonnegativeChainEmbedding ≫
      (P103.Ch11.TorBalance.restrictExtendMapIso Q' (leftTensorFunctor A')).hom =
      (P103.Ch11.TorBalance.restrictExtendMapIso Q (leftTensorFunctor A)).hom ≫
        leftTensorMap a.hom g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro x y
  change P103.BalancedTensor.tmul R (a.hom x)
      ((Q'.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom.hom
        (((HomologicalComplex.extendMap g nonnegativeChainEmbedding).f i).hom y)) =
    P103.BalancedTensor.tmul R (a.hom x)
      ((g.f i).hom ((Q.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom.hom y))
  apply congrArg (P103.BalancedTensor.tmul R (a.hom x))
  have hi := HomologicalComplex.extendMap_f g nonnegativeChainEmbedding (i := i) rfl
  have hi' := congrArg (fun k => k ≫ (Q'.extendXIso nonnegativeChainEmbedding (i := i) rfl).hom) hi
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hi'
  exact congrArg (fun k => k.hom y) hi'

theorem explicitRestrictionInverse_natural
    {S : Type*} [Ring S] (C D : ChainComplex (ModuleCat.{v} S) ℤ)
    (hC : SupportedIn C (Set.Ici 0)) (hD : SupportedIn D (Set.Ici 0))
    (f : C ⟶ D) (n : ℕ) :
    ModuleCat.ofHom (homologyMap f (n : ℤ)) ≫
        (P103.Ch11.TorBalance.restrictionHomologyEquiv D hD n).symm.toModuleIso.hom =
      (P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm.toModuleIso.hom ≫
        ModuleCat.ofHom (homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) n) := by
  have hn := P103.Ch11.TorBalance.restrictionHomologyEquiv_natural hC hD f n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (P103.Ch11.TorBalance.restrictionHomologyEquiv D hD n).symm
      (homologyMap f (n : ℤ) z) =
    homologyMap (HomologicalComplex.restrictionMap f nonnegativeChainEmbedding) n
      ((P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm z)
  apply (P103.Ch11.TorBalance.restrictionHomologyEquiv D hD n).injective
  rw [LinearEquiv.apply_symm_apply]
  have hz := (LinearMap.congr_fun hn
    ((P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm z)).symm
  change homologyMap f (n : ℤ)
    ((P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n)
      ((P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm z)) = _ at hz
  rw [LinearEquiv.apply_symm_apply] at hz
  exact hz

 theorem leftTensorExtendedHomologyIso_natural
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℕ} (g : Q ⟶ Q') (n : ℕ) :
    HomologicalComplex.homologyMap
        (leftTensorIntegerMap a (HomologicalComplex.extendMap g nonnegativeChainEmbedding)) (n : ℤ) ≫
      (leftTensorExtendedHomologyIso A' Q' n).hom =
      (leftTensorExtendedHomologyIso A Q n).hom ≫
        ModuleCat.ofHom (homologyMap (leftTensorMap a.hom g) n) := by
  let C := leftTensorComplex A (extendNonnegativeChain Q)
  let D := leftTensorComplex A' (extendNonnegativeChain Q')
  let f := leftTensorIntegerMap a (HomologicalComplex.extendMap g nonnegativeChainEmbedding)
  have hC : SupportedIn C (Set.Ici 0) := by
    intro j hj
    have hj' : j < 0 := by simpa using hj
    have hz : IsZero ((extendNonnegativeChain Q).X j) :=
      Q.isZero_extend_X nonnegativeChainEmbedding j
        (by intro i hi; change (i : ℤ) = j at hi; omega)
    exact (ModuleCat.isZero_iff_subsingleton).mp (Functor.map_isZero (leftTensorFunctor A) hz)
  have hD : SupportedIn D (Set.Ici 0) := by
    intro j hj
    have hj' : j < 0 := by simpa using hj
    have hz : IsZero ((extendNonnegativeChain Q').X j) :=
      Q'.isZero_extend_X nonnegativeChainEmbedding j
        (by intro i hi; change (i : ℤ) = j at hi; omega)
    exact (ModuleCat.isZero_iff_subsingleton).mp (Functor.map_isZero (leftTensorFunctor A') hz)
  have h₁ := categoricalHomologyIso_natural f (n : ℤ)
  have h₂ := explicitRestrictionInverse_natural C D hC hD f n
  have h₃ := congrArg ((quotientHomology (ComplexShape.down ℕ) n).map)
    (tensorRestrictExtendIso_natural a g)
  rw [Functor.map_comp, Functor.map_comp] at h₃
  dsimp only [leftTensorExtendedHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  dsimp only [C, D, f, extendNonnegativeChain, extendByZero, SupportedIn] at h₁ h₂ ⊢
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂]
  change (categoricalHomologyIso C (n : ℤ)).hom ≫
      (P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm.toModuleIso.hom ≫ _ = _
  have h₃' := congrArg (fun k => (categoricalHomologyIso C (n : ℤ)).hom ≫
    (P103.Ch11.TorBalance.restrictionHomologyEquiv C hC n).symm.toModuleIso.hom ≫ k) h₃
  dsimp only [C, D, f, extendNonnegativeChain, extendByZero, quotientHomology] at h₃' ⊢
  simpa only [Category.assoc] using h₃'

private theorem reverseHomologyIso_at_naturality
    {A : Type*} [Category* A] [Abelian A]
    {C D : ChainComplex A ℤ} (f : C ⟶ D) (a : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f reversal) a ≫
        (reverseHomologyIso D a).hom =
      (reverseHomologyIso C a).hom ≫ HomologicalComplex.homologyMap f (reversal.f a) := by
  rw [← cancel_epi ((reverseChain C).homologyπ a),
    HomologicalComplex.homologyπ_naturality_assoc]
  dsimp only [reverseHomologyIso]
  rw [HomologicalComplex.homologyπ_restrictionHomologyIso_hom,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom_assoc]
  rw [HomologicalComplex.homologyπ_naturality]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (D.iCycles (reversal.f a))]
  simp only [Category.assoc, HomologicalComplex.restrictionCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i]
  dsimp only [HomologicalComplex.restrictionMap_f, HomologicalComplex.restrictionXIso]
  rw [HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.restrictionCyclesIso_hom_iCycles_assoc]
  dsimp only [HomologicalComplex.restrictionMap_f, HomologicalComplex.restrictionXIso]
  congr 1
  exact HomologicalComplex.XIsoOfEq_hom_naturality f (rfl : reversal.f a = reversal.f a)

private theorem tensorRowIso_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (b : ℤ) :
    tensorRowHomologyMap f g b ≫ (tensorRowIso P' Q' hQ' b).hom =
      (tensorRowIso P Q hQ b).hom ≫ HomologicalComplex.restrictionMap
        (leftTensorIntegerMap (HomologicalComplex.homologyMap f (-b)) g) reversal := by
  dsimp only [tensorRowIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, tensorRowFlatIso_pair_natural f hQ hQ' g b]
  have hn := leftTensorComplexFirstIso_natural
    (HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f reversal) b)
    (HomologicalComplex.homologyMap f (-b)) (reverseHomologyIso P b)
    (reverseHomologyIso P' b) (reverseHomologyIso_at_naturality f b) g
  have hn' := congrArg ((reversal.restrictionFunctor (ModuleCat.{max v w} ℤ)).map) hn
  rw [Functor.map_comp, Functor.map_comp] at hn'
  have hn'' := congrArg (fun k => (tensorRowFlatIso P Q hQ b).hom ≫ k) hn'
  dsimp only [ComplexShape.Embedding.restrictionFunctor, reverseChain] at hn'' ⊢
  simpa only [Category.assoc] using hn''

private theorem rowFirstCenteredShortIso_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q')
    (S : TensorPages P Q) (S' : TensorPages P' Q')
    (h : FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P' Q'), S'.filtration⟩)
    (hh : h.hom = HomologicalComplex₂.total.map (tensorCochainMap f g) (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages)
    (i a b n : ℤ) (hi : i+1 = a) (hn : i+b = n) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) i n ≫
        (rowFirstCenteredShortIso P' Q' S' i a b n hi hn).hom =
      (rowFirstCenteredShortIso P Q S i a b n hi hn).hom ≫
        (HomologicalComplex.shortComplexFunctor _ _ a).map (tensorRowHomologyMap f g b) := by
  subst a n
  simpa only [rowFirstCenteredShortIso, tensorRowHomologyMap] using
    DoubleComplexFirstPages.rowFirstCohomologyShortIso_naturality (tensorCochain P Q)
      S.filtration S.formula S'.filtration S'.formula S.pages S'.pages
      (tensorCochainMap f g) h hh M i b

private theorem rowTensorShortIso_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (S : TensorPages P Q) (S' : TensorPages P' Q')
    (h : FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P' Q'), S'.filtration⟩)
    (hh : h.hom = HomologicalComplex₂.total.map (tensorCochainMap f g) (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages) (a b : ℤ) :
    FilteredPageFunctoriality.shortComplexMap M 1 (by omega) (a-1) (a+b-1) ≫
        ((rowTensorComparison P' Q' hQ' S').shortIso a b).hom =
      ((rowTensorComparison P Q hQ S).shortIso a b).hom ≫
        (HomologicalComplex.shortComplexFunctor _ _ a).map
          (HomologicalComplex.restrictionMap
            (leftTensorIntegerMap (HomologicalComplex.homologyMap f (-b)) g) reversal) := by
  dsimp only [rowTensorComparison, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, rowFirstCenteredShortIso_naturality f g S S' h hh M,
    Category.assoc, ← Functor.map_comp, tensorRowIso_naturality, Functor.map_comp,
    Category.assoc]

private theorem tensorExtendIso_naturality
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℕ} (g : Q ⟶ Q') :
    leftTensorIntegerMap a (HomologicalComplex.extendMap g nonnegativeChainEmbedding) ≫
        (tensorExtendIso A' Q').hom =
      (tensorExtendIso A Q).hom ≫
        HomologicalComplex.extendMap (leftTensorMap a.hom g) nonnegativeChainEmbedding := by
  apply HomologicalComplex.Hom.ext
  funext j
  by_cases hj : ∃ p : ℕ, (p : ℤ) = j
  · obtain ⟨p, rfl⟩ := hj
    let e := nonnegativeChainEmbedding
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      ← cancel_mono ((leftOrdinaryTensorComplex A' Q').extendXIso e (i := p) rfl).hom,
      Category.assoc, tensorExtendIso_formula]
    have hh₀ : e.f p = (p : ℤ) := rfl
    rw [HomologicalComplex.extendMap_f _ _ hh₀]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id, Category.comp_id, ← Category.assoc, tensorExtendIso_formula]
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x y
    change P103.BalancedTensor.tmul R (a.hom x)
        ((Q'.extendXIso e (i := p) rfl).hom.hom
          (((HomologicalComplex.extendMap g e).f p).hom y)) =
      P103.BalancedTensor.tmul R (a.hom x) ((g.f p).hom ((Q.extendXIso e (i := p) rfl).hom.hom y))
    apply congrArg (P103.BalancedTensor.tmul R (a.hom x))
    have hh := HomologicalComplex.extendMap_f g e (i := p) rfl
    have hh' := congrArg (fun k => k ≫ (Q'.extendXIso e (i := p) rfl).hom) hh
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh'
    exact congrArg (fun k => k.hom y) hh'
  · exact ((leftOrdinaryTensorComplex A' Q').isZero_extend_X nonnegativeChainEmbedding j
        (fun p hp => hj ⟨p,hp⟩)).eq_of_tgt _ _

private theorem canonicalOrdinaryComparison_naturality
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℕ} (g : Q ⟶ Q') (p : ℕ)
    (k : ℤ) (hk : nonnegativeChainEmbedding.f p = k) :
    let f := leftTensorIntegerMap a (HomologicalComplex.extendMap g nonnegativeChainEmbedding)
    let C := leftOrdinaryTensorComplex A Q
    let C' := leftOrdinaryTensorComplex A' Q'
    let Zi := fun (U : ChainComplex (ModuleCat.{max v w} ℤ) ℕ) =>
      U.extendHomologyIso nonnegativeChainEmbedding (j := p) (j' := k) hk
    HomologicalComplex.homologyMap f k ≫
      HomologicalComplex.homologyMap (tensorExtendIso A' Q').hom k ≫
        (Zi C').hom ≫ (categoricalHomologyIso C' p).hom =
      HomologicalComplex.homologyMap (tensorExtendIso A Q).hom k ≫
        (Zi C).hom ≫ (categoricalHomologyIso C p).hom ≫
          ModuleCat.ofHom (homologyMap (leftTensorMap a.hom g) p) := by
  subst k
  dsimp only
  have h₁ := congrArg (fun k => HomologicalComplex.homologyMap k (nonnegativeChainEmbedding.f p))
    (tensorExtendIso_naturality a g)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h₁
  rw [reassoc_of% h₁,
    HomologicalComplex.extendHomologyIso_hom_naturality_assoc,
    categoricalHomologyIso_natural]

private theorem rowTensorSecondCore_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (g : Q ⟶ Q') (S : TensorPages P Q) (S' : TensorPages P' Q')
    (h : FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P' Q'), S'.filtration⟩)
    (hh : h.hom = HomologicalComplex₂.total.map (tensorCochainMap f g) (ComplexShape.up ℤ))
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages)
    (a b : ℤ) :
    M.map 2 (a-1+1) (a+b-1+1) ≫
      (S'.next.nextIso 1 (by omega) (a-1) (a+b-1)).hom ≫
      (ShortComplex.homologyMapIso ((rowTensorComparison P' Q' hQ' S').shortIso a b)).hom =
      (S.next.nextIso 1 (by omega) (a-1) (a+b-1)).hom ≫
        (ShortComplex.homologyMapIso ((rowTensorComparison P Q hQ S).shortIso a b)).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.restrictionMap
            (leftTensorIntegerMap (HomologicalComplex.homologyMap f (-b)) g) reversal) a := by
  have h₁ := FilteredPageFunctoriality.next_naturality M S.next S'.next 1
    (by omega) (a-1) (a+b-1)
  change M.map 2 (a-1+1) (a+b-1+1) ≫
        (S'.next.nextIso 1 (by omega) (a-1) (a+b-1)).hom =
      (S.next.nextIso 1 (by omega) (a-1) (a+b-1)).hom ≫ _ at h₁
  have h₂ := congrArg (fun x => ShortComplex.homologyMap x)
    (rowTensorShortIso_naturality f hQ hQ' g S S' h hh M a b)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h₂
  simp only [ShortComplex.homologyMapIso_hom]
  rw [reassoc_of% h₁]
  exact congrArg (fun k => (S.next.nextIso 1 (by omega) (a-1) (a+b-1)).hom ≫ k) h₂

private theorem leftTensorDegreeIso_naturality
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ} (g : Q ⟶ Q')
    (b q : ℤ) (h : -b = q) (p : ℤ) :
    HomologicalComplex.homologyMap (leftTensorIntegerMap (HomologicalComplex.homologyMap f (-b)) g) p ≫
      HomologicalComplex.homologyMap
        (eqToHom (congrArg (fun c => leftTensorComplex (P'.homology c) Q') h)) p =
      HomologicalComplex.homologyMap
        (eqToHom (congrArg (fun c => leftTensorComplex (P.homology c) Q) h)) p ≫
      HomologicalComplex.homologyMap (leftTensorIntegerMap (HomologicalComplex.homologyMap f q) g) p := by
  subst q
  simp

set_option maxHeartbeats 4200000 in
theorem resolutionSecondIso_natural
    (T : CanonicalTheory.{u,v,w} R)
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    {M M' : ModuleCat.{w} R} (g : M ⟶ M')
    (Q : LeftResolution R M) (Q' : LeftResolution R M')
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (m : Q.complex ⟶ Q'.complex) (hm : ChainLift Q Q' g.hom m)
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P' (extendNonnegativeChain Q'.complex))
    (h : FilteredMap ⟨sumTotal (tensorCochain P (extendNonnegativeChain Q.complex)), S.filtration⟩
      ⟨sumTotal (tensorCochain P' (extendNonnegativeChain Q'.complex)), S'.filtration⟩)
    (hh : h.hom = HomologicalComplex₂.total.map
      (tensorCochainMap f (HomologicalComplex.extendMap m nonnegativeChainEmbedding)) (ComplexShape.up ℤ))
    (N : FilteredPageFunctoriality.MapData h S.pages S'.pages) (p : ℕ) (q : ℤ) :
    N.map 2 (-(p : ℤ)) (-((p : ℤ)+q)) ≫ (resolutionSecondIso P' M' Q' hQ' T S' p q).hom =
      (resolutionSecondIso P M Q hQ T S p q).hom ≫
        ModuleCat.ofHom (T.torMap p (HomologicalComplex.homologyMap f q) g) := by
  let a : ℤ := -(p : ℤ)
  let b : ℤ := -q
  let g' := HomologicalComplex.extendMap m nonnegativeChainEmbedding
  have h₁ := DoubleComplexFirstPages.rowPageMap_transport (tensorCochain P _)
    S.filtration S'.filtration S.pages S'.pages (tensorCochainMap f g') h hh N
    2 (-(p : ℤ)) (a-1+1) (-((p : ℤ)+q)) (a+b-1+1)
    (by dsimp [a]; omega) (by dsimp [a,b]; omega)
  have h₂ := rowTensorSecondCore_naturality f (extendedResolution_flat M Q hQ)
    (extendedResolution_flat M' Q' hQ') g' S S' h hh N a b
  have h₃ := reverseHomologyIso_at_naturality
    (leftTensorIntegerMap (HomologicalComplex.homologyMap f (-b)) g') a
  have h₄ := leftTensorDegreeIso_naturality f g' b q (neg_neg q) (-a)
  have h₅ := canonicalOrdinaryComparison_naturality
    (HomologicalComplex.homologyMap f q) m p (-a) (neg_neg (p : ℤ)).symm
  have h₆ := leftResolutionTorIso_natural T Q Q' hQ hQ'
    (HomologicalComplex.homologyMap f q) g m hm p
  simp only [resolutionSecondIso, ResolutionSecondPageComparison.iso, resolutionSecondPageComparison,
    RowTensorComparison.ordinaryHomologyIso, ordinaryTensorComparison, Iso.trans_hom, eqToIso.hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, HomologicalComplex.homologyFunctor,
    HomologicalComplex.homologyMap_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂]
  erw [reassoc_of% h₃, reassoc_of% h₄]
  erw [reassoc_of% h₅]
  erw [h₆]
  rfl

abbrev liftedCoefficient (M : ModuleCat.{w} R) : ModuleCat.{max u w} R :=
  ModuleCat.of R (ULift.{u} M)

def resolutionNatAugmentation (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    Q.complex ⟶ (HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℕ) 0).obj
      (liftedCoefficient M) :=
  HomologicalComplex.mkHomToSingle
    (ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap.comp Q.ε))
    (by
      intro i hi
      have hi' : i = 1 := by simpa using hi.symm
      subst i
      apply ModuleCat.hom_ext
      ext x
      change Q.ε ((Q.complex.d 1 0).hom x) = 0
      have hx : (Q.complex.d 1 0).hom x ∈ LinearMap.ker Q.ε := by
        rw [← Q.exact_zero]
        exact ⟨x,rfl⟩
      exact hx)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionNatAugmentation_quasiIso (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    QuasiIso (resolutionNatAugmentation M Q) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    let a : Q.complex.X 0 ⟶ liftedCoefficient M :=
      ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap.comp Q.ε)
    have he : Function.Exact (Q.complex.d 1 0).hom a.hom := by
      apply LinearMap.exact_iff.mpr
      change LinearMap.ker ((ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap.comp Q.ε) = _
      ext x
      change ULift.up (Q.ε x) = 0 ↔ _
      rw [Q.exact_zero]
      constructor
      · intro hx; exact congrArg ULift.down hx
      · intro hx; exact ULift.ext hx
    have hs : Function.Surjective a.hom :=
      (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.surjective.comp Q.surjective
    let c : CokernelCofork (Q.complex.d 1 0) :=
      CokernelCofork.ofπ a (by apply ModuleCat.hom_ext; exact LinearMap.ext he.apply_apply_eq_zero)
    let hc : IsColimit c := ModuleCat.isColimitCokernelCofork _ a he hs
    let S := Q.complex.sc' 1 0 0
    let T := ((HomologicalComplex.single (ModuleCat.{max u w} R)
      (ComplexShape.down ℕ) 0).obj (liftedCoefficient M)).sc' 1 0 0
    have hg : S.g = 0 := Q.complex.shape 0 0 (by simp)
    have hfT : T.f = 0 := by simp [T]
    have hgT : T.g = 0 := by simp [T]
    let γ : ShortComplex.RightHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' _ _ 1 0 0).map
        (resolutionNatAugmentation M Q))
      (ShortComplex.RightHomologyData.ofIsColimitCokernelCofork S hg c hc)
      (ShortComplex.RightHomologyData.ofZeros T hfT hgT) := {
      φQ := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (liftedCoefficient M)).inv
      φH := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (liftedCoefficient M)).inv
      commp := by
        simp [c, a, resolutionNatAugmentation]
        rfl
      commg' := by
        rw [ShortComplex.RightHomologyData.ofZeros_g',
          ShortComplex.RightHomologyData.ofIsColimitCokernelCofork_g']
        simp
      commι := by simp }
    exact γ.quasiIso_iff.mpr inferInstance
  | succ n =>
    apply (quasiIsoAt_iff_exactAt' _ _
      (HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega))).mpr
    apply (Q.complex.exactAt_iff' (n+2) (n+1) n
      (by simp [ChainComplex.prev]) (by simp)).mpr
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact Q.exact_succ n

def resolutionAugmentation (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    extendNonnegativeChain Q.complex ⟶
      (HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℤ) 0).obj
        (liftedCoefficient M) :=
  HomologicalComplex.extendMap (resolutionNatAugmentation M Q) nonnegativeChainEmbedding ≫
    (HomologicalComplex.extendSingleIso nonnegativeChainEmbedding (liftedCoefficient M)
      0 0 rfl).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionAugmentation_quasiIso (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    QuasiIso (resolutionAugmentation M Q) := by
  have he : QuasiIso (HomologicalComplex.extendMap (resolutionNatAugmentation M Q)
      nonnegativeChainEmbedding) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr
      (resolutionNatAugmentation_quasiIso M Q)
  dsimp only [resolutionAugmentation]
  exact quasiIso_comp _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp] theorem resolutionAugmentation_f_zero (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    (resolutionAugmentation M Q).f 0 =
      (Q.complex.extendXIso nonnegativeChainEmbedding (by rfl : (0 : ℤ) = 0)).hom ≫
        ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap.comp Q.ε) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (liftedCoefficient M)).inv := by
  dsimp only [resolutionAugmentation, HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f _ _ (by rfl : nonnegativeChainEmbedding.f 0 = 0),
    HomologicalComplex.extendSingleIso_hom_f]
  simp [resolutionNatAugmentation, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionNatAugmentation_natural
    {M N : ModuleCat.{w} R} (Q : LeftResolution R M) (T : LeftResolution R N)
    (g : M ⟶ N) (l : Q.complex ⟶ T.complex) (hl : ChainLift Q T g.hom l) :
    l ≫ resolutionNatAugmentation N T =
      resolutionNatAugmentation M Q ≫
        (HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℕ) 0).map
          ((ModuleCat.uliftFunctor.{u} R).map g) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, resolutionNatAugmentation,
    HomologicalComplex.mkHomToSingle_f]
  apply ModuleCat.hom_ext
  ext x
  change ULift.up (T.ε ((l.f 0).hom x)) = ULift.up (g.hom (Q.ε x))
  apply ULift.ext
  exact LinearMap.congr_fun hl x

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionAugmentation_natural
    {M N : ModuleCat.{w} R} (Q : LeftResolution R M) (T : LeftResolution R N)
    (g : M ⟶ N) (l : Q.complex ⟶ T.complex) (hl : ChainLift Q T g.hom l) :
    HomologicalComplex.extendMap l nonnegativeChainEmbedding ≫ resolutionAugmentation N T =
      resolutionAugmentation M Q ≫
        (HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℤ) 0).map
          ((ModuleCat.uliftFunctor.{u} R).map g) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, resolutionAugmentation_f_zero]
  rw [HomologicalComplex.extendMap_f l nonnegativeChainEmbedding
    (by rfl : nonnegativeChainEmbedding.f 0 = 0)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  ext x
  change ULift.up (T.ε ((l.f 0).hom _)) = ULift.up (g.hom (Q.ε _))
  apply ULift.ext
  exact LinearMap.congr_fun hl ((Q.complex.extendXIso nonnegativeChainEmbedding
    (by rfl : nonnegativeChainEmbedding.f 0 = 0)).hom.hom x)


open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

def tensorLiftRightEquiv (A : ModuleCat.{v} Rᵐᵒᵖ) (M : ModuleCat.{w} R) :
    P103.BalancedTensor.Tensor R A (ULift.{u} M) ≃ₗ[ℤ]
      ULift.{u} (P103.BalancedTensor.Tensor R A M) := by
  let f := (ULift.moduleEquiv : ULift.{u} (P103.BalancedTensor.Tensor R A M) ≃ₗ[ℤ]
      P103.BalancedTensor.Tensor R A M).symm.toLinearMap.comp
    (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
      (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).toLinearMap)
  let g := (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
      (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap).comp
    (ULift.moduleEquiv : ULift.{u} (P103.BalancedTensor.Tensor R A M) ≃ₗ[ℤ]
      P103.BalancedTensor.Tensor R A M).toLinearMap
  exact LinearEquiv.ofLinearMap f g (by
    apply LinearMap.ext
    intro t
    apply ULift.ext
    change ((tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
      (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).toLinearMap).comp
      (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
        (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap)) t.down = t.down
    have h : (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
      (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).toLinearMap).comp
      (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
        (ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap) = LinearMap.id := by
      apply tensor_hom_ext
      intro a m
      rfl
    exact LinearMap.congr_fun h t.down) (by
    apply tensor_hom_ext
    intro a m
    rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def coefficientLiftIso (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) :
    coefficientComplex P (liftedCoefficient M) ≅
      ((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).obj
        (coefficientComplex P M) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (tensorLiftRightEquiv (P.X i) M).toModuleIso) ?_
  intro i j h
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a m
  rfl


/-- Tensor augmentation, with the small coefficient complex embedded into the
ambient universe forced by the chosen ordinary resolution. -/
def resolutionTensorAugmentation
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    AdvancedHomologicalAlgebra.DoubleTotalization.sumTotal (tensorCochain P (extendNonnegativeChain Q.complex)) ⟶
      reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
        (ComplexShape.down ℤ)).obj (coefficientComplex P M)) :=
  tensorAugmentationMap P (liftedCoefficient M) (resolutionAugmentation M Q) ≫
    ((reversal.restrictionFunctor _).mapIso (coefficientLiftIso P M)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionTensorAugmentation_quasiIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (L : ℤ)
    (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P) :
    QuasiIso (resolutionTensorAugmentation P M Q) := by
  have hsingle : ∀ j : ℤ, j < 0 → IsZero
      (((HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℤ) 0).obj
        (liftedCoefficient M)).X j) := by
    intro j hj
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have ht := tensor_total_quasiIso R P (extendNonnegativeChain Q.complex)
    ((HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℤ) 0).obj
      (liftedCoefficient M)) L 0 0 hP hflat (extended_resolution_isZero M Q) hsingle
    (resolutionAugmentation M Q) (resolutionAugmentation_quasiIso M Q)
  unfold resolutionTensorAugmentation tensorAugmentationMap
  haveI := ht
  infer_instance


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def liftedHomologyIso (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ) :
    (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).obj C).homology n ≅
      (ModuleCat.uliftFunctor.{u} ℤ).obj (C.homology n) :=
  (C.sc n).mapHomologyIso (ModuleCat.uliftFunctor.{u} ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def resolutionTargetIso
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (L : ℤ)
    (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P) (n : ℤ) :
    (AdvancedHomologicalAlgebra.DoubleTotalization.sumTotal
      (tensorCochain P (extendNonnegativeChain Q.complex))).homology (-n) ≅
      ModuleCat.of ℤ (ULift.{u} (Homology (coefficientComplex P M) n)) := by
  letI := resolutionTensorAugmentation_quasiIso P M Q L hP hflat
  exact asIso (HomologicalComplex.homologyMap (resolutionTensorAugmentation P M Q) (-n)) ≪≫
    reverseHomologyAtNegIso _ n ≪≫ liftedHomologyIso (coefficientComplex P M) n ≪≫
    (ModuleCat.uliftFunctor.{u} ℤ).mapIso (categoricalHomologyIso (coefficientComplex P M) n)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem resolutionTensorAugmentation_zero
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (i : ℤ)
    (a : P.X (-i)) (b : Q.complex.X 0) :
    (resolutionTensorAugmentation P M Q).f i
      ((sumInjection (tensorCochain P (extendNonnegativeChain Q.complex))
        i 0 i (add_zero i))
        (P103.BalancedTensor.tmul R a
          ((Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl).inv b))) =
      ULift.up (P103.BalancedTensor.tmul R a (Q.ε b)) := by
  let aQ := resolutionAugmentation M Q
  let K := tensorCochain P (extendNonnegativeChain Q.complex)
  let K' := tensorCochain P
    ((HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℤ) 0).obj
      (liftedCoefficient M))
  let eQ := Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl
  let eM := HomologicalComplex.singleObjXSelf (ComplexShape.down ℤ) 0 (liftedCoefficient M)
  have hj :
      sumInjection K i 0 i (add_zero i) ≫ (resolutionTensorAugmentation P M Q).f i =
        (((tensorCochainMap (𝟙 P) aQ).f i).f 0) ≫
          (ModuleCat.ofHom (tensorMap (LinearMap.id : P.X (-i) →ₗ[Rᵐᵒᵖ] P.X (-i)) eM.hom.hom)) ≫
          (coefficientLiftIso P M).hom.f (-i) := by
    change sumInjection K i 0 i (add_zero i) ≫
      (HomologicalComplex₂.total.map (tensorCochainMap (𝟙 P) aQ) (ComplexShape.up ℤ)).f i ≫
      (singleTensorTotalIso P (liftedCoefficient M)).hom.f i ≫
      (coefficientLiftIso P M).hom.f (-i) = _
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
      ← Category.assoc (sumInjection K' i 0 i (add_zero i)), singleTensorTotalIso_zero]
  have hf := congrArg (fun k => k (P103.BalancedTensor.tmul R a (eQ.inv b))) hj
  change _ =
    (coefficientLiftIso P M).hom.f (-i)
      (P103.BalancedTensor.tmul R a (eM.hom (aQ.f 0 (eQ.inv b)))) at hf
  have hb : eM.hom (aQ.f 0 (eQ.inv b)) =
      ULift.up (Q.ε b) := by
    have ha : eQ.inv ≫ aQ.f 0 ≫ eM.hom =
        ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} M ≃ₗ[R] M).symm.toLinearMap.comp Q.ε) := by
      dsimp only [aQ]
      rw [resolutionAugmentation_f_zero]
      change eQ.inv ≫ eQ.hom ≫ _ ≫ eM.inv ≫ eM.hom = _
      simp
    exact congrArg (fun k => k b) ha
  exact hf.trans (by rw [hb]; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def resolutionTargetAugmentation
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) :
    TargetAugmentation P M Q where
  hom := resolutionTensorAugmentation P M Q
  zero_component := resolutionTensorAugmentation_zero P M Q
  other_components i j n h hj := by
    let aQ := resolutionAugmentation M Q
    let K := tensorCochain P (extendNonnegativeChain Q.complex)
    have hz : IsZero ((tensorCochain P
        ((HomologicalComplex.single (ModuleCat.{max u w} R) (ComplexShape.down ℤ) 0).obj
          (liftedCoefficient M))).X i |>.X j) := by
      apply tensor_isZero
      right
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (show -j ≠ 0 by omega)
    change sumInjection K i j n h ≫
      (HomologicalComplex₂.total.map (tensorCochainMap (𝟙 P) aQ) (ComplexShape.up ℤ)).f n ≫
      (singleTensorTotalIso P (liftedCoefficient M)).hom.f n ≫
      (coefficientLiftIso P M).hom.f (-n) = 0
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [Category.assoc]
    rw [hz.eq_of_src (_ ≫ _) 0, comp_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem categoricalHomologyIso_class {S : Type*} [Ring S] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} S) c) (n : ι) (z : C.cycles n) :
    (categoricalHomologyIso C n).hom (C.homologyπ n z) =
      homologyClass C n ((C.sc n).moduleCatCyclesIso.hom z) := by
  have h : (C.sc n).homologyπ ≫ (categoricalHomologyIso C n).hom =
      (C.sc n).moduleCatCyclesIso.hom ≫ ModuleCat.ofHom (homologyClass C n) := by
    dsimp only [categoricalHomologyIso, Iso.trans_hom]
    rw [ShortComplex.π_moduleCatCyclesIso_hom_assoc]
    rfl
  exact congrArg (fun f => f z) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionTargetIso_induced
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{w} R) (Q : LeftResolution R M) (L : ℤ)
    (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P) (n : ℤ) :
    (resolutionTargetAugmentation P M Q).Induces n
      (resolutionTargetIso P M Q L hP hflat n) := by
  let K := sumTotal (tensorCochain P (extendNonnegativeChain Q.complex))
  let C := coefficientComplex P M
  let C' := liftedCoefficientComplex P M
  let F := ModuleCat.uliftFunctor.{u} ℤ
  let g := resolutionTensorAugmentation P M Q
  let rev := C'.restrictionCyclesIso reversal (-n) (-n+1) (by simp)
    (show -(-n) = n by omega) (show -(-n+1) = n-1 by omega) (by simp)
  let m := (C.sc n).mapCyclesIso F
  have hrevi :
      rev.hom ≫ C'.iCycles n = (reverseChain C').iCycles (-n) ≫
        (C'.restrictionXIso reversal (by change -(-n) = n; omega)).hom :=
    C'.restrictionCyclesIso_hom_iCycles ..
  have hrevπ :
      (reverseChain C').homologyπ (-n) ≫ (reverseHomologyAtNegIso C' n).hom =
        rev.hom ≫ C'.homologyπ n := by
    unfold reverseHomologyAtNegIso
    apply HomologicalComplex.homologyπ_restrictionHomologyIso_hom
  have hmapπ :
      C'.homologyπ n ≫ (liftedHomologyIso C n).hom =
        m.hom ≫ F.map (C.homologyπ n) := by
    have hp := (TorBalance.exactHomologyComparison F).projection (C.sc n)
    change F.map (C.homologyπ n) ≫ (liftedHomologyIso C n).inv =
      m.inv ≫ C'.homologyπ n at hp
    rw [← cancel_mono (liftedHomologyIso C n).inv, ← cancel_epi m.inv]
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id]
      using hp.symm
  have hmapi : m.hom ≫ F.map (C.iCycles n) = C'.iCycles n :=
    (C.sc n).mapCyclesIso_hom_iCycles F
  intro z
  let x := HomologicalComplex.cyclesMap g (-n) z
  let y := rev.hom x
  let t : C.cycles n := ULift.down (m.hom y)
  refine ⟨(C.sc n).moduleCatCyclesIso.hom t, ?_, ?_⟩
  · have hi := congrArg (fun f => f z) (HomologicalComplex.cyclesMap_i g (-n))
    have hr := congrArg (fun f => f x) hrevi
    have hm := congrArg (fun f => ULift.down (f y)) hmapi
    have hc := congrArg (fun f => f t) (C.sc n).moduleCatCyclesIso_hom_i
    change (C.iCycles n) t = ULift.down (C'.iCycles n y) at hm
    change C'.iCycles n y = (C'.restrictionXIso reversal (by change -(-n) = n; omega)).hom
      ((reverseChain C').iCycles (-n) x) at hr
    change ((C.sc n).moduleCatCyclesIso.hom t : cycles C n).val = (C.iCycles n) t at hc
    change (reverseChain C').iCycles (-n) x = g.f (-n) (K.iCycles (-n) z) at hi
    rw [hc, hm, hr, hi]
    rfl
  · have hg := congrArg (fun f => f z) (HomologicalComplex.homologyπ_naturality g (-n))
    have hr := congrArg (fun f => f x) hrevπ
    have hm := congrArg (fun f => f y) hmapπ
    change HomologicalComplex.homologyMap g (-n) (K.homologyπ (-n) z) =
      (reverseChain C').homologyπ (-n) x at hg
    change (reverseHomologyAtNegIso C' n).hom ((reverseChain C').homologyπ (-n) x) =
      C'.homologyπ n y at hr
    change (liftedHomologyIso C n).hom (C'.homologyπ n y) =
      ULift.up (C.homologyπ n t) at hm
    change F.map (categoricalHomologyIso C n).hom
      ((liftedHomologyIso C n).hom ((reverseHomologyAtNegIso C' n).hom
        (HomologicalComplex.homologyMap g (-n) (K.homologyπ (-n) z)))) = _
    rw [hg, hr, hm]
    change ULift.up ((categoricalHomologyIso C n).hom (C.homologyπ n t)) = _
    rw [categoricalHomologyIso_class]

theorem resolution_target_comparison : Specs.ResolutionTargetComparison.{u,v,w} := by
  intro R _ P L M Q hP hf _
  exact ⟨resolutionTargetAugmentation P M Q, resolutionTensorAugmentation_quasiIso P M Q L hP hf,
    fun n => ⟨resolutionTargetIso P M Q L hP hf n, resolutionTargetIso_induced P M Q L hP hf n⟩⟩


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem singleTensorTotalIso_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ N) :
    HomologicalComplex₂.total.map (tensorCochainMap f
      ((HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).map g))
        (ComplexShape.up ℤ) ≫ (singleTensorTotalIso P' N).hom =
    (singleTensorTotalIso P M).hom ≫
      HomologicalComplex.restrictionMap (coefficientComplexMap f g) reversal := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
  intro a b hab
  by_cases hb : b = 0
  · subst b
    have ha : a = n := by change a + 0 = n at hab; omega
    subst a
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [Category.assoc, singleTensorTotalIso_zero,
      ← Category.assoc, singleTensorTotalIso_zero]
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x y
    rfl
  · have hz : IsZero (((tensorCochain P
        ((HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).obj M)).X a).X b) := by
      change IsZero (ModuleCat.of ℤ (P103.BalancedTensor.Tensor R (P.X (-a))
        (((HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).obj M).X (-b))))
      apply tensor_isZero
      right
      exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem tensorAugmentationMap_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    {M N : ModuleCat.{w} R} (f : P ⟶ P') (l : Q ⟶ Q') (g : M ⟶ N)
    (a : Q ⟶ (HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).obj M)
    (b : Q' ⟶ (HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).obj N)
    (ha : l ≫ b = a ≫
      (HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).map g) :
    HomologicalComplex₂.total.map (tensorCochainMap f l) (ComplexShape.up ℤ) ≫
        tensorAugmentationMap P' N b =
      tensorAugmentationMap P M a ≫
        HomologicalComplex.restrictionMap (coefficientComplexMap f g) reversal := by
  have hbc : tensorCochainMap f l ≫ tensorCochainMap (𝟙 P') b =
      tensorCochainMap (𝟙 P) a ≫ tensorCochainMap f
        ((HomologicalComplex.single (ModuleCat.{w} R) (ComplexShape.down ℤ) 0).map g) := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro x y
    have hy := congrArg (fun k => (k.f (-j)).hom y) ha
    exact congrArg (P103.BalancedTensor.tmul R ((f.f (-i)).hom x)) hy
  unfold tensorAugmentationMap
  rw [← Category.assoc, ← HomologicalComplex₂.total.map_comp, hbc,
    HomologicalComplex₂.total.map_comp, Category.assoc,
    singleTensorTotalIso_natural, ← Category.assoc]

section TensorPageLaws
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
  {Q : ChainComplex (ModuleCat.{w} R) ℤ}
section GenericDifferential
variable {A : Type*} [Category* A] [Abelian A]
variable {X Y : FilteredComplex A}

private theorem homologicalDifferential_square_zero {K : CochainComplex A ℤ}
    (F : Filtration K) (D : F03Specs.PageData F)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    homologicalPageDifferential F D r hr p q ≫
      homologicalPageDifferential F D r hr (p-r) (q+r-1) = 0 := by
  unfold homologicalPageDifferential
  have h : ((-p+r, -(p+q)+1) : ℤ × ℤ) =
      (-(p-r), -((p-r)+(q+r-1))) := by ext <;> dsimp <;> omega
  have hn := eqToHom_naturality
    (fun i : ℤ × ℤ => D.differential r hr i.1 i.2) h
  dsimp only at hn
  rw [Category.assoc, ← Category.assoc (eqToHom _) (D.differential _ _ _ _),
    ← hn, ← Category.assoc]
  simp only [← Category.assoc]
  rw [D.square_zero r hr (-p) (-(p+q))]
  simp

private theorem homologicalDifferential_comm {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : FilteredPageFunctoriality.MapData f D E)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    M.map r (-p) (-(p+q)) ≫ homologicalPageDifferential Y.filtration E r hr p q =
      homologicalPageDifferential X.filtration D r hr p q ≫
        M.map r (-(p-r)) (-((p-r)+(q+r-1))) := by
  unfold homologicalPageDifferential
  rw [← Category.assoc, M.differential_comm, Category.assoc, Category.assoc]
  congr 1
  have h : ((-p+r, -(p+q)+1) : ℤ × ℤ) =
      (-(p-r), -((p-r)+(q+r-1))) := by ext <;> dsimp <;> omega
  exact eqToHom_naturality (fun i : ℤ × ℤ => M.map r i.1 i.2) h
private def homologicalNextPageIso {K : CochainComplex A ℤ} (F : Filtration K)
    (D : F03Specs.PageData F) (C : PageCohomology.Data F D)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    PageCohomology.object F D (r+1) (-p) (-(p+q)) ≅
      (PageCohomology.shortComplex F D r hr (-p-r) (-(p+q)-1)).homology :=
  eqToIso (by unfold PageCohomology.object; congr 1 <;> omega) ≪≫
    C.nextIso r hr (-p-r) (-(p+q)-1)

private theorem homologicalNextPageIso_naturality {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : FilteredPageFunctoriality.MapData f D E)
    (C : PageCohomology.Data X.filtration D) (C' : PageCohomology.Data Y.filtration E)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    M.map (r+1) (-p) (-(p+q)) ≫
        (homologicalNextPageIso Y.filtration E C' r hr p q).hom =
      (homologicalNextPageIso X.filtration D C r hr p q).hom ≫
        ShortComplex.homologyMap
          (FilteredPageFunctoriality.shortComplexMap M r hr (-p-r) (-(p+q)-1)) := by
  unfold homologicalNextPageIso
  simp only [Iso.trans_hom, eqToIso.hom]
  have h : ((-p, -(p+q)) : ℤ × ℤ) = (-p-r+r, -(p+q)-1+1) := by
    ext <;> dsimp <;> omega
  have hn := eqToHom_naturality (fun i : ℤ × ℤ => M.map (r+1) i.1 i.2) h
  dsimp only at hn
  rw [← Category.assoc, hn, Category.assoc,
    FilteredPageFunctoriality.next_naturality M C C' r hr (-p-r) (-(p+q)-1)]
  simp only [Category.assoc]

end GenericDifferential

set_option maxHeartbeats 2400000 in
theorem TensorPages.differential_square_zero (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    S.differential r hr p q ≫ S.differential r hr (p-r) (q+r-1) = 0 := by
  exact homologicalDifferential_square_zero S.filtration S.pages r hr p q

/-- The three-term page complex centered at the homological bidegree `(p,q)`.
Its terms are canonically the terms with bidegrees `(p+r,q-r+1)`, `(p,q)`
and `(p-r,q+r-1)`; the maps are the reindexed page differentials. -/
abbrev TensorPages.pageComplex (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) : ShortComplex (ModuleCat.{max v w} ℤ) :=
  PageCohomology.shortComplex S.filtration S.pages r hr (-p-r) (-(p+q)-1)

/-- The next homological page is the homology at the center of the current page. -/
def TensorPages.nextPageIso (S : TensorPages P Q)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    S.term (r+1) p q ≅ (S.pageComplex r hr p q).homology :=
  eqToIso (by unfold TensorPages.term PageCohomology.object; congr 1 <;> omega) ≪≫
    S.next.nextIso r hr (-p-r) (-(p+q)-1)

abbrev TensorPages.pageMap
    {P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    {S : TensorPages P Q} {S' : TensorPages P' Q'}
    {h : FilteredMap ⟨DoubleTotalization.sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨DoubleTotalization.sumTotal (tensorCochain P' Q'), S'.filtration⟩}
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages) (r p q : ℤ) :
    S.term r p q ⟶ S'.term r p q :=
  M.map r (-p) (-(p+q))


set_option maxHeartbeats 2400000 in
theorem TensorPages.pageMap_differential
    {P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    {S : TensorPages P Q} {S' : TensorPages P' Q'}
    {h : FilteredMap ⟨DoubleTotalization.sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨DoubleTotalization.sumTotal (tensorCochain P' Q'), S'.filtration⟩}
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    TensorPages.pageMap M r p q ≫ S'.differential r hr p q =
      S.differential r hr p q ≫ TensorPages.pageMap M r (p-r) (q+r-1) := by
  exact homologicalDifferential_comm
    (X := ⟨DoubleTotalization.sumTotal (tensorCochain P Q), S.filtration⟩)
    (Y := ⟨DoubleTotalization.sumTotal (tensorCochain P' Q'), S'.filtration⟩)
    (D := S.pages) (E := S'.pages) M r hr p q

abbrev TensorPages.pageComplexMap
    {P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    {S : TensorPages P Q} {S' : TensorPages P' Q'}
    {h : FilteredMap ⟨DoubleTotalization.sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨DoubleTotalization.sumTotal (tensorCochain P' Q'), S'.filtration⟩}
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    S.pageComplex r hr p q ⟶ S'.pageComplex r hr p q :=
  FilteredPageFunctoriality.shortComplexMap M r hr (-p-r) (-(p+q)-1)

set_option maxHeartbeats 800000 in
theorem TensorPages.nextPageIso_naturality
    {P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    {S : TensorPages P Q} {S' : TensorPages P' Q'}
    {h : FilteredMap ⟨DoubleTotalization.sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨DoubleTotalization.sumTotal (tensorCochain P' Q'), S'.filtration⟩}
    (M : FilteredPageFunctoriality.MapData h S.pages S'.pages)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ) :
    TensorPages.pageMap M (r+1) p q ≫ (S'.nextPageIso r hr p q).hom =
      (S.nextPageIso r hr p q).hom ≫
        ShortComplex.homologyMap (TensorPages.pageComplexMap M r hr p q) := by
  exact homologicalNextPageIso_naturality
      (X := ⟨DoubleTotalization.sumTotal (tensorCochain P Q), S.filtration⟩)
      (Y := ⟨DoubleTotalization.sumTotal (tensorCochain P' Q'), S'.filtration⟩)
      (D := S.pages) (E := S'.pages) M S.next S'.next r hr p q

end TensorPageLaws
end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.FilteredPageFunctoriality
variable {A : Type*} [Category* A] [Abelian A]
variable {X Y Z : FilteredComplex A}

theorem MapData.map_eq_pageMap {f : FilteredMap X Y}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    (M : MapData f D E) (r p n : ℤ) :
    M.map r p n = pageMap f D E r p n :=
  pageMap_unique f D E r p n _ (M.representative_formula r p n)

theorem MapData.map_identity (D : F03Specs.PageData X.filtration)
    (M : MapData (FilteredMap.id X) D D) (r p n : ℤ) :
    M.map r p n = 𝟙 _ := by
  rw [M.map_eq_pageMap, pageMap_id]

theorem MapData.map_composition {f : FilteredMap X Y} {g : FilteredMap Y Z}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    {G : F03Specs.PageData Z.filtration}
    (M : MapData f D E) (N : MapData g E G) (T : MapData (f.comp g) D G)
    (r p n : ℤ) :
    T.map r p n = M.map r p n ≫ N.map r p n := by
  rw [T.map_eq_pageMap, M.map_eq_pageMap, N.map_eq_pageMap, pageMap_comp]
end AdvancedHomologicalAlgebra.FilteredPageFunctoriality


namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
section Transport
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex A ℤ} (F : Filtration K) (n : ℤ) (H : A)
  (e : K.homology (-n) ≅ H)
theorem transportedPiece_finite (h : CohomologyFiltrationData F) :
    ∃ a b : ℤ, (∀ p, p ≤ a → transportedPiece F n H e p = ⊥) ∧
      (∀ p, b ≤ p → transportedPiece F n H e p = ⊤) := by
  obtain ⟨a,b,ha,hb⟩ := h.finite (-n)
  refine ⟨-b,-a,?_,?_⟩
  · intro p hp
    change (Subobject.mapIsoToOrderIso e) (cohomologyPiece F (-p) (-n)) = ⊥
    rw [hb (-p) (by omega)]
    exact (Subobject.mapIsoToOrderIso e).map_bot
  · intro p hp
    change (Subobject.mapIsoToOrderIso e) (cohomologyPiece F (-p) (-n)) = ⊤
    rw [ha (-p) (by omega)]
    exact (Subobject.mapIsoToOrderIso e).map_top

end Transport

theorem tensor_page_square_zero : Specs.TensorPageSquareZero.{u,v,w} :=
  TensorPages.differential_square_zero

theorem tensor_next_page_cohomology : Specs.TensorNextPageCohomology.{u,v,w} := by
  intro R _ P Q S r hr p q
  exact ⟨S.nextPageIso r hr p q⟩

theorem resolution_second_page : Specs.ResolutionSecondPage.{u,v,w} := by
  intro R _ P M Q L hP hQ T S
  exact ⟨resolutionSecondPageComparison P M Q hQ T S⟩

theorem kunneth_construction : Specs.KunnethConstruction.{u,v,w} := by
  intro R _ T P L M Q hP hflat hQ
  obtain ⟨S,hS⟩ := resolution_page_construction R P L M Q hP
  exact ⟨{ tensorPages := S
           support := hS
           secondComparison := resolutionSecondPageComparison P M Q hQ T S
           targetIso := resolutionTargetIso P M Q L hP hflat
           targetAugmentation := resolutionTargetAugmentation P M Q
           targetQuasiIso := resolutionTensorAugmentation_quasiIso P M Q L hP hflat
           targetInduced := resolutionTargetIso_induced P M Q L hP hflat }⟩

theorem kunneth_convergence : Specs.KunnethConvergence.{u,v,w} := by
  intro R _ T P L M Q D
  refine ⟨fun p n => transportedPiece_increasing _ _ _ _ p,
    fun n => transportedPiece_finite _ _ _ _ D.tensorPages.convergence.target, ?_⟩
  intro n
  obtain ⟨r₀,hr₀,hstab⟩ := D.tensorPages.convergence.stabilization (-n)
  refine ⟨r₀,hr₀,?_⟩
  intro r hr p
  obtain ⟨I⟩ := D.tensorPages.convergence.limit D.tensorPages.pages r (-p) (-n)
    (by omega) (hstab r hr (-p))
  exact ⟨eqToIso (by unfold TensorPages.term PageCohomology.object; congr 1 <;> omega) ≪≫
    I.iso ≪≫ transportedGradedIso D.tensorPages.filtration n _ (D.targetIso n) p⟩

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteFiltrationConvergence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem coefficientLiftIso_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (f : P ⟶ P') (g : M ⟶ N) :
    coefficientComplexMap f ((ModuleCat.uliftFunctor.{u} R).map g) ≫
        (coefficientLiftIso P' N).hom =
      (coefficientLiftIso P M).hom ≫
        ((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).map
          (coefficientComplexMap f g) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a m
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionTensorAugmentation_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (Q : LeftResolution R M) (T : LeftResolution R N)
    (f : P ⟶ P') (g : M ⟶ N) (l : Q.complex ⟶ T.complex)
    (hl : ChainLift Q T g.hom l) :
    HomologicalComplex₂.total.map
      (tensorCochainMap f (HomologicalComplex.extendMap l nonnegativeChainEmbedding))
      (ComplexShape.up ℤ) ≫ resolutionTensorAugmentation P' N T =
    resolutionTensorAugmentation P M Q ≫
      HomologicalComplex.restrictionMap
        (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).map
          (coefficientComplexMap f g)) reversal := by
  unfold resolutionTensorAugmentation
  rw [← Category.assoc, tensorAugmentationMap_natural f _ _ _ _
    (resolutionAugmentation_natural Q T g l hl)]
  simp only [Category.assoc]
  congr 1
  change HomologicalComplex.restrictionMap
      (coefficientComplexMap f ((ModuleCat.uliftFunctor.{u} R).map g)) reversal ≫
    HomologicalComplex.restrictionMap (coefficientLiftIso P' N).hom reversal = _
  rw [← HomologicalComplex.restrictionMap_comp, coefficientLiftIso_natural,
    HomologicalComplex.restrictionMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem liftedHomologyIso_natural
    {C D : ChainComplex (ModuleCat.{v} ℤ) ℤ} (f : C ⟶ D) (n : ℤ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).map f) n ≫
      (liftedHomologyIso D n).hom = (liftedHomologyIso C n).hom ≫
        (ModuleCat.uliftFunctor.{u} ℤ).map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) (ModuleCat.uliftFunctor.{u} ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def coefficientTargetComparison (C : ChainComplex (ModuleCat.{v} ℤ) ℤ) (n : ℤ) :
    (reverseChain (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex
      (ComplexShape.down ℤ)).obj C)).homology (-n) ≅
      (ModuleCat.uliftFunctor.{u} ℤ).obj
        ((quotientHomology (ComplexShape.down ℤ) n).obj C) :=
  reverseHomologyAtNegIso _ n ≪≫ liftedHomologyIso C n ≪≫
    (ModuleCat.uliftFunctor.{u} ℤ).mapIso (categoricalHomologyIso C n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem coefficientTargetComparison_natural
    {C D : ChainComplex (ModuleCat.{v} ℤ) ℤ} (f : C ⟶ D) (n : ℤ) :
    HomologicalComplex.homologyMap
      (HomologicalComplex.restrictionMap
        (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).map f)
          reversal) (-n) ≫ (coefficientTargetComparison D n).hom =
    (coefficientTargetComparison C n).hom ≫
      (ModuleCat.uliftFunctor.{u} ℤ).map
        ((quotientHomology (ComplexShape.down ℤ) n).map f) := by
  dsimp only [coefficientTargetComparison, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% (reverseHomologyIso_natural
    (((ModuleCat.uliftFunctor.{u} ℤ).mapHomologicalComplex (ComplexShape.down ℤ)).map f) n)]
  rw [reassoc_of% (liftedHomologyIso_natural f n)]
  rw [← (ModuleCat.uliftFunctor.{u} ℤ).map_comp, categoricalHomologyIso_natural,
    (ModuleCat.uliftFunctor.{u} ℤ).map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem resolutionTargetIso_natural
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} (Q : LeftResolution R M) (T : LeftResolution R N)
    (f : P ⟶ P') (g : M ⟶ N) (l : Q.complex ⟶ T.complex)
    (hl : ChainLift Q T g.hom l)
    (L L' : ℤ) (hP : BoundedBelow P L) (hP' : BoundedBelow P' L')
    (hflat : FlatTerms.{u,v,w} P) (hflat' : FlatTerms.{u,v,w} P') (n : ℤ) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        (tensorCochainMap f (HomologicalComplex.extendMap l nonnegativeChainEmbedding))
        (ComplexShape.up ℤ)) (-n) ≫ (resolutionTargetIso P' N T L' hP' hflat' n).hom =
      (resolutionTargetIso P M Q L hP hflat n).hom ≫
        (ModuleCat.uliftFunctor.{u} ℤ).map
          (ModuleCat.ofHom (homologyMap (coefficientComplexMap f g) n)) := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k (-n))
    (resolutionTensorAugmentation_natural Q T f g l hl)
  simp only [HomologicalComplex.homologyMap_comp] at h
  dsimp only [resolutionTargetIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  have hc := coefficientTargetComparison_natural (coefficientComplexMap f g) n
  dsimp only [coefficientTargetComparison, Iso.trans_hom, Functor.mapIso_hom] at hc
  rw [hc]
  rfl

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y Z : FilteredComplex A}

/-- The map on the fixed homological target, transported from the total. -/
def transportedTargetMap (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H') : H ⟶ H' :=
  e.inv ≫ HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom

/-- Naturality square of the transported target map. -/
theorem transportedTargetMap_square (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H') :
    HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom =
      e.hom ≫ transportedTargetMap f n e e' := by
  simp [transportedTargetMap]

/-- A commuting target square identifies the transported map with the prescribed one. -/
theorem transportedTargetMap_of_square (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H')
    (u : H ⟶ H')
    (hu : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom ≫ u) :
    transportedTargetMap f n e e' = u := by
  simp only [transportedTargetMap, hu, Iso.inv_hom_id_assoc]

@[simp]
theorem transportedTargetMap_identity (n : ℤ) {H : A}
    (e : X.complex.homology (-n) ≅ H) :
    transportedTargetMap (FilteredMap.id X) n e e = 𝟙 H := by
  simp [transportedTargetMap, FilteredMap.id]

@[simp]
theorem transportedTargetMap_composition (f : FilteredMap X Y) (g : FilteredMap Y Z)
    (n : ℤ) {H H' H'' : A} (e : X.complex.homology (-n) ≅ H)
    (e' : Y.complex.homology (-n) ≅ H') (e'' : Z.complex.homology (-n) ≅ H'') :
    transportedTargetMap (f.comp g) n e e'' =
      transportedTargetMap f n e e' ≫ transportedTargetMap g n e' e'' := by
  simp [transportedTargetMap, FilteredMap.comp, HomologicalComplex.homologyMap_comp,
    Category.assoc]

/-- Restriction to an increasing target-filtration step of a filtered total map. -/
def transportedStepMap (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H') (p : ℤ) :
    (transportedPiece X.filtration n H e p : A) ⟶
      (transportedPiece Y.filtration n H' e' p : A) :=
  (transportedSubobjectIso e (cohomologyPiece X.filtration (-p) (-n))).inv ≫
    cohomologyStepMap f (-p) (-n) ≫
      (transportedSubobjectIso e' (cohomologyPiece Y.filtration (-p) (-n))).hom

@[reassoc]
theorem transportedStepMap_arrow (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H')
    (u : H ⟶ H')
    (hu : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom ≫ u)
    (p : ℤ) :
    transportedStepMap f n e e' p ≫ (transportedPiece Y.filtration n H' e' p).arrow =
      (transportedPiece X.filtration n H e p).arrow ≫ u := by
  dsimp only [transportedStepMap]
  simp only [Category.assoc, transportedPiece, transportedSubobjectIso_arrow,
    cohomologyStepMap_arrow_assoc]
  rw [hu, ← Category.assoc (cohomologyPiece X.filtration (-p) (-n)).arrow]
  rw [← transportedSubobjectIso_arrow]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- A morphism of filtered targets is determined by its underlying target map. -/
theorem transportedStepMap_unique (f g : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H')
    (u : H ⟶ H')
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom ≫ u)
    (hg : HomologicalComplex.homologyMap g.hom (-n) ≫ e'.hom = e.hom ≫ u)
    (p : ℤ) :
    transportedStepMap f n e e' p = transportedStepMap g n e e' p := by
  apply (cancel_mono (transportedPiece Y.filtration n H' e' p).arrow).1
  rw [transportedStepMap_arrow f n e e' u hf,
    transportedStepMap_arrow g n e e' u hg]

@[simp]
theorem transportedStepMap_identity (n : ℤ) {H : A}
    (e : X.complex.homology (-n) ≅ H) (p : ℤ) :
    transportedStepMap (FilteredMap.id X) n e e p = 𝟙 _ := by
  apply (cancel_mono (transportedPiece X.filtration n H e p).arrow).1
  rw [transportedStepMap_arrow (FilteredMap.id X) n e e (𝟙 H)]
  · simp
  · simp [FilteredMap.id]

@[simp]
theorem transportedStepMap_composition (f : FilteredMap X Y) (g : FilteredMap Y Z)
    (n : ℤ) {H H' H'' : A} (e : X.complex.homology (-n) ≅ H)
    (e' : Y.complex.homology (-n) ≅ H') (e'' : Z.complex.homology (-n) ≅ H'') (p : ℤ) :
    transportedStepMap (f.comp g) n e e'' p =
      transportedStepMap f n e e' p ≫ transportedStepMap g n e' e'' p := by
  apply (cancel_mono (transportedPiece Z.filtration n H'' e'' p).arrow).1
  rw [transportedStepMap_arrow (f.comp g) n e e''
    (transportedTargetMap (f.comp g) n e e'')
    (transportedTargetMap_square (f.comp g) n e e''), Category.assoc,
    transportedStepMap_arrow g n e' e'' (transportedTargetMap g n e' e'')
      (transportedTargetMap_square g n e' e''),
    ← Category.assoc, transportedStepMap_arrow f n e e' (transportedTargetMap f n e e')
      (transportedTargetMap_square f n e e'), Category.assoc,
    transportedTargetMap_composition f g n e e' e'']

/-- A total comparison over the identity preserves each transported filtration step. -/
theorem transportedPiece_le_of_identity (f : FilteredMap X Y) (n : ℤ) {H : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H)
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom)
    (p : ℤ) :
    transportedPiece X.filtration n H e p ≤ transportedPiece Y.filtration n H e' p := by
  apply Subobject.le_of_comm (transportedStepMap f n e e' p)
  simpa using transportedStepMap_arrow f n e e' (𝟙 H) (by simpa using hf) p

/-- An isomorphism on a filtration step over the identity identifies the
transported subobjects, including their inclusions into the fixed target. -/
theorem transportedPiece_eq_of_step_iso (f : FilteredMap X Y) (n : ℤ) {H : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H)
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom)
    (p : ℤ) [IsIso (cohomologyStepMap f (-p) (-n))] :
    transportedPiece X.filtration n H e p = transportedPiece Y.filtration n H e' p := by
  haveI : IsIso (transportedStepMap f n e e' p) := by
    dsimp only [transportedStepMap]
    infer_instance
  apply Subobject.eq_of_comm (asIso (transportedStepMap f n e e' p))
  simpa using transportedStepMap_arrow f n e e' (𝟙 H) (by simpa using hf) p

/-- Comparisons in both directions over the identity give the same filtration
on the fixed target. This applies to any two projective resolution choices. -/
theorem transportedPiece_eq_of_identity_comparisons
    (f : FilteredMap X Y) (g : FilteredMap Y X) (n : ℤ) {H : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H)
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom)
    (hg : HomologicalComplex.homologyMap g.hom (-n) ≫ e.hom = e'.hom)
    (p : ℤ) :
    transportedPiece X.filtration n H e p = transportedPiece Y.filtration n H e' p :=
  le_antisymm (transportedPiece_le_of_identity f n e e' hf p)
    (transportedPiece_le_of_identity g n e' e hg p)

end AdvancedHomologicalAlgebra.KunnethSpectralSequence


namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteFiltrationConvergence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open DoubleTotalization
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]

@[simp] theorem targetHomologyMap_identity
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) (n : ℤ) :
    targetHomologyMap (𝟙 P) (𝟙 M) n = 𝟙 (targetHomology P M n) := by
  have hc : coefficientComplexMap (𝟙 P) (𝟙 M) = 𝟙 (coefficientComplex P M) := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply tensor_hom_ext
    intro a m
    rfl
  simp [targetHomologyMap, hc, P103.Ch10.Complexes.homologyMap_id]

/-- The actual filtered tensor map associated with a chosen resolution lift. -/
def resolutionFilteredMap
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} {Q : LeftResolution R M} {T : LeftResolution R N}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P' (extendNonnegativeChain T.complex))
    (f : P ⟶ P') (l : Q.complex ⟶ T.complex) :
    FilteredMap ⟨sumTotal (tensorCochain P (extendNonnegativeChain Q.complex)), S.filtration⟩
      ⟨sumTotal (tensorCochain P' (extendNonnegativeChain T.complex)), S'.filtration⟩ :=
  (tensor_page_maps R P P' _ _ S S' f
    (HomologicalComplex.extendMap l nonnegativeChainEmbedding)).choose

theorem resolutionFilteredMap_hom
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} {Q : LeftResolution R M} {T : LeftResolution R N}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P' (extendNonnegativeChain T.complex))
    (f : P ⟶ P') (l : Q.complex ⟶ T.complex) :
    (resolutionFilteredMap S S' f l).hom =
      HomologicalComplex₂.total.map
        (tensorCochainMap f (HomologicalComplex.extendMap l nonnegativeChainEmbedding))
        (ComplexShape.up ℤ) :=
  (tensor_page_maps R P P' _ _ S S' f
    (HomologicalComplex.extendMap l nonnegativeChainEmbedding)).choose_spec.1

theorem resolutionFilteredMap_target_square
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N : ModuleCat.{w} R} {Q : LeftResolution R M} {T : LeftResolution R N}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P' (extendNonnegativeChain T.complex))
    (f : P ⟶ P') (g : M ⟶ N) (l : Q.complex ⟶ T.complex)
    (hl : ChainLift Q T g.hom l)
    (L L' : ℤ) (hP : BoundedBelow P L) (hP' : BoundedBelow P' L')
    (hflat : FlatTerms.{u,v,w} P) (hflat' : FlatTerms.{u,v,w} P') (n : ℤ) :
    HomologicalComplex.homologyMap (resolutionFilteredMap S S' f l).hom (-n) ≫
      (resolutionTargetIso P' N T L' hP' hflat' n).hom =
    (resolutionTargetIso P M Q L hP hflat n).hom ≫ targetHomologyMap f g n := by
  rw [resolutionFilteredMap_hom]
  exact resolutionTargetIso_natural Q T f g l hl L L' hP hP' hflat hflat' n


section ResolutionTargetNaturality
variable {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
variable {M N : ModuleCat.{w} R} {Q : LeftResolution R M} {T : LeftResolution R N}
variable (S : TensorPages P (extendNonnegativeChain Q.complex))
variable (S' : TensorPages P' (extendNonnegativeChain T.complex))
variable (f : P ⟶ P') (g : M ⟶ N)
variable (L L' : ℤ) (hP : BoundedBelow P L) (hP' : BoundedBelow P' L')
variable (hflat : FlatTerms.{u,v,w} P) (hflat' : FlatTerms.{u,v,w} P')

/-- The transported map on the fixed target is the prescribed original
coefficient-complex homology map. -/
theorem resolution_target_map (l : Q.complex ⟶ T.complex) (hl : ChainLift Q T g.hom l)
    (n : ℤ) :
    transportedTargetMap (resolutionFilteredMap S S' f l) n
      (resolutionTargetIso P M Q L hP hflat n)
      (resolutionTargetIso P' N T L' hP' hflat' n) = targetHomologyMap f g n :=
  transportedTargetMap_of_square _ n _ _ _
    (resolutionFilteredMap_target_square S S' f g l hl L L' hP hP' hflat hflat' n)

/-- Every original target map preserves the transported increasing filtration. -/
theorem resolution_target_step_map (l : Q.complex ⟶ T.complex) (hl : ChainLift Q T g.hom l)
    (p n : ℤ) :
    transportedStepMap (resolutionFilteredMap S S' f l) n
      (resolutionTargetIso P M Q L hP hflat n)
      (resolutionTargetIso P' N T L' hP' hflat' n) p ≫
      (transportedPiece S'.filtration n (targetHomology P' N n)
        (resolutionTargetIso P' N T L' hP' hflat' n) p).arrow =
    (transportedPiece S.filtration n (targetHomology P M n)
        (resolutionTargetIso P M Q L hP hflat n) p).arrow ≫ targetHomologyMap f g n :=
  transportedStepMap_arrow _ n _ _ _
    (resolutionFilteredMap_target_square S S' f g l hl L L' hP hP' hflat hflat' n) p

/-- Two resolution lifts of the same coefficient map induce equal maps on the
fixed target and on every target filtration step. -/
theorem resolution_target_lift_independent
    (l l' : Q.complex ⟶ T.complex) (hl : ChainLift Q T g.hom l)
    (hl' : ChainLift Q T g.hom l') (n : ℤ) :
    transportedTargetMap (resolutionFilteredMap S S' f l) n
      (resolutionTargetIso P M Q L hP hflat n)
      (resolutionTargetIso P' N T L' hP' hflat' n) =
    transportedTargetMap (resolutionFilteredMap S S' f l') n
      (resolutionTargetIso P M Q L hP hflat n)
      (resolutionTargetIso P' N T L' hP' hflat' n) ∧
    ∀ p, transportedStepMap (resolutionFilteredMap S S' f l) n
      (resolutionTargetIso P M Q L hP hflat n)
      (resolutionTargetIso P' N T L' hP' hflat' n) p =
    transportedStepMap (resolutionFilteredMap S S' f l') n
      (resolutionTargetIso P M Q L hP hflat n)
      (resolutionTargetIso P' N T L' hP' hflat' n) p := by
  constructor
  · rw [resolution_target_map S S' f g L L' hP hP' hflat hflat' l hl,
      resolution_target_map S S' f g L L' hP hP' hflat hflat' l' hl']
  · intro p
    exact transportedStepMap_unique _ _ n _ _ (targetHomologyMap f g n)
      (resolutionFilteredMap_target_square S S' f g l hl L L' hP hP' hflat hflat' n)
      (resolutionFilteredMap_target_square S S' f g l' hl' L L' hP hP' hflat hflat' n) p
end ResolutionTargetNaturality

/-- Resolution comparisons over the identity identify the actual subobjects
of the fixed target, even when different page models have been chosen. -/
theorem resolution_target_filtration_independent
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R)
    (Q T : LeftResolution R M) (hQ : Q.IsProjective) (hT : T.IsProjective)
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain T.complex))
    (L : ℤ) (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P) (p n : ℤ) :
    transportedPiece S.filtration n (targetHomology P M n)
      (resolutionTargetIso P M Q L hP hflat n) p =
    transportedPiece S'.filtration n (targetHomology P M n)
      (resolutionTargetIso P M T L hP hflat n) p := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists R M M Q T hQ LinearMap.id
  obtain ⟨k, hk⟩ := P103.Ch10.Comparison.chain_exists R M M T Q hT LinearMap.id
  apply transportedPiece_eq_of_identity_comparisons
    (resolutionFilteredMap S S' (𝟙 P) l) (resolutionFilteredMap S' S (𝟙 P) k) n
    (resolutionTargetIso P M Q L hP hflat n)
    (resolutionTargetIso P M T L hP hflat n) _ _ p
  · simpa only [targetHomologyMap_identity, Category.comp_id] using
      resolutionFilteredMap_target_square S S' (𝟙 P) (𝟙 M) l hl L L hP hP hflat hflat n
  · simpa only [targetHomologyMap_identity, Category.comp_id] using
      resolutionFilteredMap_target_square S' S (𝟙 P) (𝟙 M) k hk L L hP hP hflat hflat n


end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]
@[simp] theorem tensorCochainMap_identity
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) :
    tensorCochainMap (𝟙 P) (𝟙 Q) = 𝟙 (tensorCochain P Q) := by
  simp [tensorCochainMap, P103.Ch11.TorBalance.tensorBicomplexMap_id]

@[simp] theorem tensorCochainMap_composition
    {P P' P'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' Q'' : ChainComplex (ModuleCat.{w} R) ℤ}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    tensorCochainMap (f ≫ f') (g ≫ g') =
      tensorCochainMap f g ≫ tensorCochainMap f' g' := by
  simp [tensorCochainMap, P103.Ch11.TorBalance.tensorBicomplexMap_comp]

def tensorFilteredMap
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (S : TensorPages P Q) (S' : TensorPages P' Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    FilteredMap ⟨sumTotal (tensorCochain P Q), S.filtration⟩
      ⟨sumTotal (tensorCochain P' Q'), S'.filtration⟩ :=
  (tensor_page_maps R P P' Q Q' S S' f g).choose

theorem tensorFilteredMap_hom
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (S : TensorPages P Q) (S' : TensorPages P' Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    (tensorFilteredMap S S' f g).hom =
      HomologicalComplex₂.total.map (tensorCochainMap f g) (ComplexShape.up ℤ) :=
  (tensor_page_maps R P P' Q Q' S S' f g).choose_spec.1

private theorem filteredMap_ext {A : Type*} [Category* A] [Abelian A]
    {X Y : FilteredComplex A} {f g : FilteredMap X Y} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[simp] theorem tensorFilteredMap_identity
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q) :
    tensorFilteredMap S S (𝟙 P) (𝟙 Q) = FilteredMap.id _ := by
  apply filteredMap_ext
  rw [tensorFilteredMap_hom, tensorCochainMap_identity, HomologicalComplex₂.total.map_id]
  rfl

@[simp] theorem tensorFilteredMap_composition
    {P P' P'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' Q'' : ChainComplex (ModuleCat.{w} R) ℤ}
    (S : TensorPages P Q) (S' : TensorPages P' Q') (S'' : TensorPages P'' Q'')
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    tensorFilteredMap S S'' (f ≫ f') (g ≫ g') =
      (tensorFilteredMap S S' f g).comp (tensorFilteredMap S' S'' f' g') := by
  apply filteredMap_ext
  change _ = (tensorFilteredMap S S' f g).hom ≫ (tensorFilteredMap S' S'' f' g').hom
  rw [tensorFilteredMap_hom, tensorFilteredMap_hom, tensorFilteredMap_hom,
    tensorCochainMap_composition, HomologicalComplex₂.total.map_comp]

/-- The canonical maps of tensor pages, including their representative formulas. -/
def tensorPageMapData
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (S : TensorPages P Q) (S' : TensorPages P' Q') (f : P ⟶ P') (g : Q ⟶ Q') :
    FilteredPageFunctoriality.MapData (tensorFilteredMap S S' f g) S.pages S'.pages :=
  FilteredPageFunctoriality.mapData _ _ _

@[simp] theorem tensorPageMapData_identity
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} (S : TensorPages P Q) (r p n : ℤ) :
    (tensorPageMapData S S (𝟙 P) (𝟙 Q)).map r p n = 𝟙 _ := by
  change FilteredPageFunctoriality.pageMap _ _ _ _ _ _ = _
  rw [tensorFilteredMap_identity, FilteredPageFunctoriality.pageMap_id]

@[simp] theorem tensorPageMapData_composition
    {P P' P'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {Q Q' Q'' : ChainComplex (ModuleCat.{w} R) ℤ}
    (S : TensorPages P Q) (S' : TensorPages P' Q') (S'' : TensorPages P'' Q'')
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'')
    (r p n : ℤ) :
    (tensorPageMapData S S'' (f ≫ f') (g ≫ g')).map r p n =
      (tensorPageMapData S S' f g).map r p n ≫
        (tensorPageMapData S' S'' f' g').map r p n := by
  change FilteredPageFunctoriality.pageMap _ _ _ _ _ _ =
    FilteredPageFunctoriality.pageMap _ _ _ _ _ _ ≫ FilteredPageFunctoriality.pageMap _ _ _ _ _ _
  rw [tensorFilteredMap_composition, FilteredPageFunctoriality.pageMap_comp]

/-- Homotopic coefficient-complex maps give the same maps on every page
starting at the second page, for arbitrary choices of actual row filtrations. -/
theorem tensorPageMapData_eq_of_homotopy
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {Q Q' : ChainComplex (ModuleCat.{w} R) ℤ}
    (hQ : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q.X j))
    (hQ' : ∀ j, P103.Specs.Ch02.FlatnessTests.Flat.{u,w,v} R (Q'.X j))
    (S : TensorPages P Q) (S' : TensorPages P Q')
    {g g' : Q ⟶ Q'} (ht : Homotopy g g') (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    (tensorPageMapData S S' (𝟙 P) g).map r p n =
      (tensorPageMapData S S' (𝟙 P) g').map r p n := by
  apply page_maps_equal_later (tensorFilteredMap S S' (𝟙 P) g)
    (tensorFilteredMap S S' (𝟙 P) g') S.pages S'.pages
    (tensorPageMapData S S' (𝟙 P) g) (tensorPageMapData S S' (𝟙 P) g')
    2 (by omega) ?_ r hr p n
  intro a b
  exact tensor_second_page_maps_eq_of_homotopy P hQ hQ' S S' ht
    (tensorFilteredMap S S' (𝟙 P) g) (tensorFilteredMap S S' (𝟙 P) g')
    (tensorFilteredMap_hom S S' (𝟙 P) g) (tensorFilteredMap_hom S S' (𝟙 P) g')
    (tensorPageMapData S S' (𝟙 P) g) (tensorPageMapData S S' (𝟙 P) g') a b

/-- Independence of the lift of any fixed coefficient map from page two onward. -/
theorem resolution_page_maps_eq_of_lifts
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    {M N : ModuleCat.{w} R} (Q : LeftResolution R M) (Q' : LeftResolution R N)
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain Q'.complex))
    (g : M ⟶ N) (l l' : Q.complex ⟶ Q'.complex)
    (hl : ChainLift Q Q' g.hom l) (hl' : ChainLift Q Q' g.hom l')
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    (tensorPageMapData S S' (𝟙 P) (HomologicalComplex.extendMap l nonnegativeChainEmbedding)).map r p n =
      (tensorPageMapData S S' (𝟙 P) (HomologicalComplex.extendMap l' nonnegativeChainEmbedding)).map r p n := by
  obtain ⟨ht⟩ := P103.Ch10.Comparison.chain_unique R M N Q Q' hQ g.hom l l' hl hl'
  exact tensorPageMapData_eq_of_homotopy P
    (extendedResolution_flat M Q hQ) (extendedResolution_flat N Q' hQ') S S'
    (ht.extend nonnegativeChainEmbedding) r hr p n

/-- The maps from composed ordinary resolution lifts are composed page maps. -/
theorem resolution_page_maps_comp
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M N T : ModuleCat.{w} R}
    (Q : LeftResolution R M) (Q' : LeftResolution R N) (Q'' : LeftResolution R T)
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain Q'.complex))
    (S'' : TensorPages P (extendNonnegativeChain Q''.complex))
    (l : Q.complex ⟶ Q'.complex) (m : Q'.complex ⟶ Q''.complex) (r p n : ℤ) :
    (tensorPageMapData S S'' (𝟙 P) (HomologicalComplex.extendMap (l ≫ m) nonnegativeChainEmbedding)).map r p n =
      (tensorPageMapData S S' (𝟙 P) (HomologicalComplex.extendMap l nonnegativeChainEmbedding)).map r p n ≫
        (tensorPageMapData S' S'' (𝟙 P) (HomologicalComplex.extendMap m nonnegativeChainEmbedding)).map r p n := by
  rw [HomologicalComplex.extendMap_comp]
  have hc := tensorPageMapData_composition S S' S'' (𝟙 P) (𝟙 P)
      (HomologicalComplex.extendMap l nonnegativeChainEmbedding)
      (HomologicalComplex.extendMap m nonnegativeChainEmbedding) r p n
  have hi : (𝟙 P) ≫ (𝟙 P) = 𝟙 P := Category.id_comp _
  have he := congrArg (fun a : P ⟶ P => (tensorPageMapData S S'' a
    (HomologicalComplex.extendMap l nonnegativeChainEmbedding ≫
      HomologicalComplex.extendMap m nonnegativeChainEmbedding)).map r p n) hi
  exact he.symm.trans hc

/-- The chosen identity comparison of two ordinary projective resolutions. -/
def resolutionComparisonLift {M : ModuleCat.{w} R}
    (Q Q' : LeftResolution R M) (hQ : Q.IsProjective) : Q.complex ⟶ Q'.complex :=
  P103.Ch10.Comparison.chainMap Q Q' hQ LinearMap.id

theorem resolutionComparisonLift_lifts {M : ModuleCat.{w} R}
    (Q Q' : LeftResolution R M) (hQ : Q.IsProjective) :
    ChainLift Q Q' LinearMap.id (resolutionComparisonLift Q Q' hQ) :=
  P103.Ch10.Comparison.chainMap_lifts Q Q' hQ LinearMap.id

abbrev resolutionComparisonMap
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q Q' : LeftResolution R M}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain Q'.complex)) (hQ : Q.IsProjective)
    (r p n : ℤ) :
    PageCohomology.object S.filtration S.pages r p n ⟶
      PageCohomology.object S'.filtration S'.pages r p n :=
  (tensorPageMapData S S' (𝟙 P)
    (HomologicalComplex.extendMap (resolutionComparisonLift Q Q' hQ)
      nonnegativeChainEmbedding)).map r p n

@[simp]
theorem resolutionComparisonMap_identity
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q : LeftResolution R M}
    (S : TensorPages P (extendNonnegativeChain Q.complex)) (hQ : Q.IsProjective)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    resolutionComparisonMap S S hQ r p n = 𝟙 _ := by
  have he := resolution_page_maps_eq_of_lifts P Q Q hQ hQ S S (𝟙 M)
    (resolutionComparisonLift Q Q hQ) (𝟙 Q.complex)
    (resolutionComparisonLift_lifts Q Q hQ) (P103.Ch10.Comparison.chainLift_id Q) r hr p n
  rw [HomologicalComplex.extendMap_id] at he
  have hi := tensorPageMapData_identity S r p n
  exact he.trans hi

/-- Cocycle law: comparisons via an intermediate projective resolution equal
the direct comparison on every page from page two onward. -/
theorem resolutionComparisonMap_cocycle
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q Q' Q'' : LeftResolution R M}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain Q'.complex))
    (S'' : TensorPages P (extendNonnegativeChain Q''.complex))
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective) (hQ'' : Q''.IsProjective)
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :
    resolutionComparisonMap S S' hQ r p n ≫ resolutionComparisonMap S' S'' hQ' r p n =
      resolutionComparisonMap S S'' hQ r p n := by
  have hl : ChainLift Q Q'' (LinearMap.id : M →ₗ[R] M)
      (resolutionComparisonLift Q Q' hQ ≫ resolutionComparisonLift Q' Q'' hQ') := by
    simpa using P103.Ch10.Comparison.chainLift_comp
      (resolutionComparisonLift_lifts Q Q' hQ) (resolutionComparisonLift_lifts Q' Q'' hQ')
  have he := resolution_page_maps_eq_of_lifts P Q Q'' hQ hQ'' S S'' (𝟙 M)
    (resolutionComparisonLift Q Q' hQ ≫ resolutionComparisonLift Q' Q'' hQ')
    (resolutionComparisonLift Q Q'' hQ) hl
    (resolutionComparisonLift_lifts Q Q'' hQ) r hr p n
  rw [resolution_page_maps_comp Q Q' Q'' S S' S''] at he
  exact he

set_option maxHeartbeats 800000 in
/-- Canonical comparison isomorphisms between arbitrary projective left
resolution choices, for every homological bidegree and every page r ≥ 2. -/
def resolutionPageIso
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q Q' : LeftResolution R M}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain Q'.complex))
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) : S.term r p q ≅ S'.term r p q where
  hom := resolutionComparisonMap S S' hQ r (-p) (-(p+q))
  inv := resolutionComparisonMap S' S hQ' r (-p) (-(p+q))
  hom_inv_id := by
    rw [resolutionComparisonMap_cocycle S S' S hQ hQ' hQ r hr,
      resolutionComparisonMap_identity S hQ r hr]
  inv_hom_id := by
    rw [resolutionComparisonMap_cocycle S' S S' hQ' hQ hQ' r hr,
      resolutionComparisonMap_identity S' hQ' r hr]

set_option maxHeartbeats 800000 in
@[simp]
theorem resolutionPageIso_identity
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q : LeftResolution R M}
    (S : TensorPages P (extendNonnegativeChain Q.complex)) (hQ : Q.IsProjective)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) :
    resolutionPageIso S S hQ hQ r hr p q = Iso.refl _ := by
  apply Iso.ext
  exact resolutionComparisonMap_identity S hQ r hr (-p) (-(p+q))

set_option maxHeartbeats 800000 in
theorem resolutionPageIso_cocycle
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {Q Q' Q'' : LeftResolution R M}
    (S : TensorPages P (extendNonnegativeChain Q.complex))
    (S' : TensorPages P (extendNonnegativeChain Q'.complex))
    (S'' : TensorPages P (extendNonnegativeChain Q''.complex))
    (hQ : Q.IsProjective) (hQ' : Q'.IsProjective) (hQ'' : Q''.IsProjective)
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) :
    resolutionPageIso S S' hQ hQ' r hr p q ≪≫ resolutionPageIso S' S'' hQ' hQ'' r hr p q =
      resolutionPageIso S S'' hQ hQ'' r hr p q := by
  apply Iso.ext
  exact resolutionComparisonMap_cocycle S S' S'' hQ hQ' hQ'' r hr (-p) (-(p+q))

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
variable {R : Type u} [Ring R]
@[simp] theorem coefficientComplexMap_identity
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (M : ModuleCat.{w} R) :
    coefficientComplexMap (𝟙 P) (𝟙 M) = 𝟙 (coefficientComplex P M) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a m
  rfl
@[simp] theorem coefficientComplexMap_composition
    {P P' P'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M M' M'' : ModuleCat.{w} R} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : M ⟶ M') (g' : M' ⟶ M'') :
    coefficientComplexMap (f ≫ f') (g ≫ g') =
      coefficientComplexMap f g ≫ coefficientComplexMap f' g' := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a m
  rfl
@[simp] theorem targetHomologyMap_composition
    {P P' P'' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {M M' M'' : ModuleCat.{w} R} (f : P ⟶ P') (f' : P' ⟶ P'')
    (g : M ⟶ M') (g' : M' ⟶ M'') (n : ℤ) :
    targetHomologyMap (f ≫ f') (g ≫ g') n =
      targetHomologyMap f g n ≫ targetHomologyMap f' g' n := by
  unfold targetHomologyMap
  rw [coefficientComplexMap_composition]
  change (ModuleCat.uliftFunctor.{u} ℤ).map
      ((quotientHomology (ComplexShape.down ℤ) n).map (coefficientComplexMap f g ≫ coefficientComplexMap f' g')) = _
  rw [Functor.map_comp, Functor.map_comp]
  rfl

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y Z : FilteredComplex A}

theorem transportedStepMap_inclusion (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H') (p : ℤ) :
    Subobject.ofLE _ _ (transportedPiece_increasing X.filtration n H e p) ≫
        transportedStepMap f n e e' p =
      transportedStepMap f n e e' (p-1) ≫
        Subobject.ofLE _ _ (transportedPiece_increasing Y.filtration n H' e' p) := by
  apply (cancel_mono (transportedPiece Y.filtration n H' e' p).arrow).1
  rw [Category.assoc, transportedStepMap_arrow f n e e' (transportedTargetMap f n e e')
    (transportedTargetMap_square f n e e') p, Subobject.ofLE_arrow_assoc,
    Category.assoc, Subobject.ofLE_arrow,
    transportedStepMap_arrow f n e e' (transportedTargetMap f n e e')
      (transportedTargetMap_square f n e e') (p-1)]

/-- The map on the associated graded of the increasing transported target filtration. -/
def transportedGradedMap (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H') (p : ℤ) :
    transportedGraded X.filtration n H e p ⟶ transportedGraded Y.filtration n H' e' p :=
  cokernel.map _ _ (transportedStepMap f n e e' (p-1))
    (transportedStepMap f n e e' p) (transportedStepMap_inclusion f n e e' p)

/-- Transport of associated graded cohomology is natural for actual filtered maps. -/
theorem transportedGradedIso_naturality (f : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H') (p : ℤ) :
    gradedCohomologyMap f (-p) (-n) ≫ (transportedGradedIso Y.filtration n H' e' p).hom =
      (transportedGradedIso X.filtration n H e p).hom ≫ transportedGradedMap f n e e' p := by
  apply (cancel_epi (cokernel.π _)).1
  simp only [transportedGradedIso, cokernel.mapIso_hom, transportedGradedMap,
    gradedCohomologyMap, Category.assoc, cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc,
    transportedStepMap, Iso.hom_inv_id_assoc]

@[simp]
theorem transportedGradedMap_identity (n : ℤ) {H : A}
    (e : X.complex.homology (-n) ≅ H) (p : ℤ) :
    transportedGradedMap (FilteredMap.id X) n e e p = 𝟙 _ := by
  apply (cancel_epi (cokernel.π _)).1
  simp only [transportedGradedMap, cokernel.map, cokernel.π_desc, transportedStepMap_identity,
    Category.id_comp, Category.comp_id]

@[simp]
theorem transportedGradedMap_composition (f : FilteredMap X Y) (g : FilteredMap Y Z)
    (n : ℤ) {H H' H'' : A} (e : X.complex.homology (-n) ≅ H)
    (e' : Y.complex.homology (-n) ≅ H') (e'' : Z.complex.homology (-n) ≅ H'') (p : ℤ) :
    transportedGradedMap (f.comp g) n e e'' p =
      transportedGradedMap f n e e' p ≫ transportedGradedMap g n e' e'' p := by
  apply (cancel_epi (cokernel.π _)).1
  simp only [transportedGradedMap, cokernel.map, cokernel.π_desc, cokernel.π_desc_assoc,
    Category.assoc]
  rw [transportedStepMap_composition f g n e e' e'' p, Category.assoc]

/-- On every graded target piece, two lifts of the same fixed target map agree. -/
theorem transportedGradedMap_unique (f g : FilteredMap X Y) (n : ℤ) {H H' : A}
    (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H')
    (u : H ⟶ H')
    (hf : HomologicalComplex.homologyMap f.hom (-n) ≫ e'.hom = e.hom ≫ u)
    (hg : HomologicalComplex.homologyMap g.hom (-n) ≫ e'.hom = e.hom ≫ u) (p : ℤ) :
    transportedGradedMap f n e e' p = transportedGradedMap g n e e' p := by
  apply (cancel_epi (cokernel.π _)).1
  simp only [transportedGradedMap, cokernel.map, cokernel.π_desc]
  rw [transportedStepMap_unique f g n e e' u hf hg p]

/-- Naturality of the stabilized-page identification after transporting the
finite image filtration to the original homological target. -/
theorem transportedLimitIso_naturality (f : FilteredMap X Y)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) (r p n : ℤ)
    {H H' : A} (e : X.complex.homology (-n) ≅ H) (e' : Y.complex.homology (-n) ≅ H')
    (L : LimitIso X.filtration D r (-p) (-n)) (L' : LimitIso Y.filtration E r (-p) (-n))
    (h : Stabilized X.filtration r (-p) (-n)) :
    M.map r (-p) (-n) ≫ (L'.iso ≪≫ transportedGradedIso Y.filtration n H' e' p).hom =
      (L.iso ≪≫ transportedGradedIso X.filtration n H e p).hom ≫
        transportedGradedMap f n e e' p := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc, limitIso_naturality f D E M r (-p) (-n) L L' h,
    Category.assoc, transportedGradedIso_naturality f n e e' p, ← Category.assoc]

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

section FullAssembly
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteFiltrationConvergence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]

set_option maxHeartbeats 1500000 in
def realizationData (T : CanonicalTheory.{u,v,w} R) (X : Input.{u,v,w} R) :
    Realization T X.P X.M X.Q X.L := by
  let S := (resolution_page_construction R X.P X.L X.M X.Q X.bounded).choose
  exact { tensorPages := S
          support := (resolution_page_construction R X.P X.L X.M X.Q X.bounded).choose_spec
          secondComparison := resolutionSecondPageComparison X.P X.M X.Q X.projective T S
          targetIso := resolutionTargetIso X.P X.M X.Q X.L X.bounded X.flat
          targetAugmentation := resolutionTargetAugmentation X.P X.M X.Q
          targetQuasiIso := resolutionTensorAugmentation_quasiIso X.P X.M X.Q X.L X.bounded X.flat
          targetInduced := resolutionTargetIso_induced X.P X.M X.Q X.L X.bounded X.flat }

set_option maxHeartbeats 2000000 in
def naturalMapData (T : CanonicalTheory.{u,v,w} R) {X Y : Input.{u,v,w} R}
    (f : Input.Hom X Y) : NaturalMap T (realizationData T X) (realizationData T Y) f := by
  let D := realizationData T X
  let E := realizationData T Y
  let h := tensorFilteredMap D.tensorPages E.tensorPages f.right
    (HomologicalComplex.extendMap f.lift nonnegativeChainEmbedding)
  let N := tensorPageMapData D.tensorPages E.tensorPages f.right
    (HomologicalComplex.extendMap f.lift nonnegativeChainEmbedding)
  have hh : h.hom = HomologicalComplex₂.total.map (tensorCochainMap f.right
      (HomologicalComplex.extendMap f.lift nonnegativeChainEmbedding)) (ComplexShape.up ℤ) :=
    tensorFilteredMap_hom _ _ _ _
  have ht : ∀ n, HomologicalComplex.homologyMap h.hom (-n) ≫ (E.targetIso n).hom =
      (D.targetIso n).hom ≫ targetHomologyMap f.right f.coefficient n := by
    intro n
    rw [hh]
    exact resolutionTargetIso_natural X.Q Y.Q f.right f.coefficient f.lift f.lifts
      X.L Y.L X.bounded Y.bounded X.flat Y.flat n
  refine { filtered := h
           total := hh
           pages := N
           second := ?_
           target := ht
           step := fun p n => transportedStepMap h n (D.targetIso n) (E.targetIso n) p
           step_arrow := ?_
           graded := fun p n => transportedGradedMap h n (D.targetIso n) (E.targetIso n) p
           graded_projection := ?_
           limit_target_natural := ?_
           limit_natural := ?_ }
  · intro p q
    exact resolutionSecondIso_natural T f.right f.coefficient X.Q Y.Q X.projective Y.projective
      f.lift f.lifts D.tensorPages E.tensorPages h hh N p q
  · intro p n
    exact transportedStepMap_arrow h n _ _ _ (ht n) p
  · intro p n
    dsimp only [D, E]
    simp only [transportedGradedMap, cokernel.map, cokernel.π_desc]
  · intro r p n I J hi hj
    simpa only [Iso.trans_hom, Category.assoc] using
      transportedLimitIso_naturality h _ _ N r p n (D.targetIso n) (E.targetIso n) I J hi
  · intro r p n I J hi hj
    exact limitIso_naturality h _ _ N r (-p) (-n) I J hi

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization FiniteFiltrationConvergence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
variable {R : Type u} [Ring R]
/-- Arbitrary representatives of induced page maps satisfy the same composition law. -/
theorem mapData_composition {A : Type*} [Category* A] [Abelian A]
    {X Y Z : FilteredComplex A} {f : FilteredMap X Y} {g : FilteredMap Y Z}
    {D : F03Specs.PageData X.filtration} {E : F03Specs.PageData Y.filtration}
    {G : F03Specs.PageData Z.filtration}
    (M : FilteredPageFunctoriality.MapData f D E)
    (N : FilteredPageFunctoriality.MapData g E G)
    (P : FilteredPageFunctoriality.MapData (f.comp g) D G) (r p n : ℤ) :
    P.map r p n = M.map r p n ≫ N.map r p n := by
  rw [FilteredPageFunctoriality.pageMap_unique _ _ _ _ _ _ _ (P.representative_formula r p n),
    FilteredPageFunctoriality.pageMap_unique _ _ _ _ _ _ _ (M.representative_formula r p n),
    FilteredPageFunctoriality.pageMap_unique _ _ _ _ _ _ _ (N.representative_formula r p n)]
  exact FilteredPageFunctoriality.pageMap_comp f g D E G r p n

/-- It suffices to compare the nonnegative homological second page. -/
theorem page_maps_equal_from_second
    {T : CanonicalTheory.{u,v,w} R} {X Y : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    {f g : FilteredMap
      ⟨sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex)), D.tensorPages.filtration⟩
      ⟨sumTotal (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex)), E.tensorPages.filtration⟩}
    (M : FilteredPageFunctoriality.MapData f D.tensorPages.pages E.tensorPages.pages)
    (N : FilteredPageFunctoriality.MapData g D.tensorPages.pages E.tensorPages.pages)
    (h : ∀ (p : ℕ) (q : ℤ), M.map 2 (-p) (-(p+q)) = N.map 2 (-p) (-(p+q)))
    (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) : M.map r p n = N.map r p n := by
  apply page_maps_equal_later f g D.tensorPages.pages E.tensorPages.pages M N 2 (by omega) ?_ r hr p n
  intro a b
  by_cases ha : a ≤ 0
  · let k := (-a).toNat
    have hk : -(k : ℤ) = a := by
      have he := Int.toNat_of_nonneg (show 0 ≤ -a by omega)
      dsimp only [k]
      omega
    let q : ℤ := -b-(k : ℤ)
    have hq : -((k : ℤ)+q) = b := by dsimp only [q]; omega
    have he := h k q
    rw [hk,hq] at he
    exact he
  · have hz := D.support 2 (-a) (a-b) (Or.inl (by omega))
    have he : D.tensorPages.term 2 (-a) (a-b) =
        PageCohomology.object D.tensorPages.filtration D.tensorPages.pages 2 a b := by
      unfold TensorPages.term
      congr 1 <;> omega
    have hz' : IsZero (PageCohomology.object D.tensorPages.filtration D.tensorPages.pages 2 a b) :=
      IsZero.of_iso hz (eqToIso he.symm)
    exact hz'.eq_of_src _ _

theorem NaturalMap.page_lift_independent
    {T : CanonicalTheory.{u,v,w} R} {X Y : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    {f g : Input.Hom X Y} (M : NaturalMap T D E f) (N : NaturalMap T D E g)
    (hf : f.right = g.right) (hg : f.coefficient = g.coefficient)
    (r p q : ℤ) (hr : 2 ≤ r) : M.page r p q = N.page r p q := by
  apply page_maps_equal_from_second M.pages N.pages ?_ r hr (-p) (-(p+q))
  intro a b
  apply (cancel_mono (E.secondIso a b).hom).1
  rw [M.second, N.second, hf, hg]

set_option maxHeartbeats 3000000 in
theorem NaturalMap.page_identity
    {T : CanonicalTheory.{u,v,w} R} {X : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L}
    (M : NaturalMap T D D (Input.Hom.id X)) (r p q : ℤ) (hr : 2 ≤ r) :
    M.page r p q = 𝟙 _ := by
  let N := FilteredPageFunctoriality.mapData (FilteredMap.id
    ⟨sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex)), D.tensorPages.filtration⟩)
    D.tensorPages.pages D.tensorPages.pages
  have hn : ∀ r p n, N.map r p n = 𝟙 _ :=
    FilteredPageFunctoriality.pageMap_id _ D.tensorPages.pages
  have he := page_maps_equal_from_second M.pages N (by
    intro a b
    rw [hn]
    apply (cancel_mono (D.secondIso a b).hom).1
    rw [M.second]
    have hi : T.torMap a (HomologicalComplex.homologyMap (Input.Hom.id X).right b)
        (Input.Hom.id X).coefficient = LinearMap.id := by
      change T.torMap a (HomologicalComplex.homologyMap (𝟙 X.P) b) (𝟙 X.M) = LinearMap.id
      rw [HomologicalComplex.homologyMap_id]
      exact (T.torMaps a).id (T.rightResolutions (X.P.homology b)) X.M
    rw [hi, ModuleCat.ofHom_id, Category.comp_id, Category.id_comp]) r hr (-p) (-(p+q))
  exact he.trans (hn r (-p) (-(p+q)))

set_option maxHeartbeats 3000000 in
theorem NaturalMap.page_composition
    {T : CanonicalTheory.{u,v,w} R} {X Y Z : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    {F : Realization T Z.P Z.M Z.Q Z.L}
    {f : Input.Hom X Y} {g : Input.Hom Y Z}
    (M : NaturalMap T D E f) (N : NaturalMap T E F g)
    (P : NaturalMap T D F (f.comp g)) (r p q : ℤ) (hr : 2 ≤ r) :
    P.page r p q = M.page r p q ≫ N.page r p q := by
  let J := FilteredPageFunctoriality.mapData (M.filtered.comp N.filtered)
    D.tensorPages.pages F.tensorPages.pages
  have hj := mapData_composition M.pages N.pages J
  have he := page_maps_equal_from_second P.pages J (by
    intro a b
    rw [hj]
    apply (cancel_mono (F.secondIso a b).hom).1
    rw [P.second, Category.assoc, N.second, ← Category.assoc, M.second, Category.assoc]
    have ht := (T.torMaps a).comp (T.rightResolutions (X.P.homology b))
      (T.rightResolutions (Y.P.homology b)) (T.rightResolutions (Z.P.homology b))
      (HomologicalComplex.homologyMap f.right b) (HomologicalComplex.homologyMap g.right b)
      f.coefficient g.coefficient
    change (D.secondIso a b).hom ≫ ModuleCat.ofHom
        (T.torMap a (HomologicalComplex.homologyMap (f.right ≫ g.right) b)
          (f.coefficient ≫ g.coefficient)) = _
    rw [HomologicalComplex.homologyMap_comp]
    dsimp only [CanonicalTheory.torMap]
    rw [ht]
    rfl) r hr (-p) (-(p+q))
  exact he.trans (hj r (-p) (-(p+q)))

set_option maxHeartbeats 3000000 in
theorem comparison_page_isIso
    {T : CanonicalTheory.{u,v,w} R}
    (realize : ∀ X : Input.{u,v,w} R, Realization T X.P X.M X.Q X.L)
    (maps : ∀ {X Y : Input.{u,v,w} R} (f : Input.Hom X Y), NaturalMap T (realize X) (realize Y) f)
    (X : Input.{u,v,w} R) (Q : LeftResolution R X.M) (hQ : Q.IsProjective)
    (l : X.Q.complex ⟶ Q.complex) (hl : ChainLift X.Q Q (LinearMap.id : X.M →ₗ[R] X.M) l)
    (r p q : ℤ) (hr : 2 ≤ r) :
    IsIso ((maps (X := X) (Y := X.changeResolution Q hQ) ⟨𝟙 X.P, 𝟙 X.M, l, hl⟩).page r p q) := by
  let Y := X.changeResolution Q hQ
  obtain ⟨k, hk⟩ := P103.Ch10.Comparison.chain_exists R X.M X.M Q X.Q hQ LinearMap.id
  let f : Input.Hom X Y := ⟨𝟙 X.P, 𝟙 X.M, l, hl⟩
  let g : Input.Hom Y X := ⟨𝟙 X.P, 𝟙 X.M, k, hk⟩
  have hfg := NaturalMap.page_lift_independent (maps (f.comp g)) (maps (Input.Hom.id X))
    (show (f.comp g).right = (Input.Hom.id X).right by
      change 𝟙 X.P ≫ 𝟙 X.P = 𝟙 X.P; exact Category.id_comp _)
    (show (f.comp g).coefficient = (Input.Hom.id X).coefficient by
      change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M; exact Category.id_comp _) r p q hr
  have hgf := NaturalMap.page_lift_independent (maps (g.comp f)) (maps (Input.Hom.id Y))
    (show (g.comp f).right = (Input.Hom.id Y).right by
      change 𝟙 X.P ≫ 𝟙 X.P = 𝟙 X.P; exact Category.id_comp _)
    (show (g.comp f).coefficient = (Input.Hom.id Y).coefficient by
      change 𝟙 X.M ≫ 𝟙 X.M = 𝟙 X.M; exact Category.id_comp _) r p q hr
  have h₁ := (NaturalMap.page_composition (maps f) (maps g) (maps (f.comp g)) r p q hr).symm.trans
    (hfg.trans (NaturalMap.page_identity (maps (Input.Hom.id X)) r p q hr))
  have h₂ := (NaturalMap.page_composition (maps g) (maps f) (maps (g.comp f)) r p q hr).symm.trans
    (hgf.trans (NaturalMap.page_identity (maps (Input.Hom.id Y)) r p q hr))
  let e : (realize X).tensorPages.term r p q ≅ (realize Y).tensorPages.term r p q :=
    ⟨(maps f).page r p q, (maps g).page r p q, h₁, h₂⟩
  exact e.isIso_hom


theorem naturalMap_step_identity
    (T : CanonicalTheory.{u,v,w} R) {X : Input.{u,v,w} R}
    (D : Realization T X.P X.M X.Q X.L) (m : NaturalMap T D D (Input.Hom.id X)) (p n : ℤ) :
    m.step p n = 𝟙 _ := by
  apply (cancel_mono (D.targetPiece p n).arrow).1
  rw [m.step_arrow]
  change (D.targetPiece p n).arrow ≫ targetHomologyMap (𝟙 X.P) (𝟙 X.M) n = _
  rw [targetHomologyMap_identity]
  simp

theorem naturalMap_step_composition
    (T : CanonicalTheory.{u,v,w} R) {X Y Z : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    {G : Realization T Z.P Z.M Z.Q Z.L}
    (f : Input.Hom X Y) (g : Input.Hom Y Z)
    (m : NaturalMap T D E f) (m' : NaturalMap T E G g) (m'' : NaturalMap T D G (f.comp g))
    (p n : ℤ) : m''.step p n = m.step p n ≫ m'.step p n := by
  apply (cancel_mono (G.targetPiece p n).arrow).1
  rw [m''.step_arrow, Category.assoc, m'.step_arrow, ← Category.assoc, m.step_arrow,
    Category.assoc]
  change (D.targetPiece p n).arrow ≫
    targetHomologyMap (f.right ≫ g.right) (f.coefficient ≫ g.coefficient) n = _
  rw [targetHomologyMap_composition]

theorem naturalMap_step_lift_independent
    (T : CanonicalTheory.{u,v,w} R) {X Y : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    (f g : Input.Hom X Y) (m : NaturalMap T D E f) (m' : NaturalMap T D E g)
    (hf : f.right = g.right) (hg : f.coefficient = g.coefficient) (p n : ℤ) :
    m.step p n = m'.step p n := by
  apply (cancel_mono (E.targetPiece p n).arrow).1
  rw [m.step_arrow, m'.step_arrow, hf, hg]

theorem naturalMap_graded_identity
    (T : CanonicalTheory.{u,v,w} R) {X : Input.{u,v,w} R}
    (D : Realization T X.P X.M X.Q X.L) (m : NaturalMap T D D (Input.Hom.id X)) (p n : ℤ) :
    m.graded p n = 𝟙 _ := by
  apply (cancel_epi (cokernel.π _)).1
  rw [m.graded_projection, naturalMap_step_identity T D m p n]
  simp

theorem naturalMap_graded_composition
    (T : CanonicalTheory.{u,v,w} R) {X Y Z : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    {G : Realization T Z.P Z.M Z.Q Z.L}
    (f : Input.Hom X Y) (g : Input.Hom Y Z)
    (m : NaturalMap T D E f) (m' : NaturalMap T E G g) (m'' : NaturalMap T D G (f.comp g))
    (p n : ℤ) : m''.graded p n = m.graded p n ≫ m'.graded p n := by
  apply (cancel_epi (cokernel.π _)).1
  rw [m''.graded_projection, ← Category.assoc, m.graded_projection, Category.assoc,
    m'.graded_projection, naturalMap_step_composition T f g m m' m'' p n,
    Category.assoc]

theorem naturalMap_graded_lift_independent
    (T : CanonicalTheory.{u,v,w} R) {X Y : Input.{u,v,w} R}
    {D : Realization T X.P X.M X.Q X.L} {E : Realization T Y.P Y.M Y.Q Y.L}
    (f g : Input.Hom X Y) (m : NaturalMap T D E f) (m' : NaturalMap T D E g)
    (hf : f.right = g.right) (hg : f.coefficient = g.coefficient) (p n : ℤ) :
    m.graded p n = m'.graded p n := by
  apply (cancel_epi (cokernel.π _)).1
  rw [m.graded_projection, m'.graded_projection,
    naturalMap_step_lift_independent T f g m m' hf hg p n]

/-- The identity coefficient comparisons in both directions identify the
actual finite filtration on the fixed original target. -/
theorem naturalMap_target_choice
    (T : CanonicalTheory.{u,v,w} R)
    (realize : ∀ X : Input.{u,v,w} R, Realization T X.P X.M X.Q X.L)
    (maps : ∀ {X Y : Input.{u,v,w} R} (f : Input.Hom X Y), NaturalMap T (realize X) (realize Y) f)
    (X : Input.{u,v,w} R) (Q : LeftResolution R X.M) (hQ : Q.IsProjective) (p n : ℤ) :
    (realize X).targetPiece p n = (realize (X.changeResolution Q hQ)).targetPiece p n := by
  let Y := X.changeResolution Q hQ
  obtain ⟨l,hl⟩ := P103.Ch10.Comparison.chain_exists R X.M X.M X.Q Q X.projective LinearMap.id
  obtain ⟨k,hk⟩ := P103.Ch10.Comparison.chain_exists R X.M X.M Q X.Q hQ LinearMap.id
  let f : Input.Hom X Y := ⟨𝟙 X.P,𝟙 X.M,l,hl⟩
  let g : Input.Hom Y X := ⟨𝟙 X.P,𝟙 X.M,k,hk⟩
  apply le_antisymm
  · apply Subobject.le_of_comm ((maps f).step p n)
    have h := (maps f).step_arrow p n
    change _ = _ ≫ targetHomologyMap (𝟙 X.P) (𝟙 X.M) n at h
    simpa only [targetHomologyMap_identity, Category.comp_id] using h
  · apply Subobject.le_of_comm ((maps g).step p n)
    have h := (maps g).step_arrow p n
    change _ = _ ≫ targetHomologyMap (𝟙 X.P) (𝟙 X.M) n at h
    simpa only [targetHomologyMap_identity, Category.comp_id] using h



set_option maxHeartbeats 4000000 in
def system (T : CanonicalTheory.{u,v,w} R) : System T where
  resolution_exists M := P103.Ch10.ProjectiveResolutions.exists_projective_resolution R M
  realize := realizationData T
  lift_exists X Y f g := P103.Ch10.Comparison.chain_exists R X.M Y.M X.Q Y.Q X.projective g.hom
  map := fun f => naturalMapData T f
  page_identity X r p q hr := NaturalMap.page_identity (naturalMapData T (Input.Hom.id X)) r p q hr
  page_composition f g r p q hr := NaturalMap.page_composition
    (naturalMapData T f) (naturalMapData T g) (naturalMapData T (f.comp g)) r p q hr
  lift_independent f g hf hg r p q hr := NaturalMap.page_lift_independent
    (naturalMapData T f) (naturalMapData T g) hf hg r p q hr
  step_identity X p n := naturalMap_step_identity T _ (naturalMapData T (Input.Hom.id X)) p n
  step_composition f g p n := naturalMap_step_composition T f g
    (naturalMapData T f) (naturalMapData T g) (naturalMapData T (f.comp g)) p n
  step_lift_independent f g hf hg p n := naturalMap_step_lift_independent T f g
    (naturalMapData T f) (naturalMapData T g) hf hg p n
  graded_identity X p n := naturalMap_graded_identity T _ (naturalMapData T (Input.Hom.id X)) p n
  graded_composition f g p n := naturalMap_graded_composition T f g
    (naturalMapData T f) (naturalMapData T g) (naturalMapData T (f.comp g)) p n
  graded_lift_independent f g hf hg p n := naturalMap_graded_lift_independent T f g
    (naturalMapData T f) (naturalMapData T g) hf hg p n
  comparison_isIso := comparison_page_isIso (realizationData T) (fun f => naturalMapData T f)
  target_choice := naturalMap_target_choice T (realizationData T) (fun f => naturalMapData T f)
  finite X := (kunneth_convergence (realizationData T X)).2.1
  stable X := (kunneth_convergence (realizationData T X)).2.2

theorem kunneth_spectral_sequence : Specs.FullStatement.{u,v,w} := by
  intro R _
  exact ⟨P103.Ch11.ExtTorDefinitions.canonical_theory R, fun T => ⟨system T⟩⟩

theorem System.original_input {T : CanonicalTheory.{u,v,w} R} (S : System T)
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (L : ℤ) (M : ModuleCat.{w} R)
    (hP : BoundedBelow P L) (hflat : FlatTerms.{u,v,w} P) :
    ∃ Q : LeftResolution R M, Q.IsProjective ∧ Nonempty (Realization T P M Q L) := by
  obtain ⟨Q,hQ⟩ := S.resolution_exists M
  exact ⟨Q,hQ,⟨S.realize ⟨P,L,M,Q,hP,hflat,hQ⟩⟩⟩

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end FullAssembly

section OriginalCarrierMaps

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence

open DoubleTotalization FiniteDiagonalFiltrations
open TorBalance (LinearChainMap)
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.BalancedTensor (Tensor tmul)
open P103.Ch10.TotalComplexAssembly
  (totalTermEquiv totalTermEquiv_inclusion cochain_totalInclusion_d)
open FilteredPage

set_option maxHeartbeats 1000000

section OriginalTotal

universe v' w' a b s

variable {R : Type u} [Ring R]

/-- A linear map from a total term is determined by its values on the diagonal summands. -/
theorem cochainTotalLinear_ext {S : Type s} [Ring S] (K : Bicomplex (ModuleCat.{a} S)) (n : ℤ)
    {Z : Type b} [AddCommGroup Z] [Module S Z] {f g : (sumTotal K).X n →ₗ[S] Z}
    (h : ∀ i j (e : i+j=n) (z : (K.X i).X j),
      f ((sumInjection K i j n e).hom z) = g ((sumInjection K i j n e).hom z)) : f = g := by
  have he : f.comp (totalTermEquiv K n).symm.toLinearMap =
      g.comp (totalTermEquiv K n).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    rintro ⟨⟨i,j⟩, e⟩
    ext z
    simp only [LinearMap.comp_apply]
    rw [← totalTermEquiv_inclusion K i j n e z]
    change f ((totalTermEquiv K n).symm (totalTermEquiv K n _)) =
      g ((totalTermEquiv K n).symm (totalTermEquiv K n _))
    rw [LinearEquiv.symm_apply_apply]
    exact h i j e z
  ext z
  have hz := LinearMap.congr_fun he (totalTermEquiv K n z)
  change f ((totalTermEquiv K n).symm (totalTermEquiv K n z)) =
    g ((totalTermEquiv K n).symm (totalTermEquiv K n z)) at hz
  rw [LinearEquiv.symm_apply_apply] at hz
  exact hz

private def cochainTotalLinear {S : Type s} [Ring S] (K : Bicomplex (ModuleCat.{a} S))
    (L : Bicomplex (ModuleCat.{b} S))
    (f : ∀ i j, (K.X i).X j →ₗ[S] (L.X i).X j) (n : ℤ) :
    (sumTotal K).X n →ₗ[S] (sumTotal L).X n :=
  (DirectSum.toModule S _ ((sumTotal L).X n)
    (fun i => (sumInjection L i.val.1 i.val.2 n i.property).hom.comp
      (f i.val.1 i.val.2))).comp (totalTermEquiv K n).toLinearMap

private theorem cochainTotalLinear_inclusion {S : Type s} [Ring S] (K : Bicomplex (ModuleCat.{a} S))
    (L : Bicomplex (ModuleCat.{b} S)) (f : ∀ i j, (K.X i).X j →ₗ[S] (L.X i).X j)
    (i j n : ℤ) (e : i+j=n) (z : (K.X i).X j) :
    cochainTotalLinear K L f n ((sumInjection K i j n e).hom z) =
      (sumInjection L i j n e).hom (f i j z) := by
  let F := DirectSum.toModule S (Diagonal n) ((sumTotal L).X n)
    (fun k => (sumInjection L k.val.1 k.val.2 n k.property).hom.comp
      (f k.val.1 k.val.2))
  change F (totalTermEquiv K n ((sumInjection K i j n e).hom z)) = _
  rw [show totalTermEquiv K n ((sumInjection K i j n e).hom z) =
    DirectSum.lof S (Diagonal n) (fun k => (K.X k.val.1).X k.val.2) ⟨(i,j), e⟩ z
    from totalTermEquiv_inclusion K i j n e z]
  exact DirectSum.toModule_lof S (M := fun k : Diagonal n => (K.X k.val.1).X k.val.2)
    ⟨(i,j), e⟩ z

private theorem cochainTotal_d_inclusion (K : Bicomplex (ModuleCat.{a} ℤ))
    (i j n : ℤ) (e : i+j=n) (z : (K.X i).X j) :
    ((sumTotal K).d n (n+1)).hom ((sumInjection K i j n e).hom z) =
      (sumInjection K (i+1) j (n+1) (by omega)).hom (((K.d i (i+1)).f j).hom z) +
      i.negOnePow •
        (sumInjection K i (j+1) (n+1) (by omega)).hom (((K.X i).d j (j+1)).hom z) := by
  have hd := cochain_totalInclusion_d K i j n (n+1) e
  rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (show (i+1)+j=n+1 by omega),
    HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (show i+(j+1)=n+1 by omega)] at hd
  exact congrArg (fun k => k.hom z) hd

private def cochainTotalChainMap (K : Bicomplex (ModuleCat.{a} ℤ))
    (L : Bicomplex (ModuleCat.{b} ℤ))
    (f : ∀ i j, (K.X i).X j →ₗ[ℤ] (L.X i).X j)
    (hh : ∀ i j z, ((L.d i (i+1)).f j).hom (f i j z) =
      f (i+1) j (((K.d i (i+1)).f j).hom z))
    (hv : ∀ i j z, ((L.X i).d j (j+1)).hom (f i j z) =
      f i (j+1) (((K.X i).d j (j+1)).hom z)) :
    LinearChainMap (sumTotal K) (sumTotal L) where
  app := cochainTotalLinear K L f
  comm n m := by
    by_cases hnm : (ComplexShape.up ℤ).Rel n m
    · have hm : m = n+1 := by simpa only [ComplexShape.up_Rel] using hnm.symm
      subst m
      apply cochainTotalLinear_ext K n
      intro i j e z
      simp only [LinearMap.comp_apply, cochainTotalLinear_inclusion, cochainTotal_d_inclusion _ i j n e,
        hh, hv, map_add, Units.smul_def, map_zsmul]
    · simp only [(sumTotal L).shape _ _ hnm, (sumTotal K).shape _ _ hnm, ModuleCat.hom_zero,
        LinearMap.zero_comp, LinearMap.comp_zero]

/-- The generator-defined map between the original signed tensor totals. -/
def originalTensorTotalMap
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
    (f : LinearChainMap P P') (g : LinearChainMap Q Q') :
    LinearChainMap (sumTotal (tensorCochain P Q)) (sumTotal (tensorCochain P' Q')) :=
  cochainTotalChainMap (tensorCochain P Q) (tensorCochain P' Q')
    (fun i j => tensorMap (f.app (-i)) (g.app (-j)))
    (by
      intro i j
      suffices ((tensorMap (P'.d (-i) (-(i+1))).hom LinearMap.id).comp
          (tensorMap (f.app (-i)) (g.app (-j))) : Tensor R (P.X (-i)) (Q.X (-j)) →ₗ[ℤ] _) =
        (tensorMap (f.app (-(i+1))) (g.app (-j))).comp
          (tensorMap (P.d (-i) (-(i+1))).hom LinearMap.id) by
        exact LinearMap.congr_fun this
      apply tensor_hom_ext
      intro x y
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply]
      exact congrArg (fun a => tmul R a (g.app (-j) y)) (LinearMap.congr_fun (f.comm (-i) (-(i+1))) x))
    (by
      intro i j
      suffices ((tensorMap LinearMap.id (Q'.d (-j) (-(j+1))).hom).comp
          (tensorMap (f.app (-i)) (g.app (-j))) : Tensor R (P.X (-i)) (Q.X (-j)) →ₗ[ℤ] _) =
        (tensorMap (f.app (-i)) (g.app (-(j+1)))).comp
          (tensorMap LinearMap.id (Q.d (-j) (-(j+1))).hom) by
        exact LinearMap.congr_fun this
      apply tensor_hom_ext
      intro x y
      simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply]
      exact congrArg (tmul R (f.app (-i) x)) (LinearMap.congr_fun (g.comm (-j) (-(j+1))) y))

theorem originalTensorTotalMap_inclusion
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
    (f : LinearChainMap P P') (g : LinearChainMap Q Q') (i j n : ℤ) (e : i+j=n)
    (z : Tensor R (P.X (-i)) (Q.X (-j))) :
    (originalTensorTotalMap f g).app n ((sumInjection (tensorCochain P Q) i j n e).hom z) =
      (sumInjection (tensorCochain P' Q') i j n e).hom (tensorMap (f.app (-i)) (g.app (-j)) z) :=
  cochainTotalLinear_inclusion (tensorCochain P Q) (tensorCochain P' Q')
    (fun a b => tensorMap (f.app (-a)) (g.app (-b))) i j n e z

theorem originalTensorTotalMap_tmul
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
    (f : LinearChainMap P P') (g : LinearChainMap Q Q') (i j n : ℤ) (e : i+j=n)
    (x : P.X (-i)) (y : Q.X (-j)) :
    (originalTensorTotalMap f g).app n ((sumInjection (tensorCochain P Q) i j n e).hom (tmul R x y)) =
      (sumInjection (tensorCochain P' Q') i j n e).hom (tmul R (f.app (-i) x) (g.app (-j) y)) := by
  calc
    _ = (sumInjection (tensorCochain P' Q') i j n e).hom
          (tensorMap (f.app (-i)) (g.app (-j)) (tmul R x y)) :=
      originalTensorTotalMap_inclusion f g i j n e (tmul R x y)
    _ = _ := congrArg ((sumInjection (tensorCochain P' Q') i j n e).hom)
      (tensorMap_tmul (f.app (-i)) (g.app (-j)) x y)

end OriginalTotal

section OriginalHomology

universe a b

variable {S : Type u} [Ring S]
variable {A : ShortComplex (ModuleCat.{a} S)} {B : ShortComplex (ModuleCat.{b} S)}

private def shortKernelMap
    (mid : A.X₂ →ₗ[S] B.X₂) (last : A.X₃ →ₗ[S] B.X₃)
    (hlast : B.g.hom.comp mid = last.comp A.g.hom) :
    A.moduleCatLeftHomologyData.K →ₗ[S] B.moduleCatLeftHomologyData.K :=
  (mid.comp (LinearMap.ker A.g.hom).subtype).codRestrict _ (by
    intro z
    have h := LinearMap.congr_fun hlast z.val
    change B.g.hom (mid z.val) = 0
    change B.g.hom (mid z.val) = last (A.g.hom z.val) at h
    rw [h, LinearMap.mem_ker.mp z.property, map_zero])

/-- The map on a short complex's cycle objects across carrier sizes. -/
def shortCyclesLinearMap
    (mid : A.X₂ →ₗ[S] B.X₂) (last : A.X₃ →ₗ[S] B.X₃)
    (hlast : B.g.hom.comp mid = last.comp A.g.hom) :
    A.cycles →ₗ[S] B.cycles :=
  B.moduleCatCyclesIso.inv.hom.comp
    ((shortKernelMap mid last hlast).comp A.moduleCatCyclesIso.hom.hom)

theorem shortCyclesLinearMap_formula
    (mid : A.X₂ →ₗ[S] B.X₂) (last : A.X₃ →ₗ[S] B.X₃)
    (hlast : B.g.hom.comp mid = last.comp A.g.hom) (z : A.cycles) :
    B.iCycles.hom (shortCyclesLinearMap mid last hlast z) = mid (A.iCycles.hom z) := by
  change B.iCycles.hom (B.moduleCatCyclesIso.inv.hom
    (shortKernelMap mid last hlast (A.moduleCatCyclesIso.hom.hom z))) = mid (A.iCycles.hom z)
  have hB := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom B.moduleCatCyclesIso_inv_iCycles)
    (shortKernelMap mid last hlast (A.moduleCatCyclesIso.hom.hom z))
  have hA := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom A.moduleCatCyclesIso_hom_i) z
  change B.iCycles.hom (B.moduleCatCyclesIso.inv.hom _) =
    (shortKernelMap mid last hlast (A.moduleCatCyclesIso.hom.hom z)).val at hB
  change (A.moduleCatCyclesIso.hom.hom z).val = A.iCycles.hom z at hA
  rw [hB]
  change mid (A.moduleCatCyclesIso.hom.hom z).val = mid (A.iCycles.hom z)
  rw [hA]

private def shortQuotientMap (first : A.X₁ →ₗ[S] B.X₁)
    (mid : A.X₂ →ₗ[S] B.X₂) (last : A.X₃ →ₗ[S] B.X₃)
    (hfirst : B.f.hom.comp first = mid.comp A.f.hom)
    (hlast : B.g.hom.comp mid = last.comp A.g.hom) :
    A.moduleCatLeftHomologyData.H →ₗ[S] B.moduleCatLeftHomologyData.H :=
  (LinearMap.range A.moduleCatToCycles).mapQ (LinearMap.range B.moduleCatToCycles)
    (shortKernelMap mid last hlast) (by
      rintro _ ⟨x, rfl⟩
      refine ⟨first x, Subtype.ext ?_⟩
      exact LinearMap.congr_fun hfirst x)

/-- The map on a short complex's homology across carrier sizes. -/
def shortHomologyLinearMap (first : A.X₁ →ₗ[S] B.X₁)
    (mid : A.X₂ →ₗ[S] B.X₂) (last : A.X₃ →ₗ[S] B.X₃)
    (hfirst : B.f.hom.comp first = mid.comp A.f.hom)
    (hlast : B.g.hom.comp mid = last.comp A.g.hom) :
    A.homology →ₗ[S] B.homology :=
  B.moduleCatHomologyIso.inv.hom.comp
    ((shortQuotientMap first mid last hfirst hlast).comp A.moduleCatHomologyIso.hom.hom)

theorem shortHomologyLinearMap_formula (first : A.X₁ →ₗ[S] B.X₁)
    (mid : A.X₂ →ₗ[S] B.X₂) (last : A.X₃ →ₗ[S] B.X₃)
    (hfirst : B.f.hom.comp first = mid.comp A.f.hom)
    (hlast : B.g.hom.comp mid = last.comp A.g.hom) (z : A.cycles) :
    shortHomologyLinearMap first mid last hfirst hlast (A.homologyπ.hom z) =
      B.homologyπ.hom (shortCyclesLinearMap mid last hlast z) := by
  change B.moduleCatHomologyIso.inv.hom
    (shortQuotientMap first mid last hfirst hlast (A.moduleCatHomologyIso.hom.hom (A.homologyπ.hom z))) =
      B.homologyπ.hom (B.moduleCatCyclesIso.inv.hom
        (shortKernelMap mid last hlast (A.moduleCatCyclesIso.hom.hom z)))
  have hA := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom A.π_moduleCatCyclesIso_hom) z
  have hB := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom B.moduleCatCyclesIso_inv_π)
    (shortKernelMap mid last hlast (A.moduleCatCyclesIso.hom.hom z))
  change A.moduleCatHomologyIso.hom.hom (A.homologyπ.hom z) =
    (LinearMap.range A.moduleCatToCycles).mkQ (A.moduleCatCyclesIso.hom.hom z) at hA
  change B.homologyπ.hom (B.moduleCatCyclesIso.inv.hom _) =
    B.moduleCatHomologyIso.inv.hom ((LinearMap.range B.moduleCatToCycles).mkQ _) at hB
  rw [hA, hB]
  rfl

variable {ι : Type*} {c : ComplexShape ι}
variable {K : HomologicalComplex (ModuleCat.{a} S) c}
variable {L : HomologicalComplex (ModuleCat.{b} S) c}

/-- The map on categorical homology of the original complexes. -/
def categoricalHomologyMap (f : LinearChainMap K L) (n : ι) :
    K.homology n →ₗ[S] L.homology n :=
  shortHomologyLinearMap (A := K.sc n) (B := L.sc n)
    (f.app (c.prev n)) (f.app n) (f.app (c.next n)) (f.comm _ _) (f.comm _ _)

theorem categoricalHomologyMap_formula (f : LinearChainMap K L) :
    InducesCategoricalHomology f (categoricalHomologyMap f) := by
  intro n z
  refine ⟨shortCyclesLinearMap (A := K.sc n) (B := L.sc n)
    (f.app n) (f.app (c.next n)) (f.comm _ _) z, ?_, ?_⟩
  · exact shortCyclesLinearMap_formula _ _ _ z
  · exact shortHomologyLinearMap_formula _ _ _ _ _ z

end OriginalHomology

section OriginalPage
universe a b v' w'

variable {S : Type u} [Ring S]

/-- The restriction of an original linear map to two subobjects. -/
def subobjectLinearMap {M : ModuleCat.{a} S} {N : ModuleCat.{b} S}
    (A : Subobject M) (B : Subobject N) (f : M →ₗ[S] N)
    (h : ∀ z : (A : ModuleCat.{a} S), ∃ y : (B : ModuleCat.{b} S),
      B.arrow.hom y = f (A.arrow.hom z)) :
    (A : ModuleCat.{a} S) →ₗ[S] (B : ModuleCat.{b} S) :=
  (LinearEquiv.ofInjective B.arrow.hom
    ((ModuleCat.mono_iff_injective B.arrow).mp inferInstance)).symm.toLinearMap.comp
      ((f.comp A.arrow.hom).codRestrict (LinearMap.range B.arrow.hom) h)

theorem subobjectLinearMap_arrow {M : ModuleCat.{a} S} {N : ModuleCat.{b} S}
    (A : Subobject M) (B : Subobject N) (f : M →ₗ[S] N)
    (h : ∀ z : (A : ModuleCat.{a} S), ∃ y : (B : ModuleCat.{b} S),
      B.arrow.hom y = f (A.arrow.hom z)) (z : (A : ModuleCat.{a} S)) :
    B.arrow.hom (subobjectLinearMap A B f h z) = f (A.arrow.hom z) := by
  let e := LinearEquiv.ofInjective B.arrow.hom ((ModuleCat.mono_iff_injective B.arrow).mp inferInstance)
  change (e (e.symm ⟨f (A.arrow.hom z), h z⟩)).val = f (A.arrow.hom z)
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f (A.arrow.hom z), h z⟩)

private def elementMap {M : ModuleCat.{a} ℤ} (z : M) :
    ModuleCat.of ℤ (ULift.{a} ℤ) ⟶ M :=
  ModuleCat.ofHom {
    toFun := fun t => t.down • z
    map_add' := fun x y => add_zsmul z x.down y.down
    map_smul' := by
      intro r t
      change (r*t.down) • z = M.isModule.smul r (t.down • z)
      rw [int_smul_eq_zsmul M.isModule]
      exact mul_zsmul z r t.down }

private theorem elementMap_comp {M N : ModuleCat.{a} ℤ} (z : M) (f : M ⟶ N) :
    elementMap z ≫ f = elementMap (f.hom z) := by
  apply ModuleCat.hom_ext
  ext t
  change f.hom (t.down • z) = t.down • f.hom z
  exact map_zsmul f.hom t.down z

private theorem elementMap_add {M : ModuleCat.{a} ℤ} (x y : M) :
    elementMap (x+y) = elementMap x + elementMap y := by
  apply ModuleCat.hom_ext
  ext t
  change t.down • (x+y) = t.down • x + t.down • y
  exact zsmul_add x y t.down

private theorem elementMap_eq_zero_iff {M : ModuleCat.{a} ℤ} (z : M) :
    elementMap z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun m : ModuleCat.of ℤ (ULift.{a} ℤ) ⟶ M => m.hom (ULift.up (1 : ℤ))) h
    change (1 : ℤ) • z = 0 at hh
    simpa only [one_zsmul] using hh
  · rintro rfl
    apply ModuleCat.hom_ext
    ext t
    change t.down • (0 : M) = 0
    exact zsmul_zero _

private theorem elementMap_factors_iff {M : ModuleCat.{a} ℤ} (B : Subobject M) (z : M) :
    B.Factors (elementMap z) ↔ ∃ y : (B : ModuleCat.{a} ℤ), B.arrow.hom y = z := by
  rw [Subobject.factors_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g.hom (ULift.up 1), ?_⟩
    have hh := congrArg (fun m : ModuleCat.of ℤ (ULift.{a} ℤ) ⟶ M => m.hom (ULift.up (1 : ℤ))) hg
    change B.arrow.hom (g.hom (ULift.up 1)) = (1 : ℤ) • z at hh
    simpa only [one_zsmul] using hh
  · rintro ⟨y, hy⟩
    refine ⟨elementMap y, ?_⟩
    change elementMap y ≫ B.arrow = _
    exact (elementMap_comp y B.arrow).trans (congrArg elementMap hy)

variable {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
  {L : CochainComplex (ModuleCat.{b} ℤ) ℤ}

/-- An original cochain map preserving the two prescribed filtrations. -/
structure OriginalFilteredMap (F : Filtration K) (G : Filtration L) where
  hom : LinearChainMap K L
  preserves : ∀ p n (z : (F.piece p n : ModuleCat.{a} ℤ)),
    ∃ y : (G.piece p n : ModuleCat.{b} ℤ),
      (G.piece p n).arrow.hom y = hom.app n ((F.piece p n).arrow.hom z)

private theorem almost_range_iff {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
    (F : Filtration K) (r p n : ℤ) (z : K.X n) :
    (∃ y : (almost F r p n : ModuleCat.{a} ℤ), (almost F r p n).arrow.hom y = z) ↔
        (∃ y : (F.piece p n : ModuleCat.{a} ℤ), (F.piece p n).arrow.hom y = z) ∧
        (∃ y : (F.piece (p+r) (n+1) : ModuleCat.{a} ℤ),
          (F.piece (p+r) (n+1)).arrow.hom y = (K.d n (n+1)).hom z) := by
  rw [← elementMap_factors_iff, ← elementMap_factors_iff, ← elementMap_factors_iff,
    Subobject.inf_factors, pullback_factors_iff, elementMap_comp]

private theorem almost_preserves {F : Filtration K} {G : Filtration L}
    (f : OriginalFilteredMap F G) (r p n : ℤ) (z : (almost F r p n : ModuleCat.{a} ℤ)) :
    ∃ y : (almost G r p n : ModuleCat.{b} ℤ),
      (almost G r p n).arrow.hom y = f.hom.app n ((almost F r p n).arrow.hom z) := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := (almost_range_iff F r p n _).1 ⟨z, rfl⟩
  apply (almost_range_iff G r p n _).2
  obtain ⟨u', hu'⟩ := f.preserves p n u
  obtain ⟨v', hv'⟩ := f.preserves (p+r) (n+1) v
  refine ⟨⟨u', hu'.trans (congrArg _ hu)⟩, ⟨v', ?_⟩⟩
  rw [hv', hv]
  exact (LinearMap.congr_fun (f.hom.comm n (n+1)) _).symm

namespace OriginalFilteredMap

variable {F : Filtration K} {G : Filtration L} (f : OriginalFilteredMap F G)

def almostMap (r p n : ℤ) :
    (almost F r p n : ModuleCat.{a} ℤ) →ₗ[ℤ] (almost G r p n : ModuleCat.{b} ℤ) :=
  subobjectLinearMap _ _ (f.hom.app n) (almost_preserves f r p n)

theorem almostMap_arrow (r p n : ℤ) (z : (almost F r p n : ModuleCat.{a} ℤ)) :
    (almost G r p n).arrow.hom (f.almostMap r p n z) =
      f.hom.app n ((almost F r p n).arrow.hom z) :=
  subobjectLinearMap_arrow _ _ _ _ z

private theorem toPage_zero_decompose {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
    (F : Filtration K) (r p n : ℤ) (h : boundaries F r p n ≤ cycles F r p n)
    (z : (almost F r p n : ModuleCat.{a} ℤ)) (hz : (toPage F r p n h).hom z = 0) :
    ∃ (u : (almost F (r-1) (p+1) n : ModuleCat.{a} ℤ))
      (v : (almost F (r-1) (p-r+1) (n-1) : ModuleCat.{a} ℤ)),
      (almost F r p n).arrow.hom z =
        (almost F (r-1) (p+1) n).arrow.hom u +
          (K.d (n-1) n).hom ((almost F (r-1) (p-r+1) (n-1)).arrow.hom v) := by
  obtain ⟨T, e, he, u, v, huv⟩ := PageCohomology.decompose_page_zero F r p n h
    (elementMap z) (by rw [elementMap_comp, elementMap_eq_zero_iff]; exact hz)
  obtain ⟨t, ht⟩ := (ModuleCat.epi_iff_surjective e).mp he (ULift.up 1)
  refine ⟨u.hom t, v.hom t, ?_⟩
  have h' := congrArg (fun m : T ⟶ K.X n => m.hom t) huv
  change (almost F r p n).arrow.hom ((elementMap z).hom (e.hom t)) =
    (almost F (r-1) (p+1) n).arrow.hom (u.hom t) +
      (K.d (n-1) n).hom ((almost F (r-1) (p-r+1) (n-1)).arrow.hom (v.hom t)) at h'
  rw [ht] at h'
  change (almost F r p n).arrow.hom ((1 : ℤ) • z) = _ at h'
  simpa only [one_zsmul] using h' 

private theorem toPage_zero_of_decomposition {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
    (F : Filtration K) (r p n : ℤ) (h : boundaries F r p n ≤ cycles F r p n)
    (z : (almost F r p n : ModuleCat.{a} ℤ))
    (u : (almost F (r-1) (p+1) n : ModuleCat.{a} ℤ))
    (v : (almost F (r-1) (p-r+1) (n-1) : ModuleCat.{a} ℤ))
    (h' : (almost F r p n).arrow.hom z =
      (almost F (r-1) (p+1) n).arrow.hom u +
        (K.d (n-1) n).hom ((almost F (r-1) (p-r+1) (n-1)).arrow.hom v)) :
    (toPage F r p n h).hom z = 0 := by
  rw [← elementMap_eq_zero_iff, ← elementMap_comp]
  apply (PageCohomology.toPage_zero_iff_denominator F r p n h _).2
  have hu : (denominator F r p n).Factors (elementMap u ≫ (almost F (r-1) (p+1) n).arrow) :=
    Subobject.factors_of_le _ le_sup_left (Subobject.factors_comp_arrow _)
  have hv : (denominator F r p n).Factors
      (elementMap v ≫ (almost F (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n) :=
    Subobject.factors_of_le _ le_sup_right (imageSubobject_factors_comp_self _ _)
  rw [elementMap_comp, h', elementMap_add]
  simp only [elementMap_comp] at hu hv
  exact Subobject.factors_add _ _ hu hv

private theorem page_relation (D : F03Specs.PageData F) (E : F03Specs.PageData G)
    (r p n : ℤ) :
    LinearMap.ker (toPage F r p n (D.containment r p n)).hom ≤
      LinearMap.ker ((toPage G r p n (E.containment r p n)).hom.comp (f.almostMap r p n)) := by
  intro z hz
  obtain ⟨u, v, h⟩ := toPage_zero_decompose F r p n _ z (LinearMap.mem_ker.mp hz)
  apply LinearMap.mem_ker.mpr
  change (toPage G r p n (E.containment r p n)).hom (f.almostMap r p n z) = 0
  apply toPage_zero_of_decomposition G r p n _ _ (f.almostMap (r-1) (p+1) n u)
    (f.almostMap (r-1) (p-r+1) (n-1) v)
  simp only [almostMap_arrow, h, map_add]
  congr 1
  exact (LinearMap.congr_fun (f.hom.comm (n-1) n) _).symm

def pageMap (D : F03Specs.PageData F) (E : F03Specs.PageData G) (r p n : ℤ) :
    (PageCohomology.object F D r p n : ModuleCat.{a} ℤ) →ₗ[ℤ]
      (PageCohomology.object G E r p n : ModuleCat.{b} ℤ) :=
  ((toPage F r p n (D.containment r p n)).hom.liftOfSurjective
    ((ModuleCat.epi_iff_surjective _).mp inferInstance))
      ⟨(toPage G r p n (E.containment r p n)).hom.comp (f.almostMap r p n),
        f.page_relation D E r p n⟩

theorem pageMap_formula (D : F03Specs.PageData F) (E : F03Specs.PageData G) (r p n : ℤ) :
    (f.pageMap D E r p n).comp (toPage F r p n (D.containment r p n)).hom =
      (toPage G r p n (E.containment r p n)).hom.comp (f.almostMap r p n) := by
  ext z
  exact LinearMap.equivOfSurjective_apply _ (f.page_relation D E r p n)

private theorem restriction_comm (D : F03Specs.PageData F) (E : F03Specs.PageData G)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) (z : (almost F r p n : ModuleCat.{a} ℤ)) :
    (E.restriction r hr p n).hom (f.almostMap r p n z) =
      f.almostMap r (p+r) (n+1) ((D.restriction r hr p n).hom z) := by
  apply (ModuleCat.mono_iff_injective (almost G r (p+r) (n+1)).arrow).mp inferInstance
  have hE := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (E.restriction_arrow r hr p n))
    (f.almostMap r p n z)
  have hD := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (D.restriction_arrow r hr p n)) z
  change (almost G r (p+r) (n+1)).arrow.hom
    ((E.restriction r hr p n).hom (f.almostMap r p n z)) =
      (L.d n (n+1)).hom ((almost G r p n).arrow.hom (f.almostMap r p n z)) at hE
  change (almost F r (p+r) (n+1)).arrow.hom ((D.restriction r hr p n).hom z) =
    (K.d n (n+1)).hom ((almost F r p n).arrow.hom z) at hD
  change (almost G r (p+r) (n+1)).arrow.hom
    ((E.restriction r hr p n).hom (f.almostMap r p n z)) =
      (almost G r (p+r) (n+1)).arrow.hom (f.almostMap r (p+r) (n+1)
        ((D.restriction r hr p n).hom z))
  rw [hE, almostMap_arrow, almostMap_arrow]
  change (L.d n (n+1)).hom (f.hom.app n ((almost F r p n).arrow.hom z)) =
    f.hom.app (n+1) ((almost F r (p+r) (n+1)).arrow.hom ((D.restriction r hr p n).hom z))
  change (almost F r (p+r) (n+1)).arrow.hom ((D.restriction r hr p n).hom z) = _ at hD
  rw [hD]
  exact LinearMap.congr_fun (f.hom.comm n (n+1)) _

theorem pageMap_differential (D : F03Specs.PageData F) (E : F03Specs.PageData G)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    (E.differential r hr p n).hom.comp (f.pageMap D E r p n) =
      (f.pageMap D E r (p+r) (n+1)).comp (D.differential r hr p n).hom := by
  ext w
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r p n (D.containment r p n))).mp inferInstance w
  have hm := LinearMap.congr_fun (f.pageMap_formula D E r p n) z
  have hn := LinearMap.congr_fun (f.pageMap_formula D E r (p+r) (n+1))
    ((D.restriction r hr p n).hom z)
  have hE := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (E.representative_formula r hr p n))
    (f.almostMap r p n z)
  have hD := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (D.representative_formula r hr p n)) z
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hm hn hE hD ⊢
  rw [hm, hE, hD, hn, f.restriction_comm D E]

private theorem nextRepresentative_comm
    (D : F03Specs.PageData F) (E : F03Specs.PageData G) (r p n : ℤ)
    (z : (almost F (r+1) p n : ModuleCat.{a} ℤ)) :
    (PageCohomology.nextRepresentative G E r p n).hom (f.almostMap (r+1) p n z) =
      f.pageMap D E r p n ((PageCohomology.nextRepresentative F D r p n).hom z) := by
  let inclF := Subobject.ofLE _ _ (PageCohomology.almost_succ_le F r p n)
  let inclG := Subobject.ofLE _ _ (PageCohomology.almost_succ_le G r p n)
  have hi : inclG.hom (f.almostMap (r+1) p n z) =
      f.almostMap r p n (inclF.hom z) := by
    apply (ModuleCat.mono_iff_injective (almost G r p n).arrow).mp inferInstance
    change (almost G r p n).arrow.hom (inclG.hom (f.almostMap (r+1) p n z)) =
      (almost G r p n).arrow.hom (f.almostMap r p n (inclF.hom z))
    have hG := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (Subobject.ofLE_arrow (PageCohomology.almost_succ_le G r p n))) (f.almostMap (r+1) p n z)
    have hF := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (Subobject.ofLE_arrow (PageCohomology.almost_succ_le F r p n))) z
    change (almost G r p n).arrow.hom (inclG.hom (f.almostMap (r+1) p n z)) =
      (almost G (r+1) p n).arrow.hom (f.almostMap (r+1) p n z) at hG
    change (almost F r p n).arrow.hom (inclF.hom z) = (almost F (r+1) p n).arrow.hom z at hF
    rw [hG, f.almostMap_arrow, f.almostMap_arrow, hF]
  change (toPage G r p n (E.containment r p n)).hom (inclG.hom (f.almostMap (r+1) p n z)) =
    f.pageMap D E r p n ((toPage F r p n (D.containment r p n)).hom (inclF.hom z))
  rw [hi]
  exact (LinearMap.congr_fun (f.pageMap_formula D E r p n) (inclF.hom z)).symm

/-- Naturality of the original next-page comparison, witnessed on cycles. -/
theorem next_natural (D : F03Specs.PageData F) (E : F03Specs.PageData G)
    (C : PageCohomology.Data F D) (C' : PageCohomology.Data G E)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    let A := PageCohomology.shortComplex F D r hr p n
    let B := PageCohomology.shortComplex G E r hr p n
    ∀ z : A.cycles, ∃ y : B.cycles,
      B.iCycles.hom y = f.pageMap D E r (p+r) (n+1) (A.iCycles.hom z) ∧
      (C'.nextIso r hr p n).hom.hom
        (f.pageMap D E (r+1) (p+r) (n+1)
          ((C.nextIso r hr p n).inv.hom (A.homologyπ.hom z))) =
        B.homologyπ.hom y := by
  let A := PageCohomology.shortComplex F D r hr p n
  let B := PageCohomology.shortComplex G E r hr p n
  let g₁ : A.X₁ →ₗ[ℤ] B.X₁ := f.pageMap D E r p n
  let g₂ : A.X₂ →ₗ[ℤ] B.X₂ := f.pageMap D E r (p+r) (n+1)
  let g₃ : A.X₃ →ₗ[ℤ] B.X₃ := f.pageMap D E r (p+r+r) (n+1+1)
  have hg₁ : B.f.hom.comp g₁ = g₂.comp A.f.hom := f.pageMap_differential D E r hr p n
  have hg₂ : B.g.hom.comp g₂ = g₃.comp A.g.hom :=
    f.pageMap_differential D E r hr (p+r) (n+1)
  let κ := shortCyclesLinearMap g₂ g₃ hg₂
  let H := shortHomologyLinearMap g₁ g₂ g₃ hg₁ hg₂
  let U := A.liftCycles (PageCohomology.nextRepresentative F D r (p+r) (n+1))
    (C.next_cycle r hr p n)
  let V := B.liftCycles (PageCohomology.nextRepresentative G E r (p+r) (n+1))
    (C'.next_cycle r hr p n)
  have compare (z : (PageCohomology.object F D (r+1) (p+r) (n+1) : ModuleCat.{a} ℤ)) :
      (C'.nextIso r hr p n).hom.hom (f.pageMap D E (r+1) (p+r) (n+1) z) =
        H ((C.nextIso r hr p n).hom.hom z) := by
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
      (toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)))).mp inferInstance z
    have hm := LinearMap.congr_fun (f.pageMap_formula D E (r+1) (p+r) (n+1)) x
    change f.pageMap D E (r+1) (p+r) (n+1)
      ((toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1))).hom x) =
      (toPage G (r+1) (p+r) (n+1) (E.containment (r+1) (p+r) (n+1))).hom
        (f.almostMap (r+1) (p+r) (n+1) x) at hm
    have hC := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (C.nextIso_formula r hr p n)) x
    have hC' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (C'.nextIso_formula r hr p n))
      (f.almostMap (r+1) (p+r) (n+1) x)
    change (C.nextIso r hr p n).hom.hom
      ((toPage F (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1))).hom x) =
      A.homologyπ.hom (U.hom x) at hC
    change (C'.nextIso r hr p n).hom.hom
      ((toPage G (r+1) (p+r) (n+1) (E.containment (r+1) (p+r) (n+1))).hom
        (f.almostMap (r+1) (p+r) (n+1) x)) =
      B.homologyπ.hom (V.hom (f.almostMap (r+1) (p+r) (n+1) x)) at hC'
    rw [hm, hC, hC', shortHomologyLinearMap_formula]
    apply congrArg B.homologyπ.hom
    apply (ModuleCat.mono_iff_injective B.iCycles).mp inferInstance
    have hU := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (A.liftCycles_i _ (C.next_cycle r hr p n))) x
    have hV := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (B.liftCycles_i _ (C'.next_cycle r hr p n))) (f.almostMap (r+1) (p+r) (n+1) x)
    change A.iCycles.hom (U.hom x) = (PageCohomology.nextRepresentative F D r (p+r) (n+1)).hom x at hU
    change B.iCycles.hom (V.hom (f.almostMap (r+1) (p+r) (n+1) x)) =
      (PageCohomology.nextRepresentative G E r (p+r) (n+1)).hom
        (f.almostMap (r+1) (p+r) (n+1) x) at hV
    change B.iCycles.hom (V.hom (f.almostMap (r+1) (p+r) (n+1) x)) =
      B.iCycles.hom (shortCyclesLinearMap g₂ g₃ hg₂ (U.hom x))
    rw [hV, shortCyclesLinearMap_formula, hU]
    exact f.nextRepresentative_comm D E r (p+r) (n+1) x
  dsimp only
  intro z
  refine ⟨κ z, shortCyclesLinearMap_formula g₂ g₃ hg₂ z, ?_⟩
  change (C'.nextIso r hr p n).hom.hom
      (f.pageMap D E (r+1) (p+r) (n+1) ((C.nextIso r hr p n).inv.hom (A.homologyπ.hom z))) =
    B.homologyπ.hom (κ z)
  rw [compare, ModuleCat.hom_inv_apply]
  exact shortHomologyLinearMap_formula g₁ g₂ g₃ hg₁ hg₂ z

end OriginalFilteredMap

end OriginalPage

section OriginalFiltration

universe a b v' w'
variable {S : Type u} [Ring S] {I : Type} {Z : I → ModuleCat.{a} S}

private def coproductBiconeIso (B : Bicone Z) (hB : B.IsBilimit) :
    B.pt ≅ ModuleCat.of S (DirectSum I (fun i => ↥(Z i))) :=
  hB.isColimit.coconePointUniqueUpToIso (ModuleCat.coproductCoconeIsColimit Z)

private theorem coproductBiconeIso_ι_hom (B : Bicone Z) (hB : B.IsBilimit) (i : I) (z : Z i) :
    (coproductBiconeIso B hB).hom.hom ((B.ι i).hom z) = DirectSum.lof S I (fun i => Z i) i z := by
  exact congrArg (fun f : Z i ⟶ ModuleCat.of S (DirectSum I (fun i => ↥(Z i))) => f.hom z)
    (hB.isColimit.comp_coconePointUniqueUpToIso_hom (ModuleCat.coproductCoconeIsColimit Z) ⟨i⟩)

private def biconeLinearMap (B : Bicone Z) (hB : B.IsBilimit)
    {Y : ModuleCat.{b} S} (f : ∀ i, Z i →ₗ[S] Y) :
    B.pt →ₗ[S] Y :=
  (DirectSum.toModule S I Y f).comp (coproductBiconeIso B hB).hom.hom

private theorem biconeLinearMap_ι (B : Bicone Z) (hB : B.IsBilimit)
    {Y : ModuleCat.{b} S} (f : ∀ i, Z i →ₗ[S] Y) (i : I) (z : Z i) :
    biconeLinearMap B hB f ((B.ι i).hom z) = f i z := by
  change DirectSum.toModule S I Y f ((coproductBiconeIso B hB).hom.hom ((B.ι i).hom z)) = _
  rw [coproductBiconeIso_ι_hom]
  exact DirectSum.toModule_lof S (M := fun j : I => ↥(Z j)) i z

private theorem biconeLinearMap_ext (B : Bicone Z) (hB : B.IsBilimit)
    {Y : ModuleCat.{b} S} {f g : B.pt →ₗ[S] Y}
    (h : ∀ i z, f ((B.ι i).hom z) = g ((B.ι i).hom z)) : f = g := by
  let e := (coproductBiconeIso B hB).toLinearEquiv
  have hd : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro j
    ext z
    change f (e.symm (DirectSum.lof S I (fun i => Z i) j z)) =
      g (e.symm (DirectSum.lof S I (fun i => Z i) j z))
    rw [← coproductBiconeIso_ι_hom B hB j z]
    change f (e.symm (e ((B.ι j).hom z))) = g (e.symm (e ((B.ι j).hom z)))
    rw [e.symm_apply_apply]
    exact h j z
  ext z
  have hz := LinearMap.congr_fun hd (e z)
  change f (e.symm (e z)) = g (e.symm (e z)) at hz
  simpa only [e.symm_apply_apply] using hz

private theorem subobject_arrow_cast {Y : ModuleCat.{a} S} {U V : Subobject Y}
    (e : U = V) (z : (U : ModuleCat.{a} S)) :
    V.arrow.hom (e ▸ z) = U.arrow.hom z := by
  subst V
  rfl

variable {R : Type u} [Ring R]
variable {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
variable {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}

/-- The term-by-term tensor map preserves the row filtration. -/
def originalTensorFilteredMap (f : LinearChainMap P P') (g : LinearChainMap Q Q')
    (D : TensorPages P Q) (E : TensorPages P' Q') :
    OriginalFilteredMap D.filtration E.filtration where
  hom := originalTensorTotalMap f g
  preserves p n z := by
    obtain ⟨B, hB, ι, hι, e, hBι⟩ := D.formula p n
    obtain ⟨B', hB', ι', hι', e', hB'ι⟩ := E.formula p n
    let z₀ : (Subobject.mk ι : ModuleCat ℤ) := e ▸ z
    have hz₀ : (Subobject.mk ι).arrow.hom z₀ = (D.filtration.piece p n).arrow.hom z :=
      subobject_arrow_cast e.symm z
    let t : B.pt →ₗ[ℤ] B'.pt := biconeLinearMap B hB fun i => (B'.ι i).hom.comp
      (tensorMap (f.app (-i.val.val.1)) (g.app (-i.val.val.2)))
    have ht : ι'.hom.comp t = ((originalTensorTotalMap f g).app n).comp ι.hom := by
      apply biconeLinearMap_ext B hB
      intro i x
      change ι'.hom (t ((B.ι i).hom x)) =
        (originalTensorTotalMap f g).app n (ι.hom ((B.ι i).hom x))
      have h₁ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hBι i)) x
      have h₂ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hB'ι i))
        (tensorMap (f.app (-i.val.val.1)) (g.app (-i.val.val.2)) x)
      rw [biconeLinearMap_ι B hB]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
      change ι'.hom ((B'.ι i).hom (tensorMap (f.app (-i.val.val.1)) (g.app (-i.val.val.2)) x)) = _
      rw [h₁, h₂]
      exact (originalTensorTotalMap_inclusion f g i.val.val.1 i.val.val.2 n i.val.property x).symm
    let y₀ : (Subobject.mk ι' : ModuleCat ℤ) :=
      (Subobject.underlyingIso ι').inv.hom (t ((Subobject.underlyingIso ι).hom.hom z₀))
    have hy₀ : (Subobject.mk ι').arrow.hom y₀ =
        (originalTensorTotalMap f g).app n ((D.filtration.piece p n).arrow.hom z) := by
      have hi' := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (Subobject.underlyingIso_arrow ι'))
          (t ((Subobject.underlyingIso ι).hom.hom z₀))
      have hi := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (Subobject.underlyingIso_hom_comp_eq_mk ι)) z₀
      change (Subobject.mk ι').arrow.hom y₀ = _ at hi'
      change ι.hom ((Subobject.underlyingIso ι).hom.hom z₀) = _ at hi
      rw [hi']
      have hh := LinearMap.congr_fun ht ((Subobject.underlyingIso ι).hom.hom z₀)
      change ι'.hom (t ((Subobject.underlyingIso ι).hom.hom z₀)) =
        (originalTensorTotalMap f g).app n (ι.hom ((Subobject.underlyingIso ι).hom.hom z₀)) at hh
      rw [hh, hi, hz₀]
    exact ⟨e' ▸ y₀, (subobject_arrow_cast e' y₀).trans hy₀⟩

end OriginalFiltration

section
variable {R : Type u} [Ring R]

section OriginalTargetMaps
universe v' w'
open TorBalance (LinearChainMap)
open P103.BalancedTensor (Tensor tmul)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Tensoring an original map of right complexes and an original coefficient map. -/
def originalCoefficientComplexMap
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    (f : LinearChainMap P P') (g : M →ₗ[R] N) :
    LinearChainMap (coefficientComplex P M) (coefficientComplex P' N) where
  app n := tensorMap (f.app n) g
  comm i j := by
    apply tensor_hom_ext
    intro a b
    change ((tensorMap (P'.d i j).hom LinearMap.id).comp (tensorMap (f.app i) g))
        (tmul R a b) =
      ((tensorMap (f.app j) g).comp (tensorMap (P.d i j).hom LinearMap.id)) (tmul R a b)
    simp only [LinearMap.comp_apply, tensorMap_tmul, LinearMap.id_apply]
    exact congrArg (fun x => tmul R x (g b)) (f.comm_apply i j a)

/-- Lift the homology map of the original coefficient complex to the
carrier size used by the total comparison. -/
def originalTargetMap {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
    (f : OriginalInputMap X Y) (n : ℤ) :
    targetHomology X.P X.M n →ₗ[ℤ] targetHomology Y.P Y.M n :=
  (ULift.moduleEquiv : ULift.{u} (Homology (coefficientComplex Y.P Y.M) n) ≃ₗ[ℤ] _).symm.toLinearMap.comp
    (((originalCoefficientComplexMap f.right f.coefficient).homologyMap n).comp
      (ULift.moduleEquiv : ULift.{u} (Homology (coefficientComplex X.P X.M) n) ≃ₗ[ℤ] _).toLinearMap)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem originalTargetAugmentation_natural
    {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R} (f : OriginalInputMap X Y)
    (a : TargetAugmentation X.P X.M X.Q) (b : TargetAugmentation Y.P Y.M Y.Q)
    (n : ℤ) (z : (sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex))).X n) :
    (b.hom.f n).hom ((originalTensorTotalMap f.right f.lift.extendNonnegative).app n z) =
      ULift.up ((originalCoefficientComplexMap f.right f.coefficient).app (-n)
        (ULift.down ((a.hom.f n).hom z))) := by
  let K := tensorCochain X.P (extendNonnegativeChain X.Q.complex)
  let L := tensorCochain Y.P (extendNonnegativeChain Y.Q.complex)
  let fT := originalTensorTotalMap f.right f.lift.extendNonnegative
  let g := originalCoefficientComplexMap f.right f.coefficient
  let eX := (ULift.moduleEquiv : ULift.{u} ((coefficientComplex X.P X.M).X (-n)) ≃ₗ[ℤ] _)
  let eY := (ULift.moduleEquiv : ULift.{u} ((coefficientComplex Y.P Y.M).X (-n)) ≃ₗ[ℤ] _)
  suffices h : (b.hom.f n).hom.comp (fT.app n) =
      eY.symm.toLinearMap.comp ((g.app (-n)).comp (eX.toLinearMap.comp (a.hom.f n).hom)) by
    exact LinearMap.congr_fun h z
  apply cochainTotalLinear_ext K n
  intro i j h z'
  suffices h' : (((b.hom.f n).hom.comp (fT.app n)).comp
      (sumInjection K i j n h).hom) =
      ((eY.symm.toLinearMap.comp ((g.app (-n)).comp (eX.toLinearMap.comp (a.hom.f n).hom))).comp
        (sumInjection K i j n h).hom) from LinearMap.congr_fun h' z'
  change (_ : Tensor R (X.P.X (-i)) ((extendNonnegativeChain X.Q.complex).X (-j)) →ₗ[ℤ] _) = _
  apply tensor_hom_ext
  intro x y
  simp only [LinearMap.comp_apply]
  change (b.hom.f n).hom (fT.app n ((sumInjection K i j n h).hom (tmul R x y))) =
    ULift.up (g.app (-n) (ULift.down ((a.hom.f n).hom _)))
  have htmul :
      fT.app n ((sumInjection K i j n h).hom (tmul R x y)) =
      (sumInjection L i j n h).hom
        (tmul R (f.right.app (-i) x) (f.lift.extendNonnegative.app (-j) y)) :=
    originalTensorTotalMap_tmul f.right f.lift.extendNonnegative i j n h x y
  rw [htmul]
  by_cases hj : j = 0
  · subst j
    have hn : i = n := (add_zero i).symm.trans h
    cases hn
    let ex := X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl
    let ey := Y.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl
    let y₀ := ex.hom.hom y
    have hex : ex.inv.hom y₀ = y := ModuleCat.inv_hom_apply ex y
    change (b.hom.f n).hom ((sumInjection L n 0 n _).hom
      (tmul R (f.right.app (-n) x) (f.lift.extendNonnegative.app 0 y))) =
      ULift.up (g.app (-n) (ULift.down ((a.hom.f n).hom
        ((sumInjection K n 0 n _).hom (tmul R x y)))))
    have hExt : f.lift.extendNonnegative.app 0 (ex.inv.hom y₀) =
        ey.inv.hom (f.lift.app 0 y₀) :=
      f.lift.extendNonnegative_app_inv 0 y₀
    rw [← hex, hExt]
    rw [b.zero_component, a.zero_component]
    change ULift.up (tmul R (f.right.app (-n) x) (Y.Q.ε (f.lift.app 0 y₀))) =
      ULift.up (tmul R (f.right.app (-n) x) (f.coefficient (X.Q.ε y₀)))
    exact congrArg (fun b₀ => ULift.up (tmul R (f.right.app (-n) x) b₀))
      (LinearMap.congr_fun f.lift_augmented y₀)
  · have ha := congrArg (fun k => k.hom (tmul R x y)) (a.other_components i j n h hj)
    have hb := congrArg (fun k => k.hom (tmul R (f.right.app (-i) x)
      (f.lift.extendNonnegative.app (-j) y))) (b.other_components i j n h hj)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at ha hb
    rw [ha, hb]
    rfl

end OriginalTargetMaps

section OriginalTargetComparison

open TorBalance (LinearChainMap)
universe v' w'

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem shiftedCoefficientMap_apply
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {M : ModuleCat.{w} R} {N : ModuleCat.{w'} R}
    (g : LinearChainMap (coefficientComplex P M) (coefficientComplex P' N))
    (i j : ℤ) (h : -i = j) (z : (reverseChain (liftedCoefficientComplex P M)).X i) :
    ULift.down ((liftedCoefficientComplex P' N).restrictionXIso reversal h |>.hom
      (ULift.up (g.app (-i) z.down))) =
      g.app j (ULift.down ((liftedCoefficientComplex P M).restrictionXIso reversal h |>.hom z)) := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced map on the original quotient commutes with the two
target comparisons when the actual augmentations commute on terms. -/
theorem originalTargetIso_natural
    {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
    {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
    (f : LinearChainMap
      (sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex)))
      (sumTotal (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex))))
    (g : LinearChainMap (coefficientComplex X.P X.M) (coefficientComplex Y.P Y.M))
    (h : ∀ i z, (E.targetAugmentation.hom.f i).hom (f.app i z) =
      ULift.up (g.app (-i) (ULift.down ((D.targetAugmentation.hom.f i).hom z))))
    (hT : ∀ n,
      (sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex))).homology n →ₗ[ℤ]
      (sumTotal (tensorCochain Y.P (extendNonnegativeChain Y.Q.complex))).homology n)
    (hTf : InducesCategoricalHomology f hT)
    (hq : ∀ n,
      Homology (coefficientComplex X.P X.M) n →ₗ[ℤ] Homology (coefficientComplex Y.P Y.M) n)
    (hqf : g.InducesHomology (fun n z => hq n z))
    (ht : ∀ n, targetHomology X.P X.M n →ₗ[ℤ] targetHomology Y.P Y.M n)
    (htf : ∀ n z, ht n (ULift.up z) = ULift.up (hq n z)) (n : ℤ) :
    (E.targetIso n).hom.hom.comp (hT (-n)) = (ht n).comp (D.targetIso n).hom.hom := by
  let K := sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex))
  apply LinearMap.ext
  intro a
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (-n))).mp inferInstance a
  change (K.homologyπ (-n)).hom z = a at hz
  subst a
  obtain ⟨y, hy, hzy⟩ := hTf (-n) z
  obtain ⟨w, hw, hwclass⟩ := D.targetInduced n z
  obtain ⟨w', hw', hwy⟩ := E.targetInduced n y
  obtain ⟨t, ht', htz⟩ := hqf n w
  have he : w' = t := by
    apply Subtype.ext
    rw [hw', hy, h (-n)]
    rw [shiftedCoefficientMap_apply, ← hw]
    exact ht'.symm
  change (E.targetIso n).hom.hom
      (hT (-n) (((sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex))).homologyπ (-n)).hom z)) =
    ht n ((D.targetIso n).hom.hom
      (((sumTotal (tensorCochain X.P (extendNonnegativeChain X.Q.complex))).homologyπ (-n)).hom z))
  rw [hzy, hwy, hwclass, htf, he]
  exact congrArg ULift.up htz.symm
end OriginalTargetComparison

section OriginalTargetNaturality

universe v' w'

theorem originalTargetComparison_natural
    {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
    {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
    (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
    (f : OriginalInputMap X Y) (n : ℤ) :
    (E.targetIso n).hom.hom.comp
      (categoricalHomologyMap (originalTensorTotalMap f.right f.lift.extendNonnegative) (-n)) =
      (originalTargetMap f n).comp (D.targetIso n).hom.hom := by
  let total := originalTensorTotalMap f.right f.lift.extendNonnegative
  let g := originalCoefficientComplexMap f.right f.coefficient
  exact originalTargetIso_natural D E total g
    (originalTargetAugmentation_natural f D.targetAugmentation E.targetAugmentation)
    _ (categoricalHomologyMap_formula total) _ g.homologyMap_induces (originalTargetMap f)
    (by intros; rfl) n

end OriginalTargetNaturality

end


end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end OriginalCarrierMaps


section OriginalRowMaps

universe v' w' a b

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization DoubleComplexFirstPages FiniteDiagonalFiltrations
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section
variable {R : Type u} [Ring R]
  {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
  {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
  (f : LinearChainMap P P') (g : LinearChainMap Q Q')

/-- The horizontal map at a fixed resolution degree. -/
def originalTensorRowMap (j : ℤ) :
    LinearChainMap ((tensorCochain P Q).flip.X j) ((tensorCochain P' Q').flip.X j) where
  app i := tensorMap (f.app (-i)) (g.app (-j))
  comm i k := by
    apply tensor_hom_ext
    intro x y
    change P103.BalancedTensor.tmul R ((P'.d (-i) (-k)).hom (f.app (-i) x)) (g.app (-j) y) =
      P103.BalancedTensor.tmul R (f.app (-k) ((P.d (-i) (-k)).hom x)) (g.app (-j) y)
    exact congrArg (fun t => P103.BalancedTensor.tmul R t (g.app (-j) y))
      (LinearMap.congr_fun (f.comm (-i) (-k)) x)

variable {S : TensorPages P Q} {U : TensorPages P' Q'}
  (F : OriginalFilteredMap S.filtration U.filtration)
  (hF : F.hom = originalTensorTotalMap f g)
  (C : RowData (tensorCochain P Q) S.filtration S.formula S.pages)
  (D : RowData (tensorCochain P' Q') U.filtration U.formula U.pages)

include hF in
set_option maxHeartbeats 1500000 in
theorem originalRowFirstIso_natural (p q : ℤ) :
    (D.firstIso p q).hom.hom.comp (F.pageMap S.pages U.pages 1 p (p+q)) =
      (categoricalHomologyMap (originalTensorRowMap f g p) q).comp (C.firstIso p q).hom.hom := by
  let K := tensorCochain P Q
  let L := tensorCochain P' Q'
  let A := K.flip.X p
  let B := L.flip.X p
  let a := rowAlmostCycle K S.filtration S.formula p q (A.iCycles q) (A.iCycles_d q (q+1))
  let b := rowAlmostCycle L U.filtration U.formula p q (B.iCycles q) (B.iCycles_d q (q+1))
  let π := rowCyclesToPage K S.filtration S.formula S.pages p q
  have hC := C.first_formula p q (A.iCycles q) (A.iCycles_d q (q+1)) a
    (rowAlmostCycle_arrow K S.filtration S.formula p q _ _)
  have hD := D.first_formula p q (B.iCycles q) (B.iCycles_d q (q+1)) b
    (rowAlmostCycle_arrow L U.filtration U.formula p q _ _)
  have hA : A.liftCycles (A.iCycles q) (q+1) (by simp) (A.iCycles_d q (q+1)) = 𝟙 _ := by
    apply (cancel_mono (A.iCycles q)).mp
    simp
  have hB : B.liftCycles (B.iCycles q) (q+1) (by simp) (B.iCycles_d q (q+1)) = 𝟙 _ := by
    apply (cancel_mono (B.iCycles q)).mp
    simp
  rw [hA, Category.id_comp] at hC
  rw [hB, Category.id_comp] at hD
  have ha := rowAlmostCycle_arrow K S.filtration S.formula p q (A.iCycles q) (A.iCycles_d q (q+1))
  have hb := rowAlmostCycle_arrow L U.filtration U.formula p q (B.iCycles q) (B.iCycles_d q (q+1))
  apply LinearMap.ext
  intro x
  have : Epi π := rowCyclesToPage_epi K S.filtration S.formula S.pages p q
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance x
  obtain ⟨y, hy₁, hy₂⟩ := categoricalHomologyMap_formula (originalTensorRowMap f g p) q z
  have hy : F.almostMap 1 p (p+q) (a.hom z) = b.hom y := by
    apply (ModuleCat.mono_iff_injective (FilteredPage.almost U.filtration 1 p (p+q)).arrow).mp inferInstance
    have ha₁ := ConcreteCategory.congr_hom ha z
    have hb₁ := ConcreteCategory.congr_hom hb y
    change (FilteredPage.almost S.filtration 1 p (p+q)).arrow.hom (a.hom z) =
      (sumInjection K q p (p+q) (by omega)).hom ((A.iCycles q).hom z) at ha₁
    change (FilteredPage.almost U.filtration 1 p (p+q)).arrow.hom (b.hom y) =
      (sumInjection L q p (p+q) (by omega)).hom ((B.iCycles q).hom y) at hb₁
    change (FilteredPage.almost U.filtration 1 p (p+q)).arrow.hom (F.almostMap 1 p (p+q) (a.hom z)) = _
    rw [F.almostMap_arrow, hF, ha₁, hb₁, hy₁, originalTensorTotalMap_inclusion]
    rfl
  have hp := LinearMap.congr_fun (F.pageMap_formula S.pages U.pages 1 p (p+q)) (a.hom z)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hy] at hp
  have hC' := ConcreteCategory.congr_hom hC z
  have hD' := ConcreteCategory.congr_hom hD y
  change (C.firstIso p q).hom.hom (π z) = (A.homologyπ q).hom z at hC'
  change (D.firstIso p q).hom.hom
    ((FilteredPage.toPage U.filtration 1 p (p+q) (U.pages.containment _ _ _)).hom (b.hom y)) =
      (B.homologyπ q).hom y at hD'
  change (D.firstIso p q).hom.hom (F.pageMap S.pages U.pages 1 p (p+q) (π z)) =
    categoricalHomologyMap (originalTensorRowMap f g p) q ((C.firstIso p q).hom.hom (π z))
  change F.pageMap S.pages U.pages 1 p (p+q) (π z) = _ at hp
  rw [hp, hC', hD']
  exact hy₂.symm

end

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end OriginalRowMaps

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section OriginalRowTensorComparison

universe v' w'

variable {R : Type u} [Ring R]
  {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
  {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
  (f : LinearChainMap P P') (g : LinearChainMap Q Q')

open P103.BalancedTensor (Tensor tmul)

/-- The signed comparison untwists the row differential and induces this map
on the tensor of the original horizontal homology with the resolution. -/
def originalRowTensorComplexMap (b : ℤ) :
    LinearChainMap (rowTensorComplex P Q b) (rowTensorComplex P' Q' b) where
  app a := tensorMap (categoricalHomologyMap f (-b)) (g.app (-a))
  comm i j := by
    apply tensor_hom_ext
    intro x y
    change tmul R (categoricalHomologyMap f (-b) x) ((Q'.d (-i) (-j)).hom (g.app (-i) y)) =
      tmul R (categoricalHomologyMap f (-b) x) (g.app (-j) ((Q.d (-i) (-j)).hom y))
    rw [g.comm_apply]

private def reverseCyclesIso (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (b : ℤ) :
    (reverseChain P).cycles b ≅ P.cycles (-b) :=
  P.restrictionCyclesIso reversal b (b+1) (by simp) (show reversal.f b = -b from rfl)
    (show -(b+1) = -b-1 by omega) (by simp)

private theorem reverseCyclesIso_hom_apply (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (b : ℤ) (z : (reverseChain P).cycles b) :
    (P.iCycles (-b)).hom ((reverseCyclesIso P b).hom.hom z) =
      ((reverseChain P).iCycles b).hom z := by
  have h := P.restrictionCyclesIso_hom_iCycles reversal b (b+1) (by simp)
    (show reversal.f b = -b from rfl) (show -(b+1) = -b-1 by omega) (by simp)
  change (reverseCyclesIso P b).hom ≫ P.iCycles (-b) =
    (reverseChain P).iCycles b ≫ (P.restrictionXIso reversal (show reversal.f b = -b from rfl)).hom at h
  have he : (P.restrictionXIso reversal (show reversal.f b = -b from rfl)).hom = 𝟙 _ := rfl
  rw [he, Category.comp_id] at h
  exact congrArg (fun k => k.hom z) h

private theorem reverseHomologyIso_apply_class (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (b : ℤ) (z : (reverseChain P).cycles b) :
    (reverseHomologyIso P b).hom.hom (((reverseChain P).homologyπ b).hom z) =
      (P.homologyπ (-b)).hom ((reverseCyclesIso P b).hom.hom z) := by
  have h : (reverseChain P).homologyπ b ≫ (reverseHomologyIso P b).hom =
      (reverseCyclesIso P b).hom ≫ P.homologyπ (-b) := by
    unfold reverseHomologyIso
    apply HomologicalComplex.homologyπ_restrictionHomologyIso_hom
  exact congrArg (fun k => k.hom z) h

private theorem rowFlatHomologyProjection (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (e : TorBalance.HomologyComparison
      (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ))
    (z : (reverseChain P).cycles b) (m : Q.X (-a)) :
    (e.equivalence ((reverseChain P).sc b)).hom.hom
      (tmul R (((reverseChain P).homologyπ b).hom z) m) =
    (((tensorCochain P Q).flip.X a).homologyπ b).hom
      ((e.cyclesEquivalence ((reverseChain P).sc b)).hom.hom (tmul R z m)) := by
  exact congrArg (fun k => k.hom (tmul R z m)) (e.projection ((reverseChain P).sc b))

private theorem rowFlatCycleInclusion (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (e : TorBalance.HomologyComparison
      (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ))
    (z : (reverseChain P).cycles b) (m : Q.X (-a)) :
    (((tensorCochain P Q).flip.X a).iCycles b).hom
      ((e.cyclesEquivalence ((reverseChain P).sc b)).hom.hom (tmul R z m)) =
      tmul R (((reverseChain P).iCycles b).hom z) m := by
  exact congrArg (fun k => k.hom (tmul R z m)) (e.inclusion ((reverseChain P).sc b))

private theorem rowTensorHomologyIso_apply_class (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ)
    (e : TorBalance.HomologyComparison
      (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ))
    (z : (reverseChain P).cycles b) (m : Q.X (-a)) :
    (rowTensorHomologyIso P Q a b e).hom.hom
      ((((tensorCochain P Q).flip.X a).homologyπ b).hom
        ((e.cyclesEquivalence ((reverseChain P).sc b)).hom.hom (tmul R z m))) =
    tmul R ((P.homologyπ (-b)).hom ((reverseCyclesIso P b).hom.hom z)) m := by
  rw [← rowFlatHomologyProjection P Q a b e]
  let S := (reverseChain P).sc b
  change ((tensorFunctor (Q.X (-a))).map (reverseHomologyIso P b).hom)
    ((e.equivalence S).inv ((e.equivalence S).hom
      (tmul R (((reverseChain P).homologyπ b).hom z) m))) = _
  rw [ModuleCat.inv_hom_apply]
  change tmul R ((reverseHomologyIso P b).hom.hom
    (((reverseChain P).homologyπ b).hom z)) m = _
  rw [reverseHomologyIso_apply_class]

set_option maxHeartbeats 1500000 in
/-- The flat comparison is natural across the original carrier sizes.
The equations on cycles fix it even for arbitrary comparison witnesses. -/
theorem originalRowTensorHomologyIso_natural (a b : ℤ)
    (e : TorBalance.HomologyComparison
      (tensorFunctor (Q.X (-a)) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} ℤ))
    (e' : TorBalance.HomologyComparison
      (tensorFunctor (Q'.X (-a)) : ModuleCat.{v'} Rᵐᵒᵖ ⥤ ModuleCat.{max v' w'} ℤ)) :
    (rowTensorHomologyIso P' Q' a b e').hom.hom.comp
       (categoricalHomologyMap (originalTensorRowMap f g a) b) =
      ((originalRowTensorComplexMap f g b).app a).comp (rowTensorHomologyIso P Q a b e).hom.hom := by
  let S := (reverseChain P).sc b
  let S' := (reverseChain P').sc b
  let A := (tensorCochain P Q).flip.X a
  let B := (tensorCochain P' Q').flip.X a
  let E := e.equivalence S
  let L := (rowTensorHomologyIso P' Q' a b e').hom.hom.comp
    (categoricalHomologyMap (originalTensorRowMap f g a) b)
  let U := ((originalRowTensorComplexMap f g b).app a).comp (rowTensorHomologyIso P Q a b e).hom.hom
  suffices h : L.comp E.hom.hom = U.comp E.hom.hom by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h (E.inv x)
    change L (E.hom (E.inv x)) = U (E.hom (E.inv x)) at hx
    rw [ModuleCat.hom_inv_apply] at hx
    exact hx
  apply tensor_hom_ext
  intro x m
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((reverseChain P).homologyπ b)).mp inferInstance x
  change ((reverseChain P).homologyπ b).hom z = x at hz
  subst x
  let z₁ : A.cycles b := (e.cyclesEquivalence S).hom.hom (tmul R z m)
  let z₀ : P.cycles (-b) := (reverseCyclesIso P b).hom.hom z
  obtain ⟨y₀, hy₀, hyπ⟩ := categoricalHomologyMap_formula f (-b) z₀
  let y : (reverseChain P').cycles b := (reverseCyclesIso P' b).inv.hom y₀
  let y₁ : B.cycles b := (e'.cyclesEquivalence S').hom.hom (tmul R y (g.app (-a) m))
  have hy : (reverseCyclesIso P' b).hom.hom y = y₀ :=
    ModuleCat.hom_inv_apply (reverseCyclesIso P' b) y₀
  obtain ⟨yz, hyz, hyzπ⟩ := categoricalHomologyMap_formula (originalTensorRowMap f g a) b z₁
  have hcycle : yz = y₁ := by
    apply (ModuleCat.mono_iff_injective (B.iCycles b)).mp inferInstance
    change (B.iCycles b).hom yz = (B.iCycles b).hom y₁
    change (B.iCycles b).hom yz = (originalTensorRowMap f g a).app b ((A.iCycles b).hom z₁) at hyz
    rw [hyz]
    have h₁ : (A.iCycles b).hom z₁ = tmul R (((reverseChain P).iCycles b).hom z) m :=
      rowFlatCycleInclusion P Q a b e z m
    have h₂ : (B.iCycles b).hom y₁ = tmul R (((reverseChain P').iCycles b).hom y) (g.app (-a) m) :=
      rowFlatCycleInclusion P' Q' a b e' y (g.app (-a) m)
    rw [h₁, h₂, ← reverseCyclesIso_hom_apply P b z, ← reverseCyclesIso_hom_apply P' b y, hy, hy₀]
    rfl
  have hπ : E.hom.hom (tmul R (((reverseChain P).homologyπ b).hom z) m) = (A.homologyπ b).hom z₁ :=
    rowFlatHomologyProjection P Q a b e z m
  change L (E.hom.hom (tmul R (((reverseChain P).homologyπ b).hom z) m)) =
    U (E.hom.hom (tmul R (((reverseChain P).homologyπ b).hom z) m))
  rw [hπ]
  change (rowTensorHomologyIso P' Q' a b e').hom.hom
      (categoricalHomologyMap (originalTensorRowMap f g a) b ((A.homologyπ b).hom z₁)) =
    (originalRowTensorComplexMap f g b).app a
      ((rowTensorHomologyIso P Q a b e).hom.hom ((A.homologyπ b).hom z₁))
  change categoricalHomologyMap (originalTensorRowMap f g a) b ((A.homologyπ b).hom z₁) =
    (B.homologyπ b).hom yz at hyzπ
  rw [hyzπ, hcycle]
  have h₁ : (rowTensorHomologyIso P Q a b e).hom.hom ((A.homologyπ b).hom z₁) =
      tmul R ((P.homologyπ (-b)).hom z₀) m := rowTensorHomologyIso_apply_class P Q a b e z m
  have h₂ : (rowTensorHomologyIso P' Q' a b e').hom.hom ((B.homologyπ b).hom y₁) =
      tmul R ((P'.homologyπ (-b)).hom ((reverseCyclesIso P' b).hom.hom y)) (g.app (-a) m) :=
    rowTensorHomologyIso_apply_class P' Q' a b e' y (g.app (-a) m)
  rw [h₁, h₂, hy]
  change tmul R ((P'.homologyπ (-b)).hom y₀) (g.app (-a) m) =
    tmul R (categoricalHomologyMap f (-b) ((P.homologyπ (-b)).hom z₀)) (g.app (-a) m)
  rw [hyπ]

end OriginalRowTensorComparison
end AdvancedHomologicalAlgebra.KunnethSpectralSequence


section OriginalRowMiddle

universe v' w' a b

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open DoubleTotalization DoubleComplexFirstPages FiniteDiagonalFiltrations
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section
variable {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
  {L : CochainComplex (ModuleCat.{b} ℤ) ℤ}
  {F : Filtration K} {G : Filtration L}
  (M : OriginalFilteredMap F G)
  (D : F03Specs.PageData F) (E : F03Specs.PageData G)

/-- Index transport commutes with the original page map. -/
theorem originalPageMap_transport (r p p' n n' : ℤ) (hp : p=p') (hn : n=n') :
    (eqToHom (congrArg₂ (PageCohomology.object G E r) hp hn)).hom.comp (M.pageMap D E r p n) =
      (M.pageMap D E r p' n').comp
        (eqToHom (congrArg₂ (PageCohomology.object F D r) hp hn)).hom := by
  subst p' n'
  simp

end

section
variable {R : Type u} [Ring R]
  {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
  {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
  (f : LinearChainMap P P') (g : LinearChainMap Q Q')
  {S : TensorPages P Q} {U : TensorPages P' Q'}
  (F : OriginalFilteredMap S.filtration U.filtration)
  (hF : F.hom = originalTensorTotalMap f g)
  (C : RowTensorComparison P Q S) (D : RowTensorComparison P' Q' U)

include hF in
set_option maxHeartbeats 1300000 in
/-- The middle map of the signed comparison commutes with original tensor maps. -/
theorem originalRowShortIso_middle_natural (a b : ℤ)
    (τ : (rowTensorComplex P Q b).X a →ₗ[ℤ] (rowTensorComplex P' Q' b).X a)
    (hτ : (rowTensorHomologyIso P' Q' a b (D.flatComparison a)).hom.hom.comp
        (categoricalHomologyMap (originalTensorRowMap f g a) b) =
      τ.comp (rowTensorHomologyIso P Q a b (C.flatComparison a)).hom.hom) :
    ((D.shortIso a b).hom.τ₂).hom.comp (F.pageMap S.pages U.pages 1 (a-1+1) (a+b-1+1)) =
      τ.comp ((C.shortIso a b).hom.τ₂).hom := by
  let I := eqToHom (congrArg₂ (PageCohomology.object S.filtration S.pages 1)
    (show a-1+1 = a by omega) (show a+b-1+1 = a+b by omega))
  let J := eqToHom (congrArg₂ (PageCohomology.object U.filtration U.pages 1)
    (show a-1+1 = a by omega) (show a+b-1+1 = a+b by omega))
  have h₁ := originalPageMap_transport F S.pages U.pages 1 (a-1+1) a (a+b-1+1) (a+b)
    (by omega) (by omega)
  change J.hom.comp (F.pageMap S.pages U.pages 1 (a-1+1) (a+b-1+1)) =
    (F.pageMap S.pages U.pages 1 a (a+b)).comp I.hom at h₁
  have h₂ := originalRowFirstIso_natural f g F hF C.row D.row a b
  rw [C.middle_formula, D.middle_formula]
  apply LinearMap.ext
  intro z
  let ε : ℤ := ((a*b).negOnePow : ℤ)
  change ε • (rowTensorHomologyIso P' Q' a b (D.flatComparison a)).hom.hom
      ((D.row.firstIso a b).hom.hom (J.hom (F.pageMap S.pages U.pages 1 (a-1+1) (a+b-1+1) z))) =
    τ (ε • (rowTensorHomologyIso P Q a b (C.flatComparison a)).hom.hom
      ((C.row.firstIso a b).hom.hom (I.hom z)))
  rw [map_smul]
  apply congrArg (ε • ·)
  have h₁z := LinearMap.congr_fun h₁ z
  have h₂z := LinearMap.congr_fun h₂ (I.hom z)
  simp only [LinearMap.comp_apply] at h₁z h₂z
  rw [h₁z, h₂z]
  exact LinearMap.congr_fun hτ ((C.row.firstIso a b).hom.hom (I.hom z))

end

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end OriginalRowMiddle

section OriginalHomologyTransport
universe a b
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)

section
variable {R : Type u} [Ring R]
  {A A' : ShortComplex (ModuleCat.{a} R)} {B B' : ShortComplex (ModuleCat.{b} R)}

/-- A map on homology is determined by its action on cycles of the middle term. -/
def ActsOnHomologyClasses
    {S : ShortComplex (ModuleCat.{a} R)} {T : ShortComplex (ModuleCat.{b} R)}
    (f : S.X₂ →ₗ[R] T.X₂) (h : S.homology →ₗ[R] T.homology) : Prop :=
  ∀ z : S.cycles, ∃ y : T.cycles,
    T.iCycles.hom y = f (S.iCycles.hom z) ∧ h (S.homologyπ.hom z) = T.homologyπ.hom y

theorem ActsOnHomologyClasses.square
    {f : A.X₂ →ₗ[R] B.X₂} {g : A'.X₂ →ₗ[R] B'.X₂}
    {i : A.X₂ →ₗ[R] A'.X₂} {j : B.X₂ →ₗ[R] B'.X₂}
    {F : A.homology →ₗ[R] B.homology} {G : A'.homology →ₗ[R] B'.homology}
    {I : A.homology →ₗ[R] A'.homology} {J : B.homology →ₗ[R] B'.homology}
    (hf : ActsOnHomologyClasses f F) (hg : ActsOnHomologyClasses g G)
    (hi : ActsOnHomologyClasses i I) (hj : ActsOnHomologyClasses j J)
    (w : j.comp f = g.comp i) : J.comp F = G.comp I := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective A.homologyπ).mp inferInstance z
  obtain ⟨x,hx,hX⟩ := hf z
  obtain ⟨y,hy,hY⟩ := hi z
  obtain ⟨x',hx',hX'⟩ := hj x
  obtain ⟨y',hy',hY'⟩ := hg y
  have he : x' = y' := by
    apply (ModuleCat.mono_iff_injective B'.iCycles).mp inferInstance
    change B'.iCycles.hom x' = B'.iCycles.hom y'
    rw [hx', hy', hx, hy]
    exact LinearMap.congr_fun w (A.iCycles.hom z)
  change J (F (A.homologyπ.hom z)) = G (I (A.homologyπ.hom z))
  rw [hX, hY, hX', hY', he]

theorem ActsOnHomologyClasses.ofShortComplexHom (f : A ⟶ A') :
    ActsOnHomologyClasses f.τ₂.hom (ShortComplex.homologyMap f).hom := by
  intro z
  exact ⟨(ShortComplex.cyclesMap f).hom z,
    ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) z,
    ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f) z⟩

theorem ActsOnHomologyClasses.ofCyclesMap
    {i : A.X₂ →ₗ[R] A'.X₂} {I : A.homology →ₗ[R] A'.homology}
    (c : A.cycles ⟶ A'.cycles)
    (h₁ : A'.iCycles.hom.comp c.hom = i.comp A.iCycles.hom)
    (h₂ : I.comp A.homologyπ.hom = A'.homologyπ.hom.comp c.hom) :
    ActsOnHomologyClasses i I :=
  fun z => ⟨c.hom z, LinearMap.congr_fun h₁ z, LinearMap.congr_fun h₂ z⟩

end

section
variable {R : Type u} [Ring R]

theorem reverseHomologyIso_acts
    (K : ChainComplex (ModuleCat.{a} R) ℤ) (n : ℤ) :
    ActsOnHomologyClasses
      (S := (reverseChain K).sc n) (T := K.sc (-n))
      (K.restrictionXIso reversal (i := n) rfl).hom.hom
      (reverseHomologyIso K n).hom.hom := by
  let hk : (ComplexShape.up ℤ).next n = n+1 := by simp
  let hk' : reversal.f (n+1) = -n-1 := by change -(n+1) = _; omega
  let hk'' : (ComplexShape.down ℤ).next (-n) = -n-1 :=
    (ComplexShape.down ℤ).next_eq' (by change -n-1+1 = -n; omega)
  apply ActsOnHomologyClasses.ofCyclesMap
    (K.restrictionCyclesIso reversal n (n+1) hk rfl hk' hk'').hom
  · exact congrArg ModuleCat.Hom.hom (K.restrictionCyclesIso_hom_iCycles reversal n (n+1) hk rfl hk' hk'')
  · unfold reverseHomologyIso
    exact congrArg ModuleCat.Hom.hom (K.homologyπ_restrictionHomologyIso_hom _ _ _ _ _ _ _ _ _ _ _)

def originalReverseMap
    {K : ChainComplex (ModuleCat.{a} R) ℤ} {L : ChainComplex (ModuleCat.{b} R) ℤ}
    (f : LinearChainMap K L) : LinearChainMap (reverseChain K) (reverseChain L) where
  app i := f.app (-i)
  comm i j := f.comm (-i) (-j)

theorem originalReverseHomology_natural
    {K : ChainComplex (ModuleCat.{a} R) ℤ} {L : ChainComplex (ModuleCat.{b} R) ℤ}
    (f : LinearChainMap K L) (n : ℤ) :
    (reverseHomologyIso L n).hom.hom.comp (categoricalHomologyMap (originalReverseMap f) n) =
      (categoricalHomologyMap f (-n)).comp (reverseHomologyIso K n).hom.hom := by
  exact ActsOnHomologyClasses.square
    (categoricalHomologyMap_formula (originalReverseMap f) n)
    (categoricalHomologyMap_formula f (-n))
    (reverseHomologyIso_acts K n) (reverseHomologyIso_acts L n) rfl

open P103.Specs.Ch10.Complexes

theorem extendHomologyIso_acts (K : ChainComplex (ModuleCat.{a} R) ℕ) (n : ℕ) :
    ActsOnHomologyClasses (S := (extendNonnegativeChain K).sc (n : ℤ)) (T := K.sc n)
      (K.extendXIso nonnegativeChainEmbedding (i := n) rfl).hom.hom
      (K.extendHomologyIso nonnegativeChainEmbedding (j := n) rfl).hom.hom := by
  apply ActsOnHomologyClasses.ofCyclesMap
  · exact congrArg ModuleCat.Hom.hom (K.extendCyclesIso_hom_iCycles nonnegativeChainEmbedding (j := n) rfl)
  · exact congrArg ModuleCat.Hom.hom (K.homologyπ_extendHomologyIso_hom nonnegativeChainEmbedding (j := n) rfl)

theorem originalExtendHomology_natural
    {K : ChainComplex (ModuleCat.{a} R) ℕ} {L : ChainComplex (ModuleCat.{b} R) ℕ}
    (f : LinearChainMap K L) (n : ℕ) :
    (L.extendHomologyIso nonnegativeChainEmbedding (j := n) rfl).hom.hom.comp
        (categoricalHomologyMap f.extendNonnegative (n : ℤ)) =
      (categoricalHomologyMap f n).comp
        (K.extendHomologyIso nonnegativeChainEmbedding (j := n) rfl).hom.hom := by
  refine ActsOnHomologyClasses.square
    (categoricalHomologyMap_formula f.extendNonnegative (n : ℤ))
    (categoricalHomologyMap_formula f n) (extendHomologyIso_acts K n) (extendHomologyIso_acts L n) ?_
  apply LinearMap.ext
  intro z
  let e := K.extendXIso nonnegativeChainEmbedding (i := n) rfl
  let e' := L.extendXIso nonnegativeChainEmbedding (i := n) rfl
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance z
  change e'.hom.hom (f.extendNonnegative.app (n : ℤ) (e.inv.hom z)) = f.app n (e.hom.hom (e.inv.hom z))
  rw [f.extendNonnegative_app_inv]
  change e'.hom.hom (e'.inv.hom (f.app n z)) = f.app n (e.hom.hom (e.inv.hom z))
  simp only [ModuleCat.hom_inv_apply]

end

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end OriginalHomologyTransport

section OriginalOrdinaryTensor
universe a b v' w'
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open AdvancedHomologicalAlgebra.TorBalance
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

theorem categoricalQuotientSquare
    {S : Type u} [Ring S] {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{a} S) c}
    {L : HomologicalComplex (ModuleCat.{b} S) c} (f : LinearChainMap K L) (n : ι)
    (e : K.homology n ≅ ModuleCat.of S (Homology K n))
    (e' : L.homology n ≅ ModuleCat.of S (Homology L n))
    (he : ∀ z : K.cycles n, e.hom ((K.homologyπ n) z) =
      homologyClass K n ((K.sc n).moduleCatCyclesIso.hom z))
    (he' : ∀ z : L.cycles n, e'.hom ((L.homologyπ n) z) =
      homologyClass L n ((L.sc n).moduleCatCyclesIso.hom z)) :
    e'.hom.hom.comp (categoricalHomologyMap f n) = (f.homologyMap n).comp e.hom.hom := by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance z
  obtain ⟨y,hi,hπ⟩ := categoricalHomologyMap_formula f n z
  change e'.hom.hom (categoricalHomologyMap f n ((K.homologyπ n).hom z)) =
    f.homologyMap n (e.hom.hom ((K.homologyπ n).hom z))
  rw [hπ]
  change e'.hom ((L.homologyπ n) y) = f.homologyMap n (e.hom ((K.homologyπ n) z))
  rw [he, he']
  change homologyClass L n ((L.sc n).moduleCatCyclesIso.hom y) =
    homologyClass L n (f.cyclesMap n ((K.sc n).moduleCatCyclesIso.hom z))
  congr 1
  apply Subtype.ext
  have hK := ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_hom_i z
  have hL := ConcreteCategory.congr_hom (L.sc n).moduleCatCyclesIso_hom_i y
  change ((K.sc n).moduleCatCyclesIso.hom z).val = (K.iCycles n).hom z at hK
  change ((L.sc n).moduleCatCyclesIso.hom y).val = (L.iCycles n).hom y at hL
  change ((L.sc n).moduleCatCyclesIso.hom y).val =
    f.app n ((K.sc n).moduleCatCyclesIso.hom z).val
  rw [hK,hL,hi]

section
variable {R : Type u} [Ring R]
  {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
  {Q : ChainComplex (ModuleCat.{w} R) ℕ} {Q' : ChainComplex (ModuleCat.{w'} R) ℕ}
  (h : A →ₗ[Rᵐᵒᵖ] B) (l : LinearChainMap Q Q')

/-- The original left-tensor chain map in the extended integer grading. -/
def originalExtendedTensorMap :
    LinearChainMap (leftTensorComplex A (extendNonnegativeChain Q))
      (leftTensorComplex B (extendNonnegativeChain Q')) where
  app n := tensorMap h (l.extendNonnegative.app n)
  comm i j := by
    apply tensor_hom_ext
    intro a z
    change P103.BalancedTensor.tmul R (h a)
      (((extendNonnegativeChain Q').d i j).hom (l.extendNonnegative.app i z)) =
      P103.BalancedTensor.tmul R (h a)
        (l.extendNonnegative.app j (((extendNonnegativeChain Q).d i j).hom z))
    rw [l.extendNonnegative.comm_apply]

variable {Q₀ : ChainComplex (ModuleCat.{w} R) ℕ}
  {Q₀' : ChainComplex (ModuleCat.{w'} R) ℕ}

theorem originalTensorExtension_naturality
    (l : LinearChainMap Q₀ Q₀') (C : OrdinaryTensorComparison A Q₀)
    (D : OrdinaryTensorComparison B Q₀') (n : ℕ) :
    (D.extension.hom.f (n : ℤ)).hom.comp ((originalExtendedTensorMap h l).app (n : ℤ)) =
      ((leftTensorLinearChainMap h l).extendNonnegative.app (n : ℤ)).comp
        (C.extension.hom.f (n : ℤ)).hom := by
  let e := Q₀.extendXIso nonnegativeChainEmbedding (i := n) rfl
  let e' := Q₀'.extendXIso nonnegativeChainEmbedding (i := n) rfl
  let T := leftOrdinaryTensorComplex A Q₀
  let T' := leftOrdinaryTensorComplex B Q₀'
  let b := T.extendXIso nonnegativeChainEmbedding (i := n) rfl
  let b' := T'.extendXIso nonnegativeChainEmbedding (i := n) rfl
  suffices h' : b'.hom.hom.comp ((D.extension.hom.f (n : ℤ)).hom.comp
      ((originalExtendedTensorMap h l).app (n : ℤ))) =
      b'.hom.hom.comp (((leftTensorLinearChainMap h l).extendNonnegative.app (n : ℤ)).comp
        (C.extension.hom.f (n : ℤ)).hom) by
    apply LinearMap.ext
    intro z
    apply (ModuleCat.mono_iff_injective b'.hom).mp inferInstance
    exact LinearMap.congr_fun h' z
  change (_ : P103.BalancedTensor.Tensor R A ((extendNonnegativeChain Q₀).X (n : ℤ)) →ₗ[ℤ]
    P103.BalancedTensor.Tensor R B (Q₀'.X n)) = _
  apply tensor_hom_ext
  intro a z
  apply congrArg b'.hom.hom
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance z
  have eqA (x : A) (z : Q₀.X n) :
      (C.extension.hom.f (n : ℤ)).hom (P103.BalancedTensor.tmul R x (e.inv.hom z)) =
        b.inv.hom (P103.BalancedTensor.tmul R x z) := by
    apply (ModuleCat.mono_iff_injective b.hom).mp inferInstance
    have hC := ConcreteCategory.congr_hom (C.extension_formula n) (P103.BalancedTensor.tmul R x (e.inv.hom z))
    change b.hom.hom ((C.extension.hom.f (n : ℤ)).hom _) =
      P103.BalancedTensor.tmul R x (e.hom.hom (e.inv.hom z)) at hC
    rw [hC, ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply]
  have eqB (x : B) (z : Q₀'.X n) :
      (D.extension.hom.f (n : ℤ)).hom (P103.BalancedTensor.tmul R x (e'.inv.hom z)) =
        b'.inv.hom (P103.BalancedTensor.tmul R x z) := by
    apply (ModuleCat.mono_iff_injective b'.hom).mp inferInstance
    have hD := ConcreteCategory.congr_hom (D.extension_formula n) (P103.BalancedTensor.tmul R x (e'.inv.hom z))
    change b'.hom.hom ((D.extension.hom.f (n : ℤ)).hom _) =
      P103.BalancedTensor.tmul R x (e'.hom.hom (e'.inv.hom z)) at hD
    rw [hD, ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply]
  change (D.extension.hom.f (n : ℤ)).hom
      (P103.BalancedTensor.tmul R (h a) (l.extendNonnegative.app (n : ℤ) (e.inv.hom z))) =
    ((leftTensorLinearChainMap h l).extendNonnegative.app (n : ℤ))
      ((C.extension.hom.f (n : ℤ)).hom (P103.BalancedTensor.tmul R a (e.inv.hom z)))
  rw [l.extendNonnegative_app_inv, eqA, eqB, LinearChainMap.extendNonnegative_app_inv]
  rfl

end

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open AdvancedHomologicalAlgebra.TorBalance
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section
variable {R : Type u} [Ring R]
  {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
  {Q : ChainComplex (ModuleCat.{w} R) ℕ} {Q' : ChainComplex (ModuleCat.{w'} R) ℕ}
  (h : A →ₗ[Rᵐᵒᵖ] B) (l : LinearChainMap Q Q')
  (C : OrdinaryTensorComparison A Q) (D : OrdinaryTensorComparison B Q')

set_option maxHeartbeats 1250000 in
private theorem extensionHomologySquare (p : ℕ) :
    ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).map D.extension.hom).hom.comp
        (categoricalHomologyMap (originalExtendedTensorMap h l) (p : ℤ)) =
      (categoricalHomologyMap (leftTensorLinearChainMap h l).extendNonnegative (p : ℤ)).comp
        ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).map C.extension.hom).hom := by
  exact ActsOnHomologyClasses.square
    (categoricalHomologyMap_formula (originalExtendedTensorMap h l) (p : ℤ))
    (categoricalHomologyMap_formula (leftTensorLinearChainMap h l).extendNonnegative (p : ℤ))
    (ActsOnHomologyClasses.ofShortComplexHom (HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℤ) (p : ℤ) |>.map C.extension.hom))
    (ActsOnHomologyClasses.ofShortComplexHom (HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℤ) (p : ℤ) |>.map D.extension.hom))
    (originalTensorExtension_naturality h l C D p)

def ordinaryTailComparison (C : OrdinaryTensorComparison A Q) (p : ℕ) :
    (leftTensorComplex A (extendNonnegativeChain Q)).homology (p : ℤ) ≅
      ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex A Q) p) :=
  (HomologicalComplex.homologyFunctor _ _ (p : ℤ)).mapIso C.extension ≪≫
    (leftOrdinaryTensorComplex A Q).extendHomologyIso nonnegativeChainEmbedding (j := p) rfl ≪≫
    C.quotient p

set_option maxHeartbeats 1250000 in
theorem ordinaryTailComparison_natural (p : ℕ) :
    (ordinaryTailComparison D p).hom.hom.comp (categoricalHomologyMap (originalExtendedTensorMap h l) (p : ℤ)) =
      ((leftTensorLinearChainMap h l).homologyMap p).comp (ordinaryTailComparison C p).hom.hom := by
  have hExt := extensionHomologySquare h l C D p
  have hH := originalExtendHomology_natural (leftTensorLinearChainMap h l) p
  have hQ := categoricalQuotientSquare (leftTensorLinearChainMap h l) p (C.quotient p)
    (D.quotient p) (C.quotient_formula p) (D.quotient_formula p)
  apply LinearMap.ext
  intro z
  let e := ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).map C.extension.hom).hom
  let e' := ((HomologicalComplex.homologyFunctor _ _ (p : ℤ)).map D.extension.hom).hom
  let k := ((leftOrdinaryTensorComplex A Q).extendHomologyIso nonnegativeChainEmbedding (j := p) rfl).hom.hom
  let k' := ((leftOrdinaryTensorComplex B Q').extendHomologyIso nonnegativeChainEmbedding (j := p) rfl).hom.hom
  let H := categoricalHomologyMap (originalExtendedTensorMap h l) (p : ℤ)
  let N := categoricalHomologyMap (leftTensorLinearChainMap h l).extendNonnegative (p : ℤ)
  let M := categoricalHomologyMap (leftTensorLinearChainMap h l) p
  let q := (C.quotient p).hom.hom
  let q' := (D.quotient p).hom.hom
  change q' (k' (e' (H z))) = (leftTensorLinearChainMap h l).homologyMap p (q (k (e z)))
  calc
    _ = q' (k' (N (e z))) := congrArg (fun x => q' (k' x)) (LinearMap.congr_fun hExt z)
    _ = q' (M (k (e z))) := congrArg q' (LinearMap.congr_fun hH (e z))
    _ = _ := LinearMap.congr_fun hQ (k (e z))
end
end AdvancedHomologicalAlgebra.KunnethSpectralSequence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open AdvancedHomologicalAlgebra.TorBalance
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section
variable {R : Type u} [Ring R]
  {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
  {Q : ChainComplex (ModuleCat.{w} R) ℕ} {Q' : ChainComplex (ModuleCat.{w'} R) ℕ}

def rowOrdinaryComparison {q : ℤ} (C : OrdinaryTensorComparison (P.homology q) Q)
    (p : ℕ) (b : ℤ) (eqb : -b = q) :
    (rowTensorComplex P (extendNonnegativeChain Q) b).homology (-(p : ℤ)) ≅
      ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex (P.homology q) Q) p) :=
  let a : ℤ := -(p : ℤ)
  let e : leftTensorComplex (P.homology (-b)) (extendNonnegativeChain Q) ≅
      extendNonnegativeChain (leftOrdinaryTensorComplex (P.homology q) Q) :=
    eqToIso (by rw [eqb]) ≪≫ C.extension
  reverseHomologyIso _ a ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-a)).mapIso e ≪≫
    (leftOrdinaryTensorComplex (P.homology q) Q).extendHomologyIso
      nonnegativeChainEmbedding (j := p) (neg_neg (p : ℤ)).symm ≪≫ C.quotient p

private def ordinaryTailAt {A : ModuleCat.{v} Rᵐᵒᵖ}
    (C : OrdinaryTensorComparison A Q) (p : ℕ) (i : ℤ) (hi : (p : ℤ) = i) :
    (leftTensorComplex A (extendNonnegativeChain Q)).homology i ≅
      ModuleCat.of ℤ (Homology (leftOrdinaryTensorComplex A Q) p) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso C.extension ≪≫
    (leftOrdinaryTensorComplex A Q).extendHomologyIso nonnegativeChainEmbedding (j := p) hi ≪≫ C.quotient p

set_option maxHeartbeats 1000000 in
private theorem ordinaryTailAt_natural {A : ModuleCat.{v} Rᵐᵒᵖ} {B : ModuleCat.{v'} Rᵐᵒᵖ}
    (C : OrdinaryTensorComparison A Q) (D : OrdinaryTensorComparison B Q')
    (h : A →ₗ[Rᵐᵒᵖ] B) (l : LinearChainMap Q Q') (p : ℕ) (i : ℤ) (hi : (p : ℤ) = i) :
    (ordinaryTailAt D p i hi).hom.hom.comp (categoricalHomologyMap (originalExtendedTensorMap h l) i) =
      ((leftTensorLinearChainMap h l).homologyMap p).comp (ordinaryTailAt C p i hi).hom.hom := by
  subst i
  exact ordinaryTailComparison_natural h l C D p

set_option maxHeartbeats 1000000 in
theorem originalRowOrdinary_natural {q : ℤ}
    (C : OrdinaryTensorComparison (P.homology q) Q) (D : OrdinaryTensorComparison (P'.homology q) Q')
    (f : LinearChainMap P P') (l : LinearChainMap Q Q') (p : ℕ) (b : ℤ) (eqb : -b = q) :
    (rowOrdinaryComparison D p b eqb).hom.hom.comp
      (categoricalHomologyMap
        (originalReverseMap (originalExtendedTensorMap (categoricalHomologyMap f (-b)) l)) (-(p : ℤ))) =
      ((leftTensorLinearChainMap (categoricalHomologyMap f q) l).homologyMap p).comp
        (rowOrdinaryComparison C p b eqb).hom.hom := by
  subst q
  let k := originalExtendedTensorMap (categoricalHomologyMap f (-b)) l
  have eC : rowOrdinaryComparison C p b rfl =
      reverseHomologyIso _ (-(p : ℤ)) ≪≫ ordinaryTailAt C p (-(-(p : ℤ))) (neg_neg (p : ℤ)).symm := by
    unfold rowOrdinaryComparison ordinaryTailAt
    rw [show eqToIso (by rw [show -b = -b from rfl]) = Iso.refl
        (leftTensorComplex (P.homology (-b)) (extendNonnegativeChain Q)) from rfl]
    rw [Iso.refl_trans]
  have eD : rowOrdinaryComparison D p b rfl =
      reverseHomologyIso _ (-(p : ℤ)) ≪≫ ordinaryTailAt D p (-(-(p : ℤ))) (neg_neg (p : ℤ)).symm := by
    unfold rowOrdinaryComparison ordinaryTailAt
    rw [show eqToIso (by rw [show -b = -b from rfl]) = Iso.refl
        (leftTensorComplex (P'.homology (-b)) (extendNonnegativeChain Q')) from rfl]
    rw [Iso.refl_trans]
  rw [eC, eD]
  have hr := originalReverseHomology_natural k (-(p : ℤ))
  have ho := ordinaryTailAt_natural C D (categoricalHomologyMap f (-b)) l p (-(-(p : ℤ))) (neg_neg (p : ℤ)).symm
  apply LinearMap.ext
  intro z
  let r := (reverseHomologyIso (leftTensorComplex (P.homology (-b)) (extendNonnegativeChain Q)) (-(p : ℤ))).hom.hom
  let t := (ordinaryTailAt D p (-(-(p : ℤ))) (neg_neg (p : ℤ)).symm).hom.hom
  calc
    _ = t (categoricalHomologyMap k (-(-(p : ℤ))) (r z)) :=
      congrArg t (LinearMap.congr_fun hr z)
    _ = _ := LinearMap.congr_fun ho (r z)

end
end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end OriginalOrdinaryTensor

section OriginalTargets
universe a b v' w'

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)

section
variable {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
  {L : CochainComplex (ModuleCat.{b} ℤ) ℤ} {F : Filtration K} {G : Filtration L}
  (f : LinearChainMap K L)
  (hf : ∀ p n (z : (F.piece p n : ModuleCat.{a} ℤ)),
    ∃ y : (G.piece p n : ModuleCat.{b} ℤ), (G.piece p n).arrow.hom y = f.app n ((F.piece p n).arrow.hom z))

include hf in
theorem originalClosed_exists (p n : ℤ) (z : (closed F p n : ModuleCat.{a} ℤ)) :
    ∃ y : (closed G p n : ModuleCat.{b} ℤ),
      (closed G p n).arrow.hom y = f.app n ((closed F p n).arrow.hom z) := by
  let i := Subobject.ofLE (closed F p n) (F.piece p n) inf_le_left
  have hz := ConcreteCategory.congr_hom (Subobject.ofLE_arrow (X := closed F p n)
    (Y := F.piece p n) inf_le_left) z
  have hpiece : f.app n ((closed F p n).arrow.hom z) ∈
      ModuleCat.subobjectModule (L.X n) (G.piece p n) := by
    obtain ⟨x, hx⟩ := hf p n (i.hom z)
    exact ⟨x, hx.trans (congrArg (f.app n) hz)⟩
  have hker : f.app n ((closed F p n).arrow.hom z) ∈
      ModuleCat.subobjectModule (L.X n) (kernelSubobject (L.d n (n+1))) := by
    have hk := ConcreteCategory.congr_hom (closed_d F p n) z
    refine ⟨ModuleCat.toKernelSubobject ⟨_, ?_⟩, ModuleCat.toKernelSubobject_arrow _⟩
    change (L.d n (n+1)).hom (f.app n ((closed F p n).arrow.hom z)) = 0
    rw [f.comm_apply]
    change (K.d n (n+1)).hom ((closed F p n).arrow.hom z) = 0 at hk
    rw [hk, map_zero]
  have hy : f.app n ((closed F p n).arrow.hom z) ∈
      ModuleCat.subobjectModule (L.X n) (closed G p n) := by
    change f.app n ((closed F p n).arrow.hom z) ∈
      ModuleCat.subobjectModule (L.X n) (G.piece p n ⊓ kernelSubobject (L.d n (n+1)))
    rw [(ModuleCat.subobjectModule (L.X n)).map_inf]
    exact ⟨hpiece, hker⟩
  exact hy

variable {A : ModuleCat.{a} ℤ} {B : ModuleCat.{b} ℤ} {n : ℤ}
  (e : K.homology (-n) ≅ A) (e' : L.homology (-n) ≅ B)

def transportedClosedClass (p : ℤ) :
    (closed F (-p) (-n) : ModuleCat.{a} ℤ) ⟶ (transportedPiece F n A e p : ModuleCat.{a} ℤ) :=
  closedClass F (-p) (-n) ≫ (transportedSubobjectIso e _).hom

instance (p : ℤ) : Epi (transportedClosedClass (F := F) e p) := by
  unfold transportedClosedClass
  exact @epi_comp _ _ _ _ _ _ (closedClass_epi F (-p) (-n)) _
    (CategoryTheory.IsIso.epi_of_iso (transportedSubobjectIso e (cohomologyPiece F (-p) (-n))).hom)

theorem transportedClosedClass_arrow (p : ℤ) :
    transportedClosedClass (F := F) e p ≫ (transportedPiece F n A e p).arrow =
      K.liftCycles (closed F (-p) (-n)).arrow (-n+1) (by simp)
        (closed_d F (-p) (-n)) ≫ K.homologyπ (-n) ≫ e.hom := by
  simp only [transportedClosedClass, transportedPiece, Category.assoc,
    transportedSubobjectIso_arrow, ← closedClass_arrow_assoc]

variable {h : ∀ n, K.homology n →ₗ[ℤ] L.homology n} (hh : InducesCategoricalHomology f h)
  (g : A →ₗ[ℤ] B) (hg : e'.hom.hom.comp (h (-n)) = g.comp e.hom.hom)

include hh hg in
theorem originalClosedClass_comm (p : ℤ) (z : (closed F (-p) (-n) : ModuleCat.{a} ℤ))
    (y : (closed G (-p) (-n) : ModuleCat.{b} ℤ))
    (hy : (closed G (-p) (-n)).arrow.hom y = f.app (-n) ((closed F (-p) (-n)).arrow.hom z)) :
    (transportedPiece G n B e' p).arrow.hom (transportedClosedClass (F := G) e' p y) =
      g ((transportedPiece F n A e p).arrow.hom (transportedClosedClass (F := F) e p z)) := by
  let zc : K.cycles (-n) := K.liftCycles (closed F (-p) (-n)).arrow (-n+1)
    (by simp) (closed_d F (-p) (-n)) z
  let yc : L.cycles (-n) := L.liftCycles (closed G (-p) (-n)).arrow (-n+1)
    (by simp) (closed_d G (-p) (-n)) y
  obtain ⟨yc', hi, hπ⟩ := hh (-n) zc
  have he : yc' = yc := by
    apply (ModuleCat.mono_iff_injective (L.iCycles (-n))).mp inferInstance
    change (L.iCycles (-n)).hom yc' = (L.iCycles (-n)).hom yc
    rw [hi]
    have hzc := ConcreteCategory.congr_hom
      (K.liftCycles_i (closed F (-p) (-n)).arrow (-n+1) (by simp) (closed_d F (-p) (-n))) z
    have hyc := ConcreteCategory.congr_hom
      (L.liftCycles_i (closed G (-p) (-n)).arrow (-n+1) (by simp) (closed_d G (-p) (-n))) y
    change (K.iCycles (-n)).hom zc = _ at hzc
    change (L.iCycles (-n)).hom yc = _ at hyc
    rw [hzc, hyc, hy]
  subst yc'
  have h1 := ConcreteCategory.congr_hom (transportedClosedClass_arrow (F := F) e p) z
  have h2 := ConcreteCategory.congr_hom (transportedClosedClass_arrow (F := G) e' p) y
  change _ = e.hom.hom ((K.homologyπ (-n)).hom zc) at h1
  change _ = e'.hom.hom ((L.homologyπ (-n)).hom yc) at h2
  change (transportedPiece F n A e p).arrow.hom (transportedClosedClass (F := F) e p z) =
    e.hom.hom ((K.homologyπ (-n)).hom zc) at h1
  change (transportedPiece G n B e' p).arrow.hom (transportedClosedClass (F := G) e' p y) =
    e'.hom.hom ((L.homologyπ (-n)).hom yc) at h2
  rw [h2, h1, ← hπ]
  exact LinearMap.congr_fun hg ((K.homologyπ (-n)).hom zc)

include hf hh hg in
theorem originalTargetPiece_exists (p : ℤ) (x : (transportedPiece F n A e p : ModuleCat.{a} ℤ)) :
    ∃ y : (transportedPiece G n B e' p : ModuleCat.{b} ℤ),
      (transportedPiece G n B e' p).arrow.hom y = g ((transportedPiece F n A e p).arrow.hom x) := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (transportedClosedClass (F := F) e p)).mp inferInstance x
  obtain ⟨y, hy⟩ := originalClosed_exists f hf (-p) (-n) z
  exact ⟨transportedClosedClass (F := G) e' p y, originalClosedClass_comm f e e' hh g hg p z y hy⟩

end

end AdvancedHomologicalAlgebra.KunnethSpectralSequence


namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)

section
variable {A X : ModuleCat.{a} ℤ} {B Y : ModuleCat.{b} ℤ}
  {i : X ⟶ A} {j : Y ⟶ B} (f : X →ₗ[ℤ] Y) (g : A →ₗ[ℤ] B)
  (h : g.comp i.hom = j.hom.comp f)

include h in
private theorem originalCokernelMap_ker :
    LinearMap.ker (cokernel.π i).hom ≤ LinearMap.ker ((cokernel.π j).hom.comp g) := by
  intro z hz
  have he := ConcreteCategory.congr_hom (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom i) z
  change (ModuleCat.cokernelIsoRangeQuotient i).hom.hom ((cokernel.π i).hom z) =
    (LinearMap.range i.hom).mkQ z at he
  have hz0 : (cokernel.π i).hom z = 0 := hz
  rw [hz0, map_zero] at he
  obtain ⟨x,rfl⟩ := (Submodule.Quotient.mk_eq_zero _).1 he.symm
  change (cokernel.π j).hom (g (i.hom x)) = 0
  have hh := LinearMap.congr_fun h x
  change g (i.hom x) = j.hom (f x) at hh
  rw [hh]
  exact ConcreteCategory.congr_hom (cokernel.condition j) (f x)

def originalCokernelMap : (cokernel i : ModuleCat.{a} ℤ) →ₗ[ℤ] (cokernel j : ModuleCat.{b} ℤ) :=
  (LinearMap.liftOfSurjective (f := (cokernel.π i).hom) ((ModuleCat.epi_iff_surjective (cokernel.π i)).mp inferInstance))
    ⟨(cokernel.π j).hom.comp g, originalCokernelMap_ker f g h⟩

theorem originalCokernelMap_π :
    (originalCokernelMap f g h).comp (cokernel.π i).hom = (cokernel.π j).hom.comp g := by
  exact LinearMap.ext fun z => LinearMap.equivOfSurjective_apply _
    (originalCokernelMap_ker f g h) (m := z)

end

section
variable {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
  {L : CochainComplex (ModuleCat.{b} ℤ) ℤ} {F : Filtration K} {G : Filtration L}
  {A : ModuleCat.{a} ℤ} {B : ModuleCat.{b} ℤ} {n : ℤ}
  (e : K.homology (-n) ≅ A) (e' : L.homology (-n) ≅ B)
  (g : A →ₗ[ℤ] B)
  (s : ∀ p, (transportedPiece F n A e p : ModuleCat.{a} ℤ) →ₗ[ℤ]
    (transportedPiece G n B e' p : ModuleCat.{b} ℤ))
  (hs : ∀ p, (transportedPiece G n B e' p).arrow.hom.comp (s p) =
    g.comp (transportedPiece F n A e p).arrow.hom)

include hs in
theorem originalTargetStep_comm (p : ℤ) :
    (s p).comp (Subobject.ofLE _ _ (transportedPiece_increasing F n A e p)).hom =
      (Subobject.ofLE _ _ (transportedPiece_increasing G n B e' p)).hom.comp (s (p-1)) := by
  ext z
  apply (ModuleCat.mono_iff_injective (transportedPiece G n B e' p).arrow).mp inferInstance
  have h1 := LinearMap.congr_fun (hs p)
    ((Subobject.ofLE _ _ (transportedPiece_increasing F n A e p)).hom z)
  have h2 := LinearMap.congr_fun (hs (p-1)) z
  change (transportedPiece G n B e' p).arrow.hom (s p _) =
    (transportedPiece G n B e' p).arrow.hom
      ((Subobject.ofLE _ _ (transportedPiece_increasing G n B e' p)).hom (s (p-1) z))
  rw [show (transportedPiece G n B e' p).arrow.hom (s p _) = _ from h1]
  change g (((Subobject.ofLE _ _ (transportedPiece_increasing F n A e p)) ≫
    (transportedPiece F n A e p).arrow).hom z) =
    ((Subobject.ofLE _ _ (transportedPiece_increasing G n B e' p)) ≫
    (transportedPiece G n B e' p).arrow).hom (s (p-1) z)
  rw [Subobject.ofLE_arrow, Subobject.ofLE_arrow]
  exact h2.symm

def originalTargetGraded (p : ℤ) :
    (transportedGraded F n A e p : ModuleCat.{a} ℤ) →ₗ[ℤ]
      (transportedGraded G n B e' p : ModuleCat.{b} ℤ) :=
  originalCokernelMap (s (p-1)) (s p) (originalTargetStep_comm e e' g s hs p)

theorem originalTargetGraded_π (p : ℤ) :
    (originalTargetGraded e e' g s hs p).comp
      (cokernel.π (Subobject.ofLE _ _ (transportedPiece_increasing F n A e p))).hom =
    (cokernel.π (Subobject.ofLE _ _ (transportedPiece_increasing G n B e' p))).hom.comp (s p) :=
  originalCokernelMap_π _ _ _

end

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
open AdvancedHomologicalAlgebra.TorBalance (LinearChainMap)

section
variable {K : CochainComplex (ModuleCat.{a} ℤ) ℤ}
  {L : CochainComplex (ModuleCat.{b} ℤ) ℤ} {F : Filtration K} {G : Filtration L}
  {A : ModuleCat.{a} ℤ} {B : ModuleCat.{b} ℤ} {n p r : ℤ}
  (e : K.homology (-n) ≅ A) (e' : L.homology (-n) ≅ B)
  (f : LinearChainMap K L)
  (hf : ∀ p n (z : (F.piece p n : ModuleCat.{a} ℤ)),
      ∃ y : (G.piece p n : ModuleCat.{b} ℤ),
        (G.piece p n).arrow.hom y = f.app n ((F.piece p n).arrow.hom z))
  {h : ∀ n, K.homology n →ₗ[ℤ] L.homology n} (hh : InducesCategoricalHomology f h)
  (g : A →ₗ[ℤ] B) (hg : e'.hom.hom.comp (h (-n)) = g.comp e.hom.hom)
  {D : F03Specs.PageData F} {E : F03Specs.PageData G}
  (I : LimitIso F D r (-p) (-n)) (J : LimitIso G E r (-p) (-n))
  (page : (PageCohomology.object F D r (-p) (-n) : ModuleCat.{a} ℤ) →ₗ[ℤ]
    (PageCohomology.object G E r (-p) (-n) : ModuleCat.{b} ℤ))
  (almost : (FilteredPage.almost F r (-p) (-n) : ModuleCat.{a} ℤ) →ₗ[ℤ]
    (FilteredPage.almost G r (-p) (-n) : ModuleCat.{b} ℤ))
  (halmost : ∀ z, (FilteredPage.almost G r (-p) (-n)).arrow.hom (almost z) =
      f.app (-n) ((FilteredPage.almost F r (-p) (-n)).arrow.hom z))
  (hpage : page.comp (FilteredPage.toPage F r (-p) (-n) (D.containment r (-p) (-n))).hom =
    (FilteredPage.toPage G r (-p) (-n) (E.containment r (-p) (-n))).hom.comp almost)
  (s : (transportedPiece F n A e p : ModuleCat.{a} ℤ) →ₗ[ℤ]
    (transportedPiece G n B e' p : ModuleCat.{b} ℤ))
  (hs : (transportedPiece G n B e' p).arrow.hom.comp s = g.comp (transportedPiece F n A e p).arrow.hom)
  (m : (transportedGraded F n A e p : ModuleCat.{a} ℤ) →ₗ[ℤ]
      (transportedGraded G n B e' p : ModuleCat.{b} ℤ))
  (hm : m.comp (cokernel.π (Subobject.ofLE _ _ (transportedPiece_increasing F n A e p))).hom =
    (cokernel.π (Subobject.ofLE _ _ (transportedPiece_increasing G n B e' p))).hom.comp s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem limitIso_transported_formula :
    closedToPage F D r (-p) (-n) ≫ I.iso.hom ≫ (transportedGradedIso F n A e p).hom =
      transportedClosedClass (F := F) e p ≫ cokernel.π (Subobject.ofLE _ _
        (transportedPiece_increasing F n A e p)) := by
  rw [← Category.assoc, I.representative_formula]
  dsimp only [gradedClass, transportedClosedClass, transportedGradedIso]
  rw [cokernel.mapIso_hom]
  simp only [Category.assoc, cokernel.map, cokernel.π_desc]

include hf hh hg halmost hpage hs hm in
theorem originalLimitIso_natural (hi : Stabilized F r (-p) (-n)) :
    ((J.iso.hom ≫ (transportedGradedIso G n B e' p).hom).hom).comp page =
      m.comp (I.iso.hom ≫ (transportedGradedIso F n A e p).hom).hom := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (closedToPage F D r (-p) (-n))).mp
    (closedToPage_epi F D r (-p) (-n) hi.1) x
  obtain ⟨y, hy⟩ := originalClosed_exists f hf (-p) (-n) z
  let i := Subobject.ofLE _ _ (closed_le_almost F r (-p) (-n))
  let j := Subobject.ofLE _ _ (closed_le_almost G r (-p) (-n))
  have hrep : almost (i.hom z) = j.hom y := by
    apply (ModuleCat.mono_iff_injective (FilteredPage.almost G r (-p) (-n)).arrow).mp inferInstance
    change (FilteredPage.almost G r (-p) (-n)).arrow.hom (almost (i.hom z)) = (j ≫ _).hom y
    rw [halmost, Subobject.ofLE_arrow]
    change f.app (-n) ((i ≫ (FilteredPage.almost F r (-p) (-n)).arrow).hom z) = _
    rw [Subobject.ofLE_arrow, hy]
  have hp := LinearMap.congr_fun hpage (i.hom z)
  change page ((closedToPage F D r (-p) (-n)).hom z) =
    (FilteredPage.toPage G r (-p) (-n) (E.containment r (-p) (-n))).hom (almost (i.hom z)) at hp
  rw [hrep] at hp
  change page ((closedToPage F D r (-p) (-n)).hom z) = (closedToPage G E r (-p) (-n)).hom y at hp
  change (J.iso.hom ≫ (transportedGradedIso G n B e' p).hom).hom
      (page ((closedToPage F D r (-p) (-n)).hom z)) =
    m ((I.iso.hom ≫ (transportedGradedIso F n A e p).hom).hom
      ((closedToPage F D r (-p) (-n)).hom z))
  rw [hp]
  change (closedToPage G E r (-p) (-n) ≫ J.iso.hom ≫ (transportedGradedIso G n B e' p).hom).hom y =
    m ((closedToPage F D r (-p) (-n) ≫ I.iso.hom ≫ (transportedGradedIso F n A e p).hom).hom z)
  rw [limitIso_transported_formula e I, limitIso_transported_formula e' J]
  have hstep : s (transportedClosedClass (F := F) e p z) = transportedClosedClass (F := G) e' p y := by
    apply (ModuleCat.mono_iff_injective (transportedPiece G n B e' p).arrow).mp inferInstance
    exact (LinearMap.congr_fun hs (transportedClosedClass (F := F) e p z)).trans
      (originalClosedClass_comm f e e' hh g hg p z y hy).symm
  have hgraded := LinearMap.congr_fun hm (transportedClosedClass (F := F) e p z)
  change m _ = _ at hgraded
  change _ = m _ 
  simp only [LinearMap.comp_apply] at hgraded
  rw [hstep] at hgraded
  exact hgraded.symm

end
end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open AdvancedHomologicalAlgebra.TorBalance
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
section
universe a' b'
variable {R : Type u} [Ring R]
  {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v'} Rᵐᵒᵖ}
  {M : ModuleCat.{w} R} {M' : ModuleCat.{w'} R}
  {P : AugmentedResolution.{u,v,a} Rᵐᵒᵖ A} {P' : AugmentedResolution.{u,v',a'} Rᵐᵒᵖ A'}
  {Q : AugmentedResolution.{u,w,b} R M} {Q' : AugmentedResolution.{u,w',b'} R M'}

private theorem balanceInverse_natural
    {f : A →ₗ[Rᵐᵒᵖ] A'} {g : M →ₗ[R] M'}
    {l : LinearChainMap P.complex P'.complex} {m : LinearChainMap Q.complex Q'.complex}
    (hl : P.Lifts P' f l) (hm : Q.Lifts Q' g m)
    (α : OriginalAugmentations P Q) (β : OriginalAugmentations P' Q')
    (hαL : α.left.IsQuasiIso) (hαR : α.right.IsQuasiIso)
    (hβL : β.left.IsQuasiIso) (hβR : β.right.IsQuasiIso)
    (n : ℕ) (z : Homology (leftOrdinaryTensorComplex A Q.complex) n) :
    (β.balanceEquiv hβL hβR n).symm ((leftTensorLinearChainMap f m).homologyMap n z) =
      (tensorLinearChainMap l g).homologyMap n ((α.balanceEquiv hαL hαR n).symm z) := by
  obtain ⟨F, hF⟩ := heterogeneous_balance_naturality R A A' M M' P P' Q Q'
    f g l m hl hm α β hαL hαR hβL hβR
  have h := LinearMap.congr_fun (hF n).2.2 ((α.balanceEquiv hαL hαR n).symm z)
  apply (β.balanceEquiv hβL hβR n).injective
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    F.left_eq, F.right_eq] using h.symm

end

variable {R : Type u} [Ring R]

private abbrev chosenRightResolution (T : CanonicalTheory.{u,v,w} R) (A : ModuleCat.{v} Rᵐᵒᵖ) :=
  AugmentedResolution.ofP103 (T.rightResolutions A).val (T.rightResolutions A).property
variable {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
  {D : Realization T X.P X.M X.Q X.L} {E : Realization T' Y.P Y.M Y.Q Y.L}
  (f : OriginalInputMap X Y)
  (h : ∀ q, X.P.homology q →ₗ[Rᵐᵒᵖ] Y.P.homology q)

def originalTorLift (q : ℤ) :
    LinearChainMap (T.rightResolutions (X.P.homology q)).val.complex
      (T'.rightResolutions (Y.P.homology q)).val.complex :=
  (LinearChainMap.exists_augmentedLift (chosenRightResolution T (X.P.homology q))
    (chosenRightResolution T' (Y.P.homology q)) (h q)).choose

theorem originalTorLift_augmented (q : ℤ) :
    (T'.rightResolutions (Y.P.homology q)).val.ε.comp
        ((originalTorLift (T := T) (T' := T') h q).app 0) =
      (h q).comp (T.rightResolutions (X.P.homology q)).val.ε :=
  LinearMap.ext (LinearChainMap.exists_augmentedLift (chosenRightResolution T (X.P.homology q))
    (chosenRightResolution T' (Y.P.homology q)) (h q)).choose_spec

def originalTorMap (q : ℤ) (p : ℕ) :
    T.Tor (X.P.homology q) X.M p →ₗ[ℤ] T'.Tor (Y.P.homology q) Y.M p :=
  (tensorLinearChainMap (originalTorLift (T := T) (T' := T') h q) f.coefficient).homologyMap p

set_option maxHeartbeats 1800000 in
theorem originalTorMap_balance (q : ℤ) (p : ℕ)
    (z : Homology (leftOrdinaryTensorComplex (X.P.homology q) X.Q.complex) p) :
    (balanceEquiv (E.secondComparison.balance q) (E.secondComparison.leftQuasiIso q)
        (E.secondComparison.rightQuasiIso q) p).symm
      ((leftTensorLinearChainMap (h q) f.lift).homologyMap p z) =
    originalTorMap (T := T) (T' := T') f h q p
      ((balanceEquiv (D.secondComparison.balance q) (D.secondComparison.leftQuasiIso q)
        (D.secondComparison.rightQuasiIso q) p).symm z) := by
  let α := OriginalAugmentations.ofP103 (T.rightResolutions (X.P.homology q)).property
    X.projective (D.secondComparison.balance q)
  let β := OriginalAugmentations.ofP103 (T'.rightResolutions (Y.P.homology q)).property
    Y.projective (E.secondComparison.balance q)
  let l := originalTorLift (T := T) (T' := T') h q
  have hl : (chosenRightResolution T (X.P.homology q)).Lifts
      (chosenRightResolution T' (Y.P.homology q)) (h q) l :=
    LinearMap.congr_fun (originalTorLift_augmented (T := T) (T' := T') h q)
  have hm : (AugmentedResolution.ofP103 X.Q X.projective).Lifts
      (AugmentedResolution.ofP103 Y.Q Y.projective) f.coefficient f.lift :=
    LinearMap.congr_fun f.lift_augmented
  exact balanceInverse_natural hl hm α β
    (LinearChainMap.isQuasiIso_ofHom (D.secondComparison.leftQuasiIso q))
    (LinearChainMap.isQuasiIso_ofHom (D.secondComparison.rightQuasiIso q))
    (LinearChainMap.isQuasiIso_ofHom (E.secondComparison.leftQuasiIso q))
    (LinearChainMap.isQuasiIso_ofHom (E.secondComparison.rightQuasiIso q)) p z

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end OriginalTargets

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence

section OriginalNextSquare

universe a b
variable {K : CochainComplex (ModuleCat.{a} ℤ) ℤ} {L : CochainComplex (ModuleCat.{b} ℤ) ℤ}
  {F : Filtration K} {G : Filtration L}
  (f : OriginalFilteredMap F G) {D : F03Specs.PageData F} {E : F03Specs.PageData G}
  (C : PageCohomology.Data F D) (C' : PageCohomology.Data G E)

set_option maxHeartbeats 1000000 in
theorem originalNextIso_natural_of_middle (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    {A : ShortComplex (ModuleCat.{a} ℤ)} {B : ShortComplex (ModuleCat.{b} ℤ)}
    (I : PageCohomology.shortComplex F D r hr p n ≅ A)
    (J : PageCohomology.shortComplex G E r hr p n ≅ B)
    (g : A.X₂ →ₗ[ℤ] B.X₂) (H : A.homology →ₗ[ℤ] B.homology)
    (h : ActsOnHomologyClasses g H)
    (hmid : J.hom.τ₂.hom.comp (f.pageMap D E r (p+r) (n+1)) = g.comp I.hom.τ₂.hom) :
    (((ShortComplex.homologyMapIso J).hom.hom).comp (C'.nextIso r hr p n).hom.hom).comp
        (f.pageMap D E (r+1) (p+r) (n+1)) =
      H.comp (((ShortComplex.homologyMapIso I).hom.hom).comp (C.nextIso r hr p n).hom.hom) := by
  let A₀ := PageCohomology.shortComplex F D r hr p n
  let B₀ := PageCohomology.shortComplex G E r hr p n
  let κ : A₀.X₂ →ₗ[ℤ] B₀.X₂ := f.pageMap D E r (p+r) (n+1)
  let H₀ : A₀.homology →ₗ[ℤ] B₀.homology :=
    (C'.nextIso r hr p n).hom.hom.comp ((f.pageMap D E (r+1) (p+r) (n+1)).comp
      (C.nextIso r hr p n).inv.hom)
  have h₀ : ActsOnHomologyClasses (S := A₀) (T := B₀) κ H₀ :=
    f.next_natural D E C C' r hr p n
  have hs := ActsOnHomologyClasses.square h₀ h
    (ActsOnHomologyClasses.ofShortComplexHom I.hom) (ActsOnHomologyClasses.ofShortComplexHom J.hom) hmid
  ext z
  have hz := LinearMap.congr_fun hs ((C.nextIso r hr p n).hom.hom z)
  change (ShortComplex.homologyMap J.hom).hom ((C'.nextIso r hr p n).hom.hom
    (f.pageMap D E (r+1) (p+r) (n+1) ((C.nextIso r hr p n).inv.hom ((C.nextIso r hr p n).hom.hom z)))) =
      H ((ShortComplex.homologyMap I.hom).hom ((C.nextIso r hr p n).hom.hom z)) at hz
  rw [ModuleCat.inv_hom_apply] at hz
  exact hz

end OriginalNextSquare

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
open TorBalance (LinearChainMap leftTensorLinearChainMap)
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

section SignedRow
universe v' w'
variable {R : Type u} [Ring R]
  {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
  {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
  {S : TensorPages P Q} {U : TensorPages P' Q'}

/-- The passage to second-page homology through the signed row comparison,
before restriction to ordinary resolution degrees and balance. -/
private def signedRowPart (C : RowTensorComparison P Q S) (p : ℕ) (q : ℤ) :
    S.term 2 p q ≅ (rowTensorComplex P Q (-q)).homology (-(p : ℤ)) :=
  let a : ℤ := -(p : ℤ)
  let b : ℤ := -q
  let hp : -(p : ℤ) = a-1+1 := by dsimp [a]; omega
  let hn : -((p : ℤ)+q) = a+b-1+1 := by dsimp [a,b]; omega
  eqToIso (congrArg₂ (PageCohomology.object S.filtration S.pages 2) hp hn) ≪≫
    S.next.nextIso 1 (by omega) (a-1) (a+b-1) ≪≫
    ShortComplex.homologyMapIso (C.shortIso a b)

set_option maxHeartbeats 4000000 in
private theorem signedRowPart_natural
    (C : RowTensorComparison P Q S) (D : RowTensorComparison P' Q' U)
    (F : OriginalFilteredMap S.filtration U.filtration) (p : ℕ) (q : ℤ)
    (g : LinearChainMap (rowTensorComplex P Q (-q)) (rowTensorComplex P' Q' (-q)))
    (hmid :
      let a : ℤ := -(p : ℤ)
      let b : ℤ := -q
      (D.shortIso a b).hom.τ₂.hom.comp (F.pageMap S.pages U.pages 1 (a-1+1) (a+b-1+1)) =
        (g.app a).comp (C.shortIso a b).hom.τ₂.hom) :
    (signedRowPart D p q).hom.hom.comp (F.pageMap S.pages U.pages 2 (-p) (-(p+q))) =
      (categoricalHomologyMap g (-(p : ℤ))).comp (signedRowPart C p q).hom.hom := by
  let a : ℤ := -(p : ℤ)
  let b : ℤ := -q
  have hN := originalNextIso_natural_of_middle F S.next U.next
    1 (by omega) (a-1) (a+b-1) (C.shortIso a b) (D.shortIso a b)
    (g.app a) (categoricalHomologyMap g a) (categoricalHomologyMap_formula g a) hmid
  let hp : -(p : ℤ) = a-1+1 := by dsimp [a]; omega
  let hn : -((p : ℤ)+q) = a+b-1+1 := by dsimp [a,b]; omega
  have hR := originalPageMap_transport F S.pages U.pages 2 _ _ _ _ hp hn
  ext z
  have hz := LinearMap.congr_fun hR z
  have hz' := LinearMap.congr_fun hN
    ((eqToHom (congrArg₂ (PageCohomology.object S.filtration S.pages 2) hp hn)).hom z)
  simp only [LinearMap.comp_apply] at hz hz'
  simp only [signedRowPart, Iso.trans_hom, eqToIso.hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [hz]
  exact hz'

end SignedRow

section OriginalE2

universe v' w'
variable {R : Type u} [Ring R]
variable {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
  (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
  (f : OriginalInputMap X Y)

set_option maxHeartbeats 1500000 in
private theorem secondIso_eq_row_ordinary {V : CanonicalTheory.{u,v,w} R}
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {M : ModuleCat.{w} R}
    {Q : LeftResolution R M} {L : ℤ} (U : Realization V P M Q L) (p : ℕ) (q : ℤ) :
    U.secondIso p q =
      signedRowPart U.secondComparison.rowComparison p q ≪≫
      rowOrdinaryComparison (U.secondComparison.ordinary q) p (-q) (neg_neg q) ≪≫
      (balanceEquiv (U.secondComparison.balance q) (U.secondComparison.leftQuasiIso q)
        (U.secondComparison.rightQuasiIso q) p).symm.toModuleIso := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

set_option maxHeartbeats 4000000 in
/-- Naturality of the specified signed second-page comparison on the original
resolutions and with the actual two-augmentation Tor balance isomorphisms. -/
theorem originalSecondIso_natural (p : ℕ) (q : ℤ) :
    (E.secondIso p q).hom.hom.comp
      ((originalTensorFilteredMap f.right f.lift.extendNonnegative D.tensorPages E.tensorPages).pageMap
        D.tensorPages.pages E.tensorPages.pages 2 (-p) (-(p+q))) =
      (originalTorMap (T := T) (T' := T') f (categoricalHomologyMap f.right) q p).comp
        (D.secondIso p q).hom.hom := by
  let A : ℤ := -(p : ℤ)
  let B : ℤ := -q
  let F := originalTensorFilteredMap f.right f.lift.extendNonnegative D.tensorPages E.tensorPages
  let K := D.secondComparison.rowComparison
  let L := E.secondComparison.rowComparison
  let g := originalRowTensorComplexMap f.right f.lift.extendNonnegative B
  have hmid := originalRowShortIso_middle_natural f.right f.lift.extendNonnegative F rfl K L A B
    (g.app A) (originalRowTensorHomologyIso_natural f.right f.lift.extendNonnegative A B
      (K.flatComparison A) (L.flatComparison A))
  have hR := signedRowPart_natural K L F p q g hmid
  have hO := originalRowOrdinary_natural (D.secondComparison.ordinary q) (E.secondComparison.ordinary q)
    f.right f.lift p B (neg_neg q)
  have hg : originalReverseMap (originalExtendedTensorMap (categoricalHomologyMap f.right (-B)) f.lift) = g := rfl
  rw [hg] at hO
  have hB := originalTorMap_balance (D := D) (E := E) f (categoricalHomologyMap f.right) q p
  rw [secondIso_eq_row_ordinary D, secondIso_eq_row_ordinary E]
  apply LinearMap.ext
  intro z
  have hRz := LinearMap.congr_fun hR z
  have hOz := LinearMap.congr_fun hO ((signedRowPart D.secondComparison.rowComparison p q).hom.hom z)
  have hBz := hB ((rowOrdinaryComparison (D.secondComparison.ordinary q) p B (neg_neg q)).hom.hom
    ((signedRowPart D.secondComparison.rowComparison p q).hom.hom z))
  simp only [Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply] at hRz hOz ⊢
  rw [hRz, hOz]
  exact hBz

end OriginalE2

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open FiniteFiltrationConvergence
open TorBalance (LinearChainMap tensorLinearChainMap)
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

section OriginalNaturality

universe v' w'
variable {R : Type u} [Ring R]
variable {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
  (D : Realization T X.P X.M X.Q X.L) (E : Realization T' Y.P Y.M Y.Q Y.L)
  (f : OriginalInputMap X Y)

private def originalTensorPageMap (r p n : ℤ) :
    (PageCohomology.object D.tensorPages.filtration D.tensorPages.pages r p n :
      ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
    (PageCohomology.object E.tensorPages.filtration E.tensorPages.pages r p n :
      ModuleCat.{max u v' w'} ℤ) :=
  (originalTensorFilteredMap f.right f.lift.extendNonnegative D.tensorPages E.tensorPages).pageMap
    D.tensorPages.pages E.tensorPages.pages r p n

private theorem originalTargetStep_exists (p n : ℤ) (z : (D.targetPiece p n : ModuleCat.{max u v w} ℤ)) :
    ∃ y : (E.targetPiece p n : ModuleCat.{max u v' w'} ℤ),
      (E.targetPiece p n).arrow.hom y = originalTargetMap f n ((D.targetPiece p n).arrow.hom z) := by
  let F := originalTensorFilteredMap f.right f.lift.extendNonnegative D.tensorPages E.tensorPages
  exact originalTargetPiece_exists F.hom F.preserves (D.targetIso n) (E.targetIso n)
    (categoricalHomologyMap_formula F.hom) (originalTargetMap f n)
    (originalTargetComparison_natural D E f n) p z

private def originalTargetStep (p n : ℤ) :
    (D.targetPiece p n : ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
      (E.targetPiece p n : ModuleCat.{max u v' w'} ℤ) :=
  subobjectLinearMap _ _ (originalTargetMap f n) (originalTargetStep_exists D E f p n)

private theorem originalTargetStep_arrow (p n : ℤ) :
    (E.targetPiece p n).arrow.hom.comp (originalTargetStep D E f p n) =
      (originalTargetMap f n).comp (D.targetPiece p n).arrow.hom :=
  LinearMap.ext (subobjectLinearMap_arrow _ _ _ _)

set_option maxHeartbeats 4000000 in
/-- Assemble the original total, page, Tor, and target comparisons from the
natural second-page identification for the same signed tensor totals. -/
def originalNaturalMapData
    (second : ∀ (p : ℕ) (q : ℤ),
      (E.secondIso p q).hom.hom.comp (originalTensorPageMap D E f 2 (-p) (-(p+q))) =
        (originalTorMap (T := T) (T' := T') f (categoricalHomologyMap f.right) q p).comp
          (D.secondIso p q).hom.hom) :
    OriginalNaturalMap D E f := by
  let F := originalTensorFilteredMap f.right f.lift.extendNonnegative D.tensorPages E.tensorPages
  let g := originalCoefficientComplexMap f.right f.coefficient
  let s := originalTargetStep D E f
  let hstep := originalTargetStep_arrow D E f
  let m : ∀ p n, (D.targetGraded p n : ModuleCat.{max u v w} ℤ) →ₗ[ℤ]
      (E.targetGraded p n : ModuleCat.{max u v' w'} ℤ) :=
    fun p n => originalTargetGraded (D.targetIso n) (E.targetIso n) (originalTargetMap f n)
      (fun p => s p n) (fun p => hstep p n) p
  have hgraded := fun p n => originalTargetGraded_π (D.targetIso n) (E.targetIso n) (originalTargetMap f n)
    (fun p => s p n) (fun p => hstep p n) p
  refine
    { extended := f.lift.extendNonnegative
      extended_formula := f.lift.extendNonnegative_app_inv
      total := F.hom
      total_formula := originalTensorTotalMap_tmul f.right f.lift.extendNonnegative
      filtered := F.preserves
      almost := F.almostMap
      almost_formula := F.almostMap_arrow
      page := originalTensorPageMap D E f
      page_formula := F.pageMap_formula D.tensorPages.pages E.tensorPages.pages
      differential := F.pageMap_differential D.tensorPages.pages E.tensorPages.pages
      next_natural := F.next_natural D.tensorPages.pages E.tensorPages.pages D.tensorPages.next E.tensorPages.next
      pHomology := categoricalHomologyMap f.right
      pHomology_formula := categoricalHomologyMap_formula f.right
      tor := originalTorMap (T := T) (T' := T') f (categoricalHomologyMap f.right)
      tor_formula := ?_
      second := second
      targetChain := g
      targetChain_formula := fun _ => rfl
      augmentation := originalTargetAugmentation_natural f D.targetAugmentation E.targetAugmentation
      totalHomology := categoricalHomologyMap F.hom
      totalHomology_formula := categoricalHomologyMap_formula F.hom
      targetQuotient := g.homologyMap
      targetQuotient_formula := g.homologyMap_induces
      target := originalTargetMap f
      target_formula := fun _ _ => rfl
      target_comparison := originalTargetComparison_natural D E f
      step := s
      step_arrow := hstep
      graded := m
      graded_projection := hgraded
      limit_target_natural := ?_ }
  · intro q
    let l := originalTorLift (T := T) (T' := T') (categoricalHomologyMap f.right) q
    refine ⟨l, originalTorLift_augmented (T := T) (T' := T') (categoricalHomologyMap f.right) q,
      tensorLinearChainMap l f.coefficient, fun _ => rfl, ?_⟩
    exact (tensorLinearChainMap l f.coefficient).homologyMap_induces
  · intro r p n I J hi _
    exact originalLimitIso_natural (D.targetIso n) (E.targetIso n) F.hom F.preserves
      (categoricalHomologyMap_formula F.hom) (originalTargetMap f n)
      (originalTargetComparison_natural D E f n) I J
      (F.pageMap D.tensorPages.pages E.tensorPages.pages r (-p) (-n))
      (F.almostMap r (-p) (-n)) (F.almostMap_arrow r (-p) (-n))
      (F.pageMap_formula D.tensorPages.pages E.tensorPages.pages r (-p) (-n))
      (s p n) (hstep p n) (m p n) (hgraded p n) hi

set_option maxHeartbeats 2000000 in
theorem original_naturality : Specs.OriginalNaturality.{u,v,w,v',w'} := by
  intro R _ T T' X Y D E f g
  obtain ⟨l, hl⟩ := LinearChainMap.exists_augmentedLift
    (TorBalance.AugmentedResolution.ofP103 X.Q X.projective)
    (TorBalance.AugmentedResolution.ofP103 Y.Q Y.projective) g
  refine ⟨⟨l, LinearMap.ext hl⟩, ?_⟩
  intro l hl
  let F : OriginalInputMap X Y := ⟨f,g,l,hl⟩
  exact ⟨originalNaturalMapData D E F (originalSecondIso_natural D E F)⟩


end OriginalNaturality

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

universe v' w'
namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open AdvancedHomologicalAlgebra.TorBalance
open private AdvancedHomologicalAlgebra.TorBalance.tensorLinearChainMap_homotopic
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance

private theorem categoricalHomologyMap_unique
    {S : Type u} [Ring S] {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c} {f : LinearChainMap K L}
    {h₁ h₂ : ∀ n, K.homology n →ₗ[S] L.homology n}
    (H₁ : InducesCategoricalHomology f h₁) (H₂ : InducesCategoricalHomology f h₂) :
    h₁ = h₂ := by
  funext n
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x
  obtain ⟨y₁, hy₁, he₁⟩ := H₁ n z
  obtain ⟨y₂, hy₂, he₂⟩ := H₂ n z
  have he := (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance (hy₁.trans hy₂.symm)
  exact he₁.trans ((congrArg ((L.homologyπ n).hom) he).trans he₂.symm)

private theorem quotientHomologyMap_unique
    {S : Type u} [Ring S] {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{v} S) c}
    {L : HomologicalComplex (ModuleCat.{w} S) c} (f : LinearChainMap K L)
    (h : ∀ n, Homology K n →ₗ[S] Homology L n) (hh : f.InducesHomology (fun n z => h n z))
    (n : ι) (x : Homology K n) :
    h n x = f.homologyMap n x := by
  obtain ⟨z, rfl⟩ := (cycleBoundaries K n).mkQ_surjective x
  obtain ⟨y, hy, he⟩ := hh n z
  change h n (homologyClass K n z) = homologyClass L n y at he
  exact he.trans (congrArg (homologyClass L n) (Subtype.ext hy))

section
variable {R : Type u} [Ring R]
variable {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w} R} {Y : Input.{u,v',w'} R}
  {D : Realization T X.P X.M X.Q X.L} {E : Realization T' Y.P Y.M Y.Q Y.L}
  {f : LinearChainMap X.P Y.P} {g : X.M →ₗ[R] Y.M}
  {l m : LinearChainMap X.Q.complex Y.Q.complex}
  {a : Y.Q.ε.comp (l.app 0) = g.comp X.Q.ε} {b : Y.Q.ε.comp (m.app 0) = g.comp X.Q.ε}

private theorem OriginalNaturalMap.tor_lift_independent
    (F : OriginalNaturalMap D E ⟨f,g,l,a⟩) (G : OriginalNaturalMap D E ⟨f,g,m,b⟩) :
    F.tor = G.tor := by
  have hh := categoricalHomologyMap_unique F.pHomology_formula G.pHomology_formula
  funext q
  obtain ⟨s, hs, A, hA, hAh⟩ := F.tor_formula q
  obtain ⟨t, ht, B, hB, hBh⟩ := G.tor_formula q
  rw [← hh] at ht
  have homotopy := LinearChainMap.augmentedLifts_homotopic
    (chosenRightResolution T (X.P.homology q)) (chosenRightResolution T' (Y.P.homology q))
    (F.pHomology q) s t (LinearMap.congr_fun hs) (LinearMap.congr_fun ht)
  have hA' : A = tensorLinearChainMap s g := LinearChainMap.eq_of_app_eq (funext hA)
  have hB' : B = tensorLinearChainMap t g := LinearChainMap.eq_of_app_eq (funext hB)
  have hAB : A.homologyMap = B.homologyMap := by
    rw [hA', hB']
    exact LinearChainMap.homologyMap_eq_of_homotopic (AdvancedHomologicalAlgebra.TorBalance.tensorLinearChainMap_homotopic homotopy g)
  funext p
  exact LinearMap.ext fun z => (quotientHomologyMap_unique A _ hAh p z).trans
    ((congrArg (fun k => k p z) hAB).trans (quotientHomologyMap_unique B _ hBh p z).symm)

set_option maxHeartbeats 1800000 in
private theorem OriginalNaturalMap.page_lift_independent
    (F : OriginalNaturalMap D E ⟨f,g,l,a⟩) (G : OriginalNaturalMap D E ⟨f,g,m,b⟩) :
    ∀ (r p n : ℤ), 2 ≤ r → F.page r p n = G.page r p n := by
  have ht := F.tor_lift_independent G
  suffices H : ∀ k : ℕ, ∀ p n : ℤ, F.page (2 + k) p n = G.page (2 + k) p n by
    intro r p n hr
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r - 2 by omega)
    rw [show r = 2 + (k : ℤ) by omega]
    exact H k p n
  intro k
  induction k with
  | zero =>
    intro p n
    change F.page 2 p n = G.page 2 p n
    by_cases hp : p ≤ 0
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -p by omega)
      let q := -n-(k : ℤ)
      have e₁ : -(k : ℤ) = p := by omega
      have e₂ : -((k : ℤ)+q) = n := by dsimp [q]; omega
      rw [← e₁, ← e₂]
      apply LinearMap.ext
      intro z
      apply (ModuleCat.mono_iff_injective (E.secondIso k q).hom).mp inferInstance
      change (((E.secondIso k q).hom.hom.comp (F.page 2 (-k) (-(k+q)))) z) =
        (((E.secondIso k q).hom.hom.comp (G.page 2 (-k) (-(k+q)))) z)
      rw [F.second, G.second, ht]
    · have hz := D.support 2 (-p) (p-n) (Or.inl (by omega))
      have he : D.tensorPages.term 2 (-p) (p-n) =
          PageCohomology.object D.tensorPages.filtration D.tensorPages.pages 2 p n := by
        unfold TensorPages.term
        congr 1 <;> omega
      apply LinearMap.ext
      intro z
      haveI := (ModuleCat.isZero_iff_subsingleton).mp (IsZero.of_iso hz (eqToIso he.symm))
      rw [Subsingleton.elim z 0, map_zero, map_zero]
  | succ k ih =>
    intro p n
    let r : ℤ := 2 + k
    have hr : 0 ≤ r := by dsimp [r]; omega
    rw [show (2 + (↑(k+1) : ℤ)) = r + 1 by dsimp [r]; omega]
    let A := PageCohomology.shortComplex D.tensorPages.filtration D.tensorPages.pages r hr (p-r) (n-1)
    let B := PageCohomology.shortComplex E.tensorPages.filtration E.tensorPages.pages r hr (p-r) (n-1)
    let I := D.tensorPages.next.nextIso r hr (p-r) (n-1)
    let J := E.tensorPages.next.nextIso r hr (p-r) (n-1)
    have hp : p-r+r = p := by omega
    have hn : n-1+1 = n := by omega
    have hEq : F.page (r+1) (p-r+r) (n-1+1) = G.page (r+1) (p-r+r) (n-1+1) := by
      apply LinearMap.ext
      intro x
      have hx : Function.Surjective (fun z : A.cycles => I.inv.hom (A.homologyπ.hom z)) :=
        ((ModuleCat.epi_iff_surjective I.inv).mp inferInstance).comp
          ((ModuleCat.epi_iff_surjective A.homologyπ).mp inferInstance)
      obtain ⟨z, rfl⟩ := hx x
      obtain ⟨y, hy, h1⟩ := F.next_natural r hr (p-r) (n-1) z
      obtain ⟨y', hy', h2⟩ := G.next_natural r hr (p-r) (n-1) z
      have hyEq : y = y' := by
        apply (ModuleCat.mono_iff_injective B.iCycles).mp inferInstance
        rw [hy, hy', ih]
      apply (ModuleCat.mono_iff_injective J.hom).mp inferInstance
      exact h1.trans ((congrArg B.homologyπ.hom hyEq).trans h2.symm)
    rwa [hp, hn] at hEq

end

set_option maxHeartbeats 1000000 in
theorem original_lift_independence : Specs.OriginalLiftIndependence.{u,v,w,v',w'} := by
  intro R _ T T' X Y D E f g l m a b F G
  have hc : F.targetChain = G.targetChain := by
    apply LinearChainMap.eq_of_app_eq
    funext n
    rw [F.targetChain_formula, G.targetChain_formula]
  have htargetQ : F.targetQuotient = G.targetQuotient := by
    funext n
    apply LinearMap.ext
    intro z
    have hf := quotientHomologyMap_unique F.targetChain _ F.targetQuotient_formula n z
    have hg := quotientHomologyMap_unique G.targetChain _ G.targetQuotient_formula n z
    rw [hc] at hf
    exact hf.trans hg.symm
  have htarget : F.target = G.target := by
    funext n
    apply LinearMap.ext
    rintro ⟨z⟩
    rw [F.target_formula, G.target_formula, htargetQ]
  have hstep : F.step = G.step := by
    funext p n
    apply LinearMap.ext
    intro z
    apply (ModuleCat.mono_iff_injective (E.targetPiece p n).arrow).mp inferInstance
    have hf := LinearMap.congr_fun (F.step_arrow p n) z
    have hg := LinearMap.congr_fun (G.step_arrow p n) z
    rw [htarget] at hf
    exact hf.trans hg.symm
  refine ⟨F.page_lift_independent G, htarget, hstep, ?_⟩
  funext p n
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (cokernel.π (Subobject.ofLE _ _
      (transportedPiece_increasing D.tensorPages.filtration n _ (D.targetIso n) p)))).mp
        inferInstance z
  have hf := LinearMap.congr_fun (F.graded_projection p n) x
  have hg := LinearMap.congr_fun (G.graded_projection p n) x
  rw [hstep] at hf
  exact hf.trans hg.symm

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

section IndependentResolutionProof

universe t t' v'' w'' a b

set_option maxHeartbeats 1600000

namespace AdvancedHomologicalAlgebra.KunnethSpectralSequence

open DoubleTotalization FiniteDiagonalFiltrations FiniteFiltrationConvergence FilteredPage
open P103.BalancedTensor (Tensor tmul)
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open TorBalance (AugmentedResolution LinearChainMap tensorLinearChainMap leftTensorLinearChainMap)

open private TorBalance.LinearChainMap.liftResolution
  TorBalance.LinearChainMap.liftComplexUp TorBalance.LinearChainMap.liftComplexDown
  TorBalance.LinearChainMap.liftComplexDown_comp_up TorBalance.LinearChainMap.liftComplexUp_comp_down
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance
open private TorBalance.tensorLinearChainMap_homotopic from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.TorBalance

namespace IndependentResolution

variable {R : Type u} [Ring R]

private theorem extended_isZero {S : Type u} [Ring S]
    (Q : ChainComplex (ModuleCat.{t} S) ℕ) (j : ℤ) (hj : j < 0) :
    IsZero ((extendNonnegativeChain Q).X j) :=
  Q.isZero_extend_X nonnegativeChainEmbedding j (by
    intro i hi
    change (i : ℤ) = j at hi
    omega)

private theorem extended_flat (X : Input.{u,v,w,t} R) (j : ℤ) :
    P103.Specs.Ch02.FlatnessTests.Flat.{u,t,v} R (X.extended.X j) := by
  apply P103.Ch02.FlatnessTests.projective_flat
  by_cases hj : 0 ≤ j
  · letI := X.Q.projective j.toNat
    exact Module.Projective.of_equiv'
      (X.Q.complex.extendXIso nonnegativeChainEmbedding (Int.toNat_of_nonneg hj)).toLinearEquiv.symm
  · letI := (ModuleCat.isZero_iff_subsingleton).mp (extended_isZero X.Q.complex j (by omega))
    infer_instance

private def secondPageData (T : CanonicalTheory.{u,v,w} R)
    (X : Input.{u,v,w,t} R) (S : TensorPages X.P X.extended) : SecondPage T X S := by
  let h (q : ℤ) := TorBalance.original_balance R (X.P.homology q) X.M
    (chosenRightResolution T (X.P.homology q)) X.Q
  exact ⟨rowTensorComparison X.P X.extended (extended_flat X) S,
    fun q => ordinaryTensorComparison (X.P.homology q) X.Q.complex,
    fun q => (h q).choose, fun q => (h q).choose_spec.1, fun q => (h q).choose_spec.2⟩

private theorem extend_id {S : Type u} [Ring S] (K : ChainComplex (ModuleCat.{a} S) ℕ) :
    (LinearChainMap.id K).extendNonnegative = LinearChainMap.id (extendNonnegativeChain K) := by
  apply LinearChainMap.eq_of_app_eq
  funext i
  ext x
  by_cases hi : 0 ≤ i
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    let e := K.extendXIso nonnegativeChainEmbedding (i := j) rfl
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance x
    rw [LinearChainMap.extendNonnegative_app_inv]
    rfl
  · letI := (ModuleCat.isZero_iff_subsingleton).mp (extended_isZero K i (by omega))
    exact Subsingleton.elim _ _

private theorem extend_comp {S : Type u} [Ring S]
    {K : ChainComplex (ModuleCat.{a} S) ℕ} {L : ChainComplex (ModuleCat.{b} S) ℕ}
    {N : ChainComplex (ModuleCat.{t} S) ℕ}
    (f : LinearChainMap K L) (g : LinearChainMap L N) :
    g.extendNonnegative.comp f.extendNonnegative = (g.comp f).extendNonnegative := by
  apply LinearChainMap.eq_of_app_eq
  funext i
  apply LinearMap.ext
  intro x
  by_cases hi : 0 ≤ i
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    let e := K.extendXIso nonnegativeChainEmbedding (i := j) rfl
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance x
    change g.extendNonnegative.app (j : ℤ) (f.extendNonnegative.app (j : ℤ) (e.inv.hom z)) =
      (g.comp f).extendNonnegative.app (j : ℤ) (e.inv.hom z)
    rw [f.extendNonnegative_app_inv, g.extendNonnegative_app_inv,
      LinearChainMap.extendNonnegative_app_inv]
    rfl
  · letI := (ModuleCat.isZero_iff_subsingleton).mp (extended_isZero N i (by omega))
    exact Subsingleton.elim _ _

private theorem tensorTotal_ext
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{t} R) ℤ)
    {N : Type a} [AddCommGroup N] [Module ℤ N] (n : ℤ)
    {f g : (sumTotal (tensorCochain P Q)).X n →ₗ[ℤ] N}
    (h : ∀ i j (e : i + j = n) (x : P.X (-i)) (y : Q.X (-j)),
      f ((sumInjection (tensorCochain P Q) i j n e).hom (tmul R x y)) =
        g ((sumInjection (tensorCochain P Q) i j n e).hom (tmul R x y))) : f = g := by
  apply cochainTotalLinear_ext (tensorCochain P Q) n
  intro i j e z
  have he : f.comp (sumInjection (tensorCochain P Q) i j n e).hom =
      g.comp (sumInjection (tensorCochain P Q) i j n e).hom := by
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    exact h i j e
  exact LinearMap.congr_fun he z

private theorem tensorTotal_id
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{t} R) ℤ) :
    originalTensorTotalMap (LinearChainMap.id P) (LinearChainMap.id Q) =
      LinearChainMap.id (sumTotal (tensorCochain P Q)) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensorTotal_ext P Q
  intro i j e x y
  rw [originalTensorTotalMap_tmul]
  rfl

private theorem tensorTotal_comp
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {P'' : ChainComplex (ModuleCat.{v''} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{w} R) ℤ} {Q' : ChainComplex (ModuleCat.{w'} R) ℤ}
    {Q'' : ChainComplex (ModuleCat.{w''} R) ℤ}
    (f : LinearChainMap P P') (f' : LinearChainMap P' P'')
    (g : LinearChainMap Q Q') (g' : LinearChainMap Q' Q'') :
    (originalTensorTotalMap f' g').comp (originalTensorTotalMap f g) =
      originalTensorTotalMap (f'.comp f) (g'.comp g) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  apply tensorTotal_ext P Q
  intro i j e x y
  simp only [LinearChainMap.comp_app, LinearMap.comp_apply, originalTensorTotalMap_tmul]

private theorem chainId_comp {S : Type u} [Ring S] {ι : Type a} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{t} S) c) :
    (LinearChainMap.id K).comp (LinearChainMap.id K) = LinearChainMap.id K :=
  LinearChainMap.eq_of_app_eq (funext fun _ => LinearMap.id_comp _)

private abbrev liftedModule (X : Input.{u,v,w,t} R) : ModuleCat.{max u w t} R :=
  ModuleCat.of R (ULift.{max u w t} X.M)

private abbrev liftedResolution (X : Input.{u,v,w,t} R) : LeftResolution R (liftedModule X) :=
  TorBalance.LinearChainMap.liftResolution.{u,w,t,0} X.Q

private def liftTotal (X : Input.{u,v,w,t} R) : LinearChainMap X.total
    (sumTotal (tensorCochain X.P (extendNonnegativeChain (liftedResolution X).complex))) :=
  originalTensorTotalMap (LinearChainMap.id X.P)
    (TorBalance.LinearChainMap.liftComplexUp.{u,t,max u w t} X.Q.complex).extendNonnegative

private theorem liftTotal_quasiIso (X : Input.{u,v,w,t} R) : (liftTotal X).IsQuasiIso := by
  let U := TorBalance.LinearChainMap.liftComplexUp.{u,t,max u w t} X.Q.complex
  let D := TorBalance.LinearChainMap.liftComplexDown.{u,t,max u w t} X.Q.complex
  let g := originalTensorTotalMap (LinearChainMap.id X.P) D.extendNonnegative
  apply (liftTotal X).isQuasiIso_of_inverse g
  · change (originalTensorTotalMap _ D.extendNonnegative).comp
      (originalTensorTotalMap _ U.extendNonnegative) = _
    rw [tensorTotal_comp, chainId_comp, extend_comp,
      TorBalance.LinearChainMap.liftComplexDown_comp_up, extend_id, tensorTotal_id]
  · change (originalTensorTotalMap _ U.extendNonnegative).comp
      (originalTensorTotalMap _ D.extendNonnegative) = _
    rw [tensorTotal_comp, chainId_comp, extend_comp,
      TorBalance.LinearChainMap.liftComplexUp_comp_down, extend_id, tensorTotal_id]
    rfl

section LowerCoefficient

variable (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (M : ModuleCat.{a} R) (M' : ModuleCat.{b} R) (e : M' ≃ₗ[R] M)

private def lowerCoefficient :
    LinearChainMap (reverseChain (liftedCoefficientComplex P M')) (reverseChain (coefficientComplex P M)) :=
  (originalReverseMap (originalCoefficientComplexMap (LinearChainMap.id P) e.toLinearMap)).comp
    ⟨fun _ => ULift.moduleEquiv.toLinearMap, fun _ _ => rfl⟩

private def raiseCoefficient :
    LinearChainMap (reverseChain (coefficientComplex P M)) (reverseChain (liftedCoefficientComplex P M')) :=
  (⟨fun _ => ULift.moduleEquiv.symm.toLinearMap, fun _ _ => rfl⟩ :
    LinearChainMap (reverseChain (coefficientComplex P M')) (reverseChain (liftedCoefficientComplex P M'))).comp
    (originalReverseMap (originalCoefficientComplexMap (LinearChainMap.id P) e.symm.toLinearMap))

private theorem lowerCoefficient_quasiIso : (lowerCoefficient P M M' e).IsQuasiIso := by
  apply (lowerCoefficient P M M' e).isQuasiIso_of_inverse (raiseCoefficient P M M' e) <;>
    apply LinearChainMap.eq_of_app_eq <;> funext i
  · apply LinearMap.ext
    rintro ⟨z⟩
    apply ULift.ext
    suffices h : (tensorMap (LinearMap.id : P.X (-i) →ₗ[Rᵐᵒᵖ] P.X (-i)) e.symm.toLinearMap).comp
        (tensorMap LinearMap.id e.toLinearMap) = LinearMap.id by
      exact LinearMap.congr_fun h z
    apply tensor_hom_ext
    intro x y
    change tmul R x (e.symm (e y)) = tmul R x y
    rw [LinearEquiv.symm_apply_apply]
  · apply tensor_hom_ext
    intro x y
    change tmul R x (e (e.symm y)) = tmul R x y
    rw [LinearEquiv.apply_symm_apply]

end LowerCoefficient

private def augmentedTotal (X : Input.{u,v,w,t} R) : Augmentation X := by
  let Q := liftedResolution X
  let e : liftedModule X ≃ₗ[R] X.M := ULift.moduleEquiv
  let U := TorBalance.LinearChainMap.liftComplexUp.{u,t,max u w t} X.Q.complex
  let a := resolutionTargetAugmentation X.P (liftedModule X) Q
  let d := lowerCoefficient X.P X.M (liftedModule X) e
  refine ⟨d.comp ((LinearChainMap.ofHom a.hom).comp (liftTotal X)), ?_, ?_⟩
  · intro i x y
    change d.app i ((a.hom.f i).hom ((liftTotal X).app i
      ((sumInjection X.tensor i 0 i _).hom (tmul R x
        ((X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl).inv.hom y))))) = _
    dsimp only [liftTotal]
    rw [originalTensorTotalMap_tmul]
    change d.app i ((a.hom.f i).hom
      ((sumInjection (tensorCochain X.P (extendNonnegativeChain Q.complex)) i 0 i _).hom
        (tmul R x (U.extendNonnegative.app (↑(0 : ℕ))
          ((X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl).inv.hom y))))) = _
    erw [U.extendNonnegative_app_inv 0 y]
    erw [a.zero_component]
    rfl
  · intro i j n h hj
    apply tensor_hom_ext
    intro x y
    change d.app n ((a.hom.f n).hom ((liftTotal X).app n
      ((sumInjection X.tensor i j n h).hom (tmul R x y)))) = 0
    dsimp only [liftTotal]
    rw [originalTensorTotalMap_tmul]
    have hz := ConcreteCategory.congr_hom (a.other_components i j n h hj)
      (tmul R x (U.extendNonnegative.app (-j) y))
    change (a.hom.f n).hom
      ((sumInjection (tensorCochain X.P (extendNonnegativeChain Q.complex)) i j n h).hom
        (tmul R x (U.extendNonnegative.app (-j) y))) = 0 at hz
    change d.app n ((a.hom.f n).hom
      ((sumInjection (tensorCochain X.P (extendNonnegativeChain Q.complex)) i j n h).hom
        (tmul R x (U.extendNonnegative.app (-j) y)))) = 0
    rw [hz, map_zero]

private theorem linearQuasiIso_ofHom {S : Type u} [Ring S] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{a} S) c} {f : K ⟶ L} (h : QuasiIso f) :
    (LinearChainMap.ofHom f).IsQuasiIso := by
  apply LinearChainMap.isQuasiIso_ofHom (f := f)
  intro n
  letI := h
  let e := (categoricalHomologyIso K n).symm ≪≫
    asIso (HomologicalComplex.homologyMap f n) ≪≫ categoricalHomologyIso L n
  have he : e.hom = ModuleCat.ofHom (homologyMap f n) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [categoricalHomologyIso_natural, Iso.inv_hom_id_assoc]
  change Function.Bijective (homologyMap f n)
  rw [show homologyMap f n = e.hom.hom from (congrArg ModuleCat.Hom.hom he).symm]
  exact e.toLinearEquiv.bijective

private theorem augmentedTotal_quasiIso (X : Input.{u,v,w,t} R) :
    (augmentedTotal X).map.IsQuasiIso := by
  exact (lowerCoefficient_quasiIso X.P X.M (liftedModule X) ULift.moduleEquiv).comp
    ((linearQuasiIso_ofHom
      (resolutionTensorAugmentation_quasiIso X.P (liftedModule X) (liftedResolution X) X.L
        X.bounded (fun i => X.flat i))).comp (liftTotal_quasiIso X))

section Target

variable {X : Input.{u,v,w,t} R} (A : Augmentation X)

private def reverseHomologyTo (C : ChainComplex (ModuleCat.{a} ℤ) ℤ) {i j : ℤ} (h : -i = j) :
    (reverseChain C).homology i ≅ C.homology j :=
  reverseHomologyIso C i ≪≫ eqToIso (congrArg (fun k : ℤ => C.homology k) h)

private theorem reverseHomologyTo_acts (C : ChainComplex (ModuleCat.{a} ℤ) ℤ) {i j : ℤ} (h : -i = j) :
    ActsOnHomologyClasses (S := (reverseChain C).sc i) (T := C.sc j)
      (C.restrictionXIso reversal (i := i) h).hom.hom (reverseHomologyTo C h).hom.hom := by
  subst j
  simpa only [reverseHomologyTo, eqToIso_refl, Iso.trans_refl] using reverseHomologyIso_acts C i

private def targetEquiv (h : A.map.IsQuasiIso) (n : ℤ) :
    X.total.homology (-n) ≃ₗ[ℤ] Homology X.coefficient n :=
  let K := reverseChain X.coefficient
  let i := -n
  (categoricalHomologyIso X.total i).toLinearEquiv.trans
    ((A.map.homologyEquiv h i).trans
      (((categoricalHomologyIso K i).toLinearEquiv.symm.trans
        (reverseHomologyTo X.coefficient (neg_neg n)).toLinearEquiv).trans
          (categoricalHomologyIso X.coefficient n).toLinearEquiv))

private theorem targetEquiv_formula (h : A.map.IsQuasiIso) (n : ℤ) :
    A.Induces n (targetEquiv A h n) := by
  intro z
  let K := reverseChain X.coefficient
  let i := -n
  obtain ⟨y,hy,hyπ⟩ := categoricalHomologyMap_formula A.map i z
  obtain ⟨w,hw,hwπ⟩ := reverseHomologyTo_acts X.coefficient (neg_neg n) y
  refine ⟨(X.coefficient.sc n).moduleCatCyclesIso.hom w, ?_, ?_⟩
  · have hval := ConcreteCategory.congr_hom (X.coefficient.sc n).moduleCatCyclesIso_hom_i w
    change ((X.coefficient.sc n).moduleCatCyclesIso.hom w).val = _ at hval
    rw [hval]
    change (X.coefficient.iCycles n).hom w = _
    change (X.coefficient.iCycles n).hom w =
      (X.coefficient.restrictionXIso reversal (i := i) (neg_neg n)).hom.hom ((K.iCycles i).hom y) at hw
    rw [hw, hy]
  · have hquot := categoricalQuotientSquare A.map i
      (categoricalHomologyIso X.total i) (categoricalHomologyIso K i)
      (categoricalHomologyIso_formula X.total i) (categoricalHomologyIso_formula K i)
    have hz := LinearMap.congr_fun hquot ((X.total.homologyπ i).hom z)
    change (categoricalHomologyIso K i).hom.hom
        (categoricalHomologyMap A.map i ((X.total.homologyπ i).hom z)) = _ at hz
    rw [hyπ] at hz
    simp only [LinearMap.comp_apply] at hz
    change (categoricalHomologyIso X.coefficient n).hom.hom ((reverseHomologyTo X.coefficient (neg_neg n)).hom.hom
      ((categoricalHomologyIso K i).toLinearEquiv.symm
        (A.map.homologyMap i ((categoricalHomologyIso X.total i).hom.hom ((X.total.homologyπ i).hom z))))) = _
    rw [← hz]
    change (categoricalHomologyIso X.coefficient n).hom.hom ((reverseHomologyTo X.coefficient (neg_neg n)).hom.hom
      ((categoricalHomologyIso K i).inv.hom ((categoricalHomologyIso K i).hom.hom ((K.homologyπ i).hom y)))) = _
    rw [ModuleCat.inv_hom_apply]
    change (reverseHomologyTo X.coefficient (neg_neg n)).hom.hom ((K.homologyπ i).hom y) =
      (X.coefficient.homologyπ n).hom w at hwπ
    rw [hwπ]
    exact categoricalHomologyIso_formula X.coefficient n w

end Target

end IndependentResolution

theorem original_resolution_construction : IndependentResolution.Specs.Construction.{u,v,w,t} := by
  intro R _ T X
  obtain ⟨S⟩ := tensor_page_construction R X.P X.extended X.L 0 X.bounded
    (IndependentResolution.extended_isZero X.Q.complex)
  let a := IndependentResolution.augmentedTotal X
  let h := IndependentResolution.augmentedTotal_quasiIso X
  exact ⟨⟨S, tensor_pages_support R X.P X.extended X.L 0 X.bounded
      (IndependentResolution.extended_isZero X.Q.complex) S,
    IndependentResolution.secondPageData T X S, a, h,
    IndependentResolution.targetEquiv a h, IndependentResolution.targetEquiv_formula a h⟩⟩

namespace IndependentResolution

variable {R : Type u} [Ring R] {T : CanonicalTheory.{u,v,w} R}
  {X : Input.{u,v,w,t} R} (D : Realization T X)

private abbrev imageStep (p n : ℤ) := cohomologyPiece D.pages.filtration (-p) (-n)

private theorem mem_piece_iff (p n : ℤ) (x : Homology X.coefficient n) :
    x ∈ D.piece p n ↔ ∃ z : (imageStep D p n : ModuleCat.{max v t} ℤ),
      D.target n ((imageStep D p n).arrow.hom z) = x := by
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, h⟩
    exact ⟨z, h⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, rfl⟩

private def pieceEquiv (p n : ℤ) :
    (imageStep D p n : ModuleCat.{max v t} ℤ) ≃ₗ[ℤ] D.piece p n :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ ((D.target n).toLinearMap.comp (imageStep D p n).arrow.hom)
      (fun z => (mem_piece_iff D p n _).mpr ⟨z, rfl⟩))
    ⟨fun _ _ h => (ModuleCat.mono_iff_injective (imageStep D p n).arrow).mp inferInstance
      ((D.target n).injective (congrArg Subtype.val h)), fun x => by
        obtain ⟨z, hz⟩ := (mem_piece_iff D p n _).mp x.property
        exact ⟨z, Subtype.ext hz⟩⟩

private theorem pieceEquiv_val (p n : ℤ) (z : (imageStep D p n : ModuleCat.{max v t} ℤ)) :
    ↑(pieceEquiv D p n z) = D.target n ((imageStep D p n).arrow.hom z) := rfl

private abbrev imageTransition (p n : ℤ) :=
  Subobject.ofLE _ _ (cohomologyPiece_decreasing D.pages.filtration (-p) (-n))

private theorem imageTransition_range (p n : ℤ) :
    (LinearMap.range (imageTransition D p n).hom).map (pieceEquiv D p n).toLinearMap =
      D.gradedSubmodule p n := by
  let F := D.pages.filtration
  let A := cohomologyPiece F ((-p)+1) (-n)
  let h := show -(p-1) = (-p)+1 by omega
  let e := Subobject.isoOfEq (imageStep D (p-1) n) A (by rw [imageStep, h])
  have he (z : (imageStep D (p-1) n : ModuleCat.{max v t} ℤ)) :
      A.arrow.hom (e.hom.hom z) = (imageStep D (p-1) n).arrow.hom z := by
    have he' : e.hom ≫ A.arrow = (imageStep D (p-1) n).arrow := by
      dsimp only [e]
      rw [Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
    exact ConcreteCategory.congr_hom he' z
  have hi (z : (A : ModuleCat.{max v t} ℤ)) :
      (imageStep D p n).arrow.hom ((imageTransition D p n).hom z) = A.arrow.hom z :=
    ConcreteCategory.congr_hom (Subobject.ofLE_arrow _) z
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective e.hom).mp inferInstance z
    apply (mem_piece_iff D (p-1) n _).mpr
    refine ⟨y, ?_⟩
    change D.target n ((imageStep D (p-1) n).arrow.hom y) =
      (pieceEquiv D p n ((imageTransition D p n).hom (e.hom.hom y))).val
    rw [pieceEquiv_val, hi, he]
  · intro hx
    change x.val ∈ D.piece (p-1) n at hx
    obtain ⟨z, hz⟩ := (mem_piece_iff D (p-1) n _).mp hx
    refine ⟨(imageTransition D p n).hom (e.hom.hom z), ⟨_, rfl⟩, Subtype.ext ?_⟩
    change (pieceEquiv D p n ((imageTransition D p n).hom (e.hom.hom z))).val = x.val
    rw [pieceEquiv_val, hi, he, hz]

private def gradedEquiv (p n : ℤ) :
    (gradedCohomology D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ) ≃ₗ[ℤ] D.graded p n :=
  (ModuleCat.cokernelIsoRangeQuotient (imageTransition D p n)).toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ (pieceEquiv D p n) (imageTransition_range D p n))

private theorem gradedEquiv_projection (p n : ℤ) (z : (imageStep D p n : ModuleCat.{max v t} ℤ)) :
    gradedEquiv D p n ((cokernel.π (imageTransition D p n)).hom z) =
      (D.gradedSubmodule p n).mkQ (pieceEquiv D p n z) := by
  have h := ConcreteCategory.congr_hom
    (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (imageTransition D p n)) z
  change (ModuleCat.cokernelIsoRangeQuotient (imageTransition D p n)).hom.hom
      ((cokernel.π (imageTransition D p n)).hom z) =
    (LinearMap.range (imageTransition D p n).hom).mkQ z at h
  exact congrArg (Submodule.Quotient.equiv _ _ (pieceEquiv D p n) (imageTransition_range D p n)) h

private def limitComparison (r p n : ℤ)
    (I : LimitIso D.pages.filtration D.pages.pages r (-p) (-n)) :
    LimitComparison D r p n where
  equiv := I.iso.toLinearEquiv.trans (gradedEquiv D p n)
  closed_formula z := by
    let c := closedClass D.pages.filtration (-p) (-n)
    refine ⟨pieceEquiv D p n (c.hom z), pieceEquiv_val D p n _, ?_⟩
    have h := ConcreteCategory.congr_hom I.representative_formula z
    change I.iso.hom.hom ((closedToPage D.pages.filtration D.pages.pages r (-p) (-n)).hom z) =
      (cokernel.π (imageTransition D p n)).hom (c.hom z) at h
    change gradedEquiv D p n (I.iso.hom.hom _) = _
    rw [h, gradedEquiv_projection]

end IndependentResolution

theorem original_resolution_convergence : IndependentResolution.Specs.Convergence.{u,v,w,t} := by
  intro R _ T X D
  constructor
  · intro n
    obtain ⟨a,b,ha,hb⟩ := D.pages.convergence.target.finite (-n)
    refine ⟨-b,-a,?_,?_⟩
    · intro p hp
      change ((ModuleCat.subobjectModule (X.total.homology (-n)))
        (cohomologyPiece D.pages.filtration (-p) (-n))).map (D.target n).toLinearMap = ⊥
      rw [hb (-p) (by omega), OrderIso.map_bot, Submodule.map_bot]
    · intro p hp
      change ((ModuleCat.subobjectModule (X.total.homology (-n)))
        (cohomologyPiece D.pages.filtration (-p) (-n))).map (D.target n).toLinearMap = ⊤
      rw [ha (-p) (by omega), OrderIso.map_top, Submodule.map_top, LinearMap.range_eq_top]
      exact (D.target n).surjective
  · intro n
    obtain ⟨r₀, hr₀, hstab⟩ := D.pages.convergence.stabilization (-n)
    refine ⟨r₀, hr₀, ?_⟩
    intro r hr p
    have hi := hstab r hr (-p)
    obtain ⟨I⟩ := D.pages.convergence.limit D.pages.pages r (-p) (-n) (by omega) hi
    exact ⟨hi, ⟨IndependentResolution.limitComparison D r p n I⟩⟩

namespace IndependentResolution

section SignedRowNaturality

variable {R : Type u} [Ring R]
    {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {P' : ChainComplex (ModuleCat.{v'} Rᵐᵒᵖ) ℤ}
    {Q : ChainComplex (ModuleCat.{t} R) ℤ} {Q' : ChainComplex (ModuleCat.{t'} R) ℤ}
    {S : TensorPages P Q} {U : TensorPages P' Q'}

set_option maxHeartbeats 3000000 in
private theorem signedRowTensor_natural
    (C : RowTensorComparison P Q S) (C' : RowTensorComparison P' Q' U)
    (f : LinearChainMap P P') (g : LinearChainMap Q Q') (p : ℕ) (q : ℤ) :
    let F := originalTensorFilteredMap f g S U
    (signedRowPart C' p q).hom.hom.comp (F.pageMap S.pages U.pages 2 (-p) (-(p+q))) =
      (categoricalHomologyMap (originalRowTensorComplexMap f g (-q)) (-(p : ℤ))).comp
        (signedRowPart C p q).hom.hom := by
  let a : ℤ := -(p : ℤ)
  let b : ℤ := -q
  let F := originalTensorFilteredMap f g S U
  let G := originalRowTensorComplexMap f g b
  have hm := originalRowShortIso_middle_natural f g F rfl C C' a b (G.app a)
    (originalRowTensorHomologyIso_natural f g a b (C.flatComparison a) (C'.flatComparison a))
  exact signedRowPart_natural C C' F p q G hm

end SignedRowNaturality

section Map

variable {R : Type u} [Ring R]
  {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w,t} R} {Y : Input.{u,v',w',t'} R}
  (D : Realization T X) (E : Realization T' Y) (f : Input.Hom X Y)

private abbrev filteredTensorMap :=
  originalTensorFilteredMap f.right f.lift.extendNonnegative D.pages E.pages

private abbrev coefficientMap := originalCoefficientComplexMap f.right f.coefficient

private theorem augmentation_square
    (A : Augmentation X) (B : Augmentation Y) (i : ℤ) :
    (B.map.app i).comp ((originalTensorTotalMap f.right f.lift.extendNonnegative).app i) =
      ((coefficientMap f).app (-i)).comp (A.map.app i) := by
  apply tensorTotal_ext X.P X.extended
  intro p q h x y
  simp only [LinearMap.comp_apply, originalTensorTotalMap_tmul]
  by_cases hq : q = 0
  · subst q
    have hp : p = i := by omega
    subst p
    let e := X.Q.complex.extendXIso nonnegativeChainEmbedding (i := 0) (i' := 0) rfl
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective e.inv).mp inferInstance y
    change B.map.app i ((sumInjection Y.tensor i 0 i _).hom
      (tmul R (f.right.app (-i) x) (f.lift.extendNonnegative.app (↑(0 : ℕ)) (e.inv.hom z)))) =
      (coefficientMap f).app (-i) (A.map.app i ((sumInjection X.tensor i 0 i _).hom (tmul R x (e.inv.hom z))))
    erw [f.lift.extendNonnegative_app_inv 0 z, B.zero_component, A.zero_component]
    change tmul R (f.right.app (-i) x) (Y.Q.ε (f.lift.app 0 z)) =
      tmul R (f.right.app (-i) x) (f.coefficient (X.Q.ε z))
    rw [f.augmented z]
  · have hA := LinearMap.congr_fun (A.other_components p q i h hq) (tmul R x y)
    have hB := LinearMap.congr_fun (B.other_components p q i h hq)
      (tmul R (f.right.app (-p) x) (f.lift.extendNonnegative.app (-q) y))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hA hB
    change B.map.app i ((sumInjection Y.tensor p q i h).hom
        (tmul R (f.right.app (-p) x) (f.lift.extendNonnegative.app (-q) y))) =
      (coefficientMap f).app (-i) (A.map.app i ((sumInjection X.tensor p q i h).hom (tmul R x y)))
    rw [hB, hA, map_zero]

private theorem restriction_component_natural
    (g : LinearChainMap X.coefficient Y.coefficient) {i j : ℤ} (h : -i = j)
    (z : (reverseChain X.coefficient).X i) :
    (Y.coefficient.restrictionXIso reversal (i := i) h).hom.hom (g.app (-i) z) =
      g.app j ((X.coefficient.restrictionXIso reversal (i := i) h).hom.hom z) := by
  subst j
  rfl

set_option maxHeartbeats 1300000 in
private theorem target_square (n : ℤ) :
    (E.target n).toLinearMap.comp (categoricalHomologyMap (filteredTensorMap D E f).hom (-n)) =
      ((coefficientMap f).homologyMap n).comp (D.target n).toLinearMap := by
  let F := filteredTensorMap D E f
  let g := coefficientMap f
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (X.total.homologyπ (-n))).mp inferInstance x
  obtain ⟨y,hy,hπ⟩ := categoricalHomologyMap_formula F.hom (-n) z
  obtain ⟨s,hs,hsπ⟩ := D.target_formula n z
  obtain ⟨t,ht,htπ⟩ := E.target_formula n y
  have he : t = g.cyclesMap n s := by
    apply Subtype.ext
    change t.val = g.app n s.val
    rw [ht, hy]
    have h := LinearMap.congr_fun (augmentation_square f D.augmentation E.augmentation (-n))
      ((X.total.iCycles (-n)).hom z)
    change E.augmentation.map.app (-n) (F.hom.app (-n) ((X.total.iCycles (-n)).hom z)) =
      g.app (-(-n)) (D.augmentation.map.app (-n) ((X.total.iCycles (-n)).hom z)) at h
    rw [h, restriction_component_natural (X := X) (Y := Y) g, ← hs]
  change E.target n (categoricalHomologyMap F.hom (-n) ((X.total.homologyπ (-n)).hom z)) =
    g.homologyMap n (D.target n ((X.total.homologyπ (-n)).hom z))
  rw [hπ, htπ, hsπ, he]
  rfl

private def torLift (q : ℤ) :
    LinearChainMap (T.rightResolutions (X.P.homology q)).val.complex
      (T'.rightResolutions (Y.P.homology q)).val.complex :=
  (LinearChainMap.exists_augmentedLift (chosenRightResolution T (X.P.homology q))
    (chosenRightResolution T' (Y.P.homology q)) (categoricalHomologyMap f.right q)).choose

private theorem torLift_augmented (q : ℤ) :
    (chosenRightResolution T (X.P.homology q)).Lifts (chosenRightResolution T' (Y.P.homology q))
      (categoricalHomologyMap f.right q) (torLift (T := T) (T' := T') f q) :=
  (LinearChainMap.exists_augmentedLift (chosenRightResolution T (X.P.homology q))
    (chosenRightResolution T' (Y.P.homology q)) (categoricalHomologyMap f.right q)).choose_spec

private abbrev torMap (q : ℤ) (p : ℕ) :
    T.Tor (X.P.homology q) X.M p →ₗ[ℤ] T'.Tor (Y.P.homology q) Y.M p :=
  (tensorLinearChainMap (torLift (T := T) (T' := T') f q) f.coefficient).homologyMap p

set_option maxHeartbeats 3000000 in
private theorem second_square (p : ℕ) (q : ℤ) :
    (E.second.equiv p q).toLinearMap.comp ((filteredTensorMap D E f).pageMap
      D.pages.pages E.pages.pages 2 (-p) (-(p+q))) =
    (torMap (T := T) (T' := T') f q p).comp (D.second.equiv p q).toLinearMap := by
  let a : ℤ := -(p : ℤ)
  let b : ℤ := -q
  let F := filteredTensorMap D E f
  let C := D.second.row
  let C' := E.second.row
  let g := originalRowTensorComplexMap f.right f.lift.extendNonnegative b
  have hRow := signedRowTensor_natural C C' f.right f.lift.extendNonnegative p q
  have hOrd := originalRowOrdinary_natural (D.second.ordinary q) (E.second.ordinary q)
    f.right f.lift p b (neg_neg q)
  have hg : originalReverseMap (originalExtendedTensorMap (categoricalHomologyMap f.right (-b)) f.lift) = g := rfl
  rw [hg] at hOrd
  apply LinearMap.ext
  intro z
  let ro := (signedRowPart C p q).hom.hom
  let ro' := (signedRowPart C' p q).hom.hom
  let ord := (rowOrdinaryComparison (D.second.ordinary q) p b (neg_neg q)).hom.hom
  let ord' := (rowOrdinaryComparison (E.second.ordinary q) p b (neg_neg q)).hom.hom
  let e := ((D.second.balance q).balanceEquiv (D.second.leftQuasiIso q) (D.second.rightQuasiIso q) p).symm
  let e' := ((E.second.balance q).balanceEquiv (E.second.leftQuasiIso q) (E.second.rightQuasiIso q) p).symm
  change e' (ord' (ro' (F.pageMap D.pages.pages E.pages.pages 2 (-p) (-(p+q)) z))) =
    torMap (T := T) (T' := T') f q p (e (ord (ro z)))
  change ord'.comp (categoricalHomologyMap g a) =
    ((leftTensorLinearChainMap (categoricalHomologyMap f.right q) f.lift).homologyMap p).comp ord at hOrd
  calc
    _ = e' (ord' (categoricalHomologyMap g a (ro z))) :=
      congrArg (fun x => e' (ord' x)) (LinearMap.congr_fun hRow z)
    _ = e' ((leftTensorLinearChainMap (categoricalHomologyMap f.right q) f.lift).homologyMap p (ord (ro z))) :=
      congrArg e' (LinearMap.congr_fun hOrd (ro z))
    _ = _ := balanceInverse_natural
      (P := chosenRightResolution T (X.P.homology q)) (P' := chosenRightResolution T' (Y.P.homology q))
      (Q := X.Q) (Q' := Y.Q) (f := categoricalHomologyMap f.right q) (g := f.coefficient)
      (torLift_augmented (T := T) (T' := T') f q) f.augmented
      (D.second.balance q) (E.second.balance q) (D.second.leftQuasiIso q) (D.second.rightQuasiIso q)
      (E.second.leftQuasiIso q) (E.second.rightQuasiIso q) p (ord (ro z))


private def closedToStep (p n : ℤ) :
    (closed D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ) →ₗ[ℤ] D.piece p n :=
  (pieceEquiv D p n).toLinearMap.comp (closedClass D.pages.filtration (-p) (-n)).hom

private theorem closedToStep_surjective (p n : ℤ) : Function.Surjective (closedToStep D p n) :=
  (pieceEquiv D p n).surjective.comp
    ((ModuleCat.epi_iff_surjective (closedClass D.pages.filtration (-p) (-n))).mp
      (closedClass_epi D.pages.filtration (-p) (-n)))

private abbrev closedCycle (p n : ℤ) (z : (closed D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ)) :
    X.total.cycles (-n) :=
  X.total.liftCycles (closed D.pages.filtration (-p) (-n)).arrow (-n+1)
    (by simp) (closed_d D.pages.filtration (-p) (-n)) z

private theorem closedCycle_val (p n : ℤ) (z : (closed D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ)) :
    (X.total.iCycles (-n)).hom (closedCycle D p n z) = (closed D.pages.filtration (-p) (-n)).arrow.hom z :=
  ConcreteCategory.congr_hom (X.total.liftCycles_i (closed D.pages.filtration (-p) (-n)).arrow
    (-n+1) (by simp) (closed_d D.pages.filtration (-p) (-n))) z

private theorem closedToStep_val (p n : ℤ) (z : (closed D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ)) :
    ↑(closedToStep D p n z) = D.target n ((X.total.homologyπ (-n)).hom (closedCycle D p n z)) := by
  change (pieceEquiv D p n ((closedClass D.pages.filtration (-p) (-n)).hom z)).val = _
  rw [pieceEquiv_val]
  exact congrArg (D.target n) (ConcreteCategory.congr_hom (closedClass_arrow D.pages.filtration (-p) (-n)) z)

private theorem closedToStep_natural (p n : ℤ)
    (z : (closed D.pages.filtration (-p) (-n) : ModuleCat.{max v t} ℤ))
    (y : (closed E.pages.filtration (-p) (-n) : ModuleCat.{max v' t'} ℤ))
    (hy : (closed E.pages.filtration (-p) (-n)).arrow.hom y =
      (filteredTensorMap D E f).hom.app (-n) ((closed D.pages.filtration (-p) (-n)).arrow.hom z)) :
    (closedToStep E p n y).val = (coefficientMap f).homologyMap n (closedToStep D p n z).val := by
  let F := filteredTensorMap D E f
  let zc := closedCycle D p n z
  let yc := closedCycle E p n y
  obtain ⟨u,hu,huπ⟩ := categoricalHomologyMap_formula F.hom (-n) zc
  have he : u = yc := by
    apply (ModuleCat.mono_iff_injective (Y.total.iCycles (-n))).mp inferInstance
    change (Y.total.iCycles (-n)).hom u = (Y.total.iCycles (-n)).hom yc
    rw [hu, closedCycle_val, closedCycle_val, hy]
  change categoricalHomologyMap F.hom (-n) ((X.total.homologyπ (-n)).hom zc) =
    (Y.total.homologyπ (-n)).hom u at huπ
  rw [he] at huπ
  rw [closedToStep_val, closedToStep_val, ← huπ]
  exact LinearMap.congr_fun (target_square D E f n) ((X.total.homologyπ (-n)).hom zc)

private theorem step_mem (p n : ℤ) (x : D.piece p n) :
    (coefficientMap f).homologyMap n x.val ∈ E.piece p n := by
  let F := filteredTensorMap D E f
  obtain ⟨z,rfl⟩ := closedToStep_surjective D p n x
  obtain ⟨y,hy⟩ := originalClosed_exists F.hom F.preserves (-p) (-n) z
  rw [← closedToStep_natural D E f p n z y hy]
  exact (closedToStep E p n y).property

private def stepMap (p n : ℤ) : D.piece p n →ₗ[ℤ] E.piece p n :=
  LinearMap.codRestrict _ (((coefficientMap f).homologyMap n).comp (D.piece p n).subtype)
    (step_mem D E f p n)

private def gradedMap (p n : ℤ) : D.graded p n →ₗ[ℤ] E.graded p n :=
  (D.gradedSubmodule p n).mapQ _ (stepMap D E f p n) (fun x hx => step_mem D E f (p-1) n ⟨x.val,hx⟩)

set_option maxHeartbeats 2400000 in
private theorem limit_square (r p n : ℤ) (I : LimitComparison D r p n) (J : LimitComparison E r p n)
    (hi : Stabilized D.pages.filtration r (-p) (-n)) :
    J.equiv.toLinearMap.comp ((filteredTensorMap D E f).pageMap D.pages.pages E.pages.pages r (-p) (-n)) =
      (gradedMap D E f p n).comp I.equiv.toLinearMap := by
  let F := filteredTensorMap D E f
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (closedToPage D.pages.filtration D.pages.pages r (-p) (-n))).mp
    (closedToPage_epi _ _ _ _ _ hi.1) x
  obtain ⟨y,hy⟩ := originalClosed_exists F.hom F.preserves (-p) (-n) z
  let i := Subobject.ofLE _ _ (closed_le_almost D.pages.filtration r (-p) (-n))
  let j := Subobject.ofLE _ _ (closed_le_almost E.pages.filtration r (-p) (-n))
  have hrep : F.almostMap r (-p) (-n) (i.hom z) = j.hom y := by
    apply (ModuleCat.mono_iff_injective (almost E.pages.filtration r (-p) (-n)).arrow).mp inferInstance
    change (almost E.pages.filtration r (-p) (-n)).arrow.hom (F.almostMap r (-p) (-n) (i.hom z)) =
      (j ≫ (almost E.pages.filtration r (-p) (-n)).arrow).hom y
    rw [F.almostMap_arrow, Subobject.ofLE_arrow]
    change F.hom.app (-n) ((i ≫ (almost D.pages.filtration r (-p) (-n)).arrow).hom z) = _
    rw [Subobject.ofLE_arrow, hy]
  have hp := LinearMap.congr_fun (F.pageMap_formula D.pages.pages E.pages.pages r (-p) (-n)) (i.hom z)
  change F.pageMap D.pages.pages E.pages.pages r (-p) (-n)
      ((closedToPage D.pages.filtration D.pages.pages r (-p) (-n)).hom z) =
    (toPage E.pages.filtration r (-p) (-n) (E.pages.pages.containment r (-p) (-n))).hom
      (F.almostMap r (-p) (-n) (i.hom z)) at hp
  rw [hrep] at hp
  obtain ⟨s,hs,hsπ⟩ := I.closed_formula z
  obtain ⟨t,ht,htπ⟩ := J.closed_formula y
  have hs' : s = closedToStep D p n z :=
    Subtype.ext (hs.trans (pieceEquiv_val D p n ((closedClass D.pages.filtration (-p) (-n)).hom z)).symm)
  have ht' : t = closedToStep E p n y :=
    Subtype.ext (ht.trans (pieceEquiv_val E p n ((closedClass E.pages.filtration (-p) (-n)).hom y)).symm)
  have he : stepMap D E f p n s = t := by
    rw [hs', ht']
    exact Subtype.ext (closedToStep_natural D E f p n z y hy).symm
  change J.equiv (F.pageMap D.pages.pages E.pages.pages r (-p) (-n) _) =
    gradedMap D E f p n (I.equiv ((closedToPage D.pages.filtration D.pages.pages r (-p) (-n)).hom z))
  rw [hp, hsπ]
  change J.equiv ((closedToPage E.pages.filtration E.pages.pages r (-p) (-n)).hom y) =
    (E.gradedSubmodule p n).mkQ (stepMap D E f p n s)
  rw [htπ, he]

set_option maxHeartbeats 4500000 in
/-- The maps on the original filtered total, its pages and the augmented target. -/
private def naturalMapData
    (second : ∀ (p : ℕ) (q : ℤ),
      (E.second.equiv p q).toLinearMap.comp ((filteredTensorMap D E f).pageMap
        D.pages.pages E.pages.pages 2 (-p) (-(p+q))) =
      (torMap (T := T) (T' := T') f q p).comp (D.second.equiv p q).toLinearMap) :
    NaturalMap D E f := by
  let F := filteredTensorMap D E f
  exact {
    extended := f.lift.extendNonnegative
    extended_formula := f.lift.extendNonnegative_app_inv
    total := F.hom
    total_formula := originalTensorTotalMap_tmul f.right f.lift.extendNonnegative
    preserves_filtration := F.preserves
    almost := F.almostMap
    almost_formula := F.almostMap_arrow
    page := F.pageMap D.pages.pages E.pages.pages
    page_formula := F.pageMap_formula D.pages.pages E.pages.pages
    page_differential := F.pageMap_differential D.pages.pages E.pages.pages
    next_natural := F.next_natural D.pages.pages E.pages.pages D.pages.next E.pages.next
    right_homology := categoricalHomologyMap f.right
    right_homology_formula := categoricalHomologyMap_formula f.right
    tor := torMap (T := T) (T' := T') f
    tor_formula := fun q => ⟨torLift (T := T) (T' := T') f q, LinearMap.ext (torLift_augmented (T := T) (T' := T') f q),
      tensorLinearChainMap (torLift (T := T) (T' := T') f q) f.coefficient, fun _ => rfl, fun _ => rfl⟩
    second := second
    coefficient := coefficientMap f
    coefficient_formula := fun _ => rfl
    augmentation := augmentation_square f D.augmentation E.augmentation
    total_homology := categoricalHomologyMap F.hom
    total_homology_formula := categoricalHomologyMap_formula F.hom
    target_comparison := target_square D E f
    step := stepMap D E f
    step_formula := fun _ _ => rfl
    graded := gradedMap D E f
    graded_formula := fun _ _ => rfl
    limit_natural := fun r p n I J h _ => limit_square D E f r p n I J h }

end Map
end IndependentResolution

theorem original_resolution_naturality : IndependentResolution.Specs.Naturality.{u,v,w,t,v',w',t'} := by
  intro R _ T T' X Y D E f g
  refine ⟨LinearChainMap.exists_augmentedLift X.Q Y.Q g, ?_⟩
  intro l hl
  let k : IndependentResolution.Input.Hom X Y := ⟨f,g,l,hl⟩
  exact ⟨IndependentResolution.naturalMapData D E k (IndependentResolution.second_square D E k)⟩

namespace IndependentResolution

section LiftIndependence

variable {R : Type u} [Ring R]
  {T : CanonicalTheory.{u,v,w} R} {T' : CanonicalTheory.{u,v',w'} R}
  {X : Input.{u,v,w,t} R} {Y : Input.{u,v',w',t'} R}
  {D : Realization T X} {E : Realization T' Y}
  {f : LinearChainMap X.P Y.P} {g : X.M →ₗ[R] Y.M}
  {l m : LinearChainMap X.Q.complex Y.Q.complex} {h : X.Q.Lifts Y.Q g l} {k : X.Q.Lifts Y.Q g m}
  (F : NaturalMap D E ⟨f,g,l,h⟩) (G : NaturalMap D E ⟨f,g,m,k⟩)

private theorem tor_lift_independent : F.tor = G.tor := by
  have hH := categoricalHomologyMap_unique F.right_homology_formula G.right_homology_formula
  funext q p
  obtain ⟨s, hs, A, hA, ha⟩ := F.tor_formula q
  obtain ⟨t, ht, B, hB, hb⟩ := G.tor_formula q
  rw [← hH] at ht
  have H := LinearChainMap.augmentedLifts_homotopic
    (chosenRightResolution T (X.P.homology q)) (chosenRightResolution T' (Y.P.homology q))
    (F.right_homology q) s t (LinearMap.congr_fun hs) (LinearMap.congr_fun ht)
  have hAA : A = tensorLinearChainMap s g := LinearChainMap.eq_of_app_eq (funext hA)
  have hBB : B = tensorLinearChainMap t g := LinearChainMap.eq_of_app_eq (funext hB)
  rw [ha p, hb p, hAA, hBB]
  exact congrFun (LinearChainMap.homologyMap_eq_of_homotopic (TorBalance.tensorLinearChainMap_homotopic H g)) p

set_option maxHeartbeats 2000000 in
private theorem page_lift_independent : ∀ r p n : ℤ, 2 ≤ r → F.page r p n = G.page r p n := by
  suffices main : ∀ k : ℕ, ∀ p n : ℤ, F.page (2+k) p n = G.page (2+k) p n by
    intro r p n hr
    obtain ⟨k,rfl⟩ := Int.exists_add_of_le hr
    exact main k p n
  intro k
  induction k with
  | zero =>
    intro p n
    change F.page 2 p n = G.page 2 p n
    by_cases hp : p ≤ 0
    · let a := (-p).toNat
      let b := p-n
      have ha : -(a : ℤ) = p := by dsimp [a]; omega
      have hb : -((a : ℤ)+b) = n := by dsimp [b]; omega
      rw [← ha, ← hb]
      apply LinearMap.ext
      intro z
      apply (E.second.equiv a b).injective
      calc
        _ = F.tor b a (D.second.equiv a b z) := LinearMap.congr_fun (F.second a b) z
        _ = G.tor b a (D.second.equiv a b z) := by rw [tor_lift_independent F G]
        _ = _ := (LinearMap.congr_fun (G.second a b) z).symm
    · have hz := D.support 2 (-p) (p-n) (Or.inl (by omega))
      have he : D.pages.term 2 (-p) (p-n) =
          PageCohomology.object D.pages.filtration D.pages.pages 2 p n := by
        unfold TensorPages.term
        congr 1 <;> omega
      letI := (ModuleCat.isZero_iff_subsingleton).mp (IsZero.of_iso hz (eqToIso he.symm))
      exact LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero]
  | succ k ih =>
    intro p n
    let r : ℤ := 2 + k
    have hr : 0 ≤ r := by dsimp [r]; omega
    rw [show (2 + (↑(k+1) : ℤ)) = r+1 by dsimp [r]; omega]
    let A := PageCohomology.shortComplex D.pages.filtration D.pages.pages r hr (p-r) (n-1)
    let B := PageCohomology.shortComplex E.pages.filtration E.pages.pages r hr (p-r) (n-1)
    let I := D.pages.next.nextIso r hr (p-r) (n-1)
    let J := E.pages.next.nextIso r hr (p-r) (n-1)
    have H : F.page (r+1) (p-r+r) (n-1+1) = G.page (r+1) (p-r+r) (n-1+1) := by
      apply LinearMap.ext
      intro x
      have hx : Function.Surjective (fun z : A.cycles => I.inv.hom (A.homologyπ.hom z)) :=
        ((ModuleCat.epi_iff_surjective I.inv).mp inferInstance).comp
          ((ModuleCat.epi_iff_surjective A.homologyπ).mp inferInstance)
      obtain ⟨z,rfl⟩ := hx x
      obtain ⟨y,hy,hyπ⟩ := F.next_natural r hr (p-r) (n-1) z
      obtain ⟨u,hu,huπ⟩ := G.next_natural r hr (p-r) (n-1) z
      have he : y = u := by
        apply (ModuleCat.mono_iff_injective B.iCycles).mp inferInstance
        rw [hy, hu, ih]
      apply (ModuleCat.mono_iff_injective J.hom).mp inferInstance
      rw [hyπ, huπ, he]
    rwa [sub_add_cancel, sub_add_cancel] at H

private theorem coefficientMap_lift_independent : F.coefficient = G.coefficient :=
  LinearChainMap.eq_of_app_eq (funext fun n => (F.coefficient_formula n).trans (G.coefficient_formula n).symm)

private theorem step_lift_independent : F.step = G.step := by
  funext p n
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hf := LinearMap.congr_fun (F.step_formula p n) x
  have hg := LinearMap.congr_fun (G.step_formula p n) x
  rw [coefficientMap_lift_independent F G] at hf
  exact hf.trans hg.symm

private theorem graded_lift_independent : F.graded = G.graded := by
  funext p n
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := (D.gradedSubmodule p n).mkQ_surjective x
  have hf := LinearMap.congr_fun (F.graded_formula p n) z
  have hg := LinearMap.congr_fun (G.graded_formula p n) z
  rw [step_lift_independent F G] at hf
  exact hf.trans hg.symm

end LiftIndependence

end IndependentResolution

theorem original_resolution_lift_independence :
    IndependentResolution.Specs.LiftIndependence.{u,v,w,t,v',w',t'} := by
  intro R _ T T' X Y D E f g l m h k F G
  exact ⟨IndependentResolution.page_lift_independent F G,
    fun n => congrArg (fun x : LinearChainMap X.coefficient Y.coefficient => x.homologyMap n)
      (IndependentResolution.coefficientMap_lift_independent F G),
    IndependentResolution.step_lift_independent F G, IndependentResolution.graded_lift_independent F G⟩

namespace IndependentResolution

section InversePages

variable {R : Type u} [Ring R] {T : CanonicalTheory.{u,v,w} R}
  {X : Input.{u,v,w,t} R} {Y : Input.{u,v,w,t'} R}
  {D : Realization T X} {E : Realization T Y}
  {f : Input.Hom X Y} {g : Input.Hom Y X}
  (F : NaturalMap D E f) (G : NaturalMap E D g)

set_option maxHeartbeats 2200000 in
private theorem page_inverse_later
    (h : ∀ p n : ℤ, Function.LeftInverse (G.page 2 p n) (F.page 2 p n)) :
    ∀ r p n : ℤ, 2 ≤ r → Function.LeftInverse (G.page r p n) (F.page r p n) := by
  suffices main : ∀ k : ℕ, ∀ p n : ℤ, Function.LeftInverse (G.page (2+k) p n) (F.page (2+k) p n) by
    intro r p n hr
    obtain ⟨k,rfl⟩ := Int.exists_add_of_le hr
    exact main k p n
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro p n
    let r : ℤ := 2+k
    have hr : 0 ≤ r := by dsimp [r]; omega
    rw [show (2 + (↑(k+1) : ℤ)) = r+1 by dsimp [r]; omega]
    let A := PageCohomology.shortComplex D.pages.filtration D.pages.pages r hr (p-r) (n-1)
    let I := D.pages.next.nextIso r hr (p-r) (n-1)
    let J := E.pages.next.nextIso r hr (p-r) (n-1)
    have H : Function.LeftInverse (G.page (r+1) (p-r+r) (n-1+1)) (F.page (r+1) (p-r+r) (n-1+1)) := by
      intro x
      have hx : Function.Surjective (fun z : A.cycles => I.inv.hom (A.homologyπ.hom z)) :=
        ((ModuleCat.epi_iff_surjective I.inv).mp inferInstance).comp
          ((ModuleCat.epi_iff_surjective A.homologyπ).mp inferInstance)
      obtain ⟨z,rfl⟩ := hx x
      obtain ⟨y,hy,hyπ⟩ := F.next_natural r hr (p-r) (n-1) z
      obtain ⟨u,hu,huπ⟩ := G.next_natural r hr (p-r) (n-1) y
      have he : u = z := by
        apply (ModuleCat.mono_iff_injective A.iCycles).mp inferInstance
        rw [hu, hy]
        exact ih (p-r+r) (n-1+1) (A.iCycles.hom z)
      have hy' := congrArg J.inv.hom hyπ
      rw [ModuleCat.inv_hom_apply] at hy'
      change G.page (r+1) (p-r+r) (n-1+1)
        (F.page (r+1) (p-r+r) (n-1+1) (I.inv.hom (A.homologyπ.hom z))) =
        I.inv.hom (A.homologyπ.hom z)
      rw [hy']
      apply (ModuleCat.mono_iff_injective I.hom).mp inferInstance
      rw [huπ, he, ModuleCat.hom_inv_apply]
    rwa [sub_add_cancel, sub_add_cancel] at H

end InversePages

section ChoiceIndependence

variable {R : Type u} [Ring R] {T : CanonicalTheory.{u,v,w} R}
  {P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} {L : ℤ} {M : ModuleCat.{w} R}
  {Q : TorBalance.AugmentedResolution.{u,w,t} R M} {Q' : TorBalance.AugmentedResolution.{u,w,t'} R M}
  {b : BoundedBelow P L} {h : FlatTerms.{u,v,max w t} P} {h' : FlatTerms.{u,v,max w t'} P}

private abbrev comparisonInput (Q : TorBalance.AugmentedResolution.{u,w,t} R M)
    (h : FlatTerms.{u,v,max w t} P) : Input.{u,v,w,t} R :=
  ⟨P,L,M,Q,b,h⟩

variable {D : Realization T (comparisonInput Q h (b := b))}
  {E : Realization T (comparisonInput Q' h' (b := b))}
  {l : LinearChainMap Q.complex Q'.complex} {a : Q.Lifts Q' (LinearMap.id : M →ₗ[R] M) l}
  {m : LinearChainMap Q'.complex Q.complex} {a' : Q'.Lifts Q (LinearMap.id : M →ₗ[R] M) m}
  (F : NaturalMap D E ⟨LinearChainMap.id P,LinearMap.id,l,a⟩)
  (G : NaturalMap E D ⟨LinearChainMap.id P,LinearMap.id,m,a'⟩)

private theorem right_homology_id : F.right_homology = fun _ => LinearMap.id := by
  apply categoricalHomologyMap_unique F.right_homology_formula
  intro q z
  exact ⟨z,rfl,rfl⟩

private theorem coefficient_id : F.coefficient = LinearChainMap.id (coefficientComplex P M) := by
  apply LinearChainMap.eq_of_app_eq
  funext n
  rw [F.coefficient_formula n]
  apply tensor_hom_ext
  intros
  rfl

private theorem tor_inverse (q : ℤ) (p : ℕ) : Function.LeftInverse (G.tor q p) (F.tor q p) := by
  obtain ⟨s,hs,A,hA,ha⟩ := F.tor_formula q
  obtain ⟨t,ht,B,hB,hb⟩ := G.tor_formula q
  rw [right_homology_id F] at hs
  rw [right_homology_id G] at ht
  have hAA : A = tensorLinearChainMap s (LinearMap.id : M →ₗ[R] M) :=
    LinearChainMap.eq_of_app_eq (funext hA)
  have hBB : B = tensorLinearChainMap t (LinearMap.id : M →ₗ[R] M) :=
    LinearChainMap.eq_of_app_eq (funext hB)
  rw [ha p, hb p, hAA, hBB]
  exact LinearMap.congr_fun (TorBalance.tensor_comparison_homology_inverse
    (P := chosenRightResolution T (P.homology q)) (P' := chosenRightResolution T (P.homology q))
    (LinearMap.congr_fun hs) (LinearMap.congr_fun ht) M p)

private theorem second_page_inverse (p n : ℤ) : Function.LeftInverse (G.page 2 p n) (F.page 2 p n) := by
  intro z
  by_cases hp : p ≤ 0
  · obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -p by omega)
    let q := -n-(k : ℤ)
    have e₁ : -(k : ℤ) = p := by omega
    have e₂ : -((k : ℤ)+q) = n := by dsimp [q]; omega
    let step (i j : ℤ) := ∀ x, G.page 2 i j (F.page 2 i j x) = x
    suffices H : step (-(k : ℤ)) (-((k : ℤ)+q)) by
      rw [e₁, e₂] at H
      exact H z
    intro x
    apply (D.second.equiv k q).injective
    calc
      _ = G.tor q k (E.second.equiv k q (F.page 2 (-k) (-(k+q)) x)) :=
        LinearMap.congr_fun (G.second k q) _
      _ = G.tor q k (F.tor q k (D.second.equiv k q x)) :=
        congrArg (G.tor q k) (LinearMap.congr_fun (F.second k q) x)
      _ = _ := tor_inverse F G q k _
  · have hz := D.support 2 (-p) (p-n) (Or.inl (by omega))
    have he : D.pages.term 2 (-p) (p-n) =
        PageCohomology.object D.pages.filtration D.pages.pages 2 p n := by
      unfold TensorPages.term
      congr 1 <;> omega
    letI := (ModuleCat.isZero_iff_subsingleton).mp (IsZero.of_iso hz (eqToIso he.symm))
    exact Subsingleton.elim _ _

private theorem step_val_id (p n : ℤ) (x : D.piece p n) : (F.step p n x).val = x.val := by
  have h := LinearMap.congr_fun (F.step_formula p n) x
  rw [coefficient_id F, LinearChainMap.homologyMap_id] at h
  exact h

private theorem step_inverse (p n : ℤ) : Function.LeftInverse (G.step p n) (F.step p n) :=
  fun x => Subtype.ext ((step_val_id G p n (F.step p n x)).trans (step_val_id F p n x))

private theorem graded_inverse (p n : ℤ) : Function.LeftInverse (G.graded p n) (F.graded p n) := by
  intro x
  obtain ⟨z,rfl⟩ := (D.gradedSubmodule p n).mkQ_surjective x
  change G.graded p n (F.graded p n ((D.gradedSubmodule p n).mkQ z)) = _
  have hf := LinearMap.congr_fun (F.graded_formula p n) z
  have hg := LinearMap.congr_fun (G.graded_formula p n) (F.step p n z)
  simp only [LinearMap.comp_apply] at hf hg
  rw [hf, hg, step_inverse F G p n z]

end ChoiceIndependence
end IndependentResolution

set_option maxHeartbeats 2000000 in
private theorem choiceIndependence_of_naturality
    (naturality : IndependentResolution.Specs.Naturality.{u,v,w,t',v,w,t}) :
    IndependentResolution.Specs.ChoiceIndependence.{u,v,w,t,t'} := by
  intro R _ T P L M Q Q' b h h' D E l a F
  obtain ⟨m,a'⟩ := LinearChainMap.exists_augmentedLift Q' Q LinearMap.id
  obtain ⟨G⟩ := (naturality R T T _ _ E D
    (LinearChainMap.id P) LinearMap.id).2 m a'
  refine ⟨fun r p n hr => ?_, fun n => ?_, fun p n => ?_⟩
  · exact ⟨(IndependentResolution.page_inverse_later F G
        (IndependentResolution.second_page_inverse F G) r p n hr).injective,
      (IndependentResolution.page_inverse_later G F
        (IndependentResolution.second_page_inverse G F) r p n hr).surjective⟩
  · rw [IndependentResolution.coefficient_id F, LinearChainMap.homologyMap_id]
  · refine ⟨le_antisymm (fun x hx => ?_) (fun x hx => ?_),
        ⟨(IndependentResolution.step_inverse F G p n).injective,
          (IndependentResolution.step_inverse G F p n).surjective⟩,
        ⟨(IndependentResolution.graded_inverse F G p n).injective,
          (IndependentResolution.graded_inverse G F p n).surjective⟩⟩
    · have hv := (F.step p n ⟨x,hx⟩).property
      change (F.step p n ⟨x,hx⟩).val ∈ E.piece p n at hv
      rwa [IndependentResolution.step_val_id F p n ⟨x,hx⟩] at hv
    · have hv := (G.step p n ⟨x,hx⟩).property
      change (G.step p n ⟨x,hx⟩).val ∈ D.piece p n at hv
      rwa [IndependentResolution.step_val_id G p n ⟨x,hx⟩] at hv

theorem original_resolution_choice_independence :
    IndependentResolution.Specs.ChoiceIndependence.{u,v,w,t,t'} :=
  choiceIndependence_of_naturality original_resolution_naturality

end AdvancedHomologicalAlgebra.KunnethSpectralSequence

end IndependentResolutionProof
