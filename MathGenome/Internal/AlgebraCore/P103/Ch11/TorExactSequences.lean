import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorExactSequences
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorBalance
import MathGenome.Internal.AlgebraCore.P103.Ch10.HorseshoeNaturality

/-! Natural long exact Tor sequences over arbitrary unital rings.
The connecting maps use the positive lift-and-differentiate convention. -/
namespace P103.Ch11.TorExactSequences
open CategoryTheory CategoryTheory.Limits
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.TorExactSequences
noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Degreewise exactness in the original Tor model; only resolution terms
are projective, and the three coefficient modules are arbitrary. -/
theorem tensorSecond_degreewise_exact {R : Type u} [Ring R]
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (P : LeftResolution Rᵐᵒᵖ A) (hP : P.IsProjective)
    {B M C : Type w} [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
    [Module R B] [Module R M] [Module R C]
    (i : B →ₗ[R] M) (p : M →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p) :
    DegreewiseExact (tensorSecondMap P.complex i) (tensorSecondMap P.complex p) := by
  intro n
  refine ⟨P103.Ch11.TorBalance.right_projective_tensor_injective (hP n) i hi, ?_⟩
  exact P103.HomTensorExactness.tensorSecond_rightExact i p he hp
    (tensorMap LinearMap.id i).toAddMonoidHom
    (tensorMap LinearMap.id p).toAddMonoidHom (fun _ _ => rfl) (fun _ _ => rfl)

/-- Assemble the adjacent-degree homology theorem and its actual zero endpoint. -/
theorem longExact_of_degreewise {S : Type u} [Ring S]
    {U V W : ChainComplex (ModuleCat.{v} S) ℕ}
    (i : U ⟶ V) (p : V ⟶ W) (hs : DegreewiseExact i p) : LongExact i p := by
  have h (n : ℕ) := P103.Ch10.HomologySequence.sequence i p hs (n+1) n rfl
  choose δ hδ huniq using h
  exact ⟨⟨δ, hδ⟩, P103.Ch10.HorseshoeNaturality.chain_bottom_exact i p hs⟩

/-- Tensor preserves the degreewise splitting of every projective horseshoe. -/
theorem first_degreewise_exact {R : Type u} [Ring R]
    {A M C : Type v} [AddCommGroup A] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C]
    {i : A →ₗ[Rᵐᵒᵖ] M} {p : M →ₗ[Rᵐᵒᵖ] C}
    {L : LeftResolution Rᵐᵒᵖ A} {N : LeftResolution Rᵐᵒᵖ C}
    (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N)
    (B : Type w) [AddCommGroup B] [Module R B] :
    DegreewiseExact (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B) := by
  apply P103.Ch10.HorseshoeNaturality.split_exact
  apply P103.Ch10.HorseshoeNaturality.split_map (tensorFunctor B)
  exact P103.Ch10.HorseshoeNaturality.projective_split _ _ _ _ _ _ _ _ H

theorem first_sequence : first_sequenceType.{u,v,w} := by
  intro R _ A M C _ _ _ _ _ _ i p hi he hp L N hL hN B _ _
  refine ⟨P103.Ch10.Horseshoe.projective_horseshoe Rᵐᵒᵖ A M C i p hi he hp L N hL hN, ?_⟩
  intro H
  exact longExact_of_degreewise _ _ (first_degreewise_exact H B)

theorem second_sequence : second_sequenceType.{u,v,w} := by
  intro R _ A _ _ P hP B M C _ _ _ _ _ _ i p hi he hp
  exact longExact_of_degreewise _ _ (tensorSecond_degreewise_exact P hP i p hi he hp)

theorem terminal : terminalType.{u,v,w} := by
  constructor
  · intro R _ A M C B _ _ _ _ _ _ _ _ i p he hp
    exact P103.HomTensorExactness.tensor_first_rightExact i p he hp
      (tensorMap i LinearMap.id).toAddMonoidHom (fun _ _ => rfl)
      (tensorMap p LinearMap.id).toAddMonoidHom (fun _ _ => rfl)
  · intro R _ A B M C _ _ _ _ _ _ _ _ i p he hp
    exact P103.HomTensorExactness.tensorSecond_rightExact i p he hp
      (tensorMap LinearMap.id i).toAddMonoidHom
      (tensorMap LinearMap.id p).toAddMonoidHom (fun _ _ => rfl) (fun _ _ => rfl)

theorem zero_identification : zero_identificationType.{u,v,w} :=
  ⟨P103.Ch11.ExtTorDefinitions.tor_zero, P103.Ch11.ExtTorDefinitions.tor_zero_natural⟩

/-- Simultaneous action on the resolution and the coefficient. -/
abbrev tensorChainMap {R : Type u} [Ring R]
    {U V : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} (l : U ⟶ V)
    {B B' : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] (g : B →ₗ[R] B') :=
  tensorFirstMap l B ≫ tensorSecondMap V g

theorem tensor_first_square {R : Type u} [Ring R]
    {U V U' V' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    (i : U ⟶ V) (i' : U' ⟶ V') (α : U ⟶ U') (β : V ⟶ V')
    {B B' : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] (g : B →ₗ[R] B')
    (h : i ≫ β = α ≫ i') :
    tensorFirstMap i B ≫ tensorChainMap β g =
      tensorChainMap α g ≫ tensorFirstMap i' B' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  change tmul R ((β.f n).hom ((i.f n).hom a)) (g b) =
    tmul R ((i'.f n).hom ((α.f n).hom a)) (g b)
  exact congrArg (fun x => tmul R x (g b)) (congrArg (fun l => (l.f n).hom a) h)

theorem tensor_second_square {R : Type u} [Ring R]
    {U V : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ} (l : U ⟶ V)
    {B M B' M' : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] [AddCommGroup B'] [Module R B']
    [AddCommGroup M'] [Module R M']
    (i : B →ₗ[R] M) (i' : B' →ₗ[R] M') (b : B →ₗ[R] B') (m : M →ₗ[R] M')
    (h : m.comp i = i'.comp b) :
    tensorSecondMap U i ≫ tensorChainMap l m =
      tensorChainMap l b ≫ tensorSecondMap V i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a x
  change tmul R ((l.f n).hom a) (m (i x)) = tmul R ((l.f n).hom a) (i' (b x))
  exact congrArg (tmul R ((l.f n).hom a)) (LinearMap.congr_fun h x)

theorem first_naturality : first_naturalityType.{u,v,w} := by
  intro R _ A M C A' M' C' i p i' p' a b c hi he hp hi' he' hp' hab hbc
    L N L' N' H H' B B' g n Tn Tm δ ε hδ hε
  obtain ⟨α, β, γ, hα, hβ, hγ, hiH, hpH⟩ :=
    P103.Ch10.HorseshoeNaturality.projective_diagram Rᵐᵒᵖ A M C A' M' C'
      i p i' p' a b c hi he hp hi' he' hp' hab hbc
      L.val N.val L'.val N'.val L.property N.property L'.property N'.property H H'
  rw [Tm.formula L L' a g α hα, Tn.formula N N' c g γ hγ]
  exact (P103.Ch10.HomologySequence.naturality
    (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B)
    (tensorFirstMap H'.inclusion B') (tensorFirstMap H'.projection B')
    (tensorChainMap α g.hom) (tensorChainMap β g.hom) (tensorChainMap γ g.hom)
    (tensor_first_square _ _ _ _ g.hom hiH)
    (tensor_first_square _ _ _ _ g.hom hpH)
    (first_degreewise_exact H B) (first_degreewise_exact H' B')
    (n+1) n rfl δ ε hδ hε).2.2.1

theorem second_naturality : second_naturalityType.{u,v,w} := by
  intro R _ A A' P P' a B M C B' M' C' i p i' p' b m c
    hi he hp hi' he' hp' hab hbc n Tn Tm δ ε hδ hε
  let l := P103.Ch10.Comparison.chainMap P.val P'.val P.property a.hom
  have hl := P103.Ch10.Comparison.chainMap_lifts P.val P'.val P.property a.hom
  rw [Tm.formula P P' a b l hl, Tn.formula P P' a c l hl]
  exact (P103.Ch10.HomologySequence.naturality
    (tensorSecondMap P.val.complex i.hom) (tensorSecondMap P.val.complex p.hom)
    (tensorSecondMap P'.val.complex i'.hom) (tensorSecondMap P'.val.complex p'.hom)
    (tensorChainMap l b.hom) (tensorChainMap l m.hom) (tensorChainMap l c.hom)
    (tensor_second_square l i.hom i'.hom b.hom m.hom (congrArg ModuleCat.Hom.hom hab))
    (tensor_second_square l p.hom p'.hom m.hom c.hom (congrArg ModuleCat.Hom.hom hbc))
    (tensorSecond_degreewise_exact P.val P.property i.hom p.hom hi he hp)
    (tensorSecond_degreewise_exact P'.val P'.property i'.hom p'.hom hi' he' hp')
    (n+1) n rfl δ ε hδ hε).2.2.1

open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.HorseshoeNaturality (DegreewiseSplit)

/-- Extension by zero preserves degreewise split short exact sequences. -/
theorem split_extend {S : Type u} [Ring S] {ι κ : Type*}
    {c : ComplexShape ι} {d : ComplexShape κ}
    {U V W : HomologicalComplex (ModuleCat.{v} S) c}
    (i : U ⟶ V) (p : V ⟶ W) (hs : DegreewiseSplit i p) (e : c.Embedding d) :
    DegreewiseSplit (HomologicalComplex.extendMap i e) (HomologicalComplex.extendMap p e) := by
  classical
  intro n
  by_cases hn : ∃ a, e.f a = n
  · obtain ⟨a, rfl⟩ := hn
    obtain ⟨h, ⟨s⟩⟩ := hs a
    have hz : (HomologicalComplex.extendMap i e).f (e.f a) ≫
        (HomologicalComplex.extendMap p e).f (e.f a) = 0 := by
      simp only [HomologicalComplex.extendMap_f _ _ rfl, Category.assoc,
        Iso.inv_hom_id_assoc]
      rw [← Category.assoc (i.f a), h, zero_comp, comp_zero]
    refine ⟨hz, ⟨{
      r := (V.extendXIso e rfl).hom ≫ s.r ≫ (U.extendXIso e rfl).inv
      s := (W.extendXIso e rfl).hom ≫ s.s ≫ (V.extendXIso e rfl).inv
      f_r := ?_
      s_g := ?_
      id := ?_ }⟩⟩
    · have hr : i.f a ≫ s.r = 𝟙 _ := s.f_r
      simp [HomologicalComplex.extendMap_f _ _ rfl, Category.assoc, reassoc_of% hr]
    · have hsg : s.s ≫ p.f a = 𝟙 _ := s.s_g
      simp [HomologicalComplex.extendMap_f _ _ rfl, Category.assoc, reassoc_of% hsg]
    · have hh := congrArg (fun k => (V.extendXIso e rfl).hom ≫ k ≫
          (V.extendXIso e rfl).inv) s.id
      simpa [HomologicalComplex.extendMap_f _ _ rfl, Category.assoc,
        Preadditive.comp_add, Preadditive.add_comp] using hh
  · have hzU := U.isZero_extend_X e n (fun a h => hn ⟨a,h⟩)
    have hzV := V.isZero_extend_X e n (fun a h => hn ⟨a,h⟩)
    have hzW := W.isZero_extend_X e n (fun a h => hn ⟨a,h⟩)
    exact ⟨hzU.eq_of_src _ _, ⟨{
      r := 0, s := 0
      f_r := hzU.eq_of_src _ _
      s_g := hzW.eq_of_src _ _
      id := hzV.eq_of_src _ _ }⟩⟩

/-- A map on each summand defines a map of total terms. No compatibility
with differentials is required for this degreewise construction. -/
def totalTermMap {S : Type u} [Ring S] {K L : ChainBicomplex.{u,v} S}
    (f : ∀ p q, (K.X p).X q ⟶ (L.X p).X q) (n : ℤ) :
    (K.total (ComplexShape.down ℤ)).X n ⟶ (L.total (ComplexShape.down ℤ)).X n :=
  K.totalDesc (fun p q h => f p q ≫ L.ιTotal (ComplexShape.down ℤ) p q n h)

@[reassoc (attr := simp)] theorem inclusion_totalTermMap
    {S : Type u} [Ring S] {K L : ChainBicomplex.{u,v} S}
    (f : ∀ p q, (K.X p).X q ⟶ (L.X p).X q) (p q n : ℤ) (h : p+q=n) :
    K.ιTotal (ComplexShape.down ℤ) p q n h ≫ totalTermMap f n =
      f p q ≫ L.ιTotal (ComplexShape.down ℤ) p q n h := by
  exact HomologicalComplex₂.ι_totalDesc _ _ _ _ _

/-- Direct-sum totalization preserves componentwise split exactness. The
splittings need not commute with either bicomplex differential. -/
theorem total_degreewise_split {S : Type u} [Ring S]
    {K L M : ChainBicomplex.{u,v} S} (i : K ⟶ L) (p : L ⟶ M)
    (hs : ∀ a b, ∃ h : (i.f a).f b ≫ (p.f a).f b = 0,
      Nonempty (ShortComplex.mk ((i.f a).f b) ((p.f a).f b) h).Splitting) :
    DegreewiseSplit (HomologicalComplex₂.total.map i (ComplexShape.down ℤ))
      (HomologicalComplex₂.total.map p (ComplexShape.down ℤ)) := by
  classical
  choose h s using hs
  let σ (a b : ℤ) := Classical.choice (s a b)
  intro n
  have hz : (HomologicalComplex₂.total.map i (ComplexShape.down ℤ)).f n ≫
      (HomologicalComplex₂.total.map p (ComplexShape.down ℤ)).f n = 0 := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    rw [HomologicalComplex₂.ιTotal_map_assoc, HomologicalComplex₂.ιTotal_map,
      ← Category.assoc, h a b, zero_comp, comp_zero]
  refine ⟨hz, ⟨{
    r := totalTermMap (fun a b => (σ a b).r) n
    s := totalTermMap (fun a b => (σ a b).s) n
    f_r := ?_
    s_g := ?_
    id := ?_ }⟩⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    rw [HomologicalComplex₂.ιTotal_map_assoc, inclusion_totalTermMap,
      ← Category.assoc, (σ a b).f_r, Category.id_comp, Category.comp_id]
  · apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    rw [inclusion_totalTermMap_assoc, HomologicalComplex₂.ιTotal_map,
      ← Category.assoc, (σ a b).s_g, Category.id_comp, Category.comp_id]
  · apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    rw [Preadditive.comp_add, inclusion_totalTermMap_assoc,
      HomologicalComplex₂.ιTotal_map, HomologicalComplex₂.ιTotal_map_assoc,
      inclusion_totalTermMap, ← Category.assoc, ← Category.assoc,
      ← Preadditive.add_comp, (σ a b).id, Category.id_comp, Category.comp_id]

/-- Total tensor sequences split in each degree when the second input does. -/
theorem ordinaryTotal_split_second {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    {D E F : ChainComplex (ModuleCat.{w} R) ℕ}
    (i : D ⟶ E) (p : E ⟶ F) (hs : DegreewiseSplit i p) :
    DegreewiseSplit (ordinaryTotalMap (𝟙 C) i) (ordinaryTotalMap (𝟙 C) p) := by
  have he := split_extend i p hs nonnegativeChainEmbedding
  have ht := total_degreewise_split
    (tensorBicomplexMap (𝟙 (extendNonnegativeChain C))
      (HomologicalComplex.extendMap i nonnegativeChainEmbedding))
    (tensorBicomplexMap (𝟙 (extendNonnegativeChain C))
      (HomologicalComplex.extendMap p nonnegativeChainEmbedding)) (fun a b =>
        (P103.Ch10.HorseshoeNaturality.split_map
          (leftTensorFunctor ((extendNonnegativeChain C).X a)) _ _ he) b)
  intro n
  simpa only [ordinaryTotalMap, tensorTotalMap, ordinaryTotal, ordinaryTensorTotal,
    tensorTotal, total, extendNonnegativeChain, extendByZero,
    HomologicalComplex.extendMap_id, HomologicalComplex.restrictionMap,
    HomologicalComplex.restriction, nonnegativeChainEmbedding]
    using ht (n : ℤ)

/-- The same assertion in the first tensor variable, over the opposite ring. -/
theorem ordinaryTotal_split_first {R : Type u} [Ring R]
    {C E F : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ}
    (D : ChainComplex (ModuleCat.{w} R) ℕ)
    (i : C ⟶ E) (p : E ⟶ F) (hs : DegreewiseSplit i p) :
    DegreewiseSplit (ordinaryTotalMap i (𝟙 D)) (ordinaryTotalMap p (𝟙 D)) := by
  have he := split_extend i p hs nonnegativeChainEmbedding
  have ht := total_degreewise_split
    (tensorBicomplexMap (HomologicalComplex.extendMap i nonnegativeChainEmbedding)
      (𝟙 (extendNonnegativeChain D)))
    (tensorBicomplexMap (HomologicalComplex.extendMap p nonnegativeChainEmbedding)
      (𝟙 (extendNonnegativeChain D))) (fun a b =>
        (P103.Ch10.HorseshoeNaturality.split_map
          (tensorFunctor ((extendNonnegativeChain D).X b)) _ _ he) a)
  intro n
  simpa only [ordinaryTotalMap, tensorTotalMap, ordinaryTotal, ordinaryTensorTotal,
    tensorTotal, total, extendNonnegativeChain, extendByZero,
    HomologicalComplex.extendMap_id, HomologicalComplex.restrictionMap,
    HomologicalComplex.restriction, nonnegativeChainEmbedding]
    using ht (n : ℤ)

/-- Simultaneous augmentation naturality in both resolution variables. -/
theorem augmentation_diagrams : augmentation_naturalType.{u,v,w} :=
  P103.Ch11.TorBalance.augmentation_natural

/-- Every commuting map of degreewise exact sequences preserves the positive
connecting map, with all ordinary homology squares as well. -/
theorem sequenceComparison_of_exact {S : Type u} [Ring S]
    {U V W U' V' W' : ChainComplex (ModuleCat.{v} S) ℕ}
    (i : U ⟶ V) (p : V ⟶ W) (i' : U' ⟶ V') (p' : V' ⟶ W')
    (a : U ⟶ U') (b : V ⟶ V') (c : W ⟶ W')
    (hs : DegreewiseExact i p) (ht : DegreewiseExact i' p')
    (hi : i ≫ b = a ≫ i') (hp : p ≫ c = b ≫ p') :
    SequenceComparison i p i' p' a b c := by
  refine ⟨hi, hp, ?_⟩
  intro n δ ε hδ hε
  exact (P103.Ch10.HomologySequence.naturality i p i' p' a b c hi hp hs ht
    (n+1) n rfl δ ε hδ hε).2.2.1

theorem balancedFirst_degreewise_exact {R : Type u} [Ring R]
    {A M C : Type v} [AddCommGroup A] [AddCommGroup M] [AddCommGroup C]
    [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ C]
    {B : Type w} [AddCommGroup B] [Module R B]
    (Q : LeftResolution R B) (hQ : Q.IsProjective)
    (i : A →ₗ[Rᵐᵒᵖ] M) (p : M →ₗ[Rᵐᵒᵖ] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p) :
    DegreewiseExact (leftTensorFirstMap i Q.complex) (leftTensorFirstMap p Q.complex) := by
  intro n
  refine ⟨?_, ?_⟩
  · change Function.Injective (tensorMap i (LinearMap.id : Q.complex.X n →ₗ[R] Q.complex.X n))
    exact P103.Ch11.TorBalance.projective_tensor_injective (hQ n) i hi
  · exact P103.HomTensorExactness.tensor_first_rightExact i p he hp
      (tensorMap i LinearMap.id).toAddMonoidHom (fun _ _ => rfl)
      (tensorMap p LinearMap.id).toAddMonoidHom (fun _ _ => rfl)

theorem balancedSecond_degreewise_exact {R : Type u} [Ring R]
    {A : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    {B M C : Type w} [AddCommGroup B] [AddCommGroup M] [AddCommGroup C]
    [Module R B] [Module R M] [Module R C]
    {i : B →ₗ[R] M} {p : M →ₗ[R] C}
    {L : LeftResolution R B} {N : LeftResolution R C}
    (H : P103.Specs.Ch10.Horseshoe.ProjectiveData i p L N) :
    DegreewiseExact (leftResolutionMap A H.inclusion) (leftResolutionMap A H.projection) := by
  apply P103.Ch10.HorseshoeNaturality.split_exact
  apply P103.Ch10.HorseshoeNaturality.split_map (leftTensorFunctor A)
  exact P103.Ch10.HorseshoeNaturality.projective_split _ _ _ _ _ _ _ _ H

@[simp] theorem tensorSecondMap_id {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :
    tensorSecondMap C (LinearMap.id : B →ₗ[R] B) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

@[simp] theorem leftTensorFirstMap_id {R : Type u} [Ring R]
    (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A]
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    leftTensorFirstMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) D = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply tensor_hom_ext
  intro a b
  rfl

@[simp] theorem tensorFirstMap_id {R : Type u} [Ring R]
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ)
    (B : Type w) [AddCommGroup B] [Module R B] :
    tensorFirstMap (𝟙 C) B = 𝟙 _ :=
  ((tensorFunctor B).mapHomologicalComplex (ComplexShape.down ℕ)).map_id C

@[simp] theorem leftTensorMap_id_second {R : Type u} [Ring R]
    {A A' : Type v} [AddCommGroup A] [Module Rᵐᵒᵖ A]
    [AddCommGroup A'] [Module Rᵐᵒᵖ A'] (f : A →ₗ[Rᵐᵒᵖ] A')
    (D : ChainComplex (ModuleCat.{w} R) ℕ) :
    leftTensorMap f (𝟙 D) = leftTensorFirstMap f D := by
  change leftTensorFirstMap f D ≫
    ((leftTensorFunctor A').mapHomologicalComplex (ComplexShape.down ℕ)).map (𝟙 D) = _
  rw [((leftTensorFunctor A').mapHomologicalComplex (ComplexShape.down ℕ)).map_id D,
    Category.comp_id]

/-- Two commuting connecting squares become the commuting connecting square
under the induced identification between the two outside models. -/
theorem connecting_transport
    {S : Type u} [Ring S]
    {TU LU RU TW LW RW : Type v}
    [AddCommGroup TU] [Module S TU]
    [AddCommGroup LU] [Module S LU]
    [AddCommGroup RU] [Module S RU]
    [AddCommGroup TW] [Module S TW]
    [AddCommGroup LW] [Module S LW]
    [AddCommGroup RW] [Module S RW]
    (uL : TU ≃ₗ[S] LU) (uR : TU ≃ₗ[S] RU)
    (wL : TW ≃ₗ[S] LW) (wR : TW ≃ₗ[S] RW)
    (δT : TW →ₗ[S] TU) (δL : LW →ₗ[S] LU) (δR : RW →ₗ[S] RU)
    (hL : uL.toLinearMap.comp δT = δL.comp wL.toLinearMap)
    (hR : uR.toLinearMap.comp δT = δR.comp wR.toLinearMap) :
    (uL.symm.trans uR).toLinearMap.comp δL =
      δR.comp (wL.symm.trans wR).toLinearMap := by
  ext x
  change uR (uL.symm (δL x)) = δR (wR (wL.symm x))
  have hx : uL.symm (δL x) = δT (wL.symm x) := by
    apply uL.injective
    simpa using (LinearMap.congr_fun hL (wL.symm x)).symm
  rw [hx]
  exact LinearMap.congr_fun hR (wL.symm x)


theorem balance_compatibility : balance_compatibilityType.{u,v,w} := by
  constructor
  · intro R _ A M C B _ _ _ _ _ _ _ _ i p hi he hp L N Q hL hN hQ H α β γ
    have hs := P103.Ch10.HorseshoeNaturality.projective_split _ _ _ _ _ _ _ _ H
    have ht := P103.Ch10.HorseshoeNaturality.split_exact _ _
      (ordinaryTotal_split_first Q.complex H.inclusion H.projection hs)
    have hb := balancedFirst_degreewise_exact Q hQ i p hi he hp
    have hai := augmentation_diagrams R A M B B L H.middle Q Q i LinearMap.id
      H.inclusion (𝟙 Q.complex) H.augmentation_inclusion
      (P103.Ch10.Comparison.chainLift_id Q) α β
    have hap := augmentation_diagrams R M C B B H.middle N Q Q p LinearMap.id
      H.projection (𝟙 Q.complex) H.augmentation_projection
      (P103.Ch10.Comparison.chainLift_id Q) β γ
    refine ⟨longExact_of_degreewise _ _ ht, longExact_of_degreewise _ _ hb, ?_, ?_⟩
    · apply sequenceComparison_of_exact _ _ _ _ _ _ _ ht (first_degreewise_exact H B)
      · simpa only [tensorSecondMap_id, Category.comp_id] using hai.1
      · simpa only [tensorSecondMap_id, Category.comp_id] using hap.1
    · apply sequenceComparison_of_exact _ _ _ _ _ _ _ ht hb
      · simpa only [leftTensorMap_id_second] using hai.2
      · simpa only [leftTensorMap_id_second] using hap.2
  · intro R _ A B M C _ _ _ _ _ _ _ _ i p hi he hp P L N hP hL hN H α β γ
    have hs := P103.Ch10.HorseshoeNaturality.projective_split _ _ _ _ _ _ _ _ H
    have ht := P103.Ch10.HorseshoeNaturality.split_exact _ _
      (ordinaryTotal_split_second P.complex H.inclusion H.projection hs)
    have hb := balancedSecond_degreewise_exact (A := A) H
    have hd := tensorSecond_degreewise_exact P hP i p hi he hp
    have hai := augmentation_diagrams R A A B M P P L H.middle LinearMap.id i
      (𝟙 P.complex) H.inclusion (P103.Ch10.Comparison.chainLift_id P)
      H.augmentation_inclusion α β
    have hap := augmentation_diagrams R A A M C P P H.middle N LinearMap.id p
      (𝟙 P.complex) H.projection (P103.Ch10.Comparison.chainLift_id P)
      H.augmentation_projection β γ
    refine ⟨longExact_of_degreewise _ _ ht, longExact_of_degreewise _ _ hb, ?_, ?_⟩
    · apply sequenceComparison_of_exact _ _ _ _ _ _ _ ht hd
      · simpa only [tensorFirstMap_id, Category.comp_id, Category.id_comp] using hai.1
      · simpa only [tensorFirstMap_id, Category.comp_id, Category.id_comp] using hap.1
    · apply sequenceComparison_of_exact _ _ _ _ _ _ _ ht hb
      · simpa only [leftTensorMap, leftTensorFirstMap_id, Category.id_comp] using hai.2
      · simpa only [leftTensorMap, leftTensorFirstMap_id, Category.id_comp] using hap.2

theorem connecting_linear : connecting_linearType.{u,v,w} := by
  constructor
  · intro K _ A M C i p hi he hp L N H B n Tn Tm δ hδ r x
    have hh := first_naturality
      K A M C A M C i p i p (𝟙 A) (𝟙 M) (𝟙 C)
      hi he hp hi he hp (by simp) (by simp)
      L N L N H H B B (scalarMap B r) n Tn Tm δ δ hδ hδ
    exact (LinearMap.congr_fun hh x).symm
  · intro K _ A P B M C i p hi he hp n Tn Tm δ hδ r x
    have hh := second_naturality
      K A A P P (𝟙 A) B M C B M C i p i p
      (scalarMap B r) (scalarMap M r) (scalarMap C r)
      hi he hp hi he hp (scalarMap_naturality i r).symm
      (scalarMap_naturality p r).symm n Tn Tm δ δ hδ hδ
    exact (LinearMap.congr_fun hh x).symm

/-- Transport exactness through the actual final-term isomorphism. -/
theorem exact_post_equiv {X Y Z W : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
    (f : X →+ Y) (g : Y →+ Z) (e : Z ≃+ W) (h : Function.Exact f g) :
    Function.Exact f (e.toAddMonoidHom.comp g) := by
  intro y
  change e (g y) = 0 ↔ ∃ x, f x = y
  have hh : e (g y) = 0 ↔ g y = 0 := by
    rw [← e.map_zero]
    exact e.injective.eq_iff
  exact hh.trans (h y)

/-- Transport the next exact term through a commuting zero-degree square. -/
theorem exact_equiv_middle {X Y Z Y' Z' : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup Y'] [AddCommGroup Z']
    (f : X →+ Y) (g : Y →+ Z) (e : Y ≃+ Y') (e' : Z ≃+ Z') (k : Y' →+ Z')
    (h : Function.Exact f g) (hc : ∀ y, k (e y) = e' (g y)) :
    Function.Exact (e.toAddMonoidHom.comp f) k := by
  intro y
  constructor
  · intro hy
    have hz : g (e.symm y) = 0 := e'.injective (by
      rw [map_zero, ← hc, e.apply_symm_apply, hy])
    obtain ⟨x, hx⟩ := (h (e.symm y)).mp hz
    exact ⟨x, by change e (f x) = y; rw [hx, e.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    change k (e (f x)) = 0
    rw [hc, (h (f x)).mpr ⟨x, rfl⟩, map_zero]

/-- The final positive-degree arrow, transported by the actual Tor-zero
augmentation quotient, has the source's positive representative formula. -/
theorem first_tensor_splice : first_tensor_spliceType.{u,v,w} := by
  intro R _ A M C _ _ _ _ _ _ i p hi he hp L N hL hN B _ _ H
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence
    (tensorFirstMap H.inclusion B) (tensorFirstMap H.projection B)
    (first_degreewise_exact H B) 1 0 rfl
  obtain ⟨eL, heL⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R A L B
  obtain ⟨eM, heM⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R M H.middle B
  have hc (x : TorWith L B 0) :
      tensorMap i (LinearMap.id : B →ₗ[R] B) (eL x) =
        eM (homologyMap (tensorFirstMap H.inclusion B) 0 x) := by
    have hh := P103.Ch11.ExtTorDefinitions.tor_zero_natural R A M L H.middle B B
      i LinearMap.id H.inclusion H.augmentation_inclusion eL eM heL heM x
    simpa only [tensorSecondMap_id, Category.comp_id] using hh.symm
  have ht := P103.HomTensorExactness.tensor_first_rightExact i p he hp
    (tensorMap i (LinearMap.id : B →ₗ[R] B)).toAddMonoidHom (fun _ _ => rfl)
    (tensorMap p (LinearMap.id : B →ₗ[R] B)).toAddMonoidHom (fun _ _ => rfl)
  refine ⟨eL.toAddMonoidHom.comp δ.toAddMonoidHom, ?_, ?_, ht.1, ht.2, ?_⟩
  · exact exact_post_equiv _ _ eL hδ.2.2.1
  · exact exact_equiv_middle _ _ eL eM _ hδ.2.2.2 hc
  · intro z b a hb ha
    change eL (δ (homologyClass _ 1 z)) = _
    rw [hδ.1 z b a hb ha, heL]

/-- The same quotient transport in the original right-resolution model. -/
theorem second_tensor_splice : second_tensor_spliceType.{u,v,w} := by
  intro R _ A _ _ P hP B M C _ _ _ _ _ _ i p hi he hp
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence
    (tensorSecondMap P.complex i) (tensorSecondMap P.complex p)
    (tensorSecond_degreewise_exact P hP i p hi he hp) 1 0 rfl
  obtain ⟨eB, heB⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R A P B
  obtain ⟨eM, heM⟩ := P103.Ch11.ExtTorDefinitions.tor_zero R A P M
  have hc (x : TorWith P B 0) :
      tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i (eB x) =
        eM (homologyMap (tensorSecondMap P.complex i) 0 x) := by
    have hh := P103.Ch11.ExtTorDefinitions.tor_zero_natural R A A P P B M
      LinearMap.id i (𝟙 P.complex) (P103.Ch10.Comparison.chainLift_id P)
      eB eM heB heM x
    simpa only [tensorFirstMap_id, Category.id_comp] using hh.symm
  have ht := P103.HomTensorExactness.tensorSecond_rightExact i p he hp
    (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i).toAddMonoidHom
    (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) p).toAddMonoidHom (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨eB.toAddMonoidHom.comp δ.toAddMonoidHom, ?_, ?_, ht.1, ht.2, ?_⟩
  · exact exact_post_equiv _ _ eB hδ.2.2.1
  · exact exact_equiv_middle _ _ eB eM _ hδ.2.2.2 hc
  · intro z b a hb ha
    change eB (δ (homologyClass _ 1 z)) = _
    rw [hδ.1 z b a hb ha, heB]

/-- Actual balance equivalences conjugate all connecting maps with
no change to the source's positive sign. -/
theorem balanced_connecting : balanced_connectingType.{u,v,w} := by
  constructor
  · intro R _ A M C B _ _ _ _ _ _ _ _ i p hi he hp L N Q hL hN hQ H
    obtain ⟨α, hαL, hαR⟩ := P103.Ch11.TorBalance.balance R A B L Q hL hQ
    obtain ⟨β, _, _⟩ := P103.Ch11.TorBalance.balance R M B H.middle Q H.projective hQ
    obtain ⟨γ, hγL, hγR⟩ := P103.Ch11.TorBalance.balance R C B N Q hN hQ
    refine ⟨α, γ, hαL, hαR, hγL, hγR, ?_⟩
    intro n δ ε hδ hε
    obtain ⟨hT, _, hleft, hright⟩ :=
      balance_compatibility.1 R A M C B i p hi he hp L N Q hL hN hQ H α β γ
    obtain ⟨δT, hδT⟩ := hT.1
    have hleft' := hleft.2.2 n (δT n) δ (hδT n).1 hδ
    have hright' := hright.2.2 n (δT n) ε (hδT n).1 hε
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := (hγL (n+1)).surjective x
    change balanceEquiv α hαL hαR n (δ (homologyMap γ.left (n+1) z)) =
      ε (balanceEquiv γ hγL hγR (n+1) (homologyMap γ.left (n+1) z))
    have hzL := congrArg (fun f => f.toAddMonoidHom z) hleft'
    have hzR := congrArg (fun f => f.toAddMonoidHom z) hright'
    change homologyMap α.left n (δT n z) = δ (homologyMap γ.left (n+1) z) at hzL
    change homologyMap α.right n (δT n z) = ε (homologyMap γ.right (n+1) z) at hzR
    rw [← hzL, P103.Ch11.TorBalance.balanceEquiv_apply_left,
      P103.Ch11.TorBalance.balanceEquiv_apply_left]
    exact hzR
  · intro R _ A B M C _ _ _ _ _ _ _ _ i p hi he hp P L N hP hL hN H
    obtain ⟨α, hαL, hαR⟩ := P103.Ch11.TorBalance.balance R A B P L hP hL
    obtain ⟨β, _, _⟩ := P103.Ch11.TorBalance.balance R A M P H.middle hP H.projective
    obtain ⟨γ, hγL, hγR⟩ := P103.Ch11.TorBalance.balance R A C P N hP hN
    refine ⟨α, γ, hαL, hαR, hγL, hγR, ?_⟩
    intro n δ ε hδ hε
    obtain ⟨hT, _, hleft, hright⟩ :=
      balance_compatibility.2 R A B M C i p hi he hp P L N hP hL hN H α β γ
    obtain ⟨δT, hδT⟩ := hT.1
    have hleft' := hleft.2.2 n (δT n) δ (hδT n).1 hδ
    have hright' := hright.2.2 n (δT n) ε (hδT n).1 hε
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := (hγL (n+1)).surjective x
    change balanceEquiv α hαL hαR n (δ (homologyMap γ.left (n+1) z)) =
      ε (balanceEquiv γ hγL hγR (n+1) (homologyMap γ.left (n+1) z))
    have hzL := congrArg (fun f => f.toAddMonoidHom z) hleft'
    have hzR := congrArg (fun f => f.toAddMonoidHom z) hright'
    change homologyMap α.left n (δT n z) = δ (homologyMap γ.left (n+1) z) at hzL
    change homologyMap α.right n (δT n z) = ε (homologyMap γ.right (n+1) z) at hzR
    rw [← hzL, P103.Ch11.TorBalance.balanceEquiv_apply_left,
      P103.Ch11.TorBalance.balanceEquiv_apply_left]
    exact hzR

end
end P103.Ch11.TorExactSequences
