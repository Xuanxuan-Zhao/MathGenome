import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtScalarActions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.FirstSurvivingExt

universe u
open scoped Pointwise
open CategoryTheory CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency.types false

namespace AdvCommAlg.Depth.FirstSurvivingExt

variable {R : Type u} [CommRing R]

lemma connectingMap_nil (N M : ModuleCat.{u} R)
    (h : RingTheory.Sequence.IsRegular M []) (f : N →ₗ[R] Quotient M []) :
    connectingMap N M [] h f =
      Ext.mk₀ (ModuleCat.ofHom ((nilQuotientEquiv M).toLinearMap.comp f)) := rfl

lemma connectingMap_cons (N M : ModuleCat.{u} R) (a : R) (xs : List R)
    (h : RingTheory.Sequence.IsRegular M (a :: xs)) (f : N →ₗ[R] Quotient M (a :: xs)) :
    connectingMap N M (a :: xs) h f =
      (connectingMap N (ModuleCat.of R (QuotSMulTop a M)) xs
        ((RingTheory.Sequence.isRegular_cons_iff M a xs).mp h).2
        ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs).toLinearMap.comp f)).comp
          ((RingTheory.Sequence.isRegular_cons_iff M a xs).mp h).1.smulShortComplex_shortExact.extClass
            rfl := rfl

theorem vanishing [IsNoetherianRing R] (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] (xs : List R)
    (h : RingTheory.Sequence.IsRegular M xs)
    (hmem : ∀ a ∈ xs, a ∈ Module.annihilator R N)
    (i : ℕ) (hi : i < xs.length) : Subsingleton (Ext N M i) := by
  apply ModuleCat.subsingleton_ext_of_lt_depth
  rw [← grade_eq_extDepth]
  apply lt_of_lt_of_le (show (i : ℕ∞) < xs.length from by exact_mod_cast hi)
  by_cases hI : Module.annihilator R N • (⊤ : Submodule R M) = ⊤
  · rw [grade_of_smul_eq_top _ _ hI]
    exact le_top
  · rw [grade_of_smul_ne_top _ _ hI]
    exact le_sSup ⟨xs, h, hmem, rfl⟩

lemma postHom_bijective {U V : Type u} [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V] (N : ModuleCat.{u} R) (e : U ≃ₗ[R] V) :
    Function.Bijective (postHom N e.toLinearMap) := by
  constructor
  · intro f g he
    ext n
    exact e.injective (LinearMap.congr_fun he n)
  · intro f
    exact ⟨e.symm.toLinearMap.comp f, by ext; simp [postHom]⟩

lemma connectingMap_bijective [IsNoetherianRing R] (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] (xs : List R)
    (h : RingTheory.Sequence.IsRegular M xs)
    (hmem : ∀ a ∈ xs, a ∈ Module.annihilator R N) :
    Function.Bijective (connectingMap N M xs h) := by
  induction xs generalizing M with
  | nil =>
    exact Ext.linearEquiv₀.symm.bijective.comp
      (ModuleCat.homLinearEquiv.symm.bijective.comp
        (postHom_bijective N (nilQuotientEquiv M)))
  | cons a xs ih =>
    have ha := (RingTheory.Sequence.isRegular_cons_iff M a xs).mp h
    let V := ModuleCat.of R (QuotSMulTop a M)
    let hS := ha.1.smulShortComplex_shortExact
    have hz := vanishing N M (a :: xs) h hmem xs.length (by simp)
    have hinj : Function.Injective (hS.extClass.postcomp N
        (show xs.length + 1 = (a :: xs).length from rfl)) := by
      apply (AddCommGrpCat.mono_iff_injective (AddCommGrpCat.ofHom
        (hS.extClass.postcomp N (show xs.length + 1 = (a :: xs).length from rfl)))).mp
      exact (Ext.covariant_sequence_exact₃' N hS xs.length (xs.length + 1) rfl).mono_g
        ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr hz).eq_zero_of_src _)
    have hsurj : Function.Surjective (hS.extClass.postcomp N
        (show xs.length + 1 = (a :: xs).length from rfl)) := by
      intro x
      apply Ext.covariant_sequence_exact₁ N hS x ?_ rfl
      change x.comp (Ext.mk₀ (a • 𝟙 M)) (add_zero _) = 0
      exact (ExtScalarActions.scalar_eq_postcomposition R N M a _ x).symm.trans
        (ExtScalarActions.annihilator_smul_eq_zero R N M a
          (hmem a (by simp)) _ x)
    exact (show Function.Bijective (hS.extClass.postcompOfLinear R N rfl) from
      ⟨hinj, hsurj⟩).comp
      ((ih V ha.2 (fun b hb => hmem b (by simp [hb]))).comp
        (postHom_bijective N
          (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs)))

theorem comparison [IsNoetherianRing R] (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] (xs : List R)
    (h : RingTheory.Sequence.IsRegular M xs)
    (hmem : ∀ a ∈ xs, a ∈ Module.annihilator R N) :
    ∃ e : Ext N M xs.length ≃ₗ[R] (N →ₗ[R] Quotient M xs),
      ∀ f, e.symm f = connectingMap N M xs h f := by
  exact ⟨(LinearEquiv.ofBijective (connectingMap N M xs h)
    (connectingMap_bijective N M xs h hmem)).symm, fun _ => rfl⟩

theorem naturalityLeft (N N' M : ModuleCat.{u} R) (xs : List R)
    (h : RingTheory.Sequence.IsRegular M xs) (g : N' →ₗ[R] N)
    (f : N →ₗ[R] Quotient M xs) :
    connectingMap N' M xs h (f.comp g) =
      (Ext.mk₀ (ModuleCat.ofHom g)).comp (connectingMap N M xs h f) (zero_add _) := by
  induction xs generalizing M with
  | nil => rw [connectingMap_nil, connectingMap_nil, Ext.mk₀_comp_mk₀]; rfl
  | cons a xs ih =>
    rw [connectingMap_cons, connectingMap_cons]
    rw [show (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs).toLinearMap.comp
      (f.comp g) = ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs).toLinearMap.comp f).comp g
      from rfl, ih]
    exact Ext.comp_assoc _ _ _ (zero_add _) rfl (by simp)

def smulShortComplexMap {M M' : ModuleCat.{u} R} (a : R) (g : M →ₗ[R] M') :
    M.smulShortComplex a ⟶ M'.smulShortComplex a where
  τ₁ := ModuleCat.ofHom g
  τ₂ := ModuleCat.ofHom g
  τ₃ := ModuleCat.ofHom (QuotSMulTop.map a g)
  comm₁₂ := by ext m; exact (g.map_smul a m).symm
  comm₂₃ := by ext; rfl

lemma nilQuotientEquiv_naturality {M M' : ModuleCat.{u} R} (g : M →ₗ[R] M') :
    (nilQuotientEquiv M').toLinearMap.comp (quotientMap [] g) =
      g.comp (nilQuotientEquiv M).toLinearMap := by
  apply Submodule.quot_hom_ext
  intro m
  rfl

theorem naturalityRight (N M M' : ModuleCat.{u} R) (xs : List R)
    (h : RingTheory.Sequence.IsRegular M xs) (h' : RingTheory.Sequence.IsRegular M' xs)
    (g : M →ₗ[R] M') (f : N →ₗ[R] Quotient M xs) :
    connectingMap N M' xs h' ((quotientMap xs g).comp f) =
      (connectingMap N M xs h f).comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero _) := by
  induction xs generalizing M M' with
  | nil =>
    rw [connectingMap_nil, connectingMap_nil, Ext.mk₀_comp_mk₀]
    congr 1
    apply ModuleCat.hom_ext
    change (nilQuotientEquiv M').toLinearMap.comp ((quotientMap [] g).comp f) =
      g.comp ((nilQuotientEquiv M).toLinearMap.comp f)
    rw [← LinearMap.comp_assoc, nilQuotientEquiv_naturality, LinearMap.comp_assoc]
  | cons a xs ih =>
    have ha := (RingTheory.Sequence.isRegular_cons_iff M a xs).mp h
    have ha' := (RingTheory.Sequence.isRegular_cons_iff M' a xs).mp h'
    let V := ModuleCat.of R (QuotSMulTop a M)
    let V' := ModuleCat.of R (QuotSMulTop a M')
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a xs
    let e' := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M' a xs
    have hq : e'.toLinearMap.comp ((quotientMap (a :: xs) g).comp f) =
        (quotientMap (M := V) (M' := V') xs (QuotSMulTop.map a g)).comp
          (e.toLinearMap.comp f) := by
      rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
      congr 1
      exact Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner_naturality a xs g
    rw [connectingMap_cons, connectingMap_cons, hq,
      ih V V' ha.2 ha'.2 (QuotSMulTop.map a g) (e.toLinearMap.comp f)]
    let x := connectingMap N V xs ha.2 (e.toLinearMap.comp f)
    let c : Ext V M 1 := ha.1.smulShortComplex_shortExact.extClass
    let c' : Ext V' M' 1 := ha'.1.smulShortComplex_shortExact.extClass
    have hc : (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map a g))).comp c' (zero_add 1) =
        c.comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1) :=
      (ShortComplex.ShortExact.extClass_naturality
      ha.1.smulShortComplex_shortExact ha'.1.smulShortComplex_shortExact
        (smulShortComplexMap a g)).symm
    change (x.comp (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map a g))) (add_zero _)).comp c' rfl =
      (x.comp c rfl).comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero _)
    calc
      _ = x.comp ((Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map a g))).comp c'
          (zero_add 1)) rfl := Ext.comp_assoc_of_second_deg_zero _ _ _ rfl
      _ = x.comp (c.comp (Ext.mk₀ (ModuleCat.ofHom g)) (add_zero 1)) rfl :=
        congrArg (fun z : Ext V M' 1 => x.comp z rfl) hc
      _ = _ := (Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm

end AdvCommAlg.Depth.FirstSurvivingExt
