import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.HomDualPreservesMCM
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.MaximalCohenMacaulayExt
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.HomDetection

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
namespace AdvCommAlg.Gorenstein
open CohenMacaulay HomDualSpec

/-- Finiteness of Hom uses Noetherianity of the finite target. -/
lemma homDual_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M W : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup W] [Module R W] [Module.Finite R W] :
    Module.Finite R (M →ₗ[R] W) := inferInstance

/-- Regularity of the target passes to every Hom into it. -/
lemma homDual_regular {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) (hW : IsSMulRegular W x) :
    IsSMulRegular (M →ₗ[R] W) x := by
  intro f g h
  ext m
  exact hW (DFunLike.congr_fun h m)

/-- Reduction commutes with precomposition. -/
theorem homDual_reduction_natural : HomDualSpec.naturalityType.{u} := by
  intro R _ x M N W _ _ _ _ _ _ f g
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m => rfl

/-- In particular, reduction of evaluation is evaluation after comparison. -/
theorem homDual_reduction_evaluation : HomDualSpec.evaluationType.{u} := by
  intro R _ x M W _ _ _ _ e he m f
  rw [he]
  rfl

/-- Postcomposition with the quotient of the target, descended in the source. -/
def homDual_reduce {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) :
    (M →ₗ[R] W) →ₗ[R]
      (Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x W) where
  toFun := reductionMap x
  map_add' f g := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m => rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m => rfl

/-- Exactness of Hom lifts every map into the quotient of a regular target. -/
lemma homDual_quotient_lift {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) (hW : IsSMulRegular W x)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) 1)]
    (f : M →ₗ[R] QuotSMulTop x W) :
    ∃ g : M →ₗ[R] W, (x • (⊤ : Submodule R W)).mkQ.comp g = f := by
  let hreg : IsSMulRegular (ModuleCat.of R W) x := hW
  haveI : Subsingleton (Ext (ModuleCat.of R M) ((ModuleCat.of R W).smulShortComplex x).X₁ 1) :=
    (inferInstance : Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) 1))
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ (ModuleCat.of R M)
    hreg.smulShortComplex_shortExact (Ext.mk₀ (ModuleCat.ofHom f))
    (zero_add 1) (Subsingleton.elim _ _)
  obtain ⟨g, rfl⟩ := Ext.homEquiv₀.symm.surjective a
  refine ⟨g.hom, ?_⟩
  simp only [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] at ha
  have he := (Ext.mk₀_bijective _ _).1 ha
  exact congrArg ModuleCat.Hom.hom he

/-- The kernel consists exactly of scalar multiples of maps. -/
lemma homDual_reduce_ker {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) (hW : IsSMulRegular W x) :
    LinearMap.ker (homDual_reduce M W x) =
      Ideal.span {x} • (⊤ : Submodule R (M →ₗ[R] W)) := by
  let e := Depth.principalQuotientEquiv (ModuleCat.of R W) x
  apply le_antisymm
  · intro f hf
    have hz : (x • (⊤ : Submodule R W)).mkQ.comp f = 0 := by
      ext m
      apply e.injective
      have he := DFunLike.congr_fun hf (Submodule.Quotient.mk m)
      exact he
    let hreg : IsSMulRegular (ModuleCat.of R W) x := hW
    have hext : (Ext.mk₀ (ModuleCat.ofHom f)).comp
        (Ext.mk₀ (ModuleCat.of R W |>.smulShortComplex x).g) (add_zero 0) = 0 := by
      rw [Ext.mk₀_comp_mk₀]
      have hz' : ModuleCat.ofHom f ≫ (ModuleCat.of R W |>.smulShortComplex x).g = 0 :=
        ModuleCat.hom_ext hz
      rw [hz', Ext.mk₀_zero]
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ (ModuleCat.of R M)
      hreg.smulShortComplex_shortExact (Ext.mk₀ (ModuleCat.ofHom f)) hext
    obtain ⟨g, rfl⟩ := Ext.homEquiv₀.symm.surjective a
    simp only [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] at ha
    have hg := congrArg ModuleCat.Hom.hom ((Ext.mk₀_bijective _ _).1 ha)
    rw [Submodule.ideal_span_singleton_smul]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨g.hom, Submodule.mem_top, hg⟩
  · rw [Submodule.ideal_span_singleton_smul]
    intro f hf
    obtain ⟨g, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hf
    change homDual_reduce M W x (x • g) = 0
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      change (Ideal.span {x} • (⊤ : Submodule R W)).mkQ (x • g m) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [Submodule.ideal_span_singleton_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

lemma homDual_reduce_surjective {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) (hW : IsSMulRegular W x)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) 1)] :
    Function.Surjective (homDual_reduce M W x) := by
  intro f
  let e := Depth.principalQuotientEquiv (ModuleCat.of R W) x
  let f' := e.symm.toLinearMap.comp ((f.restrictScalars R).comp
    (Ideal.span {x} • (⊤ : Submodule R M)).mkQ)
  obtain ⟨g, hg⟩ := homDual_quotient_lift M W x hW f'
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
    have he := congrArg e (DFunLike.congr_fun hg m)
    change e (Submodule.Quotient.mk (g m)) =
      e (e.symm (f (Submodule.Quotient.mk m))) at he
    rw [e.apply_symm_apply] at he
    change (Submodule.Quotient.mk (g m) : Reduction x W) = f (Submodule.Quotient.mk m)
    simpa only [e, Depth.principalQuotientEquiv, Submodule.quotEquivOfEq_mk] using he

/-- A general regular-target comparison, requiring exactly Ext¹ vanishing. -/
noncomputable def homDualReductionEquiv {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) (hW : IsSMulRegular W x)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) 1)] :
    Reduction x (M →ₗ[R] W) ≃ₗ[R ⧸ Ideal.span {x}]
      (Reduction x M →ₗ[R ⧸ Ideal.span {x}] Reduction x W) := by
  let p : Submodule R (M →ₗ[R] W) := Ideal.span {x} • ⊤
  have hp : p = (homDual_reduce M W x).ker := (homDual_reduce_ker M W x hW).symm
  let l := p.liftQ (homDual_reduce M W x) hp.le
  have hi : Function.Injective l := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' _ _ hp)
  have hs : Function.Surjective l := by
    intro f
    obtain ⟨g, hg⟩ := homDual_reduce_surjective M W x hW f
    exact ⟨Submodule.Quotient.mk g, hg⟩
  exact (LinearEquiv.ofBijective l ⟨hi, hs⟩).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

@[simp] lemma homDualReductionEquiv_mk {R : Type u} [CommRing R]
    (M W : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module R W] (x : R) (hW : IsSMulRegular W x)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) 1)]
    (f : M →ₗ[R] W) :
    homDualReductionEquiv M W x hW (Submodule.Quotient.mk f) = reductionMap x f := rfl

/-- The comparison for every first parameter, with Ext vanishing proved upstream. -/
theorem homDual_reduction : HomDualSpec.reductionType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M _ _ _ hM x xs hs
  haveI : Nontrivial W := hW.2.1
  have hreg := firstParameter_regular_maximalCM W hW.2.2.1 x xs hs
  haveI := maximalCohenMacaulay_ext_vanishing R W hW M hM 1 (by omega)
  exact ⟨homDualReductionEquiv M W x hreg, homDualReductionEquiv_mk M W x hreg⟩

/-- A parameter is regular on M, D(M), and D²(M), including when M is zero. -/
theorem homDual_parameter_regular : HomDualSpec.regularityType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M _ _ _ hM x xs hs
  haveI : Nontrivial W := hW.2.1
  have hreg := firstParameter_regular_maximalCM W hW.2.2.1 x xs hs
  refine ⟨?_, homDual_regular M W x hreg, homDual_regular (M →ₗ[R] W) W x hreg⟩
  cases subsingleton_or_nontrivial M with
  | inl h => exact fun _ _ _ => Subsingleton.elim _ _
  | inr h => exact firstParameter_regular_maximalCM M hM x xs hs

/-- Lift the maximal CM condition through a common regular parameter. -/
lemma maximalCM_of_reduction {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (P : Type u) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Nontrivial P] (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hR : IsSMulRegular R x)
    (hP : IsSMulRegular P x)
    (hbar : letI := principalQuotientLocalRing x hx
      MaximalCohenMacaulay (R ⧸ Ideal.span {x}) (Reduction x P)) :
    MaximalCohenMacaulay R P := by
  letI := principalQuotientLocalRing x hx
  let Q := R ⧸ Ideal.span {x}
  let B := Reduction x P
  haveI : Nontrivial B := quotient_nontrivial R P _
    (Ideal.span_le.mpr (by simpa using hx))
  let e := Depth.principalQuotientEquiv (ModuleCat.of R P) x
  haveI : Nontrivial (QuotSMulTop x P) := e.nontrivial
  have hb := maximalCM_dimension B hbar
  have hlocB : LocalCohenMacaulay R B :=
    (localCohenMacaulay_of_surjective_iff B Ideal.Quotient.mk_surjective).mpr hb.2
  have hlocP : LocalCohenMacaulay R P :=
    (localCohenMacaulay_quotient_regular R P x hx hP).mpr
      ((localCohenMacaulay_congr e).mpr hlocB)
  have hdim : dimension R P = ringKrullDim R := by
    have hdrop := (dimension_quotient_regular R P x hx hP).2
    have he : dimension R (QuotSMulTop x P) = dimension Q B :=
      (Module.supportDim_eq_of_equiv e).trans
        (dimension_of_surjective B Ideal.Quotient.mk_surjective)
    rw [he, hb.1,
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hR hx] at hdrop
    exact hdrop.symm
  apply (maximalCohenMacaulay_iff_sourceDepth R P).mpr
  exact ((localCohenMacaulay_iff_sourceDepth R P).mp hlocP).trans hdim

/-- Dimension induction simultaneously proves nonvanishing and closure under duality. -/
private theorem homDual_preserves_of_dimension (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R],
    ringKrullDim R = d →
    ∀ (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    IsCanonicalModule R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    MaximalCohenMacaulay R M →
    Nontrivial (M →ₗ[R] W) ∧ MaximalCohenMacaulay R (M →ₗ[R] W) := by
  induction d with
  | zero =>
    intro R _ _ _ _ hd W _ _ _ hW M _ _ _ _ hM
    haveI : Nontrivial W := hW.2.1
    have hdepth : Depth.depth R W = 0 := by
      apply WithBot.coe_injective
      exact ((maximalCohenMacaulay_iff_sourceDepth R W).mp hW.2.2.1).trans hd
    have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R W) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson _)).symm
    obtain ⟨p, hp, hmp⟩ :=
      (Depth.grade_zero_iff_exists_associatedPrime (IsLocalRing.maximalIdeal R) W hproper).mp hdepth
    have hp' : p = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hp.isPrime.ne_top) hmp
    obtain ⟨f, hf⟩ := Depth.exists_nonzero_map_of_maximal_associated R M W (hp' ▸ hp)
    haveI : Nontrivial (M →ₗ[R] W) := nontrivial_of_ne f 0 hf
    refine ⟨inferInstance, (maximalCohenMacaulay_iff_sourceDepth R _).mpr ?_⟩
    apply le_antisymm
    · exact (Depth.depth_le_supportDim (M →ₗ[R] W)).trans
        (Module.supportDim_le_ringKrullDim R _)
    · rw [hd]
      exact WithBot.coe_le_coe.mpr (by simp)
  | succ d ih =>
    intro R _ _ _ _ hd W _ _ _ hW M _ _ _ _ hM
    haveI : Nontrivial W := hW.2.1
    obtain ⟨xs, hs⟩ := exists_systemOfParameters R R
    cases xs with
    | nil =>
      have hz := (systemOfParameters_nil_iff R R).mp hs
      rw [dimension, Module.supportDim_self_eq_ringKrullDim, hd] at hz
      norm_cast at hz
    | cons x xs =>
      have hx := hs.1 x (by simp)
      have hRM : MaximalCohenMacaulay R R := by
        apply (maximalCohenMacaulay_iff_sourceDepth R R).mpr
        exact ((localCohenMacaulay_iff_sourceDepth R R).mp hW.1).trans
          (Module.supportDim_self_eq_ringKrullDim R)
      have hR := firstParameter_regular_maximalCM R hRM x xs hs
      have hMreg := firstParameter_regular_maximalCM M hM x xs hs
      have hWreg := firstParameter_regular_maximalCM W hW.2.2.1 x xs hs
      letI := principalQuotientLocalRing x hx
      let Q := R ⧸ Ideal.span {x}
      let BM := Reduction x M
      let BW := Reduction x W
      have hqdim : ringKrullDim Q = d := by
        have he := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hR hx
        rw [hd] at he
        apply ENat.WithBot.add_one_cancel.mp
        simpa only [Nat.cast_add, Nat.cast_one] using he
      have hBW : IsCanonicalModule Q BW := canonical_reduction R W hW x xs hs
      have hBM := maximalCM_quotient M hM x hx hR hMreg
      haveI : Nontrivial BM := hBM.1
      have hdual := ih Q hqdim BW hBW BM hBM.2
      haveI : Nontrivial (BM →ₗ[Q] BW) := hdual.1
      haveI := maximalCohenMacaulay_ext_vanishing R W hW M hM 1 (by omega)
      let e := homDualReductionEquiv M W x hWreg
      haveI : Nontrivial (Reduction x (M →ₗ[R] W)) := e.nontrivial
      haveI : Nontrivial (M →ₗ[R] W) := by
        by_contra hn
        haveI : Subsingleton (M →ₗ[R] W) := not_nontrivial_iff_subsingleton.mp hn
        exact not_subsingleton (Reduction x (M →ₗ[R] W)) inferInstance
      have hbar : MaximalCohenMacaulay Q (Reduction x (M →ₗ[R] W)) := by
        apply (maximalCohenMacaulay_iff_depth_eq Q _).mpr
        rw [IsLocalRing.depth_eq_of_linearEquiv e]
        exact (maximalCohenMacaulay_iff_depth_eq Q _).mp hdual.2
      exact ⟨inferInstance, maximalCM_of_reduction (M →ₗ[R] W) x hx hR
        (homDual_regular M W x hWreg) hbar⟩

/-- Hom into a canonical module preserves finite MCM modules and detects zero. -/
theorem homDual_preservesMCM : HomDualSpec.preservesMCMType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M _ _ _ hM
  refine ⟨inferInstance, ?_⟩
  cases subsingleton_or_nontrivial M with
  | inl hz =>
    haveI : Subsingleton (M →ₗ[R] W) := inferInstance
    exact ⟨Or.inl inferInstance, ⟨fun h => False.elim (not_nontrivial _ h),
      fun h => False.elim (not_nontrivial _ h)⟩⟩
  | inr hn =>
    obtain ⟨d, hd⟩ := exists_nat_dimension (R := R) R
    have hdR : ringKrullDim R = d :=
      (Module.supportDim_self_eq_ringKrullDim R).symm.trans hd
    have h := homDual_preserves_of_dimension d R hdR W hW M hM
    exact ⟨h.2, ⟨fun _ => hn, fun _ => h.1⟩⟩

/-- The full evaluation square follows on representatives from the reduction formulas. -/
theorem homDual_evaluation_square : HomDualSpec.evaluationSquareType.{u} := by
  intro R _ x M W _ _ _ _ eM eD hM hD
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ m =>
    apply LinearMap.ext
    intro p
    induction p using Submodule.Quotient.induction_on with
    | _ f =>
      change eD (Submodule.Quotient.mk (envelopeEvaluation R W M m))
        (Submodule.Quotient.mk f) = eM (Submodule.Quotient.mk f) (Submodule.Quotient.mk m)
      rw [hD, hM]
      rfl

/-- Both comparisons and their evaluation square, with no Hom-comparison hypothesis. -/
theorem homDual_evaluation_comparison : HomDualSpec.evaluationComparisonType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M _ _ _ hM x xs hs
  have hdual := (homDual_preservesMCM R W hW M hM).2.1
  obtain ⟨eM, heM⟩ := homDual_reduction R W hW M hM x xs hs
  obtain ⟨eD, heD⟩ := homDual_reduction R W hW (M →ₗ[R] W) hdual x xs hs
  exact ⟨eM, eD, heM, heD, homDual_evaluation_square R x M W eM eD heM heD⟩

end AdvCommAlg.Gorenstein
