import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.MaximalCohenMacaulayDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.HomDualPreservesMCM
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.FiniteLengthDuality
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
namespace AdvCommAlg.Gorenstein
open CohenMacaulay HomDualSpec

/-- Lift an isomorphism modulo a regular element in the maximal ideal. -/
lemma bijective_of_reduction_bijective {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hN : IsSMulRegular N x) (hbar : Function.Bijective (reductionMap x f)) :
    Function.Bijective f := by
  have hJ : Ideal.span {x} ≤ (⊥ : Ideal R).jacobson :=
    (Ideal.span_le.mpr (by simpa using hx)).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have hs : Function.Surjective f := by
    apply f.surjective_of_surjective_comp_mkQ (Ideal.span {x}) hJ
    intro q
    obtain ⟨p, hp⟩ := hbar.2 q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ p
    exact ⟨m, hp⟩
  refine ⟨LinearMap.ker_eq_bot.mp ?_, hs⟩
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) f.ker
    (IsNoetherian.noetherian _) ?_ hJ
  intro m hm
  have hq : (Submodule.Quotient.mk m : Reduction x M) = 0 := by
    apply hbar.1
    change Submodule.Quotient.mk (f m) = reductionMap x f 0
    rw [show f m = 0 from hm, map_zero]
    rfl
  have hm' := (Submodule.Quotient.mk_eq_zero _).mp hq
  rw [Submodule.ideal_span_singleton_smul] at hm' ⊢
  obtain ⟨a, _, ha⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm'
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨a, ?_, ha⟩
  change f a = 0
  apply hN
  change x • f a = x • (0 : N)
  rw [smul_zero, ← f.map_smul, ha]
  exact hm

/-- In dimension zero a canonical module is the residue-field injective envelope. -/
lemma canonical_envelope_of_dimension_zero {R : Type u} [CommRing R] [Nontrivial R]
    [IsNoetherianRing R] [IsLocalRing R] [IsArtinianRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W]
    (hW : IsCanonicalModule R W) (hd : ringKrullDim R = 0) :
    ∃ ι : IsLocalRing.ResidueField R →ₗ[R] W, IsInjectiveEnvelope ι := by
  haveI : Nontrivial W := hW.2.1
  have hdepthR : Depth.depth R R = 0 := by
    apply WithBot.coe_injective
    exact ((localCohenMacaulay_iff_sourceDepth R R).mp hW.1).trans
      ((Module.supportDim_self_eq_ringKrullDim R).trans hd)
  have hdepthW : Depth.depth R W = 0 := by
    apply WithBot.coe_injective
    exact ((maximalCohenMacaulay_iff_sourceDepth R W).mp hW.2.2.1).trans hd
  haveI : Injective (ModuleCat.of R W) :=
    DepthZeroInjectivity.injective_of_depth_zero_of_finite_injectiveDimension R
      hdepthR (ModuleCat.of R W) hW.2.2.2.2
  haveI : Module.Injective R W := Module.injective_module_of_injective_object R W
  let e : Depth.ResidueExt (ModuleCat.of R W) 0 ≃ₗ[IsLocalRing.ResidueField R]
      Depth.ResidueHom R W := Depth.residueLinearEquiv R
        (Ext.linearEquiv₀.trans ModuleCat.homLinearEquiv)
  have hdim : Module.finrank (IsLocalRing.ResidueField R) (Depth.ResidueHom R W) = 1 := by
    rw [← e.finrank_eq]
    have ht : Depth.moduleType R (ModuleCat.of R W) = 1 := hW.2.2.2.1
    have hdegree : Depth.depthDegree R (ModuleCat.of R W) = 0 := by
      change (Depth.depth R W).toNat = 0
      rw [hdepthW]
      rfl
    unfold Depth.moduleType at ht
    rw [hdegree] at ht
    exact ht
  haveI : Nontrivial (Depth.ResidueHom R W) := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨ι, hι⟩ := exists_ne (0 : Depth.ResidueHom R W)
  haveI : IsSimpleModule R (IsLocalRing.ResidueField R) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (R := R) (S := IsLocalRing.ResidueField R) (M := IsLocalRing.ResidueField R)
      (IsLocalRing.residue_surjective (R := R))).mpr inferInstance
  refine ⟨ι, ⟨ι.injective_of_ne_zero hι, inferInstance, ?_⟩⟩
  intro N hN
  obtain ⟨S, hS, hSN⟩ := (eq_bot_or_exists_atom_le N).resolve_left hN
  haveI : IsSimpleModule R S := isSimpleModule_iff_isAtom.mpr hS
  obtain ⟨I, hI, ⟨a⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R S)
  rw [IsLocalRing.eq_maximalIdeal hI] at a
  let j : IsLocalRing.ResidueField R →ₗ[R] W := S.subtype.comp a.symm.toLinearMap
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hι j
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) c
  have hj : j = r • ι := by
    rw [← hc, ← hr]
    exact (IsScalarTower.algebraMap_smul (IsLocalRing.ResidueField R) r ι).symm
  have hSι : S ≤ LinearMap.range ι := by
    intro s hs
    have he : j (a ⟨s, hs⟩) = s := congrArg Subtype.val (a.symm_apply_apply ⟨s, hs⟩)
    refine ⟨r • a ⟨s, hs⟩, ?_⟩
    rw [ι.map_smul]
    calc
      r • ι (a ⟨s, hs⟩) = j (a ⟨s, hs⟩) := congrArg (fun f => f (a ⟨s, hs⟩)) hj.symm
      _ = s := he
  exact fun hz => hS.ne_bot (le_bot_iff.mp (hz ▸ le_inf hSN hSι))

/-- Dimension induction for the actual evaluation map. -/
private theorem evaluation_bijective_of_dimension (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R],
    ringKrullDim R = d →
    ∀ (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    IsCanonicalModule R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    MaximalCohenMacaulay R M → Function.Bijective (envelopeEvaluation R W M) := by
  induction d with
  | zero =>
    intro R _ _ _ _ hd W _ _ _ hW M _ _ _ _ hM
    haveI : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hd
    haveI : IsArtinianRing R := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    obtain ⟨ι, hι⟩ := canonical_envelope_of_dimension_zero W hW hd
    exact envelopeEvaluation_bijective ι hι M
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
      have hb := ih Q hqdim BW hBW BM hBM.2
      obtain ⟨eM, eD, heM, heD, hsq⟩ := homDual_evaluation_comparison R W hW M hM x xs hs
      have hl : Function.Bijective (LinearMap.lcomp Q BW eM.toLinearMap) :=
        (LinearEquiv.congrLeft BW Q eM).symm.bijective
      have hbar : Function.Bijective (reductionMap x (envelopeEvaluation R W M)) := by
        have hc : Function.Bijective
            (eD.toLinearMap.comp (reductionMap x (envelopeEvaluation R W M))) := by
          rw [hsq]
          exact hl.comp hb
        exact (Function.Bijective.of_comp_iff' eD.bijective _).mp hc
      have hreg := (homDual_parameter_regular R W hW M hM x xs hs).2.2
      exact bijective_of_reduction_bijective (envelopeEvaluation R W M) x hx hreg hbar

/-- Natural biduality, including the zero module. -/
theorem maximalCM_biduality : MCMDualitySpec.bidualityType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M _ _ _ hM
  refine ⟨LinearEquiv.ofBijective (envelopeEvaluation R W M) ?_, rfl⟩
  cases subsingleton_or_nontrivial M with
  | inl hz =>
    haveI : Subsingleton ((M →ₗ[R] W) →ₗ[R] W) := inferInstance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr hn =>
    obtain ⟨d, hd⟩ := exists_nat_dimension (R := R) R
    have hdR : ringKrullDim R = d := (Module.supportDim_self_eq_ringKrullDim R).symm.trans hd
    exact evaluation_bijective_of_dimension d R hdR W hW M hM

/-- Ext¹ vanishing makes the reversed Hom sequence short exact. -/
theorem maximalCM_dual_exact : MCMDualitySpec.exactnessType.{u} := by
  intro R _ _ _ _ W _ _ _ hW A B C _ _ _ _ _ _ _ _ _ hA hB hC f g hf hg hex
  refine ⟨LinearMap.lcomp_injective_of_surjective g hg, ?_,
    LinearMap.exact_lcomp_of_exact_of_surjective W hex hg⟩
  haveI := maximalCohenMacaulay_ext_vanishing R W hW C hC 1 (by omega)
  have hzero : g.comp f = 0 := by
    ext a
    exact (hex (f a)).mpr ⟨a, rfl⟩
  let S := ModuleCat.shortComplexOfCompEqZero f g hzero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hex hf hg
  intro h
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hS (ModuleCat.of R W)
    (Ext.mk₀ (ModuleCat.ofHom h)) (n₁ := 1) (by omega) (Subsingleton.elim _ _)
  obtain ⟨l, rfl⟩ := Ext.homEquiv₀.symm.surjective a
  refine ⟨l.hom, ?_⟩
  simp only [Ext.homEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] at ha
  exact congrArg ModuleCat.Hom.hom ((Ext.mk₀_bijective _ _).1 ha)

/-- Naturality of evaluation for every linear map. -/
theorem maximalCM_biduality_naturality : MCMDualitySpec.naturalityType.{u} :=
  envelopeEvaluation_naturality

/-- The coherence identity for the self-inverse contravariant duality. -/
theorem maximalCM_biduality_triangle : MCMDualitySpec.triangleType.{u} :=
  envelopeEvaluation_triangle

/-- Biduality gives the bijection on Hom sets induced by precomposition. -/
theorem maximalCM_dual_fullyFaithful : MCMDualitySpec.fullyFaithfulType.{u} := by
  intro R _ _ _ _ W _ _ _ hW M N _ _ _ _ _ _ hM hN
  obtain ⟨eM, heM⟩ := maximalCM_biduality R W hW M hM
  obtain ⟨eN, heN⟩ := maximalCM_biduality R W hW N hN
  constructor
  · intro f g h
    ext m
    apply eN.injective
    change eN.toLinearMap (f m) = eN.toLinearMap (g m)
    rw [heN]
    ext ψ
    exact congrArg (fun k => k ψ m) h
  · intro g
    let f : M →ₗ[R] N := eN.symm.toLinearMap.comp
      ((LinearMap.lcomp R W g).comp (envelopeEvaluation R W M))
    refine ⟨f, ?_⟩
    ext ψ m
    have h := congrArg (fun k : (N →ₗ[R] W) →ₗ[R] W => k ψ)
      (eN.apply_symm_apply ((LinearMap.lcomp R W g) (envelopeEvaluation R W M m)))
    change eN.toLinearMap (f m) ψ = g ψ m at h
    rw [heN] at h
    exact h

/-- Evaluation at R identifies its bidual with End(W) by the scalar action. -/
theorem canonical_scalar_isomorphism : MCMDualitySpec.scalarType.{u} := by
  intro R _ _ _ _ W _ _ _ hW
  have hR : MaximalCohenMacaulay R R := by
    apply (maximalCohenMacaulay_iff_sourceDepth R R).mpr
    exact ((localCohenMacaulay_iff_sourceDepth R R).mp hW.1).trans
      (Module.supportDim_self_eq_ringKrullDim R)
  obtain ⟨e, he⟩ := maximalCM_biduality R W hW R hR
  let a := LinearMap.ringLmapEquivSelf R R W
  let b := e.trans (LinearEquiv.congrLeft W R a)
  have hb : ∀ r : R, b r = algebraMap R (Module.End R W) r := by
    intro r
    ext w
    change e.toLinearMap r (a.symm w) = r • w
    rw [he]
    rfl
  have hbij : Function.Bijective (Algebra.ofId R (Module.End R W)) := by
    have hf : (Algebra.ofId R (Module.End R W) : R → Module.End R W) = b :=
      funext (fun r => (hb r).symm)
    rw [hf]
    exact b.bijective
  refine ⟨AlgEquiv.ofBijective (Algebra.ofId R (Module.End R W)) hbij, ?_⟩
  intro r w
  rfl

/-- Hom duals remain finite and maximal Cohen–Macaulay, with zero adjoined. -/
theorem maximalCM_dual_preserves : MCMDualitySpec.closureType.{u} := homDual_preservesMCM

/-- GC-12: exact natural Hom duality and the scalar algebra isomorphism. -/
theorem maximalCM_exactDuality : MCMDualitySpec.exactDualityType.{u} :=
  ⟨maximalCM_dual_preserves, maximalCM_dual_exact, maximalCM_biduality,
    maximalCM_biduality_naturality, maximalCM_dual_fullyFaithful,
    maximalCM_biduality_triangle, canonical_scalar_isomorphism⟩

end AdvCommAlg.Gorenstein
