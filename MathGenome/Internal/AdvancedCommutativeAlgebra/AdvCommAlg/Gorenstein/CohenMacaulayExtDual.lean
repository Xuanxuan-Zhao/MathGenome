import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CohenMacaulayExtDual
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.CohenMacaulayExtConcentration
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.ExtLocalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
namespace AdvCommAlg.Gorenstein.CMExtDual
open ConcentratedChangeOfRings FiniteExtDetection
variable {R : Type u} [CommRing R]

/-- Exactness immediately before multiplication proves injectivity. -/
lemma regular_dual_of_vanishing (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ)
    [Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x M)) (ModuleCat.of R R) c)] :
    IsSMulRegular (Dual M c) x := by
  change Function.Injective (LinearMap.lsmul R (Dual M c) x)
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  change x • a = 0 at ha
  haveI : Subsingleton (Ext (M.smulShortComplex x).X₃ (ModuleCat.of R R) c) :=
    (inferInstance : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x M)) (ModuleCat.of R R) c))
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₂
    hx.smulShortComplex_shortExact (ModuleCat.of R R) a (by
      change (Ext.mk₀ (x • 𝟙 M)).comp a (zero_add c) = 0
      simpa only [Ext.mk₀_smul,
        Ext.smul_comp, Ext.mk₀_id_comp] using ha)
  rw [Subsingleton.elim b 0] at hb
  simpa using hb.symm

/-- Exactness identifies the kernel of the connecting homomorphism. -/
lemma connecting_eq_zero_iff (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) (a : Dual M c) :
    connecting M x hx c a = 0 ↔ a ∈ x • (⊤ : Submodule R (Dual M c)) := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁
      hx.smulShortComplex_shortExact (ModuleCat.of R R) a (by omega) ha
    change (Ext.mk₀ (x • 𝟙 M)).comp b (zero_add c) = a at hb
    exact ⟨b, trivial, by simpa only [ModuleCat.smulShortComplex_f_eq_smul_id,
      Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp] using hb⟩
  · rintro ⟨b, _, rfl⟩
    change hx.smulShortComplex_shortExact.extClass.comp (x • b) (Nat.add_comm 1 c) = 0
    have he : x • b = (Ext.mk₀ (M.smulShortComplex x).f).comp b (zero_add c) := by
      change x • b = (Ext.mk₀ (x • 𝟙 M)).comp b (zero_add c)
      simp only [ModuleCat.smulShortComplex_f_eq_smul_id, Ext.mk₀_smul,
        Ext.smul_comp, Ext.mk₀_id_comp]
    rw [he]
    exact hx.smulShortComplex_shortExact.extClass_comp_assoc b

/-- Vanishing immediately after the connecting map makes it surjective. -/
lemma connecting_surjective (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) [Subsingleton (Dual M (c + 1))] :
    Function.Surjective (connecting M x hx c) := by
  intro a
  haveI : Subsingleton (Ext (M.smulShortComplex x).X₂ (ModuleCat.of R R) (c + 1)) :=
    (inferInstance : Subsingleton (Dual M (c + 1)))
  exact Ext.contravariant_sequence_exact₃ hx.smulShortComplex_shortExact
    (ModuleCat.of R R) a (Subsingleton.elim _ _) (by omega)


/-- The quotient of the connecting homomorphism. -/
def quotientConnecting (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) :
    QuotSMulTop x (Dual M c) →ₗ[R]
      Ext (ModuleCat.of R (QuotSMulTop x M)) (ModuleCat.of R R) (c + 1) :=
  (x • (⊤ : Submodule R (Dual M c))).liftQ (connecting M x hx c)
    (fun a ha => (connecting_eq_zero_iff M x hx c a).mpr ha)

lemma quotientConnecting_bijective (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) [Subsingleton (Dual M (c + 1))] :
    Function.Bijective (quotientConnecting M x hx c) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply Submodule.ker_liftQ_eq_bot
    intro a ha
    exact (connecting_eq_zero_iff M x hx c a).mp ha
  · intro a
    obtain ⟨b, hb⟩ := connecting_surjective M x hx c a
    exact ⟨Submodule.Quotient.mk b, hb⟩

/-- The canonical comparison, linear for the quotient-ring actions. -/
def reductionEquiv (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) [Subsingleton (Dual M (c + 1))] :
    QuotSMulTop x (Dual M c) ≃ₗ[R ⧸ Ideal.span {x}] ReducedExt M x c :=
  LinearEquiv.ofBijective
    (show QuotSMulTop x (Dual M c) →ₗ[R ⧸ Ideal.span {x}] ReducedExt M x c from
    { toFun := quotientConnecting M x hx c
      map_add' := (quotientConnecting M x hx c).map_add
      map_smul' := by
        intro r a
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
        change quotientConnecting M x hx c (s • a) = _
        rw [map_smul]
        exact (firstExt_smul_of_base (Ideal.Quotient.mk (Ideal.span {x}))
          (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
          (ModuleCat.of R R) (c + 1) s (quotientConnecting M x hx c a)).symm })
    (quotientConnecting_bijective M x hx c)

@[simp] lemma reductionEquiv_mk (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) [Subsingleton (Dual M (c + 1))] (a : Dual M c) :
    firstExtAddEquiv _ _ _ _ (reductionEquiv M x hx c (Submodule.Quotient.mk a)) =
      connecting M x hx c a := rfl

/-- The S-linear form is useful for dimension and depth. -/
def reductionLinearEquiv (M : ModuleCat.{u} R) (x : R)
    (hx : IsSMulRegular M x) (c : ℕ) [Subsingleton (Dual M (c + 1))] :
    QuotSMulTop x (Dual M c) ≃ₗ[R]
      Ext (ModuleCat.of R (QuotSMulTop x M)) (ModuleCat.of R R) (c + 1) :=
  LinearEquiv.ofBijective _ (quotientConnecting_bijective M x hx c)


section Local
variable [IsNoetherianRing R] [IsLocalRing R]

/-- A simple quotient contributes a nonzero top Ext class. The preceding
Ext of the submodule vanishes; in degree zero use injectivity of Hom. -/
lemma finiteLength_nontrivial (hG : LocalGorenstein R)
    (s : ℕ) (hs : ringKrullDim R = (s : WithBot ℕ∞))
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Nontrivial M → Nontrivial (Dual (ModuleCat.of R M) s) := by
  induction hM with
  | @of_subsingleton A _ _ _ =>
    intro hnt
    exact False.elim (@not_nontrivial A inferInstance hnt)
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _
    let A := ModuleCat.of R (M ⧸ N)
    obtain ⟨e⟩ := simpleModule_residue_equiv (R := R) (M ⧸ N)
    obtain ⟨b⟩ := localGorenstein_ext_equiv R hG s hs
    haveI : Nontrivial (Depth.ResidueExt (ModuleCat.of R R) s) :=
      b.toEquiv.nontrivial
    haveI : Nontrivial (Dual A s) :=
      (ExtProfile.firstArgumentExtEquiv (A := A)
        (B := ModuleCat.of R (IsLocalRing.ResidueField R)) e (ModuleCat.of R R) s).toEquiv.nontrivial
    let T := ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
      (by ext; simp)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
      (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
    haveI : Epi T.g := hT.epi_g
    let f : Dual A s →ₗ[R] Dual (ModuleCat.of R M) s :=
      (Ext.mk₀ T.g).precompOfLinear R _ (zero_add s)
    apply Function.Injective.nontrivial (f := f)
    cases s with
    | zero => exact Ext.precomp_mk₀_injective_of_epi _ T.g
    | succ k =>
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro a ha
      haveI := CMExtConcentration.finiteLength_vanishing hG (k + 1) hs N hN k (by omega)
      obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hT (ModuleCat.of R R) a ha
        (n₀ := k) (by omega)
      rw [Subsingleton.elim z 0] at hz
      simpa using hz.symm

/-- Support containment bounds the dual dimension. -/
lemma dual_dimension_le (M : ModuleCat.{u} R) [Module.Finite R M] (c : ℕ) :
    Module.supportDim R (Dual M c) ≤ Module.supportDim R M := by
  exact Order.krullDim_le_of_strictMono
    (fun p => ⟨p.val, ExtLocalization.support_subset R M (ModuleCat.of R R) c p.property⟩)
    (fun {_ _} h => h)

/-- Nonzero finite modules have nonnegative support dimension. -/
lemma supportDim_nonneg (M : Type u) [AddCommGroup M] [Module R M] [Nontrivial M] :
    (0 : WithBot ℕ∞) ≤ Module.supportDim R M := by
  rw [← WithBot.coe_unbot _ (Module.supportDim_ne_bot_of_nontrivial R M)]
  exact WithBot.coe_le_coe.mpr zero_le

/-- The dimension of a regular quotient, with a natural-number witness. -/
lemma quotient_dimension (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ) (he : Module.supportDim R M = (e : WithBot ℕ∞))
    (x : R) (hm : x ∈ IsLocalRing.maximalIdeal R) (hx : IsSMulRegular M x) :
    ∃ n : ℕ, e = n + 1 ∧
      Module.supportDim R (QuotSMulTop x M) = (n : WithBot ℕ∞) := by
  obtain ⟨hQ, hd⟩ := CohenMacaulay.dimension_quotient_regular R M x hm hx
  haveI := hQ
  change Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M at hd
  rw [he] at hd
  cases e with
  | zero =>
    have h : (1 : WithBot ℕ∞) ≤ 0 := by
      calc 1 ≤ Module.supportDim R (QuotSMulTop x M) + 1 :=
             le_add_of_nonneg_left (supportDim_nonneg (QuotSMulTop x M))
           _ = 0 := hd
    norm_num at h
  | succ n =>
    refine ⟨n, rfl, ENat.WithBot.add_one_cancel.mp ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hd

/-- Transport local CM along an ordinary linear equivalence. -/
lemma localCM_of_equiv {A B : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R A] [Module.Finite R B]
    [Nontrivial A] [Nontrivial B] (f : A ≃ₗ[R] B)
    (hB : CohenMacaulay.LocalCohenMacaulay R B) :
    CohenMacaulay.LocalCohenMacaulay R A := by
  rw [CohenMacaulay.localCohenMacaulay_iff_depth_eq,
    CohenMacaulay.dimension, Module.supportDim_eq_of_equiv f,
    IsLocalRing.depth_eq_of_iso f.toModuleIso]
  exact (CohenMacaulay.localCohenMacaulay_iff_depth_eq R B).mp hB

/-- The dual is nonzero CM with the original dimension, by dimension induction. -/
lemma dual_properties_by_dimension (hG : LocalGorenstein R)
    (s : ℕ) (hs : ringKrullDim R = (s : WithBot ℕ∞)) (e : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
      CohenMacaulay.LocalCohenMacaulay R M →
      Module.supportDim R M = (e : WithBot ℕ∞) →
      Nontrivial (Dual M (s - e)) ∧
        CohenMacaulay.LocalCohenMacaulay R (Dual M (s - e)) ∧
        Module.supportDim R (Dual M (s - e)) = (e : WithBot ℕ∞) := by
  induction e with
  | zero =>
    intro M _ _ hCM he
    have hlen : IsFiniteLength R M :=
      (CohenMacaulay.dimension_zero_iff_finiteLength R M).mp he
    haveI : Nontrivial (Dual M s) := finiteLength_nontrivial hG s hs M hlen inferInstance
    have hd : Module.supportDim R (Dual M s) = 0 :=
      le_antisymm (by simpa only [he, Nat.cast_zero] using dual_dimension_le M s)
        (supportDim_nonneg (Dual M s))
    have hCM' : CohenMacaulay.LocalCohenMacaulay R (Dual M s) := by
      apply (CohenMacaulay.localCohenMacaulay_iff_sourceDepth R (Dual M s)).mpr
      change (Depth.depth R (Dual M s) : WithBot ℕ∞) = Module.supportDim R (Dual M s)
      rw [hd]
      apply le_antisymm
      · simpa only [hd] using Depth.depth_le_supportDim (R := R) (Dual M s)
      · exact WithBot.coe_le_coe.mpr zero_le
    simpa only [Nat.sub_zero, Nat.cast_zero] using
      (show Nontrivial (Dual M s) ∧ CohenMacaulay.LocalCohenMacaulay R (Dual M s) ∧
        Module.supportDim R (Dual M s) = 0 from ⟨inferInstance, hCM', hd⟩)
  | succ n ih =>
    intro M _ _ hCM he
    have hbound : n + 1 ≤ s := cohenMacaulay_dimension_le R hG M hCM s (n + 1) hs he
    have hdepth : Depth.depth R M ≠ 0 := by
      intro hz
      have h := (CohenMacaulay.localCohenMacaulay_iff_sourceDepth R M).mp hCM
      change (Depth.depth R M : WithBot ℕ∞) = Module.supportDim R M at h
      rw [hz, he] at h
      norm_cast at h
    obtain ⟨x, hm, hx⟩ : ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular M x := by
      by_contra! h
      exact hdepth ((Depth.grade_zero_iff_no_regular _ M
        (Depth.maximalIdeal_smul_ne_top R M)).mpr h)
    let Q := ModuleCat.of R (QuotSMulTop x M)
    obtain ⟨hQ, hdim⟩ := CohenMacaulay.dimension_quotient_regular R M x hm hx
    haveI := hQ
    have hCMQ := (CohenMacaulay.localCohenMacaulay_quotient_regular R M x hm hx).mp hCM
    have heQ : Module.supportDim R Q = (n : WithBot ℕ∞) := by
      change Module.supportDim R Q + 1 = Module.supportDim R M at hdim
      rw [he] at hdim
      apply ENat.WithBot.add_one_cancel.mp
      simpa only [Nat.cast_add, Nat.cast_one] using hdim
    let c := s - (n + 1)
    have hcodim : s - n = c + 1 := by dsimp [c]; omega
    obtain ⟨hD', hCMD', hdimD'⟩ := ih Q hCMQ heQ
    rw [hcodim] at hD' hCMD' hdimD'
    haveI := hD'
    haveI : Subsingleton (Dual M (c + 1)) :=
      cohenMacaulay_ext_vanishing R hG M hCM s (n + 1) hs he (c + 1) (by dsimp [c]; omega)
    haveI : Subsingleton (Dual Q c) :=
      cohenMacaulay_ext_vanishing R hG Q hCMQ s n hs heQ c (by omega)
    have hreg : IsSMulRegular (Dual M c) x := regular_dual_of_vanishing M x hx c
    let f := reductionLinearEquiv M x hx c
    haveI : Nontrivial (QuotSMulTop x (Dual M c)) := f.toEquiv.nontrivial
    haveI : Nontrivial (Dual M c) :=
      Function.Surjective.nontrivial (Submodule.mkQ_surjective (x • (⊤ : Submodule R (Dual M c))))
    have hCMquot : CohenMacaulay.LocalCohenMacaulay R (QuotSMulTop x (Dual M c)) :=
      localCM_of_equiv f hCMD'
    have hCMD := (CohenMacaulay.localCohenMacaulay_quotient_regular R (Dual M c)
      x hm hreg).mpr hCMquot
    have hdimD := (CohenMacaulay.dimension_quotient_regular R (Dual M c) x hm hreg).2
    change Module.supportDim R (QuotSMulTop x (Dual M c)) + 1 =
      Module.supportDim R (Dual M c) at hdimD
    rw [Module.supportDim_eq_of_equiv f, hdimD'] at hdimD
    exact ⟨inferInstance, hCMD, by simpa only [Nat.cast_add, Nat.cast_one] using hdimD.symm⟩

end Local
end AdvCommAlg.Gorenstein.CMExtDual

namespace AdvCommAlg.Gorenstein
open CMExtDual

/-- GC-09: the codimension Ext dual is nonzero, finite, and CM of dimension e. -/
theorem cohenMacaulay_ext_dual : CMExtDualSpecs.dualPropertiesType.{u} := by
  intro R _ _ _ hG M _ _ hCM s e hs he
  exact ⟨cohenMacaulay_dimension_le R hG M hCM s e hs he, inferInstance,
    dual_properties_by_dimension hG s hs e M hCM he⟩

/-- GC-09: reduction by every M-regular element of the maximal ideal.
The displayed value fixes the isomorphism as the canonical connecting map. -/
theorem cohenMacaulay_ext_reduction : CMExtDualSpecs.reductionType.{u} := by
  intro R _ _ _ hG M _ _ hCM s e hs he x hm hx
  obtain ⟨n, rfl, heQ⟩ := quotient_dimension M e he x hm hx
  have hbound : n + 1 ≤ s := cohenMacaulay_dimension_le R hG M hCM s (n + 1) hs he
  let Q := ModuleCat.of R (QuotSMulTop x M)
  haveI := (CohenMacaulay.dimension_quotient_regular R M x hm hx).1
  have hCMQ := (CohenMacaulay.localCohenMacaulay_quotient_regular R M x hm hx).mp hCM
  have hcodim : s - n = s - (n + 1) + 1 := by omega
  haveI : Subsingleton (Dual M (s - (n + 1) + 1)) :=
    cohenMacaulay_ext_vanishing R hG M hCM s (n + 1) hs he _ (by omega)
  haveI : Subsingleton (Dual Q (s - (n + 1))) :=
    cohenMacaulay_ext_vanishing R hG Q hCMQ s n hs heQ _ (by omega)
  exact ⟨regular_dual_of_vanishing M x hx _, reductionEquiv M x hx _, fun _ => rfl⟩

/-- The canonical reduction maps commute with pullback in the source module. -/
theorem cohenMacaulay_ext_connecting_natural : CMExtDualSpecs.connectingNaturalityType.{u} := by
  intro R _ M M' x hx hx' f c a
  have h := ShortComplex.ShortExact.extClass_naturality
    hx.smulShortComplex_shortExact hx'.smulShortComplex_shortExact
      (Depth.FirstSurvivingExt.smulShortComplexMap x f.hom)
  change hx.smulShortComplex_shortExact.extClass.comp
      ((Ext.mk₀ f).comp a (zero_add c)) (Nat.add_comm 1 c) =
    (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map x f.hom))).comp
      (hx'.smulShortComplex_shortExact.extClass.comp a (Nat.add_comm 1 c)) _
  rw [← Ext.comp_assoc_of_second_deg_zero]
  change hx.smulShortComplex_shortExact.extClass.comp (Ext.mk₀ f) (add_zero 1) =
    (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map x f.hom))).comp
      hx'.smulShortComplex_shortExact.extClass (zero_add 1) at h
  erw [h]
  exact Ext.comp_assoc _ _ _ (zero_add 1) (Nat.add_comm 1 c) (by omega)

end AdvCommAlg.Gorenstein
