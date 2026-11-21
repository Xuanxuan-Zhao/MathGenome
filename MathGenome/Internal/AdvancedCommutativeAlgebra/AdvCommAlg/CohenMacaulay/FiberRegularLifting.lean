import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FiberRegularLifting
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.LocalFlatnessCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions

namespace AdvCommAlg.CohenMacaulay
open scoped TensorProduct Pointwise
open P103.Ch12.FiniteLengthTorVanishing
noncomputable section
set_option linter.style.haveILetI false
universe u v w t

/-- Naturality of tensoring an endomorphism in the first factor. -/
lemma tensor_endomorphism_naturality {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N]
    {A : Type w} [AddCommGroup A] [Module R A]
    {B : Type t} [AddCommGroup B] [Module R B]
    (f : N →ₗ[R] N) (g : A →ₗ[R] B) (z : N ⊗[R] A) :
    g.lTensor N (f.rTensor A z) = f.rTensor B (g.lTensor N z) := by
  have h := (LinearMap.lTensor_comp_rTensor N f g).trans
    (LinearMap.rTensor_comp_lTensor N f g).symm
  exact LinearMap.congr_fun h z

/-- Injectivity in the two outer terms of a short exact tensor sequence. -/
lemma tensor_endomorphism_injective_extension {R : Type u} [CommRing R]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Flat R N]
    {A B C : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : N →ₗ[R] N) (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p)
    (hA : Function.Injective (f.rTensor A))
    (hC : Function.Injective (f.rTensor C)) :
    Function.Injective (f.rTensor B) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hpz : p.lTensor N z = 0 := hC <| by
    rw [← tensor_endomorphism_naturality, hz, map_zero, map_zero]
  obtain ⟨a, rfl⟩ := (Module.Flat.lTensor_exact N he z).mp hpz
  have hai := Module.Flat.lTensor_preserves_injective_linearMap (M := N) i hi
  have ha : f.rTensor A a = 0 := hai <| by
    rw [tensor_endomorphism_naturality, hz, map_zero]
  rw [(injective_iff_map_eq_zero _).mp hA a ha, map_zero]

/-- The residue-field test propagates through all finite-length R-modules. -/
lemma tensor_endomorphism_injective_finiteLength {R : Type u} [CommRing R]
    [IsLocalRing R] {N : Type v} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (f : N →ₗ[R] N)
    (hk : Function.Injective (f.rTensor (R ⧸ IsLocalRing.maximalIdeal R)))
    (A : Type w) [AddCommGroup A] [Module R A] (hA : IsFiniteLength R A) :
    Function.Injective (f.rTensor A) := by
  induction hA with
  | @of_subsingleton A _ _ _ =>
    exact fun _ _ _ => Subsingleton.elim _ _
  | @of_simple_quotient A _ _ U hsimple hU ih =>
    obtain ⟨e⟩ := simple_equiv_residue R (A ⧸ U)
    have hq : Function.Injective (f.rTensor (A ⧸ U)) := by
      intro x y hxy
      apply (e.lTensor N).injective
      apply hk
      change f.rTensor _ (e.toLinearMap.lTensor N x) =
        f.rTensor _ (e.toLinearMap.lTensor N y)
      rw [← tensor_endomorphism_naturality, ← tensor_endomorphism_naturality, hxy]
    exact tensor_endomorphism_injective_extension f U.subtype U.mkQ
      U.injective_subtype (LinearMap.exact_subtype_mkQ U) ih hq

lemma tensorQuotEquiv_tmul_one {R : Type u} [CommRing R]
    (N : Type w) [AddCommGroup N] [Module R N] (I : Ideal R) (n : N) :
    TensorProduct.tensorQuotEquivQuotSMul N I (n ⊗ₜ[R] (1 : R ⧸ I)) =
      Submodule.Quotient.mk n := by
  simpa only [map_one, one_smul] using
    (TensorProduct.tensorQuotEquivQuotSMul_tmul_mk I n (1 : R))

/-- Tensoring with a ring quotient expresses the nonzerodivisor test on N/IN.
The S-submodule uses the extended ideal, so its quotient has the canonical S-action. -/
lemma tensor_smul_injective_of_quotient {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (I : Ideal R) (y : S)
    (hy : IsSMulRegular (N ⧸ (I.map (algebraMap R S) • ⊤ : Submodule S N)) y) :
    Function.Injective (((LinearMap.lsmul S N y).restrictScalars R).rTensor (R ⧸ I)) := by
  let f := (LinearMap.lsmul S N y).restrictScalars R
  let E := TensorProduct.tensorQuotEquivQuotSMul N I
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨n, hn⟩ := (I • (⊤ : Submodule R N)).mkQ_surjective (E z)
  have hzrep : z = n ⊗ₜ[R] (1 : R ⧸ I) := by
    apply E.injective
    rw [← hn]
    exact (tensorQuotEquiv_tmul_one N I n).symm
  rw [hzrep] at hz ⊢
  have hyn : y • n ∈ I • (⊤ : Submodule R N) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (y • n) ⊗ₜ[R] (1 : R ⧸ I) = 0 at hz
    have hh := congrArg E hz
    rw [tensorQuotEquiv_tmul_one, map_zero] at hh
    exact hh
  have hrestrict := Ideal.smul_restrictScalars I (⊤ : Submodule S N)
  have hyn' : y • n ∈ (I.map (algebraMap R S) • ⊤ : Submodule S N) := by
    change y • n ∈ (I.map (algebraMap R S) • (⊤ : Submodule S N)).restrictScalars R
    rw [hrestrict, Submodule.restrictScalars_top]
    exact hyn
  have hn' := mem_of_isSMulRegular_quotient_of_smul_mem hy hyn'
  apply E.injective
  rw [tensorQuotEquiv_tmul_one, map_zero]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change n ∈ I • (⊤ : Submodule R N)
  change n ∈ (I.map (algebraMap R S) • (⊤ : Submodule S N)).restrictScalars R at hn'
  simpa only [hrestrict, Submodule.restrictScalars_top] using hn'

/-- Krull intersection upgrades the finite-length tests to injectivity on N. -/
lemma smul_injective_of_fiber {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [Module.Flat R N]
    (y : S) (hy : IsSMulRegular (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) y) :
    IsSMulRegular N y := by
  let m := IsLocalRing.maximalIdeal R
  let f := (LinearMap.lsmul S N y).restrictScalars R
  have hk : Function.Injective (f.rTensor (R ⧸ m)) :=
    tensor_smul_injective_of_quotient N m y hy
  have hsep : IsHausdorff m N :=
    IsHausdorff.of_map (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro n hn
  have hnall : n ∈ ⨅ j : ℕ, m ^ j • (⊤ : Submodule R N) := by
    rw [Submodule.mem_iInf]
    intro j
    by_cases hj : j = 0
    · simp [hj]
    · have ht := tensor_endomorphism_injective_finiteLength f hk (R ⧸ m ^ j)
        (power_quotient_finite_length R j (by omega))
      have hz : n ⊗ₜ[R] (1 : R ⧸ m ^ j) = 0 :=
        (injective_iff_map_eq_zero _).mp ht _ (by simp [f, hn])
      have hh := congrArg (TensorProduct.tensorQuotEquivQuotSMul N (m ^ j)) hz
      apply (Submodule.Quotient.mk_eq_zero _).mp
      rw [tensorQuotEquiv_tmul_one, map_zero] at hh
      exact hh
  rw [hsep.iInf_pow_smul] at hnall
  exact hnall

open P103.BalancedTensor P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance

/-- The Tor sequence of a short exact sequence with flat middle term.
Injectivity of the tensor of the first arrow kills the first Tor of its cokernel. -/
lemma torOneVanishes_of_tensor_injective {R : Type u} [CommRing R]
    (A : Type v) [AddCommGroup A] [Module R A]
    {B M C : Type w} [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup C] [Module R C]
    (i : B →ₗ[R] M) (p : M →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p)
    (ht : Function.Injective (i.lTensor A)) : TorOneVanishes R A C := by
  letI := commRightModule R A
  letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
  intro P hP
  obtain ⟨δ, hδ, hδi, _⟩ := P103.Ch11.TorExactSequences.second_tensor_splice
    R A P hP B M C i p hi he hp
  have hn (z : Tensor R A B) :
      commAddEquiv (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i z) =
        i.lTensor A (commAddEquiv z) := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a b => rfl
    | ha z t hz ht => simp only [map_add, hz, ht]
  have hinj : Function.Injective (tensorMap (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) i) := by
    intro x y hxy
    apply (commAddEquiv (K := R) (A := A) (B := B)).injective
    apply ht
    simpa only [hn] using congrArg (commAddEquiv (K := R)) hxy
  letI : Subsingleton (TorWith P M 1) :=
    P103.Ch11.VanishingAndFlatness.tor_left_flat R A M
      ((P103.Ch02.FlatnessTests.commutative_flat_iff R M).mpr inferInstance) P hP 0
  have hz (z : TorWith P C 1) : z = 0 := by
    have hd : δ z = 0 := hinj <| by
      rw [map_zero]
      exact hδi.apply_apply_eq_zero z
    obtain ⟨t, ht⟩ := (hδ z).mp hd
    rw [← ht, Subsingleton.elim t 0, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The one-element lifting statement, including flatness and properness of
its quotient. No finiteness over the base ring is imposed. -/
theorem fiberRegularLifting :
    Specs.AdvCommAlg.CohenMacaulay.fiberRegularLiftingType.{u,v,w} := by
  intro R S _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ y hym hy
  have hyN := smul_injective_of_fiber N y hy
  let f := (LinearMap.lsmul S N y).restrictScalars R
  let p := (y • (⊤ : Submodule S N)).mkQ.restrictScalars R
  have he : Function.Exact f p := by
    intro n
    change Submodule.Quotient.mk n = 0 ↔ ∃ b : N, y • b = n
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  have hp : Function.Surjective p := (y • (⊤ : Submodule S N)).mkQ_surjective
  have hk : TorOneVanishes R (R ⧸ IsLocalRing.maximalIdeal R) (QuotSMulTop y N) :=
    torOneVanishes_of_tensor_injective _ f p hyN he hp
      ((f.lTensor_inj_iff_rTensor_inj _).mpr
        (tensor_smul_injective_of_quotient N _ y hy))
  letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
  let P := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (R ⧸ IsLocalRing.maximalIdeal R))
  have hflat : Module.Flat R (QuotSMulTop y N) :=
    (localFlatnessCriterion R S (QuotSMulTop y N) P.val P.property).mp
      (hk P.val P.property)
  exact ⟨hyN, hflat, nontrivial_quotSMulTop_of_mem_maximalIdeal N hym⟩

/-- Taking the closed fiber commutes with quotienting by an arbitrary lift y. -/
def fiber_quotSMulEquiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module S N] (y : S) :
    Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S (QuotSMulTop y N) ≃ₗ[S]
      QuotSMulTop y (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  exact Submodule.quotEquivOfEq _ _ (by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]) ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup (y • ⊤) (J • ⊤) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (sup_comm _ _) ≪≫ₗ
    (Submodule.quotientQuotientEquivQuotientSup (J • ⊤) (y • ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])

/-- Every finite regular sequence in the closed fiber lifts, and every prefix
quotient stays flat over R and nonzero. -/
lemma fiberRegularSequenceLiftingActions :
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N] [Module.Flat R N]
    (ys : List S), (∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal S) →
    RingTheory.Sequence.IsRegular (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) ys →
    RingTheory.Sequence.IsRegular N ys ∧
      ∀ j : ℕ, Module.Flat R
        (N ⧸ (Ideal.ofList (ys.take j) • ⊤ : Submodule S N)) ∧
      Nontrivial (N ⧸ (Ideal.ofList (ys.take j) • ⊤ : Submodule S N)) := by
  intro R S _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ ys
  induction ys generalizing N with
  | nil =>
    intro hym hy
    refine ⟨RingTheory.Sequence.IsRegular.nil S N, ?_⟩
    intro j
    let e : (N ⧸ (Ideal.ofList (([] : List S).take j) • ⊤ : Submodule S N)) ≃ₗ[S] N :=
      Submodule.quotEquivOfEqBot _ (by simp)
    exact ⟨Module.Flat.of_linearEquiv (e.restrictScalars R), e.symm.injective.nontrivial⟩
  | cons y ys ih =>
    intro hym hy
    have hymem := hym y (List.mem_cons_self ..)
    obtain ⟨hyfiber, hysfiber⟩ := (RingTheory.Sequence.isRegular_cons_iff _ _ _).mp hy
    obtain ⟨hyN, hflat, hnonzero⟩ := fiberRegularLifting R S N y hymem hyfiber
    letI := hflat
    letI := hnonzero
    have hys : RingTheory.Sequence.IsRegular
        (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S (QuotSMulTop y N)) ys :=
      ((fiber_quotSMulEquiv N y).isRegular_congr ys).mpr hysfiber
    obtain ⟨hreg, hquot⟩ := ih (QuotSMulTop y N)
      (fun a ha => hym a (List.mem_cons_of_mem _ ha)) hys
    refine ⟨hreg.cons hyN, ?_⟩
    intro j
    cases j with
    | zero =>
      let e : (N ⧸ (Ideal.ofList ((y :: ys).take 0) • ⊤ : Submodule S N)) ≃ₗ[S] N :=
        Submodule.quotEquivOfEqBot _ (by simp)
      exact ⟨Module.Flat.of_linearEquiv (e.restrictScalars R), e.symm.injective.nontrivial⟩
    | succ j =>
      obtain ⟨hflatj, hnonzeroj⟩ := hquot j
      letI := hflatj
      letI := hnonzeroj
      let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner N y (ys.take j)
      change Module.Flat R (N ⧸ (Ideal.ofList (y :: ys.take j) • ⊤ : Submodule S N)) ∧ _
      exact ⟨Module.Flat.of_linearEquiv (e.restrictScalars R), e.symm.injective.nontrivial⟩

/-- The regularity hypothesis on the closed-fiber ring is exactly the
regularity of the actions of the chosen lifts. -/
lemma closedFiber_regular_images_iff (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    (N : Type w) [AddCommGroup N] [Module S N] (ys : List S) :
    RingTheory.Sequence.IsRegular (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)
      (ys.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)))) ↔
    RingTheory.Sequence.IsRegular (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N) ys := by
  exact (AddEquiv.refl (Specs.AdvCommAlg.CohenMacaulay.ClosedFiber R S N)).isRegular_congr <|
    List.forall₂_map_left_iff.mpr <|
    List.forall₂_same.mpr fun r _ =>
      algebraMap_smul (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) r

/-- Arbitrary lifts in n of a regular sequence over S/mS form a regular
sequence on N, with all prefix quotients nonzero and R-flat. -/
theorem fiberRegularSequenceLifting :
    Specs.AdvCommAlg.CohenMacaulay.fiberRegularSequenceLiftingType.{u,v,w} := by
  intro R S _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ ys hym hy
  exact fiberRegularSequenceLiftingActions R S N ys hym
    ((closedFiber_regular_images_iff R S N ys).mp hy)

end
end AdvCommAlg.CohenMacaulay
