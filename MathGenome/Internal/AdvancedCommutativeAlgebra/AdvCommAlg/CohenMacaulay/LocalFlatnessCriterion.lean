import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.LocalFlatnessCriterion
import MathGenome.Internal.AlgebraCore.P103.Ch12.FiniteLengthTorVanishing
import MathGenome.Internal.AlgebraCore.P103.Ch11.VanishingAndFlatness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.TensorProduct.Finite

/-! Relative local flatness, via finite-colength quotients and Artin–Rees.
No import of P103.Ch12.LocalFlatnessCriterion is used. -/
namespace AdvCommAlg.CohenMacaulay

open P103.BalancedTensor P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
open P103.Ch12.FiniteLengthTorVanishing
open scoped TensorProduct

noncomputable section
set_option linter.style.haveILetI false
universe u v w

/-- The first Tor sequence, transported to Mathlib's commutative tensor product. -/
theorem rTensor_injective_of_torOneVanishes {R : Type u} [CommRing R]
    {A B C : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (M : Type w) [AddCommGroup M] [Module R M]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (he : Function.Exact i p) (hp : Function.Surjective p)
    (h : TorOneVanishes R C M) : Function.Injective (i.rTensor M) := by
  letI := commRightModule R A
  letI := commRightModule R B
  letI := commRightModule R C
  letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
  letI : IsCentralScalar R B := ⟨fun _ _ => rfl⟩
  let L := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ A)
  let Q := P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ (ModuleCat.of Rᵐᵒᵖ C)
  let i' := commRightLinear (K := R) i
  let p' := commRightLinear (K := R) p
  obtain ⟨⟨H⟩, _⟩ := P103.Ch11.TorExactSequences.first_sequence R A B C i' p'
    hi he hp L.val Q.val L.property Q.property M
  obtain ⟨δ, _, hδ, _⟩ := P103.Ch11.TorExactSequences.first_tensor_splice R A B C
    i' p' hi he hp L.val Q.val L.property Q.property M H
  letI := h Q.val Q.property
  have hinj : Function.Injective (tensorMap i' (LinearMap.id : M →ₗ[R] M)) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨t, rfl⟩ := (hδ z).mp hz
    rw [Subsingleton.elim t 0, map_zero]
  intro x y hxy
  apply (commAddEquiv (K := R) (A := A) (B := M)).symm.injective
  apply hinj
  apply (commAddEquiv (K := R) (A := B) (B := M)).injective
  have hn (z : Tensor R A M) :
      commAddEquiv (tensorMap i' LinearMap.id z) = i.rTensor M (commAddEquiv z) := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp
    | ht a m => rfl
    | ha z t hz ht => simp only [map_add, hz, ht]
  simpa only [hn, AddEquiv.apply_symm_apply] using hxy

/-- Vanishing Tor for the cokernel makes tensor exact at the source of a map. -/
theorem lTensor_kernel_exact_of_torOneVanishes {R : Type u} [CommRing R]
    {A B C : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (M : Type w) [AddCommGroup M] [Module R M]
    (f : A →ₗ[R] B) (p : B →ₗ[R] C)
    (he : Function.Exact f p) (hp : Function.Surjective p)
    (h : TorOneVanishes R C M) :
    Function.Exact (f.ker.subtype.lTensor M) (f.lTensor M) := by
  let q : A →ₗ[R] p.ker := f.codRestrict p.ker (fun a => he.apply_apply_eq_zero a)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨a, ha⟩ := (he b.val).mp b.property
    exact ⟨a, Subtype.ext ha⟩
  have hker : q.ker = f.ker := by
    ext a
    exact Subtype.ext_iff
  have hex := lTensor_exact M (LinearMap.exact_subtype_ker_map q) hq
  have hj : Function.Injective (p.ker.subtype.lTensor M) :=
    (p.ker.subtype.lTensor_inj_iff_rTensor_inj M).mpr
      (rTensor_injective_of_torOneVanishes M p.ker.subtype p
        p.ker.injective_subtype (LinearMap.exact_subtype_ker_map p) hp h)
  have hf : (p.ker.subtype.lTensor M).comp (q.lTensor M) = f.lTensor M := by
    rw [← LinearMap.lTensor_comp]
    rfl
  rw [hker] at hex
  intro z
  rw [← hf, LinearMap.comp_apply, ← map_zero (p.ker.subtype.lTensor M), hj.eq_iff]
  exact hex z

/-- Mixed-base tensor finiteness follows from cancellation of base change. -/
theorem finite_tensor_of_finite_over_algebra (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] :
    Module.Finite S (M ⊗[R] A) :=
  Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M A)


/-- A kernel element can be lifted to the intersection with any ideal J whose
corresponding quotient has vanishing Tor. -/
theorem tensor_kernel_lifts_to_intersection {R : Type u} [CommRing R]
    (M : Type w) [AddCommGroup M] [Module R M] (I J : Ideal R)
    (h : TorOneVanishes R (R ⧸ (I ⊔ J)) M)
    (z : M ⊗[R] I) (hz : I.subtype.lTensor M z = 0) :
    ∃ t : M ⊗[R] ↥(I ⊓ J), (Submodule.inclusion inf_le_left).lTensor M t = z := by
  let f : I →ₗ[R] R ⧸ J := J.mkQ.comp I.subtype
  let p : (R ⧸ J) →ₗ[R] R ⧸ (I ⊔ J) :=
    (Ideal.Quotient.factorₐ R (show J ≤ I ⊔ J from le_sup_right)).toLinearMap
  have he : Function.Exact f p := by
    intro b
    obtain ⟨r, rfl⟩ := J.mkQ_surjective b
    change Ideal.Quotient.mk (I ⊔ J) r = 0 ↔ ∃ a : I, J.mkQ a.val = J.mkQ r
    rw [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      change J.mkQ a = J.mkQ r
      rw [← hab, map_add, (show J.mkQ b = 0 from (Submodule.Quotient.mk_eq_zero J).mpr hb), add_zero]
    · rintro ⟨a, ha⟩
      refine ⟨a.val, a.property, r - a.val, ?_, add_sub_cancel _ _⟩
      apply (Submodule.Quotient.mk_eq_zero J).mp
      change J.mkQ (r - a.val) = 0
      rw [map_sub, ha, sub_self]
  have hex := lTensor_kernel_exact_of_torOneVanishes M f p he
    (Ideal.Quotient.factor_surjective le_sup_right) h
  have hfz : f.lTensor M z = 0 := by
    rw [show f = J.mkQ.comp I.subtype from rfl, LinearMap.lTensor_comp,
      LinearMap.comp_apply, hz, map_zero]
  obtain ⟨t, ht⟩ := (hex z).mp hfz
  let g : f.ker →ₗ[R] ↥(I ⊓ J) :=
    { toFun := fun a => ⟨a.val.val, a.val.property,
        (Submodule.Quotient.mk_eq_zero J).mp a.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨g.lTensor M t, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  exact ht

/-- A bound L ⊆ JI gives the corresponding bound after tensoring. -/
theorem tensor_inclusion_mem_smul {R : Type u} [CommRing R]
    (M : Type w) [AddCommGroup M] [Module R M]
    {I J L : Ideal R} (hLI : L ≤ I) (hL : L ≤ J • I) (t : M ⊗[R] L) :
    (Submodule.inclusion hLI).lTensor M t ∈ J • (⊤ : Submodule R (M ⊗[R] I)) := by
  let T : Submodule R (M ⊗[R] I) := J • ⊤
  have ht (m : M) (a : I) (ha : a.val ∈ J • I) : m ⊗ₜ[R] a ∈ T := by
    have ha' : a ∈ J • (⊤ : Submodule R I) := (Submodule.mem_smul_top_iff J I a).mpr ha
    refine Submodule.smul_induction_on ha' (fun r hr b _ => ?_) (fun b c hb hc => ?_)
    · rw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · simpa only [TensorProduct.tmul_add] using T.add_mem hb hc
  induction t using TensorProduct.inductionOn with
  | tmul m a => exact ht m (Submodule.inclusion hLI a) (hL a.property)
  | add t t' ht ht' => simpa only [map_add] using T.add_mem ht ht'

/-- The ideal test follows from vanishing on finite-colength quotients and
m-adic separatedness of each tensor with an ideal. -/
theorem flat_of_quotient_tor_and_separated (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (M : Type w) [AddCommGroup M] [Module R M]
    (h : ∀ (I : Ideal R) (j : ℕ), 1 ≤ j →
      TorOneVanishes R (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ j)) M)
    (hsep : ∀ I : Ideal R, IsHausdorff (IsLocalRing.maximalIdeal R) (M ⊗[R] I)) :
    Module.Flat R M := by
  apply Module.Flat.iff_lTensor_injective'.mpr
  intro I
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let m := IsLocalRing.maximalIdeal R
  obtain ⟨c, hc⟩ := m.exists_pow_inf_eq_pow_smul (I : Submodule R R)
  have hbound (k : ℕ) : I ⊓ m ^ (k+c+1) ≤ m ^ k • I := by
    have hc' := hc (k+c+1) (by omega)
    have htop (n : ℕ) : m ^ n • (⊤ : Submodule R R) = m ^ n := by
      change m ^ n * ⊤ = m ^ n
      exact Ideal.mul_top _
    rw [htop, inf_comm, show k+c+1-c = k+1 by omega] at hc'
    rw [hc']
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) inf_le_right
  have hzall : z ∈ ⨅ k : ℕ, m ^ k • (⊤ : Submodule R (M ⊗[R] I)) := by
    rw [Submodule.mem_iInf]
    intro k
    obtain ⟨t, ht⟩ := tensor_kernel_lifts_to_intersection M I (m ^ (k+c+1))
      (h I (k+c+1) (by omega)) z hz
    rw [← ht]
    exact tensor_inclusion_mem_smul M inf_le_left (hbound k) t
  rw [(hsep I).iInf_pow_smul] at hzall
  exact hzall

/-- Local flatness for a finite module over a local Noetherian algebra.
All ordinary projective resolutions of the actual base residue field are allowed. -/
theorem localFlatnessCriterion :
    Specs.AdvCommAlg.CohenMacaulay.localFlatnessCriterionType.{u,v,w} := by
  intro R S _ _ _ _ _ _ _ _ M _ _ _ _ _
  letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
  intro P hP
  constructor
  · intro h
    apply flat_of_quotient_tor_and_separated R M (quotient_vanishing R M P hP h)
    intro I
    letI : Module.Finite S (M ⊗[R] I) := finite_tensor_of_finite_over_algebra R S M I
    exact IsHausdorff.of_map (I := IsLocalRing.maximalIdeal R) (M := M ⊗[R] I)
      (IsLocalRing.map_maximalIdeal_le (algebraMap R S))
  · intro h
    exact P103.Ch11.VanishingAndFlatness.tor_left_flat R
      (R ⧸ IsLocalRing.maximalIdeal R) M
      ((P103.Ch02.FlatnessTests.commutative_flat_iff R M).mpr h) P hP 0

end
end AdvCommAlg.CohenMacaulay
