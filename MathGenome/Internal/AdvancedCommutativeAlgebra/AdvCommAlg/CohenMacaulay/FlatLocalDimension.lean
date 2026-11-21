import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalDimension
import Mathlib.RingTheory.TensorProduct.Finite

/-! CM-10: support and dimension in a flat local family. -/
universe u
open scoped TensorProduct
open TensorProduct
namespace AdvCommAlg.CohenMacaulay

/-- Tensor nonvanishing over a field, including the zero-factor cases. -/
lemma nontrivial_tensorProduct_iff_of_field (K X Y : Type*) [Field K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] :
    Nontrivial (X ⊗[K] Y) ↔ Nontrivial X ∧ Nontrivial Y := by
  constructor
  · intro h
    constructor
    · by_contra hx
      have : Subsingleton X := not_nontrivial_iff_subsingleton.mp hx
      exact not_subsingleton (X ⊗[K] Y) inferInstance
    · by_contra hy
      have : Subsingleton Y := not_nontrivial_iff_subsingleton.mp hy
      exact not_subsingleton (X ⊗[K] Y) inferInstance
  · rintro ⟨hX, hY⟩
    let := hX
    let := hY
    infer_instance

section Support
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Module.Finite R M] [Module.Finite S N]

/-- A scalar extension to κ(q) detects the support of M at q ∩ R. -/
lemma nontrivial_residueField_tensor_iff (q : PrimeSpectrum S) :
    Nontrivial (q.asIdeal.ResidueField ⊗[R] M) ↔
      PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M := by
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let f := Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) rfl
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := f.toAlgebra
  letI : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R q.asIdeal.ResidueField r =
        f (algebraMap R p.asIdeal.ResidueField r)
      exact (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal
          (algebraMap R S) (by rfl) r).symm
  let e := AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
    q.asIdeal.ResidueField q.asIdeal.ResidueField M
  rw [← e.nontrivial_congr,
    Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct]

/-- Finiteness over S uses finite generation of N over S and of M over R. -/
lemma tensor_finite_left : Module.Finite S (N ⊗[R] M) :=
  Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S N M)

lemma tensor_finite :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    Module.Finite S (M ⊗[R] N) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  let := tensor_finite_left R S M N
  exact Module.Finite.equiv (RegularSequence.rightTensorComm (S := S) M N).symm

/-- The support computation in fact needs neither flatness nor local rings. -/
lemma tensor_support_left :
    Module.support S (N ⊗[R] M) = Module.support S N ∩
      (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' Module.support R M := by
  let := tensor_finite_left R S M N
  ext q
  let K := q.asIdeal.ResidueField
  let e₁ := (AlgebraTensorModule.assoc R S K K N M).symm
  let e₂ := (AlgebraTensorModule.cancelBaseChange R K K (K ⊗[S] N) M).symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    e₁.nontrivial_congr, e₂.nontrivial_congr,
    nontrivial_tensorProduct_iff_of_field,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    nontrivial_residueField_tensor_iff R S M]
  rfl

/-- The source tensor order, using the canonical right-factor action. -/
theorem tensor_support :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    Module.support S (M ⊗[R] N) = Module.support S N ∩
      (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' Module.support R M := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  exact (RegularSequence.rightTensorComm (S := S) M N).support_eq.trans
    (tensor_support_left R S M N)

end Support

section Local
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)]
variable (N : Type u) [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N]

theorem closedFiber_nontrivial :
    Nontrivial (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
      (⊤ : Submodule S N))) := by
  apply quotient_nontrivial S N
  rw [Ideal.map_le_iff_le_comap]
  exact le_of_eq (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm

/-- The support of the closed fiber, viewed as an S-module. -/
theorem closedFiber_support :
    Module.support S (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
      (⊤ : Submodule S N))) = Module.support S N ∩
        (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' {IsLocalRing.closedPoint R} := by
  rw [Module.support_quotient]
  congr 1
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  change (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ q.asIdeal ↔
    PrimeSpectrum.comap (algebraMap R S) q = IsLocalRing.closedPoint R
  rw [Ideal.map_le_iff_le_comap]
  constructor
  · intro h
    apply PrimeSpectrum.ext
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
      (inferInstance : (q.asIdeal.comap (algebraMap R S)).IsPrime).ne_top h).symm
  · intro h
    have heq := congrArg PrimeSpectrum.asIdeal h
    change IsLocalRing.maximalIdeal R ≤ (PrimeSpectrum.comap (algebraMap R S) q).asIdeal
    rw [heq]
    exact le_rfl

include S in
/-- A nonzero finite S-module that is R-flat is faithfully flat over R.
Nakayama is applied over S, so N need not be finite over R. -/
theorem faithfullyFlat_of_flatLocal [Module.Flat R N] : Module.FaithfullyFlat R N := by
  constructor
  intro I hI
  have hIeq : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
  subst I
  have hq := closedFiber_nontrivial R S N
  intro h
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R S) •
      (⊤ : Submodule S N) = ⊤ := by
    apply Submodule.restrictScalars_injective R
    simpa only [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top] using h
  exact (Submodule.Quotient.nontrivial_iff.mp hq) hmap

variable (M : Type u) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Nontrivial M]

include S in
theorem tensor_nontrivial_of_flatLocal [Module.Flat R N] : Nontrivial (M ⊗[R] N) := by
  let := faithfullyFlat_of_flatLocal R S N
  infer_instance

end Local
/-- Nonvanishing in the order of parameters used in the independent specification. -/
theorem flatLocal_tensor_nontrivial : Specs.flatLocal_tensor_nontrivialType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _ _ _ _ _
  exact tensor_nontrivial_of_flatLocal R S N M

/-- Support in the order of parameters used in the independent specification. -/
theorem flatLocal_tensor_support : Specs.flatLocal_tensor_supportType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _
  intro _ _ _ _ _
  exact tensor_support R S M N

/-- A surjective scalar map preserves the support dimension of a finite module. -/
lemma supportDim_of_surjective_algebraMap (R A X : Type*)
    [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup X]
    [Module R X] [Module A X] [IsScalarTower R A X]
    [Module.Finite R X] [Module.Finite A X]
    (hf : Function.Surjective (algebraMap R A)) :
    Module.supportDim R X = Module.supportDim A X := by
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f := (Ideal.Quotient.mk (Module.annihilator A X)).comp (algebraMap R A)
  have hk : RingHom.ker f = Module.annihilator R X := by
    dsimp only [f]
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact Module.comap_annihilator
  rw [← hk]
  exact (f.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp hf)).ringKrullDim

/-- Killing a list in the maximal ideal lowers dimension by at most its length. -/
lemma supportDim_le_quotient_add_length (R X : Type*) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup X] [Module R X]
    [Module.Finite R X] (x : List R)
    (hx : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R X ≤
      Module.supportDim R (X ⧸ (Ideal.ofList x • (⊤ : Submodule R X))) + x.length := by
  induction x generalizing X with
  | nil =>
    rw [Ideal.ofList_nil, Submodule.bot_smul, List.length_nil, Nat.cast_zero, add_zero]
    exact le_of_eq (Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot
        (⊥ : Submodule R X) rfl)).symm
  | cons a x ih =>
    have h := Module.supportDim_le_supportDim_quotSMulTop_succ (M := X) (hx a (by simp))
    have h' := ih (QuotSMulTop a X) (fun b hb => hx b (by simp [hb]))
    rw [Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner X a x)]
    calc
      _ ≤ Module.supportDim R (QuotSMulTop a X) + 1 := h
      _ ≤ (Module.supportDim R
        (QuotSMulTop a X ⧸ (Ideal.ofList x • (⊤ : Submodule R (QuotSMulTop a X))))) + x.length + 1 :=
          by gcongr
      _ = _ := by simp [List.length_cons, Nat.cast_add, add_assoc]

section Upper
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)]
variable (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]

/-- After killing parameters of M, the tensor has the support of the closed fiber. -/
lemma tensor_parameter_quotient_support (x : List R)
    (hx : IsSystemOfParameters R M x) :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    Module.support S ((M ⊗[R] N) ⧸
      (Ideal.ofList (x.map (algebraMap R S)) • (⊤ : Submodule S (M ⊗[R] N)))) =
    Module.support S (N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) •
      (⊤ : Submodule S N))) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  have := tensor_finite R S M N
  have hle : Ideal.ofList x ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr hx.1
  have hsupport := (finiteLength_quotient_iff_support_singleton R M
    (Ideal.ofList x) hle).mp hx.2.2
  rw [Module.support_quotient] at hsupport
  rw [Module.support_quotient, tensor_support R S M N, closedFiber_support R S N]
  ext q
  have hz : q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList (x.map (algebraMap R S)) : Set S) ↔
      PrimeSpectrum.comap (algebraMap R S) q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList x : Set R) := by
    change Ideal.ofList (x.map (algebraMap R S)) ≤ q.asIdeal ↔
      Ideal.ofList x ≤ q.asIdeal.comap (algebraMap R S)
    rw [← Ideal.map_ofList, Ideal.map_le_iff_le_comap]
  have he := Set.ext_iff.mp hsupport (PrimeSpectrum.comap (algebraMap R S) q)
  simp only [Set.mem_inter_iff, Set.mem_preimage] at he ⊢
  rw [hz]
  tauto

/-- The parameter upper bound; its proof does not use flatness. -/
lemma tensor_dimension_le [Module.Flat R N] :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    Module.supportDim S (M ⊗[R] N) ≤ Module.supportDim R M +
      Module.supportDim (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  have := tensor_finite R S M N
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let N₀ := N ⧸ (J • (⊤ : Submodule S N))
  letI : Module.Finite (S ⧸ J) N₀ := Module.Finite.of_restrictScalars_finite S (S ⧸ J) N₀
  obtain ⟨x, hx⟩ := exists_systemOfParameters R M
  have h := supportDim_le_quotient_add_length S (M ⊗[R] N)
    (x.map (algebraMap R S)) (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact IsLocalRing.map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ (hx.1 b hb)))
  have heq : Module.supportDim S ((M ⊗[R] N) ⧸
      (Ideal.ofList (x.map (algebraMap R S)) • (⊤ : Submodule S (M ⊗[R] N)))) =
      Module.supportDim S N₀ := congrArg (fun U : Set (PrimeSpectrum S) => Order.krullDim U) (tensor_parameter_quotient_support R S M N x hx)
  rw [heq, List.length_map, hx.2.1] at h
  rw [supportDim_of_surjective_algebraMap S (S ⧸ J) N₀ Ideal.Quotient.mk_surjective] at h
  simpa only [dimension, add_comm] using h
end Upper


/-- A scalar outside p acts injectively on N/pN, by flatness. -/
lemma quotient_map_isSMulRegular (R S N : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (r : R) (hr : r ∉ p) :
    IsSMulRegular (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) (algebraMap R S r) := by
  let P : Submodule S N := p.map (algebraMap R S) • (⊤ : Submodule S N)
  have hP : P.restrictScalars R = p • (⊤ : Submodule R N) := by
    simp [P, Submodule.restrictScalars_map_smul_eq]
  let e := (quotTensorEquivQuotSMul N p) ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ hP.symm) ≪≫ₗ
    (Submodule.Quotient.restrictScalarsEquiv R P)
  have hr' : (Ideal.Quotient.mk p r) ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hreg : IsSMulRegular (R ⧸ p) r := by
    intro x y h
    exact mul_left_cancel₀ hr' h
  have h := (e.isSMulRegular_congr r).mp (hreg.rTensor N)
  simpa only [IsSMulRegular, algebraMap_smul] using h

/-- Going down on the support of a flat finite module. No flatness of S is needed. -/
lemma exists_support_le_over (R S N : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N]
    (q : PrimeSpectrum S) (hq : q ∈ Module.support S N)
    (p : PrimeSpectrum R) (hp : p ≤ PrimeSpectrum.comap (algebraMap R S) q) :
    ∃ q' : PrimeSpectrum S, q' ≤ q ∧ q' ∈ Module.support S N ∧
      PrimeSpectrum.comap (algebraMap R S) q' = p := by
  let J := p.asIdeal.map (algebraMap R S)
  let X := N ⧸ (J • (⊤ : Submodule S N))
  have hX : q ∈ Module.support S X := by
    rw [Module.support_quotient]
    exact ⟨hq, Ideal.map_le_iff_le_comap.mpr hp⟩
  obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hX)
  let q' : PrimeSpectrum S := ⟨Q, hQ.isPrime⟩
  have hq' : q' ∈ Module.support S X := Module.mem_support_iff_of_finite.mpr hQ.le
  have hq'N : q' ∈ Module.support S N := by
    rw [Module.support_quotient] at hq'
    exact hq'.1
  refine ⟨q', hQq, hq'N, PrimeSpectrum.ext ?_⟩
  apply le_antisymm
  · intro r hr
    by_contra hrp
    exact (quotient_map_isSMulRegular R S N p.asIdeal r hrp).notMem_of_mem_minimalPrimes hQ hr
  · have h := hq'
    rw [Module.support_quotient] at h
    exact Ideal.map_le_iff_le_comap.mp h.2

/-- Lift a finite support chain downwards from its prescribed last point. -/
lemma lift_support_chain (R S M N : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N]
    (l : LTSeries (Module.support R M)) (q : PrimeSpectrum S)
    (hq : q ∈ Module.support S N)
    (hql : PrimeSpectrum.comap (algebraMap R S) q = l.last.1) :
    ∃ L : LTSeries ↥(Module.support S N ∩
        (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' Module.support R M),
      L.length = l.length ∧ L.last.1 = q ∧
      PrimeSpectrum.comap (algebraMap R S) L.head.1 = l.head.1 := by
  induction l using RelSeries.inductionOn generalizing q with
  | singleton p =>
    refine ⟨RelSeries.singleton _ ⟨q, hq, ?_⟩, rfl, rfl, hql⟩
    change PrimeSpectrum.comap (algebraMap R S) q ∈ Module.support R M
    simpa only [RelSeries.last_singleton, hql] using p.2
  | cons l p hpl ih =>
    simp only [RelSeries.last_cons] at hql
    obtain ⟨L, hlen, hlast, hhead⟩ := ih q hq hql
    obtain ⟨Q, hQL, hQN, hQp⟩ := exists_support_le_over R S N L.head.1 L.head.2.1 p.1
      (by simpa only [hhead] using hpl.le)
    have hlt : Q < L.head.1 := by
      refine lt_of_le_of_ne hQL ?_
      intro heq
      have he : p.1 = l.head.1 := by simpa only [heq, hhead] using hQp.symm
      exact (ne_of_lt hpl) (Subtype.ext he)
    refine ⟨L.cons ⟨Q, hQN, ?_⟩ hlt, by simpa using hlen, ?_, ?_⟩
    · change PrimeSpectrum.comap (algebraMap R S) Q ∈ Module.support R M
      rw [hQp]
      exact p.2
    · simpa only [RelSeries.last_cons] using hlast
    · simpa only [RelSeries.head_cons] using hQp

section Lower
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)]
variable (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N] [Module.Flat R N]

/-- Concatenate a downward lift of a base chain with a chain in the closed fiber. -/
lemma tensor_dimension_ge :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    Module.supportDim R M +
      Module.supportDim (S ⧸ J) (N ⧸ (J • (⊤ : Submodule S N))) ≤
    Module.supportDim S (M ⊗[R] N) := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let N₀ := N ⧸ (J • (⊤ : Submodule S N))
  haveI : Nontrivial N₀ := closedFiber_nontrivial R S N
  letI : Module.Finite (S ⧸ J) N₀ := Module.Finite.of_restrictScalars_finite S (S ⧸ J) N₀
  change Module.supportDim R M + Module.supportDim (S ⧸ J) N₀ ≤ Module.supportDim S (M ⊗[R] N)
  rw [← supportDim_of_surjective_algebraMap S (S ⧸ J) N₀ Ideal.Quotient.mk_surjective]
  obtain ⟨x, hx⟩ := exists_systemOfParameters R M
  obtain ⟨y, hy⟩ := exists_systemOfParameters S N₀
  have hd : (x.length : WithBot ℕ∞) ≤ Order.krullDim (Module.support R M) := hx.2.1.le
  have he : (y.length : WithBot ℕ∞) ≤ Order.krullDim (Module.support S N₀) := hy.2.1.le
  obtain ⟨l₀, hl₀⟩ := Order.le_krullDim_iff.mp hd
  obtain ⟨l, hle, hmax⟩ := Module.exists_ltSeries_support_isMaximal_last_of_ltSeries_support l₀
  have hl : x.length ≤ l.length := hl₀ ▸ hle
  have hlast : l.last.1 = IsLocalRing.closedPoint R :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
  obtain ⟨k, hk⟩ := Order.le_krullDim_iff.mp he
  let U := Module.support S N ∩ (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' Module.support R M
  have hsupp := closedFiber_support R S N
  have hclosed (q : Module.support S N₀) :
      q.1 ∈ Module.support S N ∧
      PrimeSpectrum.comap (algebraMap R S) q.1 = IsLocalRing.closedPoint R := by
    have hq := (Set.ext_iff.mp hsupp q.1).mp q.2
    exact ⟨hq.1, hq.2⟩
  let f : Module.support S N₀ → U := fun q => ⟨q.1, (hclosed q).1, by
    change PrimeSpectrum.comap (algebraMap R S) q.1 ∈ Module.support R M
    rw [(hclosed q).2]
    exact IsLocalRing.closedPoint_mem_support R M⟩
  let K : LTSeries U := k.map f (fun _ _ h => h)
  obtain ⟨L, hLlen, hLlast, _⟩ := lift_support_chain R S M N l k.head.1
    (hclosed k.head).1 ((hclosed k.head).2.trans hlast.symm)
  have hconnect : L.last = K.head := Subtype.ext hLlast
  have hchain := Order.LTSeries.length_le_krullDim (L.smash K hconnect)
  have hlength : (L.smash K hconnect).length = l.length + y.length := by
    change L.length + k.length = l.length + y.length
    rw [hLlen, hk]
  have hbound : ((x.length + y.length : ℕ) : WithBot ℕ∞) ≤ Order.krullDim U := by
    calc
      _ ≤ ((l.length + y.length : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.add_le_add_right hl _
      _ ≤ _ := hlength ▸ hchain
  rw [Nat.cast_add, hx.2.1, hy.2.1] at hbound
  change Module.supportDim R M + Module.supportDim S N₀ ≤ _
  change _ ≤ Order.krullDim (Module.support S (M ⊗[R] N))
  rw [tensor_support R S M N]
  exact hbound
end Lower

/-- Dimension in a flat local family, for an R-flat module N. -/
theorem flatLocal_tensor_dimension : Specs.flatLocal_tensor_dimensionType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _
  intro _ _ _ _ _
  exact le_antisymm (tensor_dimension_le R S M N) (tensor_dimension_ge R S M N)

end AdvCommAlg.CohenMacaulay
