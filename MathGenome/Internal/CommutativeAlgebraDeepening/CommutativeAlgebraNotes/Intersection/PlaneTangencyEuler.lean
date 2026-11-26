import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.PlaneTangencyEuler
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section

open scoped Pointwise TensorProduct
open CategoryTheory

namespace CommutativeAlgebraNotes.Intersection.PlaneTangencyEuler

open CommutativeAlgebraNotes.Intersection.PlaneTangencyEuler.Specs
open IsolatedIntersectionEuler (intersectionEuler cutoffEuler cutoffEuler_eq_of_vanishes_above)
open IsolatedTorSupport (Tor torZeroEquiv koszulHomologyTorEquiv)

universe u

variable (k : Type u) [Field k]

private def oneVariable : MvPowerSeries (Fin 1) k ≃ₐ[k] PowerSeries k :=
  MvPowerSeries.renameEquiv k (Equiv.ofUnique (Fin 1) PUnit)

private theorem oneVariable_X :
    oneVariable k (MvPowerSeries.X 0) = PowerSeries.X := by
  change MvPowerSeries.rename (Equiv.ofUnique (Fin 1) PUnit) (MvPowerSeries.X 0) = _
  rw [MvPowerSeries.rename_X]
  rfl

private def outerConstant :
    PowerSeries (MvPowerSeries (Fin 1) k) →ₐ[k] MvPowerSeries (Fin 1) k where
  __ := PowerSeries.constantCoeff
  commutes' r := by simp [PowerSeries.algebraMap_apply]

private def eliminateY : Plane k →ₐ[k] PowerSeries k :=
  (oneVariable k).toAlgHom.comp
    ((outerConstant k).comp (MvPowerSeries.finSuccEquiv k 1).toAlgHom)

private theorem eliminateY_surjective : Function.Surjective (eliminateY k) :=
  (oneVariable k).surjective.comp
    (PowerSeries.constantCoeff_surj.comp (MvPowerSeries.finSuccEquiv k 1).surjective)

@[simp] private theorem eliminateY_y : eliminateY k (y k) = 0 := by
  simp [eliminateY, outerConstant]

@[simp] private theorem eliminateY_x : eliminateY k (x k) = PowerSeries.X := by
  change oneVariable k (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k 1
    (MvPowerSeries.X ((0 : Fin 1).succ)))) = _
  rw [MvPowerSeries.finSuccEquiv_X_succ, PowerSeries.constantCoeff_C, oneVariable_X]

private theorem eliminateY_eq_zero_iff (p : Plane k) :
    eliminateY k p = 0 ↔ y k ∣ p := by
  change oneVariable k (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k 1 p)) = 0 ↔ _
  rw [map_eq_zero_iff _ (oneVariable k).injective, ← PowerSeries.X_dvd_iff]
  simpa only [y, MvPowerSeries.finSuccEquiv_X_zero] using
    (map_dvd_iff (MvPowerSeries.finSuccEquiv k 1) (a := y k) (b := p))

private def translatedVariables (b : ℕ) (c : k) : Fin 2 → Plane k :=
  ![y k + MvPowerSeries.C c * x k ^ b, x k]

private theorem translatedVariables_hasSubst (b : ℕ) (hb : 1 ≤ b) (c : k) :
    MvPowerSeries.HasSubst (translatedVariables k b c) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;>
    simp [translatedVariables, MvPowerSeries.constantCoeff_X, zero_pow (by omega : b ≠ 0)]

private def translateY (b : ℕ) (hb : 1 ≤ b) (c : k) : Plane k →ₐ[k] Plane k :=
  MvPowerSeries.substAlgHom (translatedVariables_hasSubst k b hb c)

@[simp] private theorem translateY_x (b : ℕ) (hb : 1 ≤ b) (c : k) :
    translateY k b hb c (x k) = x k := by
  unfold x at *
  rw [translateY, MvPowerSeries.substAlgHom_X]
  rfl

@[simp] private theorem translateY_y (b : ℕ) (hb : 1 ≤ b) (c : k) :
    translateY k b hb c (y k) = y k + MvPowerSeries.C c * x k ^ b := by
  unfold y at *
  rw [translateY, MvPowerSeries.substAlgHom_X]
  rfl

private theorem translateY_inverse (b : ℕ) (hb : 1 ≤ b) (c : k) (p : Plane k) :
    translateY k b hb (-c) (translateY k b hb c p) = p := by
  unfold translateY
  simp only [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_comp_subst_apply
    (translatedVariables_hasSubst k b hb c) (translatedVariables_hasSubst k b hb (-c))]
  have h : (fun i => MvPowerSeries.subst (translatedVariables k b (-c))
      (translatedVariables k b c i)) = MvPowerSeries.X := by
    funext i
    rw [← MvPowerSeries.substAlgHom_apply (translatedVariables_hasSubst k b hb (-c))]
    change translateY k b hb (-c) (translatedVariables k b c i) = MvPowerSeries.X i
    fin_cases i
    · change translateY k b hb (-c) (y k + MvPowerSeries.C c * x k ^ b) = y k
      have hC : translateY k b hb (-c) (MvPowerSeries.C c) = MvPowerSeries.C c :=
        (translateY k b hb (-c)).commutes c
      simp [hC, add_assoc]
    · exact translateY_x k b hb (-c)
  rw [h, MvPowerSeries.subst_self]
  rfl

private def translation (b : ℕ) (hb : 1 ≤ b) (c : k) : Plane k ≃ₐ[k] Plane k :=
  AlgEquiv.ofAlgHom (translateY k b hb c) (translateY k b hb (-c))
    (AlgHom.ext fun p => by simpa using translateY_inverse k b hb (-c) p)
    (AlgHom.ext fun p => translateY_inverse k b hb c p)

private def interchange : Plane k ≃ₐ[k] Plane k :=
  MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) 1)

@[simp] private theorem interchange_x : interchange k (x k) = y k := by
  simp [interchange, MvPowerSeries.rename_X]

@[simp] private theorem interchange_y : interchange k (y k) = x k := by
  simp [interchange, MvPowerSeries.rename_X]

private theorem branchProjection_ker (f : Plane k) (e : Plane k ≃ₐ[k] Plane k)
    (he : e f = y k) :
    Ideal.span {f} = RingHom.ker ((eliminateY k).comp e.toAlgHom) := by
  ext p
  change p ∈ Ideal.span {f} ↔ eliminateY k (e p) = 0
  rw [Ideal.mem_span_singleton, eliminateY_eq_zero_iff, ← he, map_dvd_iff]

private theorem branchProjection_surjective (e : Plane k ≃ₐ[k] Plane k) :
    Function.Surjective ((eliminateY k).comp e.toAlgHom) :=
  (eliminateY_surjective k).comp e.surjective

/-- After a change of coordinates carrying `f` to `y`, setting `y = 0`
identifies the quotient by `f` with the remaining one-variable series ring. -/
private def branchEquiv (f : Plane k) (e : Plane k ≃ₐ[k] Plane k) (he : e f = y k) :
    Branch f ≃ₐ[k] PowerSeries k :=
  (Ideal.quotientEquivAlgOfEq k (branchProjection_ker k f e he)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (branchProjection_surjective k e))

private theorem branchEquiv_mk (f : Plane k) (e : Plane k ≃ₐ[k] Plane k)
    (he : e f = y k) (p : Plane k) :
    branchEquiv k f e he (Ideal.Quotient.mk _ p) = eliminateY k (e p) := by
  rw [branchEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]
  rfl

private theorem tangencyBranch (b : ℕ) (hb : 1 ≤ b) :
    ∃ e : Branch (y k - x k ^ b) ≃ₐ[k] PowerSeries k,
      e (Ideal.Quotient.mk _ (x k)) = PowerSeries.X ∧
      e (Ideal.Quotient.mk _ (y k)) = (PowerSeries.X : PowerSeries k) ^ b := by
  let e := translation k b hb 1
  have he : e (y k - x k ^ b) = y k := by
    change translateY k b hb 1 (y k - x k ^ b) = _
    simp
  refine ⟨branchEquiv k _ e he, ?_, ?_⟩
  · rw [branchEquiv_mk]
    change eliminateY k (translateY k b hb 1 (x k)) = _
    rw [translateY_x, eliminateY_x]
  · rw [branchEquiv_mk]
    change eliminateY k (translateY k b hb 1 (y k)) = _
    simp

private theorem axisBranch :
    ∃ e : Branch (x k) ≃ₐ[k] PowerSeries k,
      e (Ideal.Quotient.mk _ (x k)) = 0 ∧
      e (Ideal.Quotient.mk _ (y k)) = PowerSeries.X := by
  exact ⟨branchEquiv k _ (interchange k) (interchange_x k),
    by rw [branchEquiv_mk, interchange_x, eliminateY_y],
    by rw [branchEquiv_mk, interchange_y, eliminateY_x]⟩

section ScalarCokernel

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- On an algebra, the image of multiplication by a scalar is the
principal ideal generated by the image of the scalar. -/
private def scalarCokernelEquiv (r : R) :
    QuotSMulTop r A ≃ₗ[R] A ⧸ Ideal.span {algebraMap R A r} := by
  let J : Ideal A := Ideal.span {algebraMap R A r}
  have h : r • (⊤ : Submodule R A) = J.restrictScalars R := by
    ext a
    change a ∈ r • (⊤ : Submodule R A) ↔ a ∈ J
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Algebra.smul_def, J, Ideal.mem_span_singleton, Dvd.dvd, eq_comm]
  exact (Submodule.quotEquivOfEq _ _ h).trans (Submodule.Quotient.restrictScalarsEquiv R J)

end ScalarCokernel

private theorem cokernel_length {f : Plane k} (e : Branch f ≃+* PowerSeries k)
    (b : ℕ) (hy : e (Ideal.Quotient.mk _ (y k)) = (PowerSeries.X : PowerSeries k) ^ b) :
    Module.length (Plane k) (QuotSMulTop (y k) (Branch f)) = b := by
  let A := Branch f
  let S := PowerSeries k
  let J : Ideal A := Ideal.span {Ideal.Quotient.mk _ (y k)}
  let I : Ideal S := Ideal.span {(PowerSeries.X : S) ^ b}
  let : Algebra A S := e.toRingHom.toAlgebra
  let e' : A ≃ₐ[A] S :=
    { e with commutes' := fun _ => rfl }
  have hI : I = J.map e.toRingHom := by
    simp [I, J, Ideal.map_span, hy]
    rfl
  have h₁ : Module.length (Plane k) (QuotSMulTop (y k) A) =
      Module.length (Plane k) (A ⧸ J) := (scalarCokernelEquiv (A := A) (y k)).length_eq
  have h₂ : Module.length (Plane k) (A ⧸ J) = Module.length A (A ⧸ J) :=
    Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
  have h₃ : Module.length A (A ⧸ J) = Module.length A (S ⧸ I) :=
    (Ideal.quotientEquivAlg J I e' hI).toLinearEquiv.length_eq
  have h₄ : Module.length A (S ⧸ I) = Module.length S (S ⧸ I) :=
    Module.length_eq_of_surjective e.surjective
  rw [h₁, h₂, h₃, h₄]
  have hpow : I = IsLocalRing.maximalIdeal S ^ b := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
  rw [hpow]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal S b

private theorem axisCokernel :
    letI : Algebra (Plane k) k :=
      (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)).toAlgebra
    Nonempty (QuotSMulTop (y k) (Branch (x k)) ≃ₗ[Plane k] k) := by
  let R := Plane k
  let : Algebra R k := (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)).toAlgebra
  let I : Ideal R := Ideal.span {x k}
  let J : Ideal R := Ideal.span {y k}
  obtain ⟨_, _, _, hmax, _, _, _, e, he⟩ :=
    CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 2
  have hsum : I ⊔ J = IsLocalRing.maximalIdeal R := by
    change Ideal.span {x k} ⊔ Ideal.span {y k} = _
    rw [hmax, ← Ideal.span_union]
    congr 1
    ext p
    constructor
    · rintro (hx | hy)
      · exact ⟨1, (Set.mem_singleton_iff.mp hx).symm⟩
      · exact ⟨0, (Set.mem_singleton_iff.mp hy).symm⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [x, y]
  have hJ : Ideal.span {algebraMap R (R ⧸ I) (y k)} =
      J.map (Ideal.Quotient.mkₐ R I) := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eRes : IsLocalRing.ResidueField R ≃ₐ[R] k :=
    AlgEquiv.ofRingEquiv (f := e) he
  exact ⟨(scalarCokernelEquiv (A := R ⧸ I) (y k)).trans
    (((Ideal.quotientEquivAlgOfEq R hJ).trans
      ((DoubleQuot.quotQuotEquivQuotSupₐ R I J).trans
        ((Ideal.quotientEquivAlgOfEq R hsum).trans eRes))).toLinearEquiv)⟩

private theorem branch_multiplication_injective {f : Plane k}
    (e : Branch f ≃+* PowerSeries k) (hy : e (Ideal.Quotient.mk _ (y k)) ≠ 0) :
    Function.Injective (fun n : branchModule f => y k • n) := by
  intro a b hab
  have h := congrArg e hab
  change e (Ideal.Quotient.mk _ (y k) * a) = e (Ideal.Quotient.mk _ (y k) * b) at h
  simp only [map_mul] at h
  exact e.injective (mul_left_cancel₀ hy h)

private theorem plane_intersection [IsRegularLocalRing (Plane k)]
    (f : Plane k) (b : ℕ)
    (hy : Function.Injective (fun n : branchModule f => y k • n))
    (hlen : Module.length (Plane k) (QuotSMulTop (y k) (branchModule f)) = b) :
    IsFiniteLength (Plane k) (branchModule (y k) ⊗[Plane k] branchModule f) ∧
    intersectionEuler (branchModule (y k)) (branchModule f) = (b : ℤ) := by
  let R := Plane k
  let M := branchModule (y k)
  let N := branchModule f
  have htensor : Module.length R (M ⊗[R] N) = b :=
    (QuotSMulTop.equivQuotTensor (y k) N).length_eq.symm.trans hlen
  refine ⟨Module.length_ne_top_iff.mp (htensor ▸ ENat.natCast_ne_top b), ?_⟩
  have hyR : y k ≠ 0 := by
    intro h
    have hX := congrArg (MvPowerSeries.finSuccEquiv k 1) h
    simp at hX
  have hy_mem : y k ∈ IsLocalRing.maximalIdeal R := by
    have h := (CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 2).2.2.2.1
    rw [h]
    exact Ideal.subset_span ⟨0, rfl⟩
  have hreg : RingTheory.Sequence.IsRegular R [y k] :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R
      (fun r hr => (List.mem_singleton.mp hr).symm ▸ hy_mem)
      ((RingTheory.Sequence.isWeaklyRegular_singleton_iff R (y k)).2
        (fun _ _ h => mul_left_cancel₀ hyR h))
  have hweak : RingTheory.Sequence.IsWeaklyRegular N [y k] :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff N (y k)).2 hy
  -- The singleton Koszul resolution has the two free terms for multiplication by y.
  have hvanish : ∀ i : ℕ, 0 < i → Subsingleton (Tor M N i) := by
    intro i hi
    have := AdvCommAlg.Koszul.weaklyRegular_acyclic N [y k] hweak i hi
    have htor :=
      (koszulHomologyTorEquiv N [y k] hreg i).symm.injective.subsingleton
    have hList : AdvCommAlg.Koszul.listIdeal [y k] = Ideal.span {y k} :=
      Ideal.ofList_singleton (y k)
    change Subsingleton (Tor (ModuleCat.of (Plane k) (Plane k ⧸ Ideal.span {y k})) N i)
    rw [← hList]
    exact htor
  have htor₀ : Module.length R (Tor M N 0) = b :=
    (torZeroEquiv M N).length_eq.trans htensor
  change cutoffEuler M N _ = _
  rw [cutoffEuler_eq_of_vanishes_above M N 0 _ (Nat.zero_le _) hvanish]
  simp [cutoffEuler, IsolatedIntersectionEuler.Specs.cutoffEuler]
  change (Module.length R (Tor M N 0)).toNat = b
  rw [htor₀, ENat.toNat_natCast]

theorem tangency : Specs.tangency.{u} := by
  intro k _ b hb
  obtain ⟨e, hx, hy⟩ := tangencyBranch k b hb
  have hinj := branch_multiplication_injective k e.toRingEquiv
    (by rw [AlgEquiv.coe_toRingEquiv, hy]; exact pow_ne_zero _ PowerSeries.X_ne_zero)
  have hlen := cokernel_length k e.toRingEquiv b hy
  let reg := (CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 2).2.1
  let : IsRegularLocalRing (Plane k) := reg
  obtain ⟨hfinite, heuler⟩ := plane_intersection k (y k - x k ^ b) b hinj hlen
  exact ⟨⟨e, hx, hy⟩, hinj, hlen, hfinite, ⟨reg, heuler⟩⟩

theorem axes : Specs.axes.{u} := by
  intro k _
  obtain ⟨e, hx, hy⟩ := axisBranch k
  have hinj := branch_multiplication_injective k e.toRingEquiv
    (by rw [AlgEquiv.coe_toRingEquiv, hy]; exact PowerSeries.X_ne_zero)
  have hlen := cokernel_length k e.toRingEquiv 1 (by simpa using hy)
  let reg := (CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k 2).2.1
  let : IsRegularLocalRing (Plane k) := reg
  obtain ⟨hfinite, heuler⟩ := plane_intersection k (x k) 1 hinj hlen
  exact ⟨⟨e, hx, hy⟩, hinj, axisCokernel k, hfinite, ⟨reg, heuler⟩⟩

end CommutativeAlgebraNotes.Intersection.PlaneTangencyEuler
