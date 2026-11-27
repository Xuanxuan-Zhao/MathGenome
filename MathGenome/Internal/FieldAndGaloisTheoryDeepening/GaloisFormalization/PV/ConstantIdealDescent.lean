import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.ConstantIdealDescent
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Quotient

namespace GaloisFormalization.PV.Operator

open scoped TensorProduct

variable {kind : OperatorKind} {C S B : Type*}

/-- The given field maps onto exactly the constants of the operator ring. -/
def HasConstantField [Field C] [CommRing S] [Algebra C S] (E : Operator kind S) : Prop :=
  ∀ s : S, E.IsConstant s ↔ ∃ c : C, algebraMap C S c = s

theorem HasConstantField.isAlgebra [Field C] [CommRing S] [Algebra C S]
    {E : Operator kind S} (h : HasConstantField (C := C) E) :
    (trivial kind C).IsAlgebra E := by
  intro c
  have hc := (h (algebraMap C S c)).mpr ⟨c, rfl⟩
  cases kind with
  | differential =>
    change E (algebraMap C S c) = 0 at hc
    simpa only [trivial_differential_apply, _root_.map_zero] using hc.symm
  | difference =>
    exact hc.symm

section Coordinates

variable {D : Type*} {ι : Type*} [DecidableEq ι]
variable [Field C] [CommRing S] [CommRing D] [Algebra C S] [Algebra C D]
variable {E : Operator kind S} {G : Operator kind (S ⊗[C] D)}

private noncomputable abbrev coefficients (b : Module.Basis ι C D) :
    (S ⊗[C] D) ≃ₗ[C] (ι →₀ S) :=
  TensorProduct.equivFinsuppOfBasisRight b

private theorem coefficients_map (b : Module.Basis ι C D)
    (F : S ⊗[C] D →+ S ⊗[C] D) (f : S →+ S)
    (h : ∀ s i, F (s ⊗ₜ[C] b i) = f s ⊗ₜ[C] b i)
    (x : S ⊗[C] D) (i : ι) :
    coefficients b (F x) i = f (coefficients b x i) := by
  classical
  have hs (j : ι) (s : S) :
      (coefficients b).symm (Finsupp.single j s) = s ⊗ₜ[C] b j := by
    change (TensorProduct.equivFinsuppOfBasisRight b).symm (Finsupp.single j s) = _
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_single_index]
    exact TensorProduct.zero_tmul _ _
  obtain ⟨c, rfl⟩ := (coefficients b).symm.surjective x
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [_root_.map_add, Finsupp.add_apply, hc, hd]
  | single j s =>
    rw [hs j s, h s j, ← hs j (f s), ← hs j s]
    simp only [LinearEquiv.apply_symm_apply]
    by_cases hij : j = i
    · subst j
      simp
    · simp [Finsupp.single_eq_of_ne (Ne.symm hij)]

private def operatorAddHom {R : Type*} [CommRing R] (P : Operator kind R) : R →+ R where
  toFun := P
  map_zero' := P.map_zero
  map_add' := P.map_add

private theorem constantTensor_tmul (hG : Specs.tensorLaws (R := C) E (trivial kind D) G)
    (s : S) (d : D) : G (s ⊗ₜ[C] d) = E s ⊗ₜ[C] d := by
  cases kind with
  | differential =>
    have h : G (s ⊗ₜ[C] d) = E s ⊗ₜ[C] d + s ⊗ₜ[C] (0 : D) := hG.1 s d
    rw [h, TensorProduct.tmul_zero, add_zero]
  | difference => exact hG.1.1 s d

private theorem coefficients_operator (b : Module.Basis ι C D)
    (hG : Specs.tensorLaws (R := C) E (trivial kind D) G) (x : S ⊗[C] D) (i : ι) :
    coefficients b (G x) i = E (coefficients b x i) :=
  coefficients_map b (operatorAddHom G) (operatorAddHom E)
    (fun s j => constantTensor_tmul hG s (b j)) x i

private theorem coefficients_inverse (b : Module.Basis ι C D)
    {E : Operator .difference S} {G : Operator .difference (S ⊗[C] D)}
    (hG : Specs.tensorLaws (kind := .difference) (R := C) E (trivial .difference D) G)
    (x : S ⊗[C] D) (i : ι) :
    coefficients b (G.toRingEquiv.symm x) i = E.toRingEquiv.symm (coefficients b x i) :=
  coefficients_map b G.toRingEquiv.symm.toRingHom.toAddMonoidHom
    E.toRingEquiv.symm.toRingHom.toAddMonoidHom (fun s j => hG.1.2 s (b j)) x i

private theorem coefficients_left_mul (b : Module.Basis ι C D)
    (s : S) (x : S ⊗[C] D) (i : ι) :
    coefficients b ((s ⊗ₜ[C] (1 : D)) * x) i = s * coefficients b x i :=
  coefficients_map b (AddMonoidHom.mulLeft (s ⊗ₜ[C] (1 : D))) (AddMonoidHom.mulLeft s)
    (by intro t j; change (s ⊗ₜ[C] (1 : D)) * (t ⊗ₜ[C] b j) = (s * t) ⊗ₜ[C] b j
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]) x i

private theorem exists_tmul_of_constant (b : Module.Basis ι C D)
    (hC : HasConstantField (C := C) E)
    (hG : Specs.tensorLaws (R := C) E (trivial kind D) G)
    {x : S ⊗[C] D} (hx : G.IsConstant x) :
    ∃ d : D, (1 : S) ⊗ₜ[C] d = x := by
  classical
  have hc (i : ι) : E.IsConstant (coefficients b x i) := by
    cases kind with
    | differential =>
      change G x = 0 at hx
      change E (coefficients b x i) = 0
      rw [← coefficients_operator b hG, hx]
      simp
    | difference =>
      change G x = x at hx
      change E (coefficients b x i) = coefficients b x i
      rw [← coefficients_operator b hG, hx]
  choose c hcoeff using fun i => (hC (coefficients b x i)).mp (hc i)
  refine ⟨∑ i ∈ (coefficients b x).support, c i • b i, ?_⟩
  calc
    (1 : S) ⊗ₜ[C] (∑ i ∈ (coefficients b x).support, c i • b i) =
        ∑ i ∈ (coefficients b x).support, coefficients b x i ⊗ₜ[C] b i := by
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← TensorProduct.smul_tmul, ← hcoeff i, Algebra.smul_def, mul_one]
    _ = x :=
      (TensorProduct.equivFinsuppOfBasisRight_symm_apply b (coefficients b x)).symm.trans
        ((coefficients b).symm_apply_apply x)

/-- All constants of the tensor product come from its right factor. -/
theorem constantTensorConstants : Specs.constantTensorConstants := by
  classical
  intro kind C S D _ _ _ _ _ E G _ hC hG
  ext x
  rw [show x ∈ Specs.constantSubring G ↔ IsConstant (kind := kind) G x from by
    cases kind <;> rfl, _root_.RingHom.mem_range]
  change IsConstant (kind := kind) G x ↔ ∃ d : D, (1 : S) ⊗ₜ[C] d = x
  constructor
  · exact exists_tmul_of_constant (Module.Free.chooseBasis C D) hC hG
  · rintro ⟨d, rfl⟩
    exact Commutes.isConstant (D := trivial kind D) (f := (Algebra.TensorProduct.includeRight :
      D →ₐ[C] S ⊗[C] D).toRingHom) hG.2.2 (by cases kind <;> rfl)

private theorem ideal_eq_bot_of_zero_contraction (b : Module.Basis ι C D)
    (hS : E.IsSimple) (hC : HasConstantField (C := C) E)
    (hG : Specs.tensorLaws (R := C) E (trivial kind D) G)
    (I : _root_.Ideal (S ⊗[C] D)) (hI : G.IsStable (I : Set (S ⊗[C] D)))
    (hzero : ∀ d : D, (1 : S) ⊗ₜ[C] d ∈ I → d = 0) :
    I = ⊥ := by
  classical
  let : Nontrivial S := hS.1
  apply le_antisymm ?_ bot_le
  intro x₀ hx₀
  rw [_root_.Ideal.mem_bot]
  by_contra hx₀ne
  let P (n : ℕ) :=
    ∃ x ∈ I, x ≠ 0 ∧ (coefficients b x).support.card = n
  have hex : ∃ n, P n := ⟨_, x₀, hx₀, hx₀ne, rfl⟩
  obtain ⟨x, hx, hxne, hcard⟩ := Nat.find_spec hex
  let t := (coefficients b x).support
  have htn : t.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun h => hxne ((coefficients b).injective (h.trans ((coefficients b).map_zero).symm)))
  obtain ⟨i, hi⟩ := htn
  have minimal (z : S ⊗[C] D) (hz : z ∈ I)
      (hs : ∀ j ∉ t.erase i, coefficients b z j = 0) : z = 0 := by
    by_contra hzne
    have hsub : (coefficients b z).support ⊆ t.erase i := by
      intro j hj
      by_contra hj'
      exact (Finsupp.mem_support_iff.mp hj) (hs j hj')
    have hle := Nat.find_min' hex (show P (coefficients b z).support.card from
      ⟨z, hz, hzne, rfl⟩)
    have hlt := (Finset.card_le_card hsub).trans_lt (Finset.card_lt_card (Finset.erase_ssubset hi))
    exact (not_lt_of_ge hle) (hlt.trans_eq hcard)
  let K : _root_.Ideal S :=
    { carrier := {s | ∃ y ∈ I, (∀ j ∉ t, coefficients b y j = 0) ∧ coefficients b y i = s}
      zero_mem' := ⟨0, I.zero_mem, by simp, by simp⟩
      add_mem' := by
        rintro a c ⟨y, hy, hys, hya⟩ ⟨z, hz, hzs, hzc⟩
        refine ⟨y + z, I.add_mem hy hz, ?_, ?_⟩
        · intro j hj
          simp only [_root_.map_add, Finsupp.add_apply, hys j hj, hzs j hj, add_zero]
        · simp only [_root_.map_add, Finsupp.add_apply, hya, hzc]
      smul_mem' := by
        rintro a s ⟨y, hy, hys, hya⟩
        refine ⟨(a ⊗ₜ[C] (1 : D)) * y, I.mul_mem_left _ hy, ?_, ?_⟩
        · intro j hj
          rw [coefficients_left_mul, hys j hj, mul_zero]
        · rw [coefficients_left_mul, hya, smul_eq_mul] }
  have hforward {s : S} (hs : s ∈ K) : E s ∈ K := by
    obtain ⟨y, hy, hys, hya⟩ := hs
    exact ⟨G y, hI.apply_mem hy,
      fun j hj => by rw [coefficients_operator b hG, hys j hj, Operator.map_zero],
      by rw [coefficients_operator b hG, hya]⟩
  have hstable : E.IsStable (K : Set S) := by
    cases kind with
    | differential =>
      change ∀ ⦃s : S⦄, s ∈ K → E s ∈ K
      exact fun _ hs => hforward hs
    | difference =>
      change (∀ ⦃s : S⦄, s ∈ K → E s ∈ K) ∧
        (∀ ⦃s : S⦄, s ∈ K → E.toRingEquiv.symm s ∈ K)
      refine ⟨fun _ hs => hforward hs, ?_⟩
      rintro s ⟨y, hy, hys, hya⟩
      exact ⟨G.toRingEquiv.symm y, hI.symm_apply_mem hy,
        fun j hj => by rw [coefficients_inverse b hG, hys j hj, _root_.map_zero],
        by rw [coefficients_inverse b hG, hya]⟩
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hxK : coefficients b x i ∈ K :=
      ⟨x, hx, fun j hj => by exact Finsupp.notMem_support_iff.mp hj, rfl⟩
    exact (Finsupp.mem_support_iff.mp hi) (_root_.Ideal.mem_bot.mp (hbot ▸ hxK))
  have hK := (hS.2 K hstable).resolve_left hKne
  have h1 : (1 : S) ∈ K := hK.symm ▸ (show (1 : S) ∈ (⊤ : _root_.Ideal S) by simp)
  obtain ⟨y, hy, hys, hyi⟩ := h1
  have hyne : y ≠ 0 := by
    intro hy0
    simp [hy0] at hyi
  have hyconst : G.IsConstant y := by
    cases kind with
    | differential =>
      change G y = 0
      apply minimal (G y) (hI.apply_mem hy)
      intro j hj
      rw [coefficients_operator b hG]
      by_cases hji : j = i
      · subst j
        rw [hyi]
        exact E.toDerivation.map_one_eq_zero
      · rw [hys j (fun h => hj (Finset.mem_erase.mpr ⟨hji, h⟩)), Operator.map_zero]
    | difference =>
      change G y = y
      apply sub_eq_zero.mp
      apply minimal (G y - y) (I.sub_mem (hI.apply_mem hy) hy)
      intro j hj
      simp only [_root_.map_sub, Finsupp.sub_apply, coefficients_operator b hG]
      by_cases hji : j = i
      · subst j
        rw [hyi]
        exact sub_eq_zero.mpr E.toRingEquiv.map_one
      · rw [hys j (fun h => hj (Finset.mem_erase.mpr ⟨hji, h⟩)), Operator.map_zero, sub_zero]
  obtain ⟨d, hd⟩ := exists_tmul_of_constant b hC hG hyconst
  have hd0 := hzero d (hd.symm ▸ hy)
  exact hyne (by simpa [hd0] using hd.symm)

end Coordinates

private theorem stable_image {R T : Type*} [CommRing R] [CommRing T]
    {P : Operator kind R} {Q : Operator kind T} {f : R →+* T}
    (hf : Function.Surjective f) (hcomm : P.Commutes Q f)
    {I : _root_.Ideal R} (hI : P.IsStable (I : Set R)) :
    Q.IsStable (I.map f : Set T) := by
  have hforward {x : T} (hx : x ∈ I.map f) : Q x ∈ I.map f := by
    obtain ⟨y, hy, rfl⟩ := (_root_.Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [← hcomm y]
    exact _root_.Ideal.mem_map_of_mem f (hI.apply_mem hy)
  cases kind with
  | differential =>
    change ∀ ⦃x : T⦄, x ∈ I.map f → Q x ∈ I.map f
    exact fun _ hx => hforward hx
  | difference =>
    change (∀ ⦃x : T⦄, x ∈ I.map f → Q x ∈ I.map f) ∧
      (∀ ⦃x : T⦄, x ∈ I.map f → Q.toRingEquiv.symm x ∈ I.map f)
    refine ⟨fun _ hx => hforward hx, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (_root_.Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [← hcomm.difference_symm y]
    exact _root_.Ideal.mem_map_of_mem f (hI.symm_apply_mem hy)

/-- Stable ideals in a tensor product with constants are extended from the right factor. -/
theorem constantIdealDescent : Specs.constantIdealDescent := by
  classical
  intro kind C S D _ _ _ _ _ E G hS hC hG I hI
  change Operator kind S at E
  change Operator kind (S ⊗[C] D) at G
  change IsSimple (kind := kind) E at hS
  change HasConstantField (kind := kind) (C := C) E at hC
  change IsStable (kind := kind) G (I : Set (S ⊗[C] D)) at hI
  let i := (Algebra.TensorProduct.includeRight : D →ₐ[C] S ⊗[C] D).toRingHom
  let j := I.comap i
  let J := j.map i
  change I = J
  have hJI : J ≤ I := _root_.Ideal.map_le_iff_le_comap.mpr le_rfl
  let e : (S ⊗[C] (D ⧸ j)) ≃ₐ[S] (S ⊗[C] D) ⧸ J :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := C) S D S j
  let f := e.symm.toRingEquiv.toRingHom.comp (_root_.Ideal.Quotient.mk J)
  have hf : Function.Surjective f := e.symm.surjective.comp _root_.Ideal.Quotient.mk_surjective
  have hfker : _root_.RingHom.ker f = J := by
    change _root_.RingHom.ker (e.symm.toRingEquiv.toRingHom.comp (_root_.Ideal.Quotient.mk J)) = J
    rw [_root_.RingHom.ker_comp_of_injective _ e.symm.injective]
    ext x
    exact _root_.Ideal.Quotient.eq_zero_iff_mem
  have hft (s : S) (d : D) : f (s ⊗ₜ[C] d) = s ⊗ₜ[C] (_root_.Ideal.Quotient.mk j d) :=
    Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul (R := C) S D S j s d
  let G' : Operator kind (S ⊗[C] (D ⧸ j)) :=
    tensor hC.isAlgebra (trivial_isAlgebra kind)
  have hG' : Specs.tensorLaws (R := C) E (trivial kind (D ⧸ j)) G' :=
    tensor_laws hC.isAlgebra (trivial_isAlgebra kind)
  have hcomm : Commutes (kind := kind) G G' f := by
    intro x
    change f (apply G x) = G' (f x)
    induction x using TensorProduct.inductionOn with
    | tmul s d =>
      rw [constantTensor_tmul (kind := kind) hG, hft, hft, constantTensor_tmul hG']
    | add x y hx hy =>
      simp only [Operator.map_add, _root_.map_add, hx, hy]
  have hpre : (I.map f).comap f = I := by
    rw [_root_.Ideal.comap_map_of_surjective f hf, ← _root_.RingHom.ker_eq_comap_bot,
      hfker, sup_of_le_left hJI]
  have hzero (d' : D ⧸ j) (hd' : (1 : S) ⊗ₜ[C] d' ∈ I.map f) : d' = 0 := by
    obtain ⟨d, rfl⟩ := _root_.Ideal.Quotient.mk_surjective d'
    rw [← hft] at hd'
    have hdI : i d ∈ (I.map f).comap f := hd'
    rw [hpre] at hdI
    exact _root_.Ideal.Quotient.eq_zero_iff_mem.mpr hdI
  have hbot := ideal_eq_bot_of_zero_contraction (Module.Free.chooseBasis C (D ⧸ j))
    hS hC hG' (I.map f) (stable_image hf hcomm hI) hzero
  rw [hbot, ← _root_.RingHom.ker_eq_comap_bot, hfker] at hpre
  exact hpre.symm

section Multiplication

variable [CommRing C] [CommRing S] [CommRing B]
variable [Algebra C S] [Algebra C B] [Algebra S B] [IsScalarTower C S B]

/-- Multiplication of the two factors inside their common extension. -/
def constantTensorMul (D : _root_.Subalgebra C B) : S ⊗[C] D →ₐ[S] B :=
  Algebra.TensorProduct.lift (Algebra.ofId S B) D.val (fun _ _ => Commute.all _ _)

@[simp] theorem constantTensorMul_tmul (D : _root_.Subalgebra C B) (s : S) (d : D) :
    constantTensorMul (S := S) D (s ⊗ₜ[C] d) = algebraMap S B s * (d : B) :=
  rfl

theorem constantTensorMul_surjective (D : _root_.Subalgebra C B)
    (hgen : Algebra.adjoin S (D : Set B) = ⊤) :
    Function.Surjective (constantTensorMul (S := S) D) := by
  let f := constantTensorMul (S := S) D
  have hle : Algebra.adjoin S (D : Set B) ≤ f.range := by
    refine Algebra.adjoin_le ?_
    intro d hd
    exact ⟨(1 : S) ⊗ₜ[C] (⟨d, hd⟩ : D), by simp [f]⟩
  rw [hgen] at hle
  intro b
  exact hle (show b ∈ (⊤ : _root_.Subalgebra S B) by simp)

theorem constantTensorMul_commutes {E : Operator kind S} {F : Operator kind B}
    (D : _root_.Subalgebra C B) {G : Operator kind (S ⊗[C] D)}
    (hEF : E.IsAlgebra F) (hG : Specs.tensorLaws (R := C) E (trivial kind D) G)
    (hD : ∀ d : D, F.IsConstant (d : B)) :
    G.Commutes F (constantTensorMul (S := S) D) := by
  let f := constantTensorMul (S := S) D
  intro x
  change f (G x) = F (f x)
  induction x using TensorProduct.inductionOn with
  | tmul s d =>
    have hs := hEF s
    change algebraMap S B (E s) = F (algebraMap S B s) at hs
    have hd := hD d
    cases kind with
    | differential =>
      have htmul : G (s ⊗ₜ[C] d) = E s ⊗ₜ[C] d + s ⊗ₜ[C] (0 : D) := hG.1 s d
      rw [htmul, TensorProduct.tmul_zero, add_zero]
      simp only [f, constantTensorMul_tmul]
      change algebraMap S B (E s) * (d : B) =
        F.toDerivation (algebraMap S B s * (d : B))
      change F.toDerivation (d : B) = 0 at hd
      rw [F.toDerivation.leibniz, hd, smul_zero, zero_add, smul_eq_mul, mul_comm (d : B)]
      exact congrArg (fun b => b * (d : B)) hs
    | difference =>
      have htmul : G (s ⊗ₜ[C] d) = E s ⊗ₜ[C] d := hG.1.1 s d
      rw [htmul]
      simp only [f, constantTensorMul_tmul]
      change algebraMap S B (E s) * (d : B) =
        F.toRingEquiv (algebraMap S B s * (d : B))
      change F.toRingEquiv (d : B) = (d : B) at hd
      rw [F.toRingEquiv.map_mul, hd]
      exact congrArg (fun b => b * (d : B)) hs
  | add x y hx hy =>
    simp only [Operator.map_add, _root_.map_add, hx, hy]

/-- An extension generated by constants is identified with the tensor product by multiplication. -/
theorem constantTensorMulIsEquiv : Specs.constantTensorMulIsEquiv := by
  intro kind C S B _ _ _ _ _ _ _ E F D G hS hC hEF hG hD hgen
  change Operator kind S at E
  change Operator kind B at F
  change Operator kind (S ⊗[C] D) at G
  change IsExtension (kind := kind) E F at hEF
  let f := constantTensorMul (S := S) D
  let I := _root_.RingHom.ker f.toRingHom
  have hcomm : Commutes (kind := kind) G F f :=
    constantTensorMul_commutes D hEF.1 hG hD
  have hforward {x : S ⊗[C] D} (hx : x ∈ I) : apply G x ∈ I := by
    change f x = 0 at hx
    change f (apply G x) = 0
    rw [hcomm x, hx, Operator.map_zero]
  have hI : IsStable (kind := kind) G (I : Set (S ⊗[C] D)) := by
    cases kind with
    | differential =>
      change ∀ ⦃x : S ⊗[C] D⦄, x ∈ I → apply G x ∈ I
      exact fun _ hx => hforward hx
    | difference =>
      change (∀ ⦃x : S ⊗[C] D⦄, x ∈ I → apply G x ∈ I) ∧
        (∀ ⦃x : S ⊗[C] D⦄, x ∈ I → (toRingEquiv G).symm x ∈ I)
      refine ⟨fun _ hx => hforward hx, ?_⟩
      intro x hx
      change f x = 0 at hx
      change f ((toRingEquiv G).symm x) = 0
      rw [hcomm.difference_symm x, hx, _root_.map_zero]
  let i := (Algebra.TensorProduct.includeRight : D →ₐ[C] S ⊗[C] D).toRingHom
  have hj : I.comap i = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro d hd
    change f ((1 : S) ⊗ₜ[C] d) = 0 at hd
    have hval : (d : B) = 0 := by simpa [f] using hd
    exact _root_.Ideal.mem_bot.mpr (Subtype.ext hval)
  have hdesc : I = (I.comap i).map i := constantIdealDescent hS hC hG I hI
  rw [hj, _root_.Ideal.map_bot] at hdesc
  have hinj : Function.Injective f :=
    (_root_.RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr hdesc
  exact ⟨⟨AlgEquiv.ofBijective f ⟨hinj, constantTensorMul_surjective D hgen⟩, hcomm⟩, rfl⟩

end Multiplication

end GaloisFormalization.PV.Operator
