import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.FirstOrder
import Mathlib.Tactic.Abel

namespace LieNotes.BialgebraDeformation

open TensorProduct LinearMap
open scoped TensorProduct

noncomputable section

variable {k : Type*} [Field k]

local notation "s" => (DualNumber.eps : D k)

section Coefficients

variable {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

private theorem scaled_generator (a : D k) (x : X) :
    a ⊗ₜ[k] x = a • ((1 : D k) ⊗ₜ[k] x) := by
  rw [TensorProduct.smul_tmul']
  change a ⊗ₜ[k] x = (a * 1) ⊗ₜ[k] x
  rw [mul_one]

private theorem extension_ext {Z : Type*} [AddCommMonoid Z] [Module (D k) Z]
    {p q : Extended k X →ₗ[D k] Z}
    (h : ∀ x : X, p (1 ⊗ₜ[k] x) = q (1 ⊗ₜ[k] x)) : p = q := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a x => rw [scaled_generator a x, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp] theorem coeff₀_tmul (a : D k) (x : X) :
    coeff₀ (a ⊗ₜ[k] x) = a.fst • x := by
  rfl

@[simp] theorem coeff₁_tmul (a : D k) (x : X) :
    coeff₁ (a ⊗ₜ[k] x) = a.snd • x := by
  rfl

private theorem scalar_decomposition (a : D k) :
    a = a.fst • (1 : D k) + a.snd • s := by
  apply TrivSqZeroExt.ext <;> simp

private theorem decompose_coefficients (x : Extended k X) :
    x = (1 : D k) ⊗ₜ[k] coeff₀ x + s ⊗ₜ[k] coeff₁ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [coeff₀_tmul, coeff₁_tmul, ← smul_tmul, ← add_tmul]
    congr 1
    exact scalar_decomposition a
  | add x y hx hy =>
    rw [map_add, map_add, tmul_add, tmul_add, add_add_add_comm, ← hx, ← hy]

theorem coefficient_decomposition : Expected.coefficient_decomposition := by
  intro k X _ _ _ x
  exact decompose_coefficients x

@[simp] theorem jet_tmul (p q : X →ₗ[k] Y) (a : D k) (x : X) :
    jet p q (a ⊗ₜ[k] x) = a ⊗ₜ[k] p x + (s * a) ⊗ₜ[k] q x := rfl

private theorem jet_inj {p q p' q' : X →ₗ[k] Y} :
    jet p q = jet p' q' ↔ p = p' ∧ q = q' := by
  constructor
  · intro h
    constructor
    · ext x
      simpa using congrArg (fun l : Extended k X →ₗ[D k] Extended k Y =>
        coeff₀ (l (1 ⊗ₜ[k] x))) h
    · ext x
      simpa using congrArg (fun l : Extended k X →ₗ[D k] Extended k Y =>
        coeff₁ (l (1 ⊗ₜ[k] x))) h
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] private theorem jet_id : jet (LinearMap.id : X →ₗ[k] X) 0 = LinearMap.id := by
  apply extension_ext
  intro x
  simp

private theorem jet_comp {Z : Type*} [AddCommGroup Z] [Module k Z]
    (p q : X →ₗ[k] Y) (r t : Y →ₗ[k] Z) :
    (jet r t).comp (jet p q) = jet (r.comp p) (r.comp q + t.comp p) := by
  apply extension_ext
  intro x
  simp only [comp_apply, jet_tmul, mul_one, map_add, DualNumber.eps_mul_eps,
    zero_tmul, add_zero, add_apply, tmul_add]
  abel_nf

end Coefficients

section Transport

variable {R : Type*} [CommSemiring R]
variable {X Y Z X' Y' Z' : Type*}
variable [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
variable [AddCommMonoid Z] [Module R Z] [AddCommMonoid X'] [Module R X']
variable [AddCommMonoid Y'] [Module R Y'] [AddCommMonoid Z'] [Module R Z']

@[simp] private theorem transport_at (e : X ≃ₗ[R] X') (f : Y ≃ₗ[R] Y') (p : X →ₗ[R] Y) (x : X) :
    transport e f p (e x) = f (p x) := by
  simp [transport]

private theorem transport_inj (e : X ≃ₗ[R] X') (f : Y ≃ₗ[R] Y') :
    Function.Injective (transport e f) := by
  intro p q h
  ext x
  apply f.injective
  simpa using LinearMap.congr_fun h (e x)

private theorem transport_comp (e : X ≃ₗ[R] X') (f : Y ≃ₗ[R] Y') (g : Z ≃ₗ[R] Z')
    (p : X →ₗ[R] Y) (q : Y →ₗ[R] Z) :
    (transport f g q).comp (transport e f p) = transport e g (q.comp p) := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp

@[simp] private theorem transport_id (e : X ≃ₗ[R] X') :
    transport e e (LinearMap.id : X →ₗ[R] X) = LinearMap.id := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp

@[simp] private theorem transport_refl (p : X →ₗ[R] Y) :
    transport (.refl R X) (.refl R Y) p = p := rfl

end Transport

section TensorCalculus

variable {X Y Z W : Type*}
variable [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
variable [AddCommGroup Z] [Module k Z] [AddCommGroup W] [Module k W]
variable {X' Y' Z' W' : Type*}
variable [AddCommMonoid X'] [Module (D k) X'] [AddCommMonoid Y'] [Module (D k) Y']
variable [AddCommMonoid Z'] [Module (D k) Z'] [AddCommMonoid W'] [Module (D k) W']

local notation "T" => tensorCoordinates (k := k)

@[simp] private theorem tensorCoordinates_tmul (e : Extended k X ≃ₗ[D k] X')
    (f : Extended k Y ≃ₗ[D k] Y') (a : D k) (x : X) (y : Y) :
    T e f (a ⊗ₜ[k] (x ⊗ₜ[k] y)) = e (a ⊗ₜ[k] x) ⊗ₜ[D k] f (1 ⊗ₜ[k] y) := by
  simp [tensorCoordinates]

private theorem transport_extension_ext {V U : Type*} [AddCommMonoid V] [Module (D k) V]
    [AddCommMonoid U] [Module (D k) U]
    (e : Extended k X ≃ₗ[D k] V) {p q : V →ₗ[D k] U}
    (h : ∀ x : X, p (e (1 ⊗ₜ[k] x)) = q (e (1 ⊗ₜ[k] x))) : p = q := by
  apply (transport_inj e.symm (.refl (D k) U))
  apply extension_ext
  exact h

private theorem map_jet
    (e : Extended k X ≃ₗ[D k] X') (f : Extended k Y ≃ₗ[D k] Y')
    (h : Extended k Z ≃ₗ[D k] Z') (i : Extended k W ≃ₗ[D k] W')
    (p q : X →ₗ[k] Z) (r t : Y →ₗ[k] W) :
    TensorProduct.map (transport e h (jet p q)) (transport f i (jet r t)) =
      transport (T e f) (T h i) (jet (TensorProduct.map p r)
        (TensorProduct.map q r + TensorProduct.map p t)) := by
  apply transport_extension_ext (T e f)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [transport_at, tensorCoordinates_tmul]
    simp only [TensorProduct.map_tmul, transport_at, jet_tmul, mul_one, add_apply,
      tmul_add, map_add, tensorCoordinates_tmul, add_tmul]
    rw [scaled_generator s (q x), scaled_generator s (t y), scaled_generator s (p x)]
    simp only [map_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    have sq (z : Z' ⊗[D k] W') : s • (s • z) = 0 := by
      calc
        s • (s • z) = (s * s) • z := (mul_smul s s z).symm
        _ = 0 := by
          rw [DualNumber.eps_mul_eps]
          exact zero_smul (D k) z
    rw [sq, add_zero, add_assoc]
  | add x y hx hy =>
    simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy

end TensorCalculus

section StructuralMaps

variable {B : Type*} [Ring B] [Bialgebra k B]

local notation "V" => Extended k B
local notation "E" => carrierCoordinates k B
local notation "S" => scalarCoordinates k
local notation "T" => tensorCoordinates (k := k)
local notation "Q" => squareCoordinates k B
local notation "A" => LinearEquiv.toLinearMap (TensorProduct.assoc k B B B)

private theorem transport_jet_id {X X' : Type*} [AddCommGroup X] [Module k X]
    [AddCommMonoid X'] [Module (D k) X'] (e : Extended k X ≃ₗ[D k] X') :
    transport e e (jet (LinearMap.id : X →ₗ[k] X) 0) = LinearMap.id := by
  rw [jet_id, transport_id]

private theorem transport_jet_eq {X Y X' Y' : Type*}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommMonoid X'] [Module (D k) X'] [AddCommMonoid Y'] [Module (D k) Y']
    (e : Extended k X ≃ₗ[D k] X') (f : Extended k Y ≃ₗ[D k] Y')
    (p q p' q' : X →ₗ[k] Y) :
    transport e f (jet p q) = transport e f (jet p' q') ↔ p = p' ∧ q = q' :=
  (transport_inj e f).eq_iff.trans jet_inj

private theorem constant_transport {X Y X' Y' : Type*}
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [AddCommMonoid X'] [Module (D k) X'] [AddCommMonoid Y'] [Module (D k) Y']
    (e : Extended k X ≃ₗ[D k] X') (f : Extended k Y ≃ₗ[D k] Y')
    (p : X →ₗ[k] Y) (q : X' →ₗ[D k] Y')
    (h : ∀ x : X, q (e (1 ⊗ₜ[k] x)) = f (1 ⊗ₜ[k] p x)) :
    q = transport e f (jet p 0) := by
  apply transport_extension_ext e
  intro x
  simpa only [transport_at, jet_tmul, zero_apply, tmul_zero, add_zero] using h x

private theorem generator_scalar {X : Type*} [AddCommGroup X] [Module k X] (a : k) (x : X) :
    (1 : D k) ⊗ₜ[k] (a • x) = (a • (1 : D k)) • ((1 : D k) ⊗ₜ[k] x) := by
  rw [← TensorProduct.smul_tmul, scaled_generator (a • (1 : D k))]

private theorem transported_lid :
    (TensorProduct.lid (D k) V).toLinearMap =
      transport (T S E) E (jet (TensorProduct.lid k B).toLinearMap 0) := by
  apply constant_transport
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorCoordinates_tmul, LinearEquiv.coe_toLinearMap, TensorProduct.lid_tmul,
      AlgebraTensorModule.rid_tmul, LinearEquiv.refl_apply, generator_scalar]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

private theorem transported_rid :
    (TensorProduct.rid (D k) V).toLinearMap =
      transport (T E S) E (jet (TensorProduct.rid k B).toLinearMap 0) := by
  apply constant_transport
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [tensorCoordinates_tmul, LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul,
      AlgebraTensorModule.rid_tmul, LinearEquiv.refl_apply, generator_scalar]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

private theorem transported_scalar_lid :
    (TensorProduct.lid (D k) (D k)).toLinearMap =
      transport (T S S) S (jet (TensorProduct.lid k k).toLinearMap 0) := by
  apply constant_transport
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [tensorCoordinates_tmul, LinearEquiv.coe_toLinearMap, TensorProduct.lid_tmul,
      AlgebraTensorModule.rid_tmul, ← Algebra.algebraMap_eq_smul_one, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

private theorem transported_scalar_lid_symm :
    (TensorProduct.lid (D k) (D k)).symm.toLinearMap =
      transport S (T S S) (jet (TensorProduct.lid k k).symm.toLinearMap 0) := by
  apply constant_transport
  intro a
  simp only [LinearEquiv.coe_toLinearMap, TensorProduct.lid_symm_apply, tensorCoordinates_tmul,
    AlgebraTensorModule.rid_tmul, one_smul]

private theorem transported_assoc :
    (TensorProduct.assoc (D k) V V V).toLinearMap =
      transport (T Q E) (T E Q) (jet A 0) := by
  apply constant_transport
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul w c =>
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [squareCoordinates, carrierCoordinates, tensorCoordinates, LinearEquiv.trans_apply,
        AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul]
    | add x y hx hy => simp only [add_tmul, tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

private theorem transported_middleFlip :
    middleFlip (D k) V =
      transport (T Q Q) (T Q Q) (jet (middleFlip k B) 0) := by
  apply constant_transport
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul w v =>
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      induction v using TensorProduct.inductionOn with
      | tmul c d =>
        simp only [squareCoordinates, carrierCoordinates, tensorCoordinates, LinearEquiv.trans_apply,
          AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
          LinearEquiv.coe_toLinearMap, tensorTensorTensorComm_tmul]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [add_tmul, tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

end StructuralMaps

section OriginalLaws

variable {B : Type*} [Ring B] [Bialgebra k B]

local notation "m" => mulTensor k B
local notation "d" => comul k B
local notation "e" => unit k B
local notation "c" => counit k B

@[simp] private theorem mulTensor_tmul (a b : B) : m (a ⊗ₜ[k] b) = a * b := rfl

private theorem original_laws : Laws (mulTensor k B) (comul k B) (unit k B) (counit k B) := by
  constructor
  · apply TensorProduct.ext'
    intro a b
    simp [Algebra.smul_def]
  · apply TensorProduct.ext'
    intro b a
    simp [Algebra.smul_def, Algebra.commutes]
  · apply TensorProduct.ext_threefold
    intro a b z
    simp [mul_assoc]
  · have h := Coalgebra.rTensor_counit_comp_comul (R := k) (A := B)
    rw [rTensor_def] at h
    rw [h]
    ext x
    simp
  · have h := Coalgebra.lTensor_counit_comp_comul (R := k) (A := B)
    rw [lTensor_def] at h
    rw [h]
    ext x
    simp
  · simpa only [rTensor_def, lTensor_def] using Coalgebra.coassoc (R := k) (A := B)
  · apply LinearMap.ext_ring
    simp
  · apply TensorProduct.ext'
    intro a b
    simp [smul_eq_mul]
  · apply LinearMap.ext_ring
    simp [Algebra.TensorProduct.one_def]
  · have tensorMul :
        (TensorProduct.map m m).comp (middleFlip k B) =
          TensorProduct.lift (LinearMap.mul k (B ⊗[k] B)) := by
      apply TensorProduct.ext_fourfold'
      intro a b x y
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [← LinearMap.comp_assoc, tensorMul]
    apply TensorProduct.ext'
    intro a b
    simpa only [comp_apply, mulTensor_tmul, TensorProduct.map_tmul,
      TensorProduct.lift.tmul, LinearMap.mul_apply'] using Bialgebra.comul_mul (R := k) a b

end OriginalLaws

section Changes

variable {B : Type*} [Ring B] [Bialgebra k B]

local notation "E" => carrierCoordinates k B
local notation "m" => mulTensor k B
local notation "d" => comul k B
local notation "e" => unit k B
local notation "c" => counit k B
local notation "ι" => (LinearMap.id : B →ₗ[k] B)

local instance dualNumberTower : IsScalarTower k (D k) (D k) where
  smul_assoc a b x := by
    change (a • b) * x = a • (b * x)
    exact (congrArg (· * x) (Algebra.smul_def a b)).trans
      ((mul_assoc _ _ _).trans (Algebra.smul_def a (b * x)).symm)

private theorem comp_unit_zero {Y : Type*} [AddCommGroup Y] [Module k Y]
    (p : B →ₗ[k] Y) : p.comp e = 0 ↔ p 1 = 0 := by
  constructor
  · intro h
    simpa using LinearMap.congr_fun h 1
  · intro h
    apply LinearMap.ext_ring
    simpa using h

private theorem jet_reduces (u : B →ₗ[k] B) (x : Extended k B) :
    coeff₀ (jet ι u x) = coeff₀ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp [TrivSqZeroExt.fst_mul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

private theorem allowed_jet (T : Change k B) (u : B →ₗ[k] B)
    (hT : T.toLinearMap = jet ι u) : Allowed T ↔ NormalizedChange u := by
  have T_as_transport : T.toLinearMap = transport E E (jet ι u) := hT
  have reduce (x : Extended k B) : coeff₀ (T x) = coeff₀ x :=
    (congrArg (fun p : Extended k B →ₗ[D k] Extended k B => coeff₀ (p x)) hT).trans
      (jet_reduces u x)
  simp only [Allowed, NormalizedChange, reduce, implies_true, true_and]
  rw [T_as_transport]
  simp only [fixedUnit, fixedCounit, transport_comp, jet_comp, LinearMap.id_comp,
    LinearMap.comp_id, comp_zero, zero_add, add_zero, transport_jet_eq,
    true_and, comp_unit_zero]

/-- A coordinate change reducing to the identity is determined by its infinitesimal
coefficient on the generators `1 ⊗ b`. -/
theorem allowed_iff : Expected.allowed_iff := by
  intro k B _ _ _ _ T
  constructor
  · intro h
    let u : B →ₗ[k] B := coeff₁.comp ((T.toLinearMap.restrictScalars k).comp (TensorProduct.mk k _ _ 1))
    have hT : T.toLinearMap = jet LinearMap.id u := by
      apply extension_ext
      intro b
      change T (1 ⊗ₜ[k] b) = _
      have hb := coefficient_decomposition (T (1 ⊗ₜ[k] b))
      rw [h.1] at hb
      simpa [u] using hb
    refine ⟨u, ⟨(allowed_jet T u hT).mp h, hT⟩, ?_⟩
    intro v hv
    exact (jet_inj.mp (hv.2.symm.trans hT)).2
  · rintro ⟨u, ⟨hn, hT⟩, _⟩
    exact (allowed_jet T u hT).mpr hn

private def coordinateEquiv (u : B →ₗ[k] B) : Change k B :=
  LinearEquiv.ofLinearMap (jet ι u) (jet ι (-u))
    (by rw [jet_comp]; simp) (by rw [jet_comp]; simp)

/-- The map `1 + s*u` is invertible with inverse `1 - s*u`. -/
theorem coordinate_change : Expected.coordinate_change := by
  intro k B _ _ _ _ u
  exact ⟨coordinateEquiv u, rfl, rfl, allowed_jet (coordinateEquiv u) u rfl⟩

private theorem tensorDerivative_neg (u : B →ₗ[k] B) :
    tensorDerivative (-u) = -tensorDerivative u := by
  simp only [tensorDerivative, ← rTensor_def, ← lTensor_def, rTensor_neg, lTensor_neg, neg_add]

theorem pullback : Expected.pullback := by
  intro k B _ _ _ _ T u hT f g
  have hTe : T = coordinateEquiv u := LinearEquiv.toLinearMap_injective hT
  have hTi : T.symm.toLinearMap = jet LinearMap.id (-u) := by
    rw [hTe]
    rfl
  have hT' : T.toLinearMap = transport (carrierCoordinates k B) (carrierCoordinates k B)
      (jet LinearMap.id u) := hT
  have hTi' : T.symm.toLinearMap = transport (carrierCoordinates k B) (carrierCoordinates k B)
      (jet LinearMap.id (-u)) := hTi
  constructor
  · simp only [pullMul, hT', hTi', deformedMul, map_jet, transport_comp, jet_comp,
      TensorProduct.map_id, LinearMap.id_comp, LinearMap.comp_id,
      tensorDerivative, changedMul, LinearMap.neg_comp, sub_eq_add_neg, add_comm]
  · simp only [pullComul, hT', hTi', deformedComul, map_jet, transport_comp, jet_comp,
      TensorProduct.map_id, LinearMap.id_comp, LinearMap.comp_id, transport_jet_eq, true_and,
      changedComul, sub_eq_add_neg]
    rw [← tensorDerivative, tensorDerivative_neg, LinearMap.neg_comp, add_comm _ g]

theorem equivalent_iff : Expected.equivalent_iff := by
  intro k B _ _ _ _ x y
  constructor
  · rintro ⟨T, hT, hm, hd⟩
    obtain ⟨u, ⟨hn, hu⟩, _⟩ := allowed_iff T |>.mp hT
    obtain ⟨hp, hq⟩ := pullback T u hu x.f x.g
    rw [hp] at hm
    rw [hq] at hd
    exact ⟨u, hn, ((transport_jet_eq ..).mp hm).2.symm, ((transport_jet_eq ..).mp hd).2.symm⟩
  · rintro ⟨u, hn, hm, hd⟩
    obtain ⟨T, hu, _, hT⟩ := coordinate_change u
    obtain ⟨hp, hq⟩ := pullback T u hu x.f x.g
    exact ⟨T, hT.mpr hn, hp.trans (congrArg deformedMul hm.symm),
      hq.trans (congrArg deformedComul hd.symm)⟩

private theorem tensorDerivative_add (u v : B →ₗ[k] B) :
    tensorDerivative (u + v) = tensorDerivative u + tensorDerivative v := by
  simp only [tensorDerivative, TensorProduct.map_add_left, TensorProduct.map_add_right]
  abel

/-- Pullback by the allowed changes defines an equivalence relation on deformations. -/
theorem equivalent_isEquivalence [CharZero k] :
    Equivalence (Equivalent (k := k) (B := B)) := by
  constructor
  · intro x
    apply (equivalent_iff x x).2
    exact ⟨0, by simp [NormalizedChange], by simp [changedMul, tensorDerivative],
      by simp [changedComul, tensorDerivative]⟩
  · intro x y h
    obtain ⟨u, hu, hm, hd⟩ := (equivalent_iff x y).1 h
    apply (equivalent_iff y x).2
    refine ⟨-u, ⟨by simp [hu.1], by simp [hu.2]⟩, ?_, ?_⟩
    · rw [hm]
      simp only [changedMul, tensorDerivative_neg, LinearMap.comp_neg, LinearMap.neg_comp]
      abel
    · rw [hd]
      simp only [changedComul, tensorDerivative_neg, LinearMap.comp_neg, LinearMap.neg_comp]
      abel
  · intro x y z hxy hyz
    obtain ⟨u, hu, hm, hd⟩ := (equivalent_iff x y).1 hxy
    obtain ⟨v, hv, hm', hd'⟩ := (equivalent_iff y z).1 hyz
    apply (equivalent_iff x z).2
    refine ⟨u + v, ⟨by simp [hu.1, hv.1], by rw [comp_add, hu.2, hv.2, add_zero]⟩, ?_, ?_⟩
    · rw [hm', hm]
      simp only [changedMul, tensorDerivative_add, LinearMap.comp_add, LinearMap.add_comp]
      abel
    · rw [hd', hd]
      simp only [changedComul, tensorDerivative_add, LinearMap.comp_add, LinearMap.add_comp]
      abel

end Changes

section Linearization

variable {B : Type*} [Ring B] [Bialgebra k B]

local notation "V" => Extended k B
local notation "E" => carrierCoordinates k B
local notation "S" => scalarCoordinates k
local notation "m" => mulTensor k B
local notation "d" => comul k B
local notation "e" => unit k B
local notation "c" => counit k B
local notation "ι" => (LinearMap.id : B →ₗ[k] B)
local notation "I" => (LinearMap.id : V →ₗ[D k] V)
local notation "α" => LinearEquiv.toLinearMap (TensorProduct.assoc k B B B)
local notation "αD" => LinearEquiv.toLinearMap (TensorProduct.assoc (D k) V V V)

private theorem left_unit_coefficient (f : B ⊗[k] B →ₗ[k] B) :
    f.comp (TensorProduct.map e ι) = 0 ↔ ∀ b : B, f (1 ⊗ₜ[k] b) = 0 := by
  constructor
  · intro h b
    simpa using LinearMap.congr_fun h ((1 : k) ⊗ₜ[k] b)
  · intro h
    apply TensorProduct.ext'
    intro a b
    simp only [comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', LinearMap.map_smul,
      h, smul_zero, zero_apply]

private theorem right_unit_coefficient (f : B ⊗[k] B →ₗ[k] B) :
    f.comp (TensorProduct.map ι e) = 0 ↔ ∀ b : B, f (b ⊗ₜ[k] 1) = 0 := by
  constructor
  · intro h b
    simpa using LinearMap.congr_fun h (b ⊗ₜ[k] (1 : k))
  · intro h
    apply TensorProduct.ext'
    intro b a
    simp only [comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, Algebra.linearMap_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, LinearMap.map_smul,
      h, smul_zero, zero_apply]

private theorem assoc_coefficient (f : B ⊗[k] B →ₗ[k] B) :
    (m).comp (TensorProduct.map f ι) + f.comp (TensorProduct.map m ι) =
      (m).comp ((TensorProduct.map ι f).comp α) +
        f.comp ((TensorProduct.map ι m).comp α) ↔
    ∀ a b z : B, a * f (b ⊗ₜ[k] z) - f ((a * b) ⊗ₜ[k] z) +
      f (a ⊗ₜ[k] (b * z)) - f (a ⊗ₜ[k] b) * z = 0 := by
  constructor
  · intro h a b z
    have h' := LinearMap.congr_fun h ((a ⊗ₜ[k] b) ⊗ₜ[k] z)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, mulTensor_tmul, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul] at h'
    rw [← sub_eq_zero] at h'
    convert congrArg Neg.neg h' using 1 <;> abel
  · intro h
    apply TensorProduct.ext_threefold
    intro a b z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, mulTensor_tmul, LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul]
    apply sub_eq_zero.mp
    convert congrArg Neg.neg (h a b z) using 1 <;> abel

private theorem equiv_comp_eq_zero {R X Y Z : Type*} [CommSemiring R]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    [AddCommMonoid Z] [Module R Z] (h : Y ≃ₗ[R] Z) (p : X →ₗ[R] Y) :
    h.toLinearMap.comp p = 0 ↔ p = 0 := by
  constructor
  · intro eq
    ext x
    apply h.injective
    simpa using LinearMap.congr_fun eq x
  · rintro rfl
    exact comp_zero _

private theorem linearize_laws (f : B ⊗[k] B →ₗ[k] B) (g : B →ₗ[k] B ⊗[k] B) :
    Laws (deformedMul f) (deformedComul g) (fixedUnit k B) (fixedCounit k B) ↔
      Linearized f g := by
  let M := deformedMul f
  let G := deformedComul g
  let U := fixedUnit k B
  let C := fixedCounit k B
  have hbase := original_laws (k := k) (B := B)
  have hleft : M.comp (TensorProduct.map U I) = (TensorProduct.lid (D k) V).toLinearMap ↔
      ∀ b : B, f (1 ⊗ₜ[k] b) = 0 := by
    simp only [M, U, deformedMul, fixedUnit, ← transport_jet_id E, map_jet,
      transported_lid (B := B), transport_comp, jet_comp, TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, zero_add, comp_zero, transport_jet_eq, hbase.unit_left,
      true_and, left_unit_coefficient]
  have hright : M.comp (TensorProduct.map I U) = (TensorProduct.rid (D k) V).toLinearMap ↔
      ∀ b : B, f (b ⊗ₜ[k] 1) = 0 := by
    simp only [M, U, deformedMul, fixedUnit, ← transport_jet_id E, map_jet,
      transported_rid (B := B), transport_comp, jet_comp, TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, zero_add, comp_zero, transport_jet_eq, hbase.unit_right,
      true_and, right_unit_coefficient]
  have hassoc :
      M.comp (TensorProduct.map M I) = M.comp ((TensorProduct.map I M).comp αD) ↔
        ∀ a b z : B, a * f (b ⊗ₜ[k] z) - f ((a * b) ⊗ₜ[k] z) +
          f (a ⊗ₜ[k] (b * z)) - f (a ⊗ₜ[k] b) * z = 0 := by
    simp only [M, deformedMul, ← transport_jet_id E, map_jet, transported_assoc (B := B),
      transport_comp, jet_comp, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
      zero_add, add_zero, comp_zero, transport_jet_eq, hbase.assoc, true_and, assoc_coefficient]
  have hcleft : (TensorProduct.lid (D k) V).toLinearMap.comp
      ((TensorProduct.map C I).comp G) = I ↔ (TensorProduct.map c ι).comp g = 0 := by
    simp only [C, G, fixedCounit, deformedComul, ← transport_jet_id E, map_jet,
      transported_lid (B := B), transport_comp, jet_comp, TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, zero_comp, add_zero, transport_jet_eq,
      hbase.counit_left, true_and, equiv_comp_eq_zero]
  have hcright : (TensorProduct.rid (D k) V).toLinearMap.comp
      ((TensorProduct.map I C).comp G) = I ↔ (TensorProduct.map ι c).comp g = 0 := by
    simp only [C, G, fixedCounit, deformedComul, ← transport_jet_id E, map_jet,
      transported_rid (B := B), transport_comp, jet_comp, TensorProduct.map_zero_left,
      TensorProduct.map_zero_right, zero_comp, add_zero, transport_jet_eq,
      hbase.counit_right, true_and, equiv_comp_eq_zero]
  have hcoassoc :
      (αD).comp ((TensorProduct.map G I).comp G) = (TensorProduct.map I G).comp G ↔
        (α).comp ((TensorProduct.map d ι).comp g + (TensorProduct.map g ι).comp d) -
          (TensorProduct.map ι d).comp g - (TensorProduct.map ι g).comp d = 0 := by
    simp only [G, deformedComul, ← transport_jet_id E, map_jet, transported_assoc (B := B),
      transport_comp, jet_comp, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
      zero_add, add_zero, zero_comp, transport_jet_eq, hbase.coassoc, true_and]
    constructor
    · intro h
      ext x
      have hx := LinearMap.congr_fun h x
      simp only [LinearMap.sub_apply, LinearMap.zero_apply, LinearMap.add_apply] at hx ⊢
      rw [hx]
      abel
    · intro h
      ext x
      have hx := LinearMap.congr_fun h x
      simp only [LinearMap.sub_apply, LinearMap.zero_apply, LinearMap.add_apply] at hx ⊢
      exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans hx)
  have hcunit : C.comp U = (LinearMap.id : D k →ₗ[D k] D k) := by
    simp only [C, U, fixedCounit, fixedUnit, ← transport_jet_id S, transport_comp, jet_comp,
      zero_comp, comp_zero, add_zero, hbase.counit_unit]
  have hcmul : C.comp M = (TensorProduct.lid (D k) (D k)).toLinearMap.comp
      (TensorProduct.map C C) ↔ (c).comp f = 0 := by
    simp only [C, M, fixedCounit, deformedMul, transported_scalar_lid (k := k), map_jet,
      transport_comp, jet_comp, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
      add_zero, comp_zero, zero_comp, transport_jet_eq, hbase.counit_mul, true_and]
  have hgunit : G.comp U = (TensorProduct.map U U).comp
      (TensorProduct.lid (D k) (D k)).symm.toLinearMap ↔ g 1 = 0 := by
    simp only [G, U, deformedComul, fixedUnit, transported_scalar_lid_symm (k := k), map_jet,
      transport_comp, jet_comp, TensorProduct.map_zero_left, TensorProduct.map_zero_right,
      zero_add, add_zero, comp_zero, zero_comp, transport_jet_eq, hbase.comul_unit, true_and,
      comp_unit_zero]
  have hcompat : G.comp M = (TensorProduct.map M M).comp
      ((middleFlip (D k) V).comp (TensorProduct.map G G)) ↔
      (d).comp f + g.comp m =
        (TensorProduct.map f m + TensorProduct.map m f).comp
          ((middleFlip k B).comp (TensorProduct.map d d)) +
        (TensorProduct.map m m).comp ((middleFlip k B).comp
          (TensorProduct.map g d + TensorProduct.map d g)) := by
    simp only [G, M, deformedComul, deformedMul, transported_middleFlip (B := B), map_jet,
      transport_comp, jet_comp, zero_comp, zero_add, transport_jet_eq, hbase.compatibility,
      true_and, add_comm]
  constructor
  · intro h
    exact ⟨hleft.mp h.unit_left, hright.mp h.unit_right, hcmul.mp h.counit_mul,
      hgunit.mp h.comul_unit, hcleft.mp h.counit_left, hcright.mp h.counit_right,
      hassoc.mp h.assoc, hcoassoc.mp h.coassoc, hcompat.mp h.compatibility⟩
  · intro h
    exact ⟨hleft.mpr h.left_unit, hright.mpr h.right_unit, hassoc.mpr h.assoc,
      hcleft.mpr h.left_counit, hcright.mpr h.right_counit, hcoassoc.mpr h.coassoc,
      hcunit, hcmul.mpr h.counit_mul, hgunit.mpr h.comul_unit, hcompat.mpr h.compatibility⟩

/-- The normalized first-order equations are equivalent to the bialgebra laws
for the two operations on the scalar extension with fixed unit and counit. -/
theorem laws_iff : Expected.laws_iff := by
  intro k B _ _ _ _ f g
  exact linearize_laws f g

end Linearization

end

end LieNotes.BialgebraDeformation
