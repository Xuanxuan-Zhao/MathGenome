import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.IrreducibleRealForms
import MathGenome.Internal.AlgebraCore.P103.Ch08.FrobeniusSchurIndicator
import MathGenome.Internal.AlgebraCore.P103.Ch08.UnitarityPairing
import MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
import Mathlib.Tactic.Module

noncomputable section
universe u v
namespace P103.Ch08.IrreducibleRealForms
open RealFormSpecs FrobeniusSchurSpecs

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

theorem selfDual_real_character : selfDualRealCharacterType.{u,v} := by
  intro G _ _ V _ _ _ ρ hρ g
  obtain ⟨e⟩ := hρ
  have he := congrFun (Representation.char_iso e) g
  change CharacterSpecs.characterValue ρ g = CharacterSpecs.characterValue ρ.dual g at he
  rw [show CharacterSpecs.characterValue ρ.dual g =
      CharacterSpecs.characterValue ρ g⁻¹ from Representation.char_dual ρ g,
    character_inverse_conjugate] at he
  exact he.symm


namespace Hermitian

variable (h : PositiveHermitianForm V)

/-- The algebraic Hermitian duality, with the source's first-variable convention. -/
def dualMap : V →ₗ⋆[ℂ] Module.Dual ℂ V where
  toFun y :=
    { toFun := fun x => h.toFun x y
      map_add' := fun x z => h.add_left x z y
      map_smul' := fun c x => h.smul_left c x y }
  map_add' x y := by ext z; exact h.add_right z x y
  map_smul' c x := by ext z; exact h.smul_right c z x

@[simp] lemma dualMap_apply (y x : V) : dualMap h y x = h.toFun x y := rfl

lemma dualMap_injective : Function.Injective (dualMap h) := by
  apply (dualMap h).ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  change dualMap h x = 0 at hx
  by_contra hn
  have hp := h.positive x hn
  have hz := congrArg (fun f : Module.Dual ℂ V => (f x).re) hx
  change (h.toFun x x).re = 0 at hz
  linarith

/-- Coordinate conjugation is used only to prove that Hermitian duality is onto. -/
def coordinateConjugation [FiniteDimensional ℂ V] : V ≃ₗ⋆[ℂ] V :=
  ((Module.finBasis ℂ V).equivFun.trans (starLinearEquiv ℂ)).trans
    (Module.finBasis ℂ V).equivFun.symm

def dualEquiv [FiniteDimensional ℂ V] : V ≃ₗ⋆[ℂ] Module.Dual ℂ V := by
  let K := coordinateConjugation (V := V)
  let f : V →ₗ[ℂ] Module.Dual ℂ V := (dualMap h).comp K.toLinearMap
  have hi : Function.Injective f := (dualMap_injective h).comp K.injective
  have hs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℂ) (V := V)).symm).mp hi
  exact LinearEquiv.ofBijective (dualMap h) ⟨dualMap_injective h,
    fun y => by obtain ⟨x, hx⟩ := hs y; exact ⟨K x, hx⟩⟩

@[simp] lemma dualEquiv_apply [FiniteDimensional ℂ V] (y x : V) :
    dualEquiv h y x = h.toFun x y := rfl

lemma self_real (x : V) : h.toFun x x = ((h.toFun x x).re : ℂ) := by
  have hh := h.conj_symm x x
  exact (Complex.conj_eq_iff_re.mp hh).symm

end Hermitian


/-- Riesz duality applied to a complex bilinear form is conjugate-linear. -/
def bilinearConjugate [FiniteDimensional ℂ V] (h : PositiveHermitianForm V)
    (B : LinearMap.BilinForm ℂ V) : V →ₗ⋆[ℂ] V :=
  (Hermitian.dualEquiv h).symm.toLinearMap.comp B.flip

lemma bilinearConjugate_pairing [FiniteDimensional ℂ V] (h : PositiveHermitianForm V)
    (B : LinearMap.BilinForm ℂ V) (x y : V) :
    h.toFun x (bilinearConjugate h B y) = B x y := by
  exact congrArg (fun f : Module.Dual ℂ V => f x)
    ((Hermitian.dualEquiv h).apply_symm_apply (B.flip y))

lemma bilinearConjugate_injective [FiniteDimensional ℂ V] (h : PositiveHermitianForm V)
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) :
    Function.Injective (bilinearConjugate h B) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hB.2
  intro z
  have hh := congrArg (fun w => h.toFun z w) hxy
  rw [bilinearConjugate_pairing, bilinearConjugate_pairing] at hh
  simpa using sub_eq_zero.mpr hh

lemma bilinearConjugate_equivariant [FiniteDimensional ℂ V] (h : PositiveHermitianForm V)
    (ρ : Representation ℂ G V) (hh : ∀ g x y, h.toFun (ρ g x) (ρ g y) = h.toFun x y)
    (B : LinearMap.BilinForm ℂ V) (hB : Invariant ρ B) (g : G) (y : V) :
    bilinearConjugate h B (ρ g y) = ρ g (bilinearConjugate h B y) := by
  apply (Hermitian.dualMap_injective h)
  ext x
  change h.toFun x (bilinearConjugate h B (ρ g y)) =
    h.toFun x (ρ g (bilinearConjugate h B y))
  rw [bilinearConjugate_pairing]
  have h₁ := hB g (ρ g⁻¹ x) y
  have h₂ := hh g (ρ g⁻¹ x) (bilinearConjugate h B y)
  simp only [Representation.self_inv_apply, bilinearConjugate_pairing] at h₁ h₂
  exact h₁.trans h₂.symm

/-- The square of the conjugate-linear map is an ordinary intertwiner. -/
def conjugateSquare (ρ : Representation ℂ G V) (J : V →ₗ⋆[ℂ] V)
    (hJ : ∀ g x, J (ρ g x) = ρ g (J x)) : ρ.IntertwiningMap ρ where
  toLinearMap := J.comp J
  isIntertwining' g := by
    ext x
    change J (J (ρ g x)) = ρ g (J (J x))
    rw [hJ, hJ]

/-- Positivity determines the sign of the Schur scalar, and a positive real
rescaling normalizes the square. -/
lemma normalized_of_form [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Irreducible ℂ G V ρ)
    (B : LinearMap.BilinForm ℂ V) (hB : Invariant ρ B) (hne : B ≠ 0)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hsign : ∀ x y, B y x = (ε : ℂ) * B x y) :
    HasConjugateStructure ρ (ε : ℂ) := by
  obtain ⟨h, hh⟩ := existsInvariantHermitian ρ
  let J := bilinearConjugate h B
  have hJ : ∀ g x, J (ρ g x) = ρ g (J x) := bilinearConjugate_equivariant h ρ hh B hB
  have hi : Function.Injective J := bilinearConjugate_injective h B
    (FrobeniusSchurIndicator.invariant_nondegenerate ρ hρ B hB hne)
  obtain ⟨c, hc, _⟩ := Schur.uniqueScalar ρ hρ (conjugateSquare ρ J hJ)
  have hsq (x : V) : J (J x) = c • x :=
    congrArg (fun f : ρ.IntertwiningMap ρ => f x) hc
  have : Nontrivial V := hρ.1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hJx : J x ≠ 0 := fun hz => hx (hi (by simpa using hz))
  have hcstar : star c = c := by
    apply smul_left_injective (R := ℂ) hJx
    calc
      star c • J x = J (c • x) := (J.map_smulₛₗ c x).symm
      _ = J (J (J x)) := congrArg J (hsq x).symm
      _ = c • J x := hsq (J x)
  have hcr : (c.re : ℂ) = c := Complex.conj_eq_iff_re.mp hcstar
  have hp : 0 < (h.toFun x x).re := h.positive x hx
  have hq : 0 < (h.toFun (J x) (J x)).re := h.positive (J x) hJx
  have hpq : h.toFun (J x) (J x) = (ε : ℂ) * star c * h.toFun x x := by
    calc
      h.toFun (J x) (J x) = B (J x) x := bilinearConjugate_pairing h B _ _
      _ = (ε : ℂ) * B x (J x) := hsign x (J x)
      _ = (ε : ℂ) * h.toFun x (J (J x)) := by rw [bilinearConjugate_pairing]
      _ = (ε : ℂ) * star c * h.toFun x x := by rw [hsq, h.smul_right]; ring
  have hec : 0 < ε * c.re := by
    have hre := congrArg Complex.re hpq
    rw [← hcr] at hre
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, zero_mul, mul_zero, add_zero, sub_zero] at hre
    exact (mul_pos_iff_of_pos_right hp).mp (hre ▸ hq)
  let r : ℝ := Real.sqrt (ε * c.re)
  have hr : 0 < r := Real.sqrt_pos.mpr hec
  have hr2 : r * r = ε * c.re := by simpa [r, pow_two] using Real.sq_sqrt hec.le
  have hscale : ((r⁻¹ : ℝ) : ℂ) * star ((r⁻¹ : ℝ) : ℂ) * c = (ε : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← hcr, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have he2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have hrc : r * r * ε = c.re := by
      calc
        r * r * ε = ε * c.re * ε := by rw [hr2]
        _ = (ε * ε) * c.re := by ring
        _ = c.re := by rw [he2, one_mul]
    rw [← hrc]
    field_simp
  refine ⟨(r⁻¹ : ℂ) • J, ?_, ?_⟩
  · intro g y
    change (r⁻¹ : ℂ) • J (ρ g y) = ρ g ((r⁻¹ : ℂ) • J y)
    rw [hJ, map_smul]
  · intro y
    change (r⁻¹ : ℂ) • J ((r⁻¹ : ℂ) • J y) = (ε : ℂ) • y
    rw [J.map_smulₛₗ, hsq, smul_smul, smul_smul]
    simpa only [Complex.ofReal_inv, starRingEnd_apply] using congrArg (fun a : ℂ => a • y) hscale

/-- Both signs are normalized on the original representation space. -/
theorem normalized_structures : normalizedStructuresType.{u,v} := by
  intro G _ _ V _ _ _ ρ hρ
  have hc := FrobeniusSchurIndicator.classification ρ hρ
  constructor
  · intro hν
    obtain ⟨B, hne, hB, hs⟩ := hc.2.2.1.mp hν
    simpa using normalized_of_form ρ hρ B hB hne 1 (Or.inl rfl)
      (fun x y => by simpa using hs.eq y x)
  · intro hν
    obtain ⟨B, hne, hB, ha⟩ := hc.2.2.2.mp hν
    simpa using normalized_of_form ρ hρ B hB hne (-1) (Or.inr rfl)
      (fun x y => by simpa using (ha.neg_eq x y).symm)

section Descent

local instance : Module ℝ V := Module.compHom V (algebraMap ℝ ℂ)
local instance : IsScalarTower ℝ ℂ V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The fixed vectors form a genuine real vector subspace. -/
def fixedSpace (J : V →ₗ⋆[ℂ] V) : Submodule ℝ V where
  carrier := {x | J x = x}
  zero_mem' := J.map_zero
  add_mem' hx hy := by
    change J _ = _ at hx hy ⊢
    rw [map_add, hx, hy]
  smul_mem' r x hx := by
    change J x = x at hx
    change J ((r : ℂ) • x) = (r : ℂ) • x
    rw [J.map_smulₛₗ, hx]
    simp

/-- The original group action restricted to the fixed real subspace. -/
def fixedRepresentation (ρ : Representation ℂ G V) (J : V →ₗ⋆[ℂ] V)
    (hJ : ∀ g x, J (ρ g x) = ρ g (J x)) : Representation ℝ G (fixedSpace J) where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, by change J (ρ g x) = ρ g x; rw [hJ, x.property]⟩
      map_add' := fun x y => Subtype.ext ((ρ g).map_add x y)
      map_smul' := fun r x => Subtype.ext ((ρ g).map_smul_of_tower r x) }
  map_one' := by ext x; exact congrArg (fun f : Module.End ℂ V => f x) ρ.map_one
  map_mul' g k := by ext x; exact congrArg (fun f : Module.End ℂ V => f x) (ρ.map_mul g k)

/-- Complex-linear extension of the inclusion of fixed vectors. -/
def fixedEvaluation (J : V →ₗ⋆[ℂ] V) : TensorProduct ℝ ℂ (fixedSpace J) →ₗ[ℂ] V :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (fixedSpace J).subtype)

@[simp] lemma fixedEvaluation_tmul (J : V →ₗ⋆[ℂ] V) (c : ℂ) (x : fixedSpace J) :
    fixedEvaluation J (TensorProduct.tmul ℝ c x) = c • (x : V) := rfl

/-- Every tensor has two real coordinates, with respect to 1 and i. -/
lemma tensor_decomposition {U : Type v} [AddCommGroup U] [Module ℝ U]
    (z : TensorProduct ℝ ℂ U) : ∃ a b : U,
    z = TensorProduct.tmul ℝ 1 a + TensorProduct.tmul ℝ Complex.I b := by
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    refine ⟨c.re • x, c.im • x, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    simp [Complex.real_smul]
  | add z t hz ht =>
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨c, d, rfl⟩ := ht
    refine ⟨a + c, b + d, ?_⟩
    simp only [TensorProduct.tmul_add]
    abel

lemma fixedEvaluation_bijective (J : V →ₗ⋆[ℂ] V) (hJJ : ∀ x, J (J x) = x) :
    Function.Bijective (fixedEvaluation J) := by
  constructor
  · apply (fixedEvaluation J).ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨a, b, rfl⟩ := tensor_decomposition z
    have he : (a : V) + Complex.I • (b : V) = 0 := by
      simpa only [LinearMap.mem_ker, map_add, fixedEvaluation_tmul, one_smul] using hz
    have hj := congrArg J he
    have hJa : J (a : V) = (a : V) := a.property
    have hJb : J (b : V) = (b : V) := b.property
    rw [J.map_add, J.map_smulₛₗ, hJa, hJb, J.map_zero] at hj
    simp only [Complex.conj_I] at hj
    have ha : (a : V) = 0 := by
      have hd : (2 : ℂ) • (a : V) = 0 := calc
        (2 : ℂ) • (a : V) = ((a : V) + Complex.I • (b : V)) +
            ((a : V) + (-Complex.I) • (b : V)) := by module
        _ = 0 := by rw [he, hj, add_zero]
      exact (smul_eq_zero.mp hd).resolve_left (by norm_num)
    have hb : (b : V) = 0 := by
      rw [ha, zero_add] at he
      exact (smul_eq_zero.mp he).resolve_left Complex.I_ne_zero
    have ha' : a = 0 := Subtype.ext ha
    have hb' : b = 0 := Subtype.ext hb
    simp [ha', hb']
  · intro x
    let a : fixedSpace J := ⟨(1 / 2 : ℂ) • (x + J x), by
      change J ((1 / 2 : ℂ) • (x + J x)) = (1 / 2 : ℂ) • (x + J x)
      simp only [map_smulₛₗ, starRingEnd_apply, map_add, hJJ]
      norm_num
      module⟩
    let b : fixedSpace J := ⟨(-Complex.I / 2 : ℂ) • (x - J x), by
      change J ((-Complex.I / 2 : ℂ) • (x - J x)) = (-Complex.I / 2 : ℂ) • (x - J x)
      simp only [map_smulₛₗ, starRingEnd_apply, map_sub, hJJ]
      simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
      module⟩
    refine ⟨TensorProduct.tmul ℝ 1 a + TensorProduct.tmul ℝ Complex.I b, ?_⟩
    simp only [map_add, fixedEvaluation_tmul, one_smul]
    change (1 / 2 : ℂ) • (x + J x) + Complex.I • ((-Complex.I / 2 : ℂ) • (x - J x)) = x
    rw [smul_smul]
    have hs : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]; ring
    rw [hs]
    module

/-- Fixed-space descent supplies both the representation and the tensor equivalence. -/
theorem realForm_of_conjugateStructure (ρ : Representation ℂ G V)
    (h : HasConjugateStructure ρ 1) : HasRealForm ρ := by
  obtain ⟨J, hJ, hJJ⟩ := h
  have hJJ' : ∀ x, J (J x) = x := by simpa using hJJ
  let e := LinearEquiv.ofBijective (fixedEvaluation J) (fixedEvaluation_bijective J hJJ')
  refine ⟨fixedSpace J, inferInstance, inferInstance, fixedRepresentation ρ J hJ, e, ?_⟩
  intro g z
  induction z using TensorProduct.inductionOn with
  | tmul c x => exact (ρ g).map_smul c x |>.symm
  | add z t hz ht => simp only [map_add, hz, ht]

end Descent

/-- Canonical conjugation of a scalar extension, acting only on its ℂ factor. -/
def tensorConjugation {U : Type v} [AddCommGroup U] [Module ℝ U] :
    TensorProduct ℝ ℂ U →ₗ⋆[ℂ] TensorProduct ℝ ℂ U where
  toFun := TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id
  map_add' := (TensorProduct.map Complex.conjAe.toLinearMap (LinearMap.id : U →ₗ[ℝ] U)).map_add
  map_smul' c z := by
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      change TensorProduct.tmul ℝ (star (c * a)) x =
        TensorProduct.tmul ℝ (star c * star a) x
      rw [star_mul, mul_comm]
    | add z t hz ht => simp only [smul_add, map_add, hz, ht]

@[simp] lemma tensorConjugation_tmul {U : Type v} [AddCommGroup U] [Module ℝ U]
    (c : ℂ) (x : U) : tensorConjugation (TensorProduct.tmul ℝ c x) =
    TensorProduct.tmul ℝ (star c) x := rfl

lemma tensorConjugation_square {U : Type v} [AddCommGroup U] [Module ℝ U]
    (z : TensorProduct ℝ ℂ U) : tensorConjugation (tensorConjugation z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => simp
  | add z t hz ht => simp only [map_add, hz, ht]

lemma tensorConjugation_equivariant {U : Type v} [AddCommGroup U] [Module ℝ U]
    (σ : Representation ℝ G U) (g : G) (z : TensorProduct ℝ ℂ U) :
    tensorConjugation (complexification σ g z) =
      complexification σ g (tensorConjugation z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add z t hz ht => simp only [map_add, hz, ht]

/-- Transport the usual conjugation along the given complexification isomorphism. -/
theorem conjugateStructure_of_realForm (ρ : Representation ℂ G V)
    (h : HasRealForm ρ) : HasConjugateStructure ρ 1 := by
  obtain ⟨U, _, _, σ, e, he⟩ := h
  let J : V →ₗ⋆[ℂ] V := e.toLinearMap.comp (tensorConjugation.comp e.symm.toLinearMap)
  have hinv (g : G) (x : V) : e.symm (ρ g x) = complexification σ g (e.symm x) := by
    apply e.injective
    simpa only [e.apply_symm_apply] using (he g (e.symm x)).symm
  refine ⟨J, ?_, ?_⟩
  · intro g x
    change e (tensorConjugation (e.symm (ρ g x))) = ρ g (e (tensorConjugation (e.symm x)))
    rw [hinv, tensorConjugation_equivariant, he]
  · intro x
    change e (tensorConjugation (e.symm (e (tensorConjugation (e.symm x))))) = (1 : ℂ) • x
    rw [e.symm_apply_apply, tensorConjugation_square, e.apply_symm_apply, one_smul]

/-- The Hermitian pairing becomes complex bilinear after applying an antilinear
map in its second variable. -/
def conjugateForm (h : PositiveHermitianForm V) (J : V →ₗ⋆[ℂ] V) :
    LinearMap.BilinForm ℂ V := ((Hermitian.dualMap h).comp J).flip

@[simp] lemma conjugateForm_apply (h : PositiveHermitianForm V) (J : V →ₗ⋆[ℂ] V)
    (x y : V) : conjugateForm h J x y = h.toFun x (J y) := rfl

lemma conjugateForm_invariant (ρ : Representation ℂ G V)
    (h : PositiveHermitianForm V) (hh : ∀ g x y, h.toFun (ρ g x) (ρ g y) = h.toFun x y)
    (J : V →ₗ⋆[ℂ] V) (hJ : ∀ g x, J (ρ g x) = ρ g (J x)) :
    Invariant ρ (conjugateForm h J) := by
  intro g x y
  change h.toFun (ρ g x) (J (ρ g y)) = h.toFun x (J y)
  rw [hJ, hh]

/-- Symmetrization is nonzero: on (Jx,x) its real part is the sum of two
nonnegative diagonal Hermitian values, one strictly positive. -/
lemma symmetricForm_of_conjugateStructure [Fintype G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hne : Nontrivial V)
    (h : HasConjugateStructure ρ 1) : HasSymmetricForm ρ := by
  obtain ⟨J, hJ, hJJ⟩ := h
  have hJJ' : ∀ x, J (J x) = x := by simpa using hJJ
  obtain ⟨h, hh⟩ := existsInvariantHermitian ρ
  let B := conjugateForm h J
  have hB : Invariant ρ B := conjugateForm_invariant ρ h hh J hJ
  refine ⟨B + B.flip, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_ne (0 : V)
    intro hz
    have hval := congrArg (fun C : LinearMap.BilinForm ℂ V => (C (J x) x).re) hz
    change (h.toFun (J x) (J x) + h.toFun x (J (J x))).re = 0 at hval
    rw [hJJ', Complex.add_re] at hval
    have hp := h.positive x hx
    have hq := h.nonneg (J x)
    linarith
  · exact (invariantForms ρ).add_mem hB (FrobeniusSchurIndicator.invariant_flip hB)
  · exact ⟨fun x y => add_comm _ _⟩

/-- The +1 indicator characterizes actual realization over ℝ. -/
theorem realization : realizationType.{u,v} := by
  intro G _ _ V _ _ _ ρ hρ
  constructor
  · intro hν
    exact realForm_of_conjugateStructure ρ ((normalized_structures ρ hρ).1 hν)
  · intro hreal
    exact (FrobeniusSchurIndicator.classification ρ hρ).2.2.1.mpr
      (symmetricForm_of_conjugateStructure ρ hρ.1 (conjugateStructure_of_realForm ρ hreal))

/-- The quaternionic case has real character and cannot have a real form. -/
theorem negative : negativeType.{u,v} := by
  intro G _ _ V _ _ _ ρ hρ hν
  have hc := FrobeniusSchurIndicator.classification ρ hρ
  constructor
  · apply selfDual_real_character ρ
    apply (FrobeniusSchurIndicator.selfDual_iff_form_types hρ).mpr
    exact Or.inr (hc.2.2.2.mp hν)
  · intro hreal
    have hpos := (realization ρ hρ).mpr hreal
    rw [hν] at hpos
    norm_num at hpos

end P103.Ch08.IrreducibleRealForms
