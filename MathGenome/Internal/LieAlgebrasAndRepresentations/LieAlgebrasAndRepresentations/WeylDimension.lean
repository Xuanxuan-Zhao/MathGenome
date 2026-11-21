import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylDimension
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylCharacter
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDenominator
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Batteries.Tactic.OpenPrivate

/-! LA-H04, by specializing the Weyl alternants and taking a limit at zero. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.WeylDimension

open _root_.Specs.LieAlgebrasAndRepresentations
open WeylDenominatorSpecs
open VermaModules (Direction Regular U borel_value IsWeightCharacter)
open SerreRelations (positive)
open VermaWeightsUniversal (inducedLieRingModule inducedLieModule)
open SimpleHighestWeightQuotient (simpleQuotient_value)
open SolvableRadical (IsSemisimple_value)
open FiniteModuleWeights (weightWeylGroup)
open _root_.Specs.LieAlgebrasAndRepresentations.FormalCharacters (character integralWeights)
open _root_.Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
  (weightForm_value weightRepresentative_value)
open _root_.Specs.LieAlgebrasAndRepresentations.WeylDimension (CorootCompatible DimensionFormula)
open RootForm (rootForm_value coroot_value)
open Filter
open scoped BigOperators Topology

universe u v

section Evaluation

variable {P : Type u} [AddCommGroup P]

/-- Evaluate a formal exponential using an additive functional. -/
private def expMonoidHom (f : P →+ ℂ) (t : ℂ) : Multiplicative P →* ℂ where
  toFun x := Complex.exp (t * f x.toAdd)
  map_one' := by simp
  map_mul' x y := by
    change Complex.exp (t * f (x.toAdd + y.toAdd)) = _
    rw [map_add, mul_add, Complex.exp_add]

private def evaluate (f : P →+ ℂ) (t : ℂ) : AddMonoidAlgebra ℤ P →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ P (expMonoidHom f t)

@[simp] private theorem evaluate_single (f : P →+ ℂ) (t : ℂ) (a : P) (n : ℤ) :
    evaluate f t (AddMonoidAlgebra.single a n) = (n : ℂ) * Complex.exp (t * f a) := by
  rw [evaluate, AddMonoidAlgebra.lift_single, zsmul_eq_mul]
  rfl

private theorem continuous_evaluate (f : P →+ ℂ) (F : AddMonoidAlgebra ℤ P) :
    Continuous fun t => evaluate f t F := by
  simp only [evaluate, AddMonoidAlgebra.lift_apply', Finsupp.sum, expMonoidHom]
  apply continuous_finsetSum
  intro a _
  change Continuous (fun t : ℂ => algebraMap ℤ ℂ (F.coeff a) * Complex.exp (t * f a))
  fun_prop

private theorem evaluate_at_zero (f : P →+ ℂ) (F : AddMonoidAlgebra ℤ P) :
    evaluate f 0 F = evaluate 0 0 F := by
  simp [evaluate, AddMonoidAlgebra.lift_apply', Finsupp.sum, expMonoidHom]

private theorem map_evaluate_zero {Q : Type v} [AddCommGroup Q] (g : P →+ Q)
    (F : AddMonoidAlgebra ℤ P) :
    evaluate 0 0 (AddMonoidAlgebra.mapDomainRingHom ℤ g F) = evaluate 0 0 F := by
  let A : AddMonoidAlgebra ℤ P →+* ℂ :=
    (evaluate 0 0).toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom ℤ g)
  have he : A = (evaluate 0 0).toRingHom := by
    apply RingHom.toAddMonoidHom_injective
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a n
    change evaluate 0 0 (AddMonoidAlgebra.mapDomainRingHom ℤ g
      (AddMonoidAlgebra.single a n)) = evaluate 0 0 (AddMonoidAlgebra.single a n)
    simp
  exact DFunLike.congr_fun he F

private theorem tendsto_exp_difference (b : ℂ) :
    Tendsto (fun t : ℂ => (1 - Complex.exp (-(t * b))) / t) (𝓝[≠] 0) (𝓝 b) := by
  have hlin : HasDerivAt (fun t : ℂ => t * (-b)) (-b) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const (-b)
  have he := (Complex.hasDerivAt_exp ((0 : ℂ) * (-b))).comp 0 hlin
  have hd : HasDerivAt (fun t : ℂ => 1 - Complex.exp (t * (-b))) b 0 := by
    simpa [Function.comp_def] using he.const_sub 1
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero

private def normalizedProduct {I : Type v} (S : Finset I) (b : I → ℂ) (c t : ℂ) :=
  Complex.exp (t * c) * ∏ a ∈ S, ((1 - Complex.exp (-(t * b a))) / t)

private theorem tendsto_normalizedProduct {I : Type v} (S : Finset I) (b : I → ℂ) (c : ℂ) :
    Tendsto (normalizedProduct S b c) (𝓝[≠] 0) (𝓝 (∏ a ∈ S, b a)) := by
  have hc : ContinuousAt (fun t : ℂ => Complex.exp (t * c)) 0 := by fun_prop
  change Tendsto (fun t : ℂ => Complex.exp (t * c) *
    ∏ a ∈ S, ((1 - Complex.exp (-(t * b a))) / t)) (𝓝[≠] 0) (𝓝 (∏ a ∈ S, b a))
  simpa only [zero_mul, Complex.exp_zero, one_mul] using (hc.mono_left nhdsWithin_le_nhds).mul
    (tendsto_finsetProd S fun a _ => tendsto_exp_difference (b a))

private theorem evaluate_denominator {I : Type v} (S : Finset I) (r : P) (α : I → P)
    (f : P →+ ℂ) (t : ℂ) :
    evaluate f t (denominator r S α) =
      Complex.exp (t * f r) * ∏ a ∈ S, (1 - Complex.exp (-(t * f (α a)))) := by
  simp [denominator, map_prod, mul_neg]

private theorem denominator_limit {I : Type v} (S : Finset I) (r : P) (α : I → P)
    (f g : P →+ ℂ) (F : AddMonoidAlgebra ℤ P)
    (h : ∀ t, evaluate f t (denominator r S α) * evaluate f t F =
      evaluate g t (denominator r S α))
    (hn : ∀ a ∈ S, f (α a) ≠ 0) :
    evaluate 0 0 F = ∏ a ∈ S, g (α a) / f (α a) := by
  let N := normalizedProduct S (fun a => f (α a)) (f r)
  let M := normalizedProduct S (fun a => g (α a)) (g r)
  have hN := tendsto_normalizedProduct S (fun a => f (α a)) (f r)
  have hM := tendsto_normalizedProduct S (fun a => g (α a)) (g r)
  have hF := (continuous_evaluate f F).continuousAt (x := 0)
  have he : (fun t => N t * evaluate f t F) =ᶠ[𝓝[≠] (0 : ℂ)] M := by
    refine Eventually.of_forall fun t => ?_
    have ht := h t
    rw [evaluate_denominator, evaluate_denominator] at ht
    simp only [N, M, normalizedProduct, Finset.prod_div_distrib]
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : ℂ => z * (∏ _a ∈ S, t)⁻¹) ht
  have hp := tendsto_nhds_unique_of_eventuallyEq
    (hN.mul (hF.mono_left nhdsWithin_le_nhds)) hM he
  dsimp only at hp
  rw [evaluate_at_zero] at hp
  rw [Finset.prod_div_distrib, eq_div_iff (Finset.prod_ne_zero_iff.mpr hn)]
  rwa [mul_comm]

end Evaluation

section Cartan

open FiniteModuleWeights (weightReflection)
open RootDecomposition (rootSet_value)
open _root_.LieAlgebrasAndRepresentations.FormalCharacters
  (integralInclusion integralInclusion_character)
open private finiteCharacter_eq_sum finite_weightSpaces_internal
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacters

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)

private theorem evaluate_character_at_zero (hss : IsSemisimple_value ℂ L)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] :
    evaluate 0 0 (character H φ V) = (Module.finrank ℂ V : ℂ) := by
  classical
  let b := (finite_weightSpaces_internal (V := V) H hss).collectedBasis
    (fun a => Module.finBasis ℂ (HighestWeightData.weightSpace_value V H a))
  letI := Module.Finite.finite_basis b
  letI := Fintype.ofFinite
    (Σ a : Module.Dual ℂ H, Fin (Module.finrank ℂ (HighestWeightData.weightSpace_value V H a)))
  have hb (i : _) : b i ∈ HighestWeightData.weightSpace_value V H i.1 :=
    DirectSum.IsInternal.collectedBasis_mem _ _ _
  calc
    _ = evaluate 0 0 (integralInclusion H φ (character H φ V)) :=
      (map_evaluate_zero (integralWeights H φ).subtype.toAddMonoidHom
        (character H φ V)).symm
    _ = (Module.finrank ℂ V : ℂ) := by
      rw [integralInclusion_character H φ V hss, finiteCharacter_eq_sum H b Sigma.fst hb,
        map_sum, Module.finrank_eq_card_basis b]
      simp

omit [H.IsCartanSubalgebra] in
private theorem rootForm_symm (x y : Module.Dual ℂ H) :
    rootForm_value H x y = rootForm_value H y x :=
  killingForm_symmetric ℂ L _ _

private theorem rootForm_weyl (hss : IsSemisimple_value ℂ L)
    (w : weightWeylGroup H) (x y : Module.Dual ℂ H) :
    rootForm_value H (w.val x) (w.val y) = rootForm_value H x y := by
  let B := rootForm_value H
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hgen (a : Module.Dual ℂ H) (ha : a ∈ rootSet_value H) :
      ∀ x y, B (weightReflection H a x) (weightReflection H a y) = B x y := by
    intro x y
    have hlen : B a a ≠ 0 := rootForm_self_ne_zero hss H hH a ha
    have hn : a (coroot_value H a) = 2 := by
      rw [killingCoroot_pairing hss H hH]
      exact mul_div_cancel_right₀ 2 hlen
    have hx : x (coroot_value H a) = 2 * B x a / B a a := killingCoroot_pairing hss H hH a x
    have hy : y (coroot_value H a) = 2 * B y a / B a a := killingCoroot_pairing hss H hH a y
    simp only [weightReflection, dite_eq_left hn]
    change B (x - x (coroot_value H a) • a) (y - y (coroot_value H a) • a) = B x y
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hx, hy]
    rw [show B a y = B y a from rootForm_symm H a y]
    field_simp
    ring
  let G : Subgroup (Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) := {
    carrier := {g | ∀ x y, B (g x) (g y) = B x y}
    one_mem' := fun _ _ => rfl
    mul_mem' := by
      intro a b ha hb x y
      change B (a (b x)) (a (b y)) = B x y
      rw [ha, hb]
    inv_mem' := by
      intro a ha x y
      have he := ha (a.symm x) (a.symm y)
      simpa using he.symm }
  have hle : weightWeylGroup H ≤ G := (Subgroup.closure_le G).mpr (by
    rintro _ ⟨a, ha, rfl⟩
    exact hgen a ha)
  exact hle w.property x y

omit [H.IsCartanSubalgebra] in
private theorem cartanSign_inv (w : weightWeylGroup H) :
    cartanSign H w⁻¹ = cartanSign H w := by
  have hdet : LinearMap.det w.val.toLinearMap * LinearMap.det w.val.symm.toLinearMap = 1 := by
    rw [← LinearMap.det_comp]
    simp
  have hiff : LinearMap.det w.val.symm.toLinearMap = 1 ↔
      LinearMap.det w.val.toLinearMap = 1 := by
    constructor <;> intro h <;> simpa [h] using hdet
  unfold cartanSign
  change (if LinearMap.det w.val.symm.toLinearMap = 1 then 1 else -1) = _
  simp only [hiff]

omit [H.IsCartanSubalgebra] in
private def pairWith (y : Module.Dual ℂ H) : integralWeights H φ →+ ℂ where
  toFun x := rootForm_value H x.val y
  map_zero' := by simp
  map_add' x z := by
    change rootForm_value H (x.val + z.val) y = _
    simp

private theorem evaluate_swap (hss : IsSemisimple_value ℂ L) [Fintype (weightWeylGroup H)]
    (hW : ∀ w : weightWeylGroup H, ∀ a ∈ integralWeights H φ,
      w.val a ∈ integralWeights H φ) (x y : integralWeights H φ) (t : ℂ) :
    evaluate (pairWith H φ y.val) t (cartanAlternant H φ hW x) =
      evaluate (pairWith H φ x.val) t (cartanAlternant H φ hW y) := by
  simp only [cartanAlternant, alternant, finsum_eq_sum_of_fintype, map_sum, evaluate_single]
  rw [← Equiv.sum_comp (Equiv.inv (weightWeylGroup H))]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Equiv.inv_apply, cartanSign_inv]
  congr 2
  apply congrArg (fun z : ℂ => t * z)
  change rootForm_value H (w.val.symm x.val) y.val =
    rootForm_value H (w.val y.val) x.val
  have he := rootForm_weyl H hss w (w.val.symm x.val) y.val
  rw [LinearEquiv.apply_symm_apply, rootForm_symm H x.val] at he
  exact he.symm

end Cartan

section Denominators

open _root_.Specs.LieAlgebrasAndRepresentations.RealRootSpace (E realRoots rootRestriction)
open private extension_injective from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteModuleWeights
open private finiteDimensional_of_rootSystem extension_image_positive
  extension_mem_positive rho_in_simpleChamber from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDenominator
open private invariant_assoc from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightCasimir

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)

private theorem rho_coroot_ne_zero (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (hS : (positive H φ).Finite) {α : Module.Dual ℂ H} (ha : α ∈ positive H φ) :
    cartanRho H φ hS (coroot_value H α) ≠ 0 := by
  classical
  let d := RealRootSpace.realization hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  let R := realRoots H
  have hR : IsRootSystem R := d.root_system
  letI := finiteDimensional_of_rootSystem hR
  let v := (InnerProductSpace.toDual ℝ (E H)).symm (φ.comp d.j).toContinuousLinearMap
  have hv (x : E H) : inner ℝ v x = φ (d.j x) := InnerProductSpace.toDual_symm_apply
  have hvR : RootRegular R v := by
    rintro x ⟨β, hβ, rfl⟩
    rw [hv, d.extension_root β hβ]
    exact hφ β hβ
  have hpos := extension_image_positive d φ v hv
  have hf := positiveRoots_finite hR.toRootAxioms v
  have hSF : hS.toFinset = hf.toFinset.image d.j := by
    ext β
    simp only [Set.Finite.mem_toFinset, Finset.mem_image]
    rw [← hpos]
    rfl
  have hρj : cartanRho H φ hS = d.j (rootRho R v) := by
    unfold cartanRho rootRho
    rw [hSF, Finset.sum_image (extension_injective d).injOn,
      finsum_mem_eq_finite_toFinset_sum _ hf, map_smul, map_sum]
    rw [← IsScalarTower.algebraMap_smul ℂ (1 / 2 : ℝ)]
    congr 1
    norm_num [Complex.coe_algebraMap]
  have hαreal : rootRestriction H α ∈ positiveRoots R v :=
    (extension_mem_positive d φ v hv _).mp (by
      rw [d.extension_root α ha.1]
      exact ha)
  have hρ := rho_in_simpleChamber hR hvR
  have hcone : ∀ z ∈ AddSubmonoid.closure (simpleRoots R v),
      z = 0 ∨ 0 < inner ℝ (rootRho R v) z := by
    intro z hz
    induction hz using AddSubmonoid.closure_induction with
    | mem z hz => exact Or.inr (hρ z hz)
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | hx
      · simpa using hy
      rcases hy with rfl | hy
      · simpa using (Or.inr hx : x = 0 ∨ 0 < inner ℝ (rootRho R v) x)
      exact Or.inr (by rw [inner_add_right]; exact add_pos hx hy)
  have hne := hR.nonzero _ hαreal.1
  have hstrict := (hcone _ (positive_mem_closure_simple hR.toRootAxioms v hαreal)).resolve_left hne
  rw [hρj, d.coroot_evaluation _ α ha.1]
  apply Complex.ofReal_ne_zero.mpr
  rw [coroot, real_inner_smul_right]
  exact (mul_pos (div_pos two_pos (real_inner_self_pos.mpr hne)) hstrict).ne'

private theorem killing_coroot_compatible (hss : IsSemisimple_value ℂ L) :
    CorootCompatible H φ (rootForm_value H) := by
  intro α ha
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  exact ⟨rootForm_self_ne_zero hss H hH α ha.1, killingCoroot_pairing hss H hH α⟩

/-- The dual form induced by an invariant form gives the normalized coroot pairings. -/
private theorem invariant_coroot_compatible (hss : IsSemisimple_value ℂ L)
    (B : LinearMap.BilinForm ℂ L) (hInv : B.lieInvariant L) (hB : B.Nondegenerate) :
    CorootCompatible H φ (weightForm_value H B) := by
  intro α ha
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  obtain ⟨e, f, _, hf, _, _, hef, _, _⟩ := exists_root_triple hss H hH α ha.1
  obtain ⟨_, pairing⟩ := HighestWeightCasimir.representative_pairing H hss B hInv hB
  have hSymm := HighestWeightCasimir.symmetry hss B hInv
  have bracket_pairing (h : H) : B (coroot_value H α : L) (h : L) = B e f * α h := by
    rw [← hef, invariant_assoc B hInv, ← lie_skew f (h : L),
      (mem_rootSpace H (-α) f).mp hf h]
    simp [mul_comm]
  let t := weightRepresentative_value H B
  have eval (μ : Module.Dual ℂ H) :
      μ (coroot_value H α) = B e f * weightForm_value H B μ α := by
    calc
      _ = B (t μ : L) (coroot_value H α : L) := (pairing μ _).symm
      _ = B (coroot_value H α : L) (t μ : L) := hSymm.eq _ _
      _ = B e f * α (t μ) := bracket_pairing _
      _ = _ := by
        change B e f * α (t μ) = B e f * B (t μ : L) (t α : L)
        rw [← pairing α (t μ), hSymm.eq (t α : L) (t μ : L)]
  have htwo : α (coroot_value H α) = 2 := by
    rw [killingCoroot_pairing hss H hH]
    exact mul_div_cancel_right₀ 2 (rootForm_self_ne_zero hss H hH α ha.1)
  have hnorm := (eval α).symm.trans htwo
  have hlength : weightForm_value H B α α ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hnorm
    norm_num at hnorm
  refine ⟨hlength, fun μ => (eq_div_iff hlength).2 ?_⟩
  rw [eval μ, mul_right_comm, hnorm]

omit [H.IsCartanSubalgebra] in
private theorem compare_coroot_ratios
    (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H))
    (hB : CorootCompatible H φ B)
    (x y : Module.Dual ℂ H) {α : Module.Dual ℂ H} (ha : α ∈ positive H φ)
    (hy : y (coroot_value H α) ≠ 0) :
    B y α ≠ 0 ∧ B x α / B y α = x (coroot_value H α) / y (coroot_value H α) := by
  obtain ⟨hα, hc⟩ := hB α ha
  have hn : B y α ≠ 0 := by
    intro hz
    apply hy
    rw [hc y, hz, mul_zero, zero_div]
  refine ⟨hn, ?_⟩
  rw [hc x, hc y]
  field_simp

end Denominators

open _root_.Specs.LieAlgebrasAndRepresentations.WeylCharacter (ClearedFormula)

private theorem dimension_of_character
    {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (hss : IsSemisimple_value ℂ L) (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]
    (φ : Direction H) (hφ : Regular H φ) (lam : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) (hc : ClearedFormula H φ lam χ) :
    DimensionFormula H φ lam χ := by
  classical
  obtain ⟨fd, hS, hρ, hP, hW, htop, _, hchar⟩ := hc
  obtain ⟨hS', hρ', hP', hW', hfin, _, hden⟩ := WeylDenominator.cartan_identity hss H φ hφ
  letI := hfin
  letI := Fintype.ofFinite (weightWeylGroup H)
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  letI := fd
  let V := simpleQuotient_value H φ χ
  let ρ := cartanRho H φ hS
  let r : integralWeights H φ := ⟨ρ, hρ⟩
  let x : integralWeights H φ := ⟨lam + ρ, htop⟩
  let α (a : Module.Dual ℂ H) : integralWeights H φ :=
    if ha : a ∈ positive H φ then ⟨a, hP a ha⟩ else 0
  let F := character H φ V
  let f := pairWith H φ ρ
  let g := pairWith H φ (lam + ρ)
  have hd : denominator r hS.toFinset α = cartanAlternant H φ hW r := hden
  change cartanAlternant H φ hW r * F = cartanAlternant H φ hW x at hchar
  have he (t : ℂ) :
      evaluate f t (denominator r hS.toFinset α) * evaluate f t F =
        evaluate g t (denominator r hS.toFinset α) := by
    rw [hd, ← map_mul, hchar]
    exact evaluate_swap H φ hss hW x r t
  have hρc (a : Module.Dual ℂ H) (ha : a ∈ positive H φ) :
      ρ (coroot_value H a) ≠ 0 := rho_coroot_ne_zero H φ hss hφ hS ha
  have hB := killing_coroot_compatible H φ hss
  have hr (a : Module.Dual ℂ H) (ha : a ∈ positive H φ) :=
    compare_coroot_ratios H φ (rootForm_value H) hB (lam + ρ) ρ ha (hρc a ha)
  have hα (a : Module.Dual ℂ H) (ha : a ∈ hS.toFinset) :
      (α a).val = a := by simp [α, hS.mem_toFinset.mp ha]
  have hn (a : Module.Dual ℂ H) (ha : a ∈ hS.toFinset) : f (α a) ≠ 0 := by
    change rootForm_value H (α a).val ρ ≠ 0
    rw [hα a ha, rootForm_symm]
    exact (hr a (hS.mem_toFinset.mp ha)).1
  have hdim : (Module.finrank ℂ V : ℂ) =
      ∏ a ∈ hS.toFinset, rootForm_value H (lam + ρ) a / rootForm_value H ρ a := by
    rw [← evaluate_character_at_zero H φ hss V, denominator_limit hS.toFinset r α f g F he hn]
    apply Finset.prod_congr rfl
    intro a ha
    change rootForm_value H (α a).val (lam + ρ) / rootForm_value H (α a).val ρ = _
    rw [hα a ha, rootForm_symm H a (lam + ρ), rootForm_symm H a ρ]
  have hcprod : (Module.finrank ℂ V : ℂ) =
      ∏ a ∈ hS.toFinset, (lam + ρ) (coroot_value H a) / ρ (coroot_value H a) := by
    rw [hdim]
    exact Finset.prod_congr rfl fun a ha => (hr a (hS.mem_toFinset.mp ha)).2
  have hprod (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (hB : CorootCompatible H φ B) :
      (∀ a ∈ positive H φ, B ρ a ≠ 0) ∧
        (Module.finrank ℂ V : ℂ) = ∏ a ∈ hS.toFinset, B (lam + ρ) a / B ρ a := by
    have hratio (a : Module.Dual ℂ H) (ha : a ∈ positive H φ) :=
      compare_coroot_ratios H φ B hB (lam + ρ) ρ ha (hρc a ha)
    refine ⟨fun a ha => (hratio a ha).1, hcprod.trans ?_⟩
    exact Finset.prod_congr rfl fun a ha => (hratio a (hS.mem_toFinset.mp ha)).2.symm
  refine ⟨fd, hS, fun a ha => ⟨(hr a ha).1, hρc a ha⟩, hdim, hcprod, hprod, ?_, ?_, ?_, ?_⟩
  · intro B hInv hB
    exact hprod (weightForm_value H B) (invariant_coroot_compatible H φ hss B hInv hB)
  · intro hz
    have h := hcprod
    rw [hz, zero_add] at h
    have hOne : (∏ a ∈ hS.toFinset, ρ (coroot_value H a) / ρ (coroot_value H a)) = 1 :=
      Finset.prod_eq_one fun a ha => div_self (hρc a (hS.mem_toFinset.mp ha))
    rw [hOne] at h
    exact_mod_cast h
  · intro hEmpty
    have he : hS.toFinset = ∅ := by
      ext a
      simp [hEmpty]
    rw [he, Finset.prod_empty] at hdim
    exact_mod_cast hdim
  · intro hZero
    letI := hZero
    have he : hS.toFinset = ∅ := by
      ext a
      have hR := (RealRootSpace.zero_rank H).1
      simp [positive, hR]
    rw [he, Finset.prod_empty] at hdim
    exact_mod_cast hdim

/-- Weyl's dimension formula for the simple quotient of the prescribed character. -/
theorem formula :
    _root_.Specs.LieAlgebrasAndRepresentations.WeylDimension.formulaType.{u} := by
  intro L _ _ _ hss H _ φ hφ lam χ hdom hχ
  exact dimension_of_character hss H φ hφ lam χ
    (WeylCharacter.formula hss H φ hφ lam χ hdom hχ)

/-- The formula for the simple module of every dominant integral weight. -/
theorem formula_for_dominant :
    _root_.Specs.LieAlgebrasAndRepresentations.WeylDimension.formulaForDominantType.{u} := by
  intro L _ _ _ hss H _ φ hφ lam hdom
  obtain ⟨χ, hχ, hf⟩ := WeylCharacter.formula_for_dominant hss H φ hφ lam hdom
  exact ⟨χ, hχ, dimension_of_character hss H φ hφ lam χ hf⟩

end LieAlgebrasAndRepresentations.WeylDimension
