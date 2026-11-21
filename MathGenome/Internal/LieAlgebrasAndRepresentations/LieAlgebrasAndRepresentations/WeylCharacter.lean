import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeylCharacter
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacters
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDenominator
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TruncatedVermaExpansion
import Batteries.Tactic.OpenPrivate

/-! Proof of the Weyl character formula using a finite truncation of the Verma
character expansion at the finitely many coefficients needed for each exponent. -/

noncomputable section

namespace LieAlgebrasAndRepresentations.WeylCharacter

open scoped Classical BigOperators
open AddMonoidAlgebra Module Set
open _root_.Specs.LieAlgebrasAndRepresentations
open VermaModules VermaWeightsUniversal SerreRelations SimpleHighestWeightQuotient
open HighestWeightData (weightSpace_value)
open IntegrableHighestWeightQuotient (IsDominant)
open SolvableRadical (IsSemisimple_value)
open RootDecomposition (rootSet_value)
open _root_.Specs.LieAlgebrasAndRepresentations.FormalCharacters
open _root_.LieAlgebrasAndRepresentations.FormalCharacters
  (integralInclusion integralInclusion_character)
open TruncatedVermaExpansion HighestWeightCasimir FiniteModuleWeights RealRootSpace
open WeylDenominator

open private integralInclusion_injective
  finite_weightSpaces_internal map_weightSpace_eq from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacters
open private quotient_highest_ne_zero from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open private positiveRoot_mem_cone from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open private positive_direction from MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FormalCharacterDefinitions
open private mem_cone_iff from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TruncatedVermaExpansion
open private complexifyAutomorphism complexifyAutomorphism_apply extension_injective
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteModuleWeights
open private map_denominator map_alternant extension_image_positive extension_mem_simple
  complexify_det finiteDimensional_of_rootSystem sign_reflection
  rho_in_simpleChamber from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDenominator

universe u v
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

private def complete : GroupRing H →ₐ[ℤ] Completion H φ :=
  AddMonoidAlgebra.lift ℤ _ _ {
    toFun := monomial H φ
    map_one' := (LieAlgebrasAndRepresentations.FormalCharacters.monomial_laws H φ).1
    map_mul' := fun a b => ((LieAlgebrasAndRepresentations.FormalCharacters.monomial_laws H φ).2 a b).symm
  }

private lemma complete_single (a : Module.Dual ℂ H) (k : ℤ) :
    complete H φ (single a k) = k • monomial H φ a := by
  exact AddMonoidAlgebra.lift_single _ _ _

private def coeffLinear : Completion H φ →ₗ[ℤ] (Module.Dual ℂ H → ℤ) where
  toFun := coeff H φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma complete_coeff (F : GroupRing H) (x : Module.Dual ℂ H) :
    coeff H φ (complete H φ F) x = F.coeff x := by
  induction F using AddMonoidAlgebra.induction_on with
  | of a =>
    change coeff H φ (complete H φ (single a 1)) x = (single a (1 : ℤ) : GroupRing H).coeff x
    rw [complete_single, one_smul]
    change (HahnSeries.single (exponent H φ a) (1 : ℤ)).coeff (exponent H φ x) = _
    by_cases h : a = x
    · subst x
      simp
    · simp [Ne.symm h]
  | add p q hp hq =>
    change (coeffLinear H φ) (complete H φ (p + q)) x = _
    rw [map_add, map_add, Pi.add_apply, coeff_add, Finsupp.add_apply]
    exact congrArg₂ (· + ·) hp hq
  | smul k p hp =>
    change (coeffLinear H φ) (complete H φ (k • p)) x = _
    rw [map_smul, map_smul, Pi.smul_apply, coeff_smul_apply]
    exact congrArg (k • ·) hp

private lemma complete_coeff_mul_single (a x : Module.Dual ℂ H) (k : ℤ)
    (F : Completion H φ) :
    coeff H φ (complete H φ (single a k) * F) x = k * coeff H φ F (x - a) := by
  rw [complete_single, smul_mul_assoc]
  change (coeffLinear H φ) (k • (monomial H φ a * F)) x = _
  simp only [map_smul, Pi.smul_apply, Int.zsmul_eq_mul]
  change k * (HahnSeries.single (exponent H φ a) (1 : ℤ) * F.val).coeff (exponent H φ x) = _
  rw [HahnSeries.coeff_single_mul, one_mul]
  rfl


private lemma denominator_expansion {K : Type*} [AddCommGroup K] (r : K) (S : Finset K) :
    denominator r S id =
      ∑ T ∈ S.powerset, single (r - ∑ a ∈ T, a) ((-1 : ℤ) ^ T.card) := by
  unfold denominator
  simp only [id_eq]
  rw [Finset.prod_sub, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  simp only [Finset.prod_const_one, mul_one, prod_single]
  have hneg : ((-1 : AddMonoidAlgebra ℤ K) ^ T.card) =
      ((-1 : ℤ) ^ T.card) • (1 : AddMonoidAlgebra ℤ K) := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one, mul_one]
  rw [hneg, smul_mul_assoc, one_mul, mul_smul_comm, single_mul_single, Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]


private lemma denominator_coefficients (r x : Module.Dual ℂ H)
    (S : Finset (Module.Dual ℂ H)) (F : Completion H φ) :
    coeff H φ (complete H φ (denominator r S id) * F) x =
      ∑ T ∈ S.powerset, (-1 : ℤ) ^ T.card * coeff H φ F (x - (r - ∑ a ∈ T, a)) := by
  rw [denominator_expansion, map_sum, Finset.sum_mul]
  change (coeffLinear H φ) (∑ T ∈ S.powerset, _) x = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro T _
  exact complete_coeff_mul_single H φ _ _ _ _

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private lemma verma_cancel (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (hS : (SerreRelations.positive H φ).Finite) (r μ : Module.Dual ℂ H)
    (χ : U (borel_value H φ) →ₐ[ℂ] ℂ) (hχ : IsWeightCharacter H φ μ χ) :
    ∃ F : Completion H φ, (∀ y, coeff H φ F y = vermaMultiplicity H φ χ y) ∧
      complete H φ (denominator r hS.toFinset id) * F = monomial H φ (r + μ) := by
  obtain ⟨S, hS', g, hg, he⟩ :=
    LieAlgebrasAndRepresentations.FormalCharacters.verma_character hss H φ hφ μ χ hχ
  let F := monomial H φ μ * ∏ a ∈ S, ((g a)⁻¹).val
  refine ⟨F, he, ?_⟩
  have hmap : S.image Subtype.val = hS.toFinset := by
    ext a
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨fun ⟨b, _, h⟩ => h ▸ b.property, fun ha => ⟨⟨a, ha⟩, hS' ⟨a, ha⟩, rfl⟩⟩
  rw [denominator, map_mul, map_prod, complete_single, one_smul, ← hmap,
    Finset.prod_image Subtype.val_injective.injOn]
  have hprod : (∏ x ∈ S, complete H φ (1 - single (-id x.val) 1)) = ∏ a ∈ S, (g a).val := by
    apply Finset.prod_congr rfl
    intro a _
    rw [hg, map_sub, map_one, complete_single, one_smul]
    rfl
  rw [hprod]
  dsimp only [F]
  calc
    _ = (monomial H φ r * monomial H φ μ) *
        ((∏ a ∈ S, (g a).val) * ∏ a ∈ S, ((g a)⁻¹).val) := by ac_rfl
    _ = monomial H φ (r + μ) := by
      rw [← Finset.prod_mul_distrib]
      simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, Finset.prod_const_one, mul_one]
      exact (LieAlgebrasAndRepresentations.FormalCharacters.monomial_laws H φ).2 r μ

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
private lemma multiplicity_eq_zero_of_weightSpace_eq_bot
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (y : Module.Dual ℂ H) (hy : weightSpace_value V H y = ⊥) :
    FormalCharacters.multiplicity H V y = 0 := by
  unfold FormalCharacters.multiplicity
  rw [hy, finrank_bot]
  rfl

private lemma verma_mult_zero (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (μ y : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
    (hχ : IsWeightCharacter H φ μ χ) (hn : μ - y ∉ cone H φ) :
    vermaMultiplicity H φ χ y = 0 := by
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  have hw := (VermaWeightsUniversal.verma_weights hss H φ hφ μ χ hχ).2.2.1 y
  have hb : weightSpace_value (induced_value H φ χ) H y = ⊥ := by
    by_contra h
    exact hn (hw.mp h)
  change multiplicity H (induced_value H φ χ) y = 0
  exact multiplicity_eq_zero_of_weightSpace_eq_bot H _ _ hb

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
private lemma finite_cutoff (lam : Module.Dual ℂ H) (S : Finset (Module.Dual ℂ H)) :
    ∃ N : ℕ, ∀ y ∈ S, lam - y ∈ cone H φ → HeightAtMost H φ (lam - y) N := by
  classical
  let n (y : Module.Dual ℂ H) :=
    if h : lam - y ∈ cone H φ then ((mem_cone_iff H φ _).mp h).choose.length else 0
  refine ⟨S.sup n, fun y hy h => ⟨((mem_cone_iff H φ _).mp h).choose,
    ((mem_cone_iff H φ _).mp h).choose_spec, ?_⟩⟩
  have hn : n y ≤ S.sup n := Finset.le_sup hy
  simpa only [n, dite_eq_left h] using hn

omit [FiniteDimensional ℂ L] in
private lemma numerator_support_and_top
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] (lam r : Module.Dual ℂ H) (hS : (SerreRelations.positive H φ).Finite)
    (hroots : ∀ a ∈ SerreRelations.positive H φ, a ∈ cone H φ)
    (hbelow : ∀ y, weightSpace_value V H y ≠ ⊥ → lam - y ∈ cone H φ)
    (htop : multiplicity H V lam = 1) :
    let F := denominator r hS.toFinset id * finiteCharacter H V
    (∀ x, F.coeff x ≠ 0 → (lam + r) - x ∈ cone H φ) ∧ F.coeff (lam + r) = 1 := by
  dsimp only
  have hcoeff (x : Module.Dual ℂ H) :
      (denominator r hS.toFinset id * finiteCharacter H V).coeff x =
        ∑ T ∈ hS.toFinset.powerset, (-1 : ℤ) ^ T.card *
          multiplicity H V (x - (r - ∑ a ∈ T, a)) := by
    rw [← complete_coeff H φ, map_mul, denominator_coefficients]
    simp only [complete_coeff]
    rfl
  have memSum (T : Finset (Module.Dual ℂ H)) (hT : T ∈ hS.toFinset.powerset) :
      (∑ a ∈ T, a) ∈ cone H φ :=
    Submodule.sum_mem _ fun a ha => hroots a (hS.mem_toFinset.mp (Finset.mem_powerset.mp hT ha))
  constructor
  · intro x hx
    rw [hcoeff] at hx
    obtain ⟨T, hT, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have hm : multiplicity H V (x - (r - ∑ a ∈ T, a)) ≠ 0 := by
      intro he
      exact ht (by rw [he, mul_zero])
    have hb := hbelow _ (fun hb => hm (multiplicity_eq_zero_of_weightSpace_eq_bot H _ _ hb))
    have he : lam + r - x = lam - (x - (r - ∑ a ∈ T, a)) + ∑ a ∈ T, a := by abel
    rw [he]
    exact (cone H φ).add_mem hb (memSum T hT)
  · rw [hcoeff, Finset.sum_eq_single ∅]
    · simpa using htop
    · intro T hT hn
      suffices multiplicity H V (lam + r - (r - ∑ a ∈ T, a)) = 0 by rw [this, mul_zero]
      by_contra hm
      have hb := hbelow _ (fun hb => hm (multiplicity_eq_zero_of_weightSpace_eq_bot H _ _ hb))
      have ht : 0 < φ (∑ a ∈ T, a) := by
        rw [map_sum]
        exact Finset.sum_pos (fun a ha => (hS.mem_toFinset.mp (Finset.mem_powerset.mp hT ha)).2)
          (Finset.nonempty_iff_ne_empty.mpr hn)
      rcases positive_direction H φ hb with he | hp
      · have he' := congrArg φ he
        simp only [map_sub, map_add, map_zero] at he'
        linarith
      · simp only [map_sub, map_add] at hp
        linarith
    · simp

private lemma numerator_casimir
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] (lam r : Module.Dual ℂ H) (hS : (SerreRelations.positive H φ).Finite)
    (B : Form (L := L)) (hB : B.Nondegenerate) (hInv : B.lieInvariant L)
    (hpos : PositiveOnRealRoots H B)
    (hbelow : ∀ y, weightSpace_value V H y ≠ ⊥ → lam - y ∈ cone H φ)
    (hscalar : ∀ z : V,
      LieAlgebrasAndRepresentations.ModuleCasimir.action ℂ L V
        (casimir_value B hB (Module.finBasis ℂ L)) z = eigenvalue_value H φ B lam • z)
    (x : Module.Dual ℂ H)
    (hx : (denominator r hS.toFinset id * finiteCharacter H V).coeff x ≠ 0) :
    eigenvalue_value H φ B (x - r) = eigenvalue_value H φ B lam := by
  let S := hS.toFinset.powerset
  let y (T : Finset (Module.Dual ℂ H)) := x - (r - ∑ a ∈ T, a)
  obtain ⟨N, hN⟩ := finite_cutoff H φ lam (S.image y)
  obtain ⟨χ, hχ, l, hl, htrunc⟩ :=
    LieAlgebrasAndRepresentations.TruncatedVermaExpansion.truncated_verma_expansion
      hss H φ hφ B hB hInv hpos (Module.finBasis ℂ L) V lam (eigenvalue_value H φ B lam) N
      (finite_weightSpaces_internal H hss) (fun _ => inferInstance) hbelow hscalar
  choose F hF hcF using fun μ => verma_cancel H φ hss hφ hS r μ (χ μ) (hχ μ)
  have hagree (T : Finset (Module.Dual ℂ H)) (hT : T ∈ S) :
      multiplicity H V (y T) = ∑ μ ∈ l.support, l μ * coeff H φ (F μ) (y T) := by
    by_cases hy : lam - y T ∈ cone H φ
    · have h := htrunc (y T) (hN _ (Finset.mem_image_of_mem y hT) hy)
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
        Pi.smul_apply, Int.zsmul_eq_mul, hF] using h
    · have hbot : weightSpace_value V H (y T) = ⊥ := by
        by_contra h
        exact hy (hbelow _ h)
      rw [multiplicity_eq_zero_of_weightSpace_eq_bot H V (y T) hbot]
      symm
      apply Finset.sum_eq_zero
      intro μ hμ
      have hb := (hl μ (Finsupp.mem_support_iff.mp hμ)).1
      have hn : μ - y T ∉ cone H φ := by
        intro hc
        apply hy
        rw [← sub_add_sub_cancel lam μ (y T)]
        exact (cone H φ).add_mem hb hc
      rw [hF, verma_mult_zero H φ hss hφ μ (y T) (χ μ) (hχ μ) hn, mul_zero]
  let G := ∑ μ ∈ l.support, l μ • F μ
  have he :
      (denominator r hS.toFinset id * finiteCharacter H V).coeff x =
        coeff H φ (complete H φ (denominator r hS.toFinset id) * G) x := by
    rw [← complete_coeff H φ, map_mul, denominator_coefficients, denominator_coefficients]
    apply Finset.sum_congr rfl
    intro T hT
    congr 1
    rw [complete_coeff]
    change multiplicity H V (y T) = (coeffLinear H φ) G (y T)
    rw [hagree T hT]
    simp only [G, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, Int.zsmul_eq_mul]
    rfl
  have hcoeff :
      coeff H φ (complete H φ (denominator r hS.toFinset id) * G) x =
        ∑ μ ∈ l.support, l μ * (single (r + μ) (1 : ℤ) : GroupRing H).coeff x := by
    dsimp only [G]
    rw [Finset.mul_sum]
    simp only [mul_smul_comm, hcF]
    change (coeffLinear H φ) (∑ μ ∈ l.support, l μ • monomial H φ (r + μ)) x = _
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, Int.zsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro μ _
    exact congrArg (l μ * ·) (by
      change coeff H φ (monomial H φ (r + μ)) x = _
      simpa only [complete_single, one_smul] using complete_coeff H φ (single (r + μ) 1) x)
  rw [he, hcoeff] at hx
  obtain ⟨μ, hm, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  have hEq : r + μ = x := by
    by_contra hn
    exact hμ (by simp [hn])
  rw [← hEq, add_comm, add_sub_cancel_right]
  exact (hl μ (Finsupp.mem_support_iff.mp hm)).2

private lemma killing_on_real (hss : IsSemisimple_value ℂ L) (d : Realization H)
    (x y : E H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    weightForm_value H (TraceCriterion.killingForm_value ℂ L) (d.j x) (d.j y) =
      (inner ℝ x y : ℂ) := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  let B := TraceCriterion.killingForm_value ℂ L
  have hB : B.Nondegenerate := (semisimple_iff_killingForm_nondegenerate ℂ L).mp hss
  obtain ⟨hC, hpair⟩ := LieAlgebrasAndRepresentations.HighestWeightCasimir.representative_pairing
    H hss B (LieModule.traceForm_lieInvariant ℂ L L) hB
  have hrep (a : E H) : weightRepresentative_value H B (d.j a) = (d.q a : H) := by
    apply ((B.restrict H.toSubmodule).toDual hC).injective
    ext h
    exact hpair (d.j a) h
  change RealRootSpace.killing H (weightRepresentative_value H B (d.j x))
    (weightRepresentative_value H B (d.j y)) = _
  rw [hrep, hrep]
  exact d.killing_restrict_real (d.q x) (d.q y)

private lemma killing_positive_on_roots (hss : IsSemisimple_value ℂ L) (d : Realization H) :
    PositiveOnRealRoots H (TraceCriterion.killingForm_value ℂ L) := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  intro a ha hn
  have hm : a ∈ LinearMap.range d.j :=
    (Submodule.span_le.mpr (fun b hb => LinearMap.mem_range.mpr ⟨rootRestriction H b, d.extension_root b hb⟩)) ha
  obtain ⟨x, rfl⟩ := hm
  rw [killing_on_real H hss d]
  exact ⟨by
    rw [Complex.ofReal_re]
    exact real_inner_self_pos.mpr (fun hx => hn (hx ▸ map_zero d.j)),
    Complex.ofReal_im _⟩

section RealChambers

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
variable {R : Set E'} {v₀ : E'}

private lemma strict_chamber_orbit_injective (hR : IsRootSystem R) (hv : RootRegular R v₀)
    {x : E'} (hx : x ∈ simpleChamber R v₀) :
    Function.Injective (fun w : rootWeylGroup R => w.val x) := by
  intro w z hwz
  change w.val x = z.val x at hwz
  let t := z⁻¹ * w
  have ht : t.val x = x := by
    change z.val.symm (w.val x) = x
    rw [hwz, LinearEquiv.symm_apply_apply]
  have hreg := simpleChamber_regular hR.toRootAxioms hv hx
  have hc := rootWeylGroup_image_component hR.toRootAxioms t hreg
  rw [ht] at hc
  have hC := simpleChamber_connectedComponent R hR v₀ hv
  have hm : x ∈ connectedComponentIn (rootHyperplaneComplement R) v₀ := hC ▸ hx
  have hcomp : connectedComponentIn (rootHyperplaneComplement R) x =
      simpleChamber R v₀ := (connectedComponentIn_eq hm).symm.trans hC.symm
  rw [hcomp] at hc
  exact (inv_mul_eq_one.mp (weyl_simpleChamber_stabilizer hR hv t hc)).symm

private lemma strict_chamber_inner
    {x y : E'} (hx : x ∈ simpleChamber R v₀) (hy : y ∈ simpleChamber R v₀)
    {δ : E'} (hd : δ ∈ Submodule.span ℕ (simpleRoots R v₀)) :
    δ = 0 ∨ 0 < inner ℝ δ (x + y) := by
  refine Submodule.span_induction (p := fun a _ => a = 0 ∨ 0 < inner ℝ a (x + y))
    ?_ (Or.inl rfl) ?_ ?_ hd
  · intro a ha
    right
    rw [real_inner_comm, inner_add_left]
    exact add_pos (hx a ha) (hy a ha)
  · rintro a b _ _ (rfl | ha) (rfl | hb)
    · simp
    · simpa using Or.inr hb
    · simpa using Or.inr ha
    · exact Or.inr (by rw [inner_add_left]; exact add_pos ha hb)
  · rintro n a _ (rfl | ha)
    · simp
    cases n with
    | zero => simp
    | succ n =>
      right
      rw [← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_left]
      exact mul_pos (by positivity) ha

end RealChambers

section OrbitAlgebra

variable {K : Type*} [AddCommGroup K]
variable {W : Type*} [Group W] [Fintype W]
variable (g : W → (K ≃+ K)) (sgn : W → ℤ)
variable (hsgn : ∀ w z, sgn (w * z) = sgn w * sgn z)

private def onRing (w : W) : AddMonoidAlgebra ℤ K ≃+* AddMonoidAlgebra ℤ K :=
  mapDomainRingEquiv ℤ (g w)

omit [Group W] [Fintype W] in
private lemma onRing_coeff (w : W) (F : AddMonoidAlgebra ℤ K) (x : K) :
    (onRing g w F).coeff (g w x) = F.coeff x := by
  simp [onRing]

include hsgn
private lemma onRing_alternant (hg : ∀ (w z : W) (x : K), g (w * z) x = g w (g z x))
    (hsq : ∀ w, sgn w * sgn w = 1) (w : W) (a : K) :
    onRing g w (alternant sgn (fun z => g z a)) =
      sgn w • alternant sgn (fun z => g z a) := by
  have hs := hsq w
  simp only [alternant, finsum_eq_sum_of_fintype, map_sum,
    Finset.smul_sum]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft w)]
  apply Finset.sum_congr rfl
  intro z _
  change onRing g w (single (g z a) (sgn z)) =
    sgn w • single (g (w * z) a) (sgn (w * z))
  simp [onRing, hg, hsgn, ← mul_assoc, hs]

omit [Group W] hsgn in
private lemma coefficients_define_alternant (F : AddMonoidAlgebra ℤ K) (a : K)
    (hcoeff : ∀ (w : W) x, F.coeff (g w x) = sgn w * F.coeff x)
    (htop : F.coeff a = 1)
    (hinj : Function.Injective (fun w : W => g w a))
    (hsupport : ∀ x, F.coeff x ≠ 0 → ∃ w : W, g w a = x) :
    F = alternant sgn (fun w => g w a) := by
  apply AddMonoidAlgebra.ext
  ext x
  simp only [alternant, finsum_eq_sum_of_fintype,
    coeff_sum, Finsupp.finsetSum_apply]
  by_cases he : ∃ w : W, g w a = x
  · obtain ⟨w, rfl⟩ := he
    rw [hcoeff, htop, mul_one, Finset.sum_eq_single w]
    · simp
    · intro z _ hzw
      simp [show g z a ≠ g w a from fun h => hzw (hinj h)]
    · simp
  · rw [show F.coeff x = 0 from not_not.mp (fun h => he (hsupport x h))]
    symm
    exact Finset.sum_eq_zero (fun w _ => by simp [show g w a ≠ x from fun h => he ⟨w, h⟩])

end OrbitAlgebra

open private exists_normalized from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightClassification

/-- The character of the canonical finite-dimensional simple quotient satisfies
both denominator-cleared expressions in the integral weight group ring. -/
theorem formula : Specs.LieAlgebrasAndRepresentations.WeylCharacter.formulaType.{u} := by
  intro L _ _ _ hss H _ φ hφ lam χ hlam hχ
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let V := simpleQuotient_value H φ χ
  letI fd : FiniteDimensional ℂ V :=
    ((LieAlgebrasAndRepresentations.HighestWeightClassification.finite_simple_iff_dominant
      hss H φ hφ lam χ hχ).mpr hlam).1
  obtain ⟨hS, hρ, hP, hW, hfinite, hdet, hDA⟩ :=
    LieAlgebrasAndRepresentations.WeylDenominator.cartan_identity hss H φ hφ
  let r := cartanRho H φ hS
  let t := lam + r
  have hlamP : lam ∈ integralWeights H φ := fun i => by
    obtain ⟨n, hn⟩ := hlam i
    exact ⟨n, by simpa using hn⟩
  have htP : t ∈ integralWeights H φ := (integralWeights H φ).add_mem hlamP hρ
  refine ⟨fd, hS, hρ, hP, hW, htP, ?_⟩
  suffices he : cartanDenominator H φ hS hρ hP * character H φ V =
      cartanAlternant H φ hW ⟨t, htP⟩ by
    exact ⟨he, (congrArg (fun d => d * character H φ V) hDA).symm.trans he⟩
  letI := hfinite
  letI := Fintype.ofFinite (weightWeylGroup H)
  let I := integralInclusion H φ
  let D := denominator r hS.toFinset id
  let C := finiteCharacter H V
  let F := D * C
  let g (w : weightWeylGroup H) := w.val.toAddEquiv
  let sgn := cartanSign H
  have hID : I (cartanDenominator H φ hS hρ hP) = D := by
    unfold I integralInclusion cartanDenominator
    rw [map_denominator]
    apply congrArg (fun f => single r 1 * f)
    apply Finset.prod_congr rfl
    intro a ha
    simp [hS.mem_toFinset.mp ha]
  have hIA (a : integralWeights H φ) :
      I (cartanAlternant H φ hW a) = alternant sgn (fun w => g w a.val) := by
    unfold I integralInclusion cartanAlternant
    rw [map_alternant]
    rfl
  have hIC : I (character H φ V) = C := integralInclusion_character H φ V hss
  have hF (x : Module.Dual ℂ H) (hx : F.coeff x ≠ 0) : x ∈ integralWeights H φ := by
    by_contra hn
    have hIF : F = I (cartanDenominator H φ hS hρ hP * character H φ V) := by
      rw [map_mul, hID, hIC]
    rw [hIF] at hx
    apply hx
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, rfl⟩
    exact hn a.property
  apply integralInclusion_injective H φ
  change I (_ * _) = I _
  rw [map_mul, hID, hIC, hIA]
  change F = alternant sgn (fun w => g w t)
  have hsign (w z : weightWeylGroup H) : sgn (w * z) = sgn w * sgn z := by
    exact_mod_cast (show (sgn (w * z) : ℂ) = (sgn w : ℂ) * (sgn z : ℂ) by
      simp only [sgn, hdet]
      exact LinearMap.det_comp _ _)
  have hsq (w : weightWeylGroup H) : sgn w * sgn w = 1 := by
    dsimp [sgn, cartanSign]
    split <;> norm_num
  have hDn : D = alternant sgn (fun w => g w r) := by
    simpa only [hID, hIA] using congrArg I hDA
  have hCw (w : weightWeylGroup H) : onRing g w C = C := by
    apply AddMonoidAlgebra.ext
    ext y
    obtain ⟨x, rfl⟩ := (g w).surjective y
    rw [onRing_coeff]
    exact (LieAlgebrasAndRepresentations.FormalCharacters.weyl_invariance hss H V w x).symm
  have hequiv (w : weightWeylGroup H) (x : Module.Dual ℂ H) :
      F.coeff (g w x) = sgn w * F.coeff x := by
    have he := onRing_coeff g w F x
    have hDw : onRing g w D = sgn w • D := by
      rw [hDn]
      exact onRing_alternant g sgn hsign (fun _ _ _ => rfl) hsq w r
    rw [show F = D * C from rfl, map_mul, hDw, hCw, smul_mul_assoc] at he
    change sgn w * F.coeff (g w x) = F.coeff x at he
    rw [← he, ← mul_assoc, hsq w, one_mul]
  obtain ⟨hint, _, hs, hline⟩ :=
    LieAlgebrasAndRepresentations.VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ
  have hmap := map_weightSpace_eq H (quotientMap H φ χ)
    (LieSubmodule.Quotient.surjective_mk' _) hint
  have hbelow (a : Module.Dual ℂ H) : weightSpace_value V H a ≠ ⊥ → lam - a ∈ cone H φ := by
    intro ha
    apply (hs a).mp
    intro hb
    apply ha
    have hm := hmap a
    rw [hb, Submodule.map_bot] at hm
    exact hm.symm
  have htop : multiplicity H V lam = 1 := by
    have hm := hmap lam
    rw [hline, Submodule.map_span, Set.image_singleton] at hm
    change (Module.finrank ℂ (weightSpace_value V H lam) : ℤ) = 1
    rw [← hm]
    change (Module.finrank ℂ (ℂ ∙ quotientHighestVector H φ χ) : ℤ) = 1
    rw [finrank_span_singleton (quotient_highest_ne_zero H φ χ hss hφ lam hχ)]
    rfl
  have hroots (a : Module.Dual ℂ H) (ha : a ∈ SerreRelations.positive H φ) :
      a ∈ cone H φ := positiveRoot_mem_cone H φ hss ⟨a, ha⟩
  obtain ⟨hsupp, htopF⟩ := numerator_support_and_top H φ V lam r hS hroots hbelow htop
  obtain ⟨d, hd⟩ := LieAlgebrasAndRepresentations.HighestWeight.cartan_lattice_comparison.{u,u} hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  let R := realRoots H
  have hR : IsRootSystem R := d.root_system
  letI := finiteDimensional_of_rootSystem hR
  let p := (InnerProductSpace.toDual ℝ (E H)).symm (φ.comp d.j).toContinuousLinearMap
  have hp (x : E H) : inner ℝ p x = φ (d.j x) := InnerProductSpace.toDual_symm_apply
  have hpR : RootRegular R p := by
    rintro x ⟨α, hα, rfl⟩
    rw [hp, d.extension_root α hα]
    exact hφ α hα
  have hj := extension_injective d
  have hpos := extension_image_positive d φ p hp
  have hsimp := extension_mem_simple d φ p hp
  let s₀ : simpleRoots R p → simple H φ := fun a => ⟨d.j a.val, (hsimp a).mpr a.property⟩
  have hs₀ : Function.Bijective s₀ := by
    constructor
    · intro a b he
      exact Subtype.ext (hj (congrArg Subtype.val he))
    · intro a
      have ha : a.val ∈ d.j '' positiveRoots R p := hpos.symm ▸ a.property.1
      obtain ⟨x, _, hxa⟩ := ha
      exact ⟨⟨x, (hsimp x).mp (hxa ▸ a.property)⟩, Subtype.ext hxa⟩
  let s : simple H φ ≃ simpleRoots R p := (Equiv.ofBijective s₀ hs₀).symm
  have hsimple (i : simple H φ) : d.j (s i : E H) = i.val :=
    congrArg Subtype.val ((Equiv.ofBijective s₀ hs₀).apply_symm_apply i)
  obtain ⟨b, c, a, hb, hbasis, hpair, _, _, hcone, hlat, hdom, hreal, _⟩ := hd p hpR s
  simp only [hsimple] at hcone hdom hreal
  change (Submodule.span ℕ (Set.range b)).map (d.j.restrictScalars ℕ) = cone H φ at hcone
  have hm : lam ∈ d.j '' {x | x ∈ weightLattice b ∧ x ∈ closedSimpleChamber R p} :=
    hdom.symm ▸ hlam
  obtain ⟨l, hl, hjl⟩ := hm
  have hl' : l ∈ closedSimpleChamber R p := hl.2
  have hrr : r = d.j (rootRho R p) := by
    have hf := positiveRoots_finite hR.toRootAxioms p
    have hSF : hS.toFinset = hf.toFinset.image d.j := by
      ext α
      simp only [Set.Finite.mem_toFinset, Finset.mem_image]
      rw [← hpos]
      rfl
    unfold r cartanRho rootRho
    rw [hSF, Finset.sum_image hj.injOn, finsum_mem_eq_finite_toFinset_sum _ hf, map_smul, map_sum]
    rw [← IsScalarTower.algebraMap_smul ℂ (1 / 2 : ℝ)]
    congr 1
    norm_num [Complex.coe_algebraMap]
  let t₀ := l + rootRho R p
  have ht₀ : d.j t₀ = t := by dsimp [t₀, t]; rw [map_add, hjl, ← hrr]
  have hstrict : t₀ ∈ simpleChamber R p := by
    intro a ha
    change 0 < inner ℝ (l + rootRho R p) a
    rw [inner_add_left]
    exact add_pos_of_nonneg_of_pos (hl' a ha) (rho_in_simpleChamber hR hpR a ha)
  obtain ⟨_, G, hG⟩ := LieAlgebrasAndRepresentations.FiniteModuleWeights.weyl_complexification H d
  have hact (w : rootWeylGroup R) (x : E H) : g (G w) (d.j x) = d.j (w.val x) := by
    exact (hG w x).symm
  have hsignG (w : rootWeylGroup R) : sgn (G w) = sign w := by
    have hw : (G w).val = complexifyAutomorphism d w.val := by
      apply LinearEquiv.toLinearMap_injective
      refine LinearMap.ext_on d.roots_span fun α hα => ?_
      change (G w).val α = complexifyAutomorphism d w.val α
      rw [← d.extension_root α hα, complexifyAutomorphism_apply]
      exact hact w _
    have he := hdet (G w)
    rw [hw, complexify_det, ← sign_cast hR w] at he
    exact_mod_cast he
  have hinj : Function.Injective (fun w : weightWeylGroup H => g w t) := by
    intro w z he
    obtain ⟨w, rfl⟩ := G.surjective w
    obtain ⟨z, rfl⟩ := G.surjective z
    change g (G w) t = g (G z) t at he
    rw [← ht₀, hact, hact] at he
    exact congrArg G (strict_chamber_orbit_injective hR hpR hstrict (hj he))
  let B := TraceCriterion.killingForm_value ℂ L
  have hB : B.Nondegenerate := (semisimple_iff_killingForm_nondegenerate ℂ L).mp hss
  have hInv : B.lieInvariant L := LieModule.traceForm_lieInvariant ℂ L L
  obtain ⟨e, f, hef⟩ := exists_normalized hss H φ
  have he : RaisingVectors H φ e := fun i => ⟨(hef i).1, (hef i).2.2.1⟩
  have hgen := (LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.simple_quotient
    hss H φ hφ lam χ hχ e he).2
  have hg := (LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.highest_weight_iff_positive
    hss H φ e he V lam (quotientHighestVector H φ χ)).mp hgen
  have hscalar := LieAlgebrasAndRepresentations.HighestWeightCasimir.eigenvalue_action
    H hss φ hφ B hB hInv (Module.finBasis ℂ L) V lam (quotientHighestVector H φ χ)
    hg.2.1 (fun x hx => hg.2.2.1 ⟨x, hx⟩) hg.2.2.2
  have hrho : rho_value H φ = r := by
    letI : Fintype (SerreRelations.positive H φ) := hS.fintype
    unfold rho_value r cartanRho
    congr 1
    rw [finsum_eq_sum_of_fintype]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact hS.mem_toFinset.mpr a.property
    · intro a _ b _ he
      exact Subtype.ext he
    · intro a ha
      exact ⟨⟨a, hS.mem_toFinset.mp ha⟩, Finset.mem_univ _, rfl⟩
    · intros; rfl
  have hnorm (x : E H) (hx : F.coeff (d.j x) ≠ 0) : inner ℝ x x = inner ℝ t₀ t₀ := by
    have he := numerator_casimir H φ hss hφ V lam r hS B hB hInv
      (killing_positive_on_roots H hss d) hbelow hscalar (d.j x) hx
    rw [LieAlgebrasAndRepresentations.HighestWeightCasimir.eigenvalue_difference H hss φ B hInv,
      LieAlgebrasAndRepresentations.HighestWeightCasimir.eigenvalue_difference H hss φ B hInv,
      hrho, sub_add_cancel, ← show t = lam + r from rfl, ← ht₀,
      killing_on_real H hss d, killing_on_real H hss d] at he
    exact Complex.ofReal_injective (sub_left_injective he)
  apply coefficients_define_alternant g sgn F t hequiv htopF hinj
  intro x hx
  obtain ⟨x₀, _, hjx, _⟩ := hreal x (hF x hx)
  obtain ⟨w, hw⟩ := exists_weyl_into_closedSimpleChamber hR p x₀
  let y := w.val x₀
  have hy : F.coeff (d.j y) ≠ 0 := by
    rw [show d.j y = g (G w) x by rw [← hjx, hact], hequiv]
    exact mul_ne_zero (fun h => by simpa [h] using hsq (G w)) hx
  have hyStrict : y ∈ simpleChamber R p := by
    intro a ha
    have hnonneg := hw a ha
    by_contra! hn
    have hz := le_antisymm hn hnonneg
    let z : rootWeylGroup R :=
      ⟨rootReflectionEquiv a, Subgroup.subset_closure ⟨a, ha.1.1, rfl⟩⟩
    have hzy : z.val y = y := by
      change rootReflectionEquiv a y = y
      simp [rootReflection, hz]
    have h := hequiv (G z) (d.j y)
    rw [hact, hzy, hsignG, show sign z = -1 from sign_reflection hR ha.1.1] at h
    apply hy
    linarith
  have hδ : t₀ - y ∈ Submodule.span ℕ (simpleRoots R p) := by
    have h := hsupp (d.j y) hy
    change t - d.j y ∈ cone H φ at h
    rw [← ht₀, ← map_sub, ← hcone] at h
    obtain ⟨z, hz, he⟩ := Submodule.mem_map.mp h
    have he' : d.j z = d.j (t₀ - y) := he
    rwa [← hj he', ← hb]
  have he : y = t₀ := by
    rcases strict_chamber_inner hstrict hyStrict hδ with he | hn
    · exact (sub_eq_zero.mp he).symm
    · rw [inner_sub_left, inner_add_right t₀ t₀ y, inner_add_right y t₀ y,
        real_inner_comm y t₀, hnorm y hy] at hn
      linarith
  refine ⟨(G w)⁻¹, ?_⟩
  have hwx : g (G w) x = t := by rw [← hjx, hact, show w.val x₀ = y from rfl, he, ht₀]
  change (g (G w)).symm t = x
  rw [← hwx, AddEquiv.symm_apply_apply]

/-- The prescribed Borel character exists for every dominant integral weight. -/
theorem formula_for_dominant :
    Specs.LieAlgebrasAndRepresentations.WeylCharacter.formulaForDominantType.{u} := by
  intro L _ _ _ hss H _ φ hφ lam hlam
  obtain ⟨χ, hχ, _⟩ :=
    LieAlgebrasAndRepresentations.VermaModules.character_existsUnique hss H φ hφ lam
  exact ⟨χ, hχ, formula hss H φ hφ lam χ hlam hχ⟩

end LieAlgebrasAndRepresentations.WeylCharacter
