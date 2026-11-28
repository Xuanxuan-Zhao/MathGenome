import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanQuotient
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.VermaModules
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BorelInduction
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace LieNotes.Contragredient.VermaModules

open CartanQuotient
open UniversalEnvelopingAlgebra (ι)
open Specs.LieNotes.Contragredient.VermaModules
  (IsWeightCharacter cartanInBorel positiveInBorel IsHighestVector cartanAction
    wordMultiplicity lowerWeight wordVector)

open _root_.RepTheorySurvey.CategoryO.BorelInduction
open scoped TensorProduct

noncomputable section

set_option linter.style.haveILetI false

abbrev borel := @Specs.LieNotes.Contragredient.VermaModules.borel
abbrev weightCharacter := @Specs.LieNotes.Contragredient.VermaModules.weightCharacter
abbrev characterModule := @Specs.LieNotes.Contragredient.VermaModules.characterModule
abbrev Verma := @Specs.LieNotes.Contragredient.VermaModules.Verma
abbrev top := @Specs.LieNotes.Contragredient.VermaModules.top
abbrev weightSpaceAt := @Specs.LieNotes.Contragredient.VermaModules.weightSpaceAt

universe u v w

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]

variable (R : Realization A H)

private theorem lie_cartan_positive (h : H) {x : Algebra R} (hx : x ∈ positive R) :
    ⁅cartan R h, x⁆ ∈ positive R := by
  change x ∈ (positive R).toSubmodule at hx
  change x ∈ (positive R).toSubmodule.comap (cartanAdjoint R h)
  apply (show (positive R).toSubmodule ≤
      (positive R).toSubmodule.comap (cartanAdjoint R h) from ?_) hx
  rw [← iSup_positive_grade R]
  refine iSup_le fun q ↦ iSup_le fun hq ↦ ?_
  intro y hy
  change ⁅cartan R h, y⁆ ∈ ⨆ q, ⨆ (_ : PositiveDegree q), grade R q
  refine Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hq ?_)
  simpa only [zero_add] using lie_mem_grade R (cartan_mem_grade R h) hy

private theorem lie_cartan_add_positive (h k : H) {x y : Algebra R}
    (hx : x ∈ positive R) (hy : y ∈ positive R) :
    ⁅cartan R h + x, cartan R k + y⁆ ∈ positive R := by
  classical
  rw [add_lie, lie_add, lie_add, (definingRelations R).cartan_cartan, zero_add,
    ← lie_skew (x := x) (y := cartan R k)]
  exact (positive R).add_mem (lie_cartan_positive R h hy)
    ((positive R).add_mem ((positive R).neg_mem (lie_cartan_positive R k hx))
      ((positive R).lie_mem hx hy))

private theorem borel_underlying (R : Realization A H) :
    (borel R).toSubmodule = (cartan R).range ⊔ (positive R).toSubmodule := by
  let P := (cartan R).range ⊔ (positive R).toSubmodule
  let B : LieSubalgebra ℂ (Algebra R) :=
    { P with
      lie_mem' := by
        intro x y hx hy
        obtain ⟨_, ⟨h, rfl⟩, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨_, ⟨k, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
        exact (le_sup_right : (positive R).toSubmodule ≤ P)
          (lie_cartan_add_positive R h k ha hb) }
  apply le_antisymm
  · change (borel R).toSubmodule ≤ B.toSubmodule
    have h : borel R ≤ B := LieSubalgebra.lieSpan_le.mpr (by
      rintro x (hx | hx)
      · exact (le_sup_left : (cartan R).range ≤ P) hx
      · exact (le_sup_right : (positive R).toSubmodule ≤ P) hx)
    exact h
  · refine sup_le ?_ ?_
    · rintro _ ⟨h, rfl⟩
      exact (cartanInBorel R h).property
    · intro x hx
      exact (positiveInBorel R ⟨x, hx⟩).property

theorem borelUnderlying : Specs.LieNotes.Contragredient.VermaModules.BorelUnderlying.{u, v} := by
  intro I A H _ _ _ R
  refine ⟨borel_underlying R, ?_⟩
  rw [← grade_zero, ← iSup_positive_grade]
  exact (grade_iSupIndep R).disjoint_biSup
    (show (0 : Q I) ∉ {q | PositiveDegree q} from fun h ↦ h.1 rfl)

private def borelAdd : (H × positive R) →ₗ[ℂ] borel R :=
  ((cartan R).coprod (positive R).toSubmodule.subtype).codRestrict (borel R).toSubmodule
    (fun p ↦ (borel R).add_mem (cartanInBorel R p.1).property
      (positiveInBorel R p.2).property)

private theorem borelAdd_decompose (z : borel R) :
    ∃ h : H, ∃ x : positive R, cartanInBorel R h + positiveInBorel R x = z := by
  have hz := z.property
  change z.val ∈ (borel R).toSubmodule at hz
  rw [borel_underlying R] at hz
  obtain ⟨_, ⟨h, rfl⟩, x, hx, he⟩ := Submodule.mem_sup.mp hz
  exact ⟨h, ⟨x, hx⟩, Subtype.ext he⟩

private def borelAddEquiv : (H × positive R) ≃ₗ[ℂ] borel R := by
  refine LinearEquiv.ofBijective (borelAdd R) ⟨?_, ?_⟩
  · intro x y h
    have he := (triangularAdd_bijective R).1
      (show triangularAdd R (0, x.1, x.2) = triangularAdd R (0, y.1, y.2) by
        simp only [triangularAdd_apply, Submodule.coe_zero, zero_add]
        exact congrArg Subtype.val h)
    exact congrArg Prod.snd he
  · intro z
    obtain ⟨h, x, hz⟩ := borelAdd_decompose R z
    exact ⟨(h, x), hz⟩

attribute [local instance 100] LieRing.ofAssociativeRing in
theorem weightCharacterExists :
    Specs.LieNotes.Contragredient.VermaModules.WeightCharacterExists.{u, v} := by
  intro I A H _ _ _ R Λ
  let F := borelAddEquiv R
  let p : borel R →ₗ[ℂ] ℂ :=
    (Λ.comp (LinearMap.fst ℂ H (positive R))).comp F.symm.toLinearMap
  have hcartan (h : H) : p (cartanInBorel R h) = Λ h := by
    have he : F (h, 0) = cartanInBorel R h := by
      apply Subtype.ext
      change cartan R h + 0 = cartan R h
      exact add_zero _
    rw [← he]
    change Λ (F.symm (F (h, 0))).1 = Λ h
    rw [F.symm_apply_apply]
  have hpositive (x : positive R) : p (positiveInBorel R x) = 0 := by
    have he : F (0, x) = positiveInBorel R x := by
      apply Subtype.ext
      change cartan R 0 + (x : Algebra R) = x
      rw [map_zero, zero_add]
    rw [← he]
    change Λ (F.symm (F (0, x))).1 = 0
    rw [F.symm_apply_apply]
    exact map_zero Λ
  let φ : borel R →ₗ⁅ℂ⁆ ℂ :=
    { toLinearMap := p
      map_lie' := by
        intro a b
        obtain ⟨h, x, rfl⟩ := borelAdd_decompose R a
        obtain ⟨k, y, rfl⟩ := borelAdd_decompose R b
        let z : positive R := ⟨_, lie_cartan_add_positive R h k x.property y.property⟩
        change p (positiveInBorel R z) = _ * _ - _ * _
        rw [hpositive, mul_comm, sub_self] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ φ, ⟨?_, ?_⟩, ?_⟩
  · intro h
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hcartan h
  · intro x
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hpositive x
  · intro χ hχ
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro z
    obtain ⟨h, x, rfl⟩ := borelAdd_decompose R z
    change χ (ι ℂ (cartanInBorel R h + positiveInBorel R x)) =
      UniversalEnvelopingAlgebra.lift ℂ φ (ι ℂ (cartanInBorel R h + positiveInBorel R x))
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, map_add (ι ℂ), map_add χ, map_add φ]
    change χ (ι ℂ (cartanInBorel R h)) + χ (ι ℂ (positiveInBorel R x)) =
      p (cartanInBorel R h) + p (positiveInBorel R x)
    rw [hχ.1, hχ.2, hcartan, hpositive]

private theorem characterScalarTower (R : Realization A H) (Λ : Module.Dual ℂ H)
    (hχ : ∃! χ, IsWeightCharacter R Λ χ) :
    letI := characterModule R Λ hχ
    IsScalarTower ℂ (U (borel R)) ℂ := by
  letI := characterModule R Λ hχ
  let χ := weightCharacter R Λ hχ
  refine ⟨fun c a z ↦ ?_⟩
  change χ (algebraMap ℂ (U (borel R)) c * a) * z = c * (χ a * z)
  rw [map_mul, χ.commutes, Algebra.algebraMap_self_apply, mul_assoc]

theorem inductionUniversal :
    Specs.LieNotes.Contragredient.VermaModules.InductionUniversal.{u, v, w} := by
  intro I A H _ _ _ R Λ hχ V _ _
  letI := characterModule R Λ hχ
  letI := characterScalarTower R Λ hχ
  exact universal (E := ℂ) (inclusion (borel R)) V

/-- The PBW map once the Borel has been identified with the triangular complement. -/
theorem pbw_of_isCompl (R : Realization A H) (Λ : Module.Dual ℂ H)
    (hχ : ∃! χ, IsWeightCharacter R Λ χ)
    (hc : IsCompl (negative R).toSubmodule (borel R).toSubmodule) :
    ∃ F : U (negative R) ≃ₗ[ℂ] Verma R Λ hχ,
      ∀ a, F a = inclusion (negative R) a • top R Λ hχ := by
  letI := characterModule R Λ hχ
  letI := characterScalarTower R Λ hχ
  let F := inducedPBWEquiv (negative R) (borel R) (E := ℂ) hc
  refine ⟨(TensorProduct.rid ℂ (U (negative R))).symm.trans F, fun a ↦ ?_⟩
  change F (a ⊗ₜ[ℂ] (1 : ℂ)) = _
  rw [inducedPBWEquiv_tensor]
  symm
  change inclusion (negative R) a • induceTensor (inclusion (borel R)) 1 (1 : ℂ) = _
  rw [smul_tensor, mul_one]

theorem pbw : Specs.LieNotes.Contragredient.VermaModules.PBW.{u, v} := by
  intro I A H _ _ _ R Λ hχ
  apply pbw_of_isCompl R Λ hχ
  rw [borel_underlying R]
  exact isCompl_negative_cartan_sup_positive R

variable (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ)

/-- The top vector generates the whole Verma module under the enveloping action. -/
theorem top_cyclic (z : Verma R Λ hχ) :
    ∃ a : U (Algebra R), a • top R Λ hχ = z := by
  obtain ⟨F, hF⟩ := pbw R Λ hχ
  obtain ⟨a, rfl⟩ := F.surjective z
  exact ⟨inclusion (negative R) a, (hF a).symm⟩

private theorem act_top (a : U (borel R)) :
    inclusion (borel R) a • top R Λ hχ = weightCharacter R Λ hχ a • top R Λ hχ := by
  letI := characterModule R Λ hχ
  let i := inclusion (borel R)
  change i a • induceTensor i 1 (1 : ℂ) = _
  rw [smul_tensor, mul_one, ← one_mul (i a), balance_tensor]
  let q := (balance i ℂ).mkQ.restrictScalars ℂ
  let χ := weightCharacter R Λ hχ
  change q ((1 : U (Algebra R)) ⊗ₜ[ℂ] (χ a * 1)) =
    χ a • q ((1 : U (Algebra R)) ⊗ₜ[ℂ] (1 : ℂ))
  rw [← map_smul]
  exact congrArg q (TensorProduct.tmul_smul (χ a) _ (1 : ℂ))

theorem top_isHighest : IsHighestVector R Λ (top R Λ hχ) := by
  have hchar := Specs.LieNotes.Contragredient.VermaModules.weightCharacter_spec R Λ hχ
  constructor
  · intro h
    have he := act_top R Λ hχ (ι ℂ (cartanInBorel R h))
    rw [inclusion_ι, hchar.1 h] at he
    simpa only [cartanInBorel] using he
  · intro x
    have he := act_top R Λ hχ (ι ℂ (positiveInBorel R x))
    rw [inclusion_ι, hchar.2 x, zero_smul] at he
    simpa only [positiveInBorel] using he

theorem highestWeightUniversal :
    Specs.LieNotes.Contragredient.VermaModules.HighestWeightUniversal.{u, v, w} := by
  intro I A H _ _ _ R Λ hχ
  refine ⟨top_isHighest R Λ hχ, ?_⟩
  intro V _ _
  let G := U (Algebra R)
  let B := U (borel R)
  let i := inclusion (borel R)
  let χ := weightCharacter R Λ hχ
  letI : Module ℂ V := scalarModule (B := G) V
  letI : IsScalarTower ℂ G V := IsScalarTower.of_algebraMap_smul (A := G) fun _ _ => rfl
  letI := restrictModule i V
  letI : IsScalarTower ℂ B V := IsScalarTower.of_algebraMap_smul (A := B) fun c z => by
    change i (algebraMap ℂ B c) • z = algebraMap ℂ G c • z
    rw [i.commutes]
  letI := characterModule R Λ hχ
  letI := characterScalarTower R Λ hχ
  intro z hz
  have hchar := Specs.LieNotes.Contragredient.VermaModules.weightCharacter_spec R Λ hχ
  have hgen (x : borel R) : (ι ℂ x : B) • z = χ (ι ℂ x) • z := by
    obtain ⟨h, y, rfl⟩ := borelAdd_decompose R x
    have hc : (ι ℂ (cartanInBorel R h) : B) • z = Λ h • z := by
      change i (ι ℂ (cartanInBorel R h)) • z = _
      rw [inclusion_ι]
      exact hz.1 h
    have hp : (ι ℂ (positiveInBorel R y) : B) • z = 0 := by
      change i (ι ℂ (positiveInBorel R y)) • z = 0
      rw [inclusion_ι]
      exact hz.2 y
    simp only [χ, map_add, add_smul, hc, hp, hchar.1 h, hchar.2 y, add_zero]
  have hact (b : B) : b • z = χ b • z := by
    induction b using Shared.Lie.enveloping_induction ℂ (borel R) with
    | scalar c => rw [algebraMap_smul, χ.commutes, Algebra.algebraMap_self_apply]
    | generator x => exact hgen x
    | mul a b ha hb =>
      rw [mul_smul, hb, smul_comm a (χ b), ha, smul_smul, map_mul, mul_comm]
    | add a b ha hb => rw [add_smul, ha, hb, map_add, add_smul]
  let f : ℂ →ₗ[B] V :=
    { toFun := fun c => c • z
      map_add' := fun a b => add_smul a b z
      map_smul' := fun b c => by
        change (χ b * c) • z = b • (c • z)
        rw [smul_comm b c, hact, smul_smul, mul_comm] }
  let φ : Verma R Λ hχ →ₗ[G] V := (homEquiv i).symm f
  have hφ : φ (top R Λ hχ) = z := by
    change extend i f (induceTensor i 1 (1 : ℂ)) = z
    rw [extend_tensor, one_smul]
    exact one_smul ℂ z
  refine ⟨φ, hφ, fun ψ hψ ↦ ?_⟩
  obtain ⟨F, hF⟩ := pbw R Λ hχ
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := F.surjective x
  rw [hF, map_smul, map_smul, hφ, hψ]


section Weights

attribute [local instance 100] LieRing.ofAssociativeRing

theorem mem_weightSpaceAt {μ : Module.Dual ℂ H} {z : Verma R Λ hχ} :
    z ∈ weightSpaceAt R Λ hχ μ ↔
      ∀ h : H, (ι ℂ (cartan R h) : U (Algebra R)) • z = μ h • z := Iff.rfl

private theorem lowerWeight_zero : lowerWeight R Λ (0 : I →₀ ℕ) = Λ := by
  simp [lowerWeight]

private theorem lowerWeight_single_add (i : I) (m : I →₀ ℕ) :
    lowerWeight R Λ (Finsupp.single i 1 + m) = lowerWeight R Λ m - R.α i := by
  let c : (I →₀ ℕ) →+ (I →₀ ℤ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  change Λ - R.rootWeight (c (Finsupp.single i 1 + m)) =
    Λ - R.rootWeight (c m) - R.α i
  have hc : c (Finsupp.single i 1) = simpleDegree i := by
    change Finsupp.mapRange (fun n : ℕ ↦ (n : ℤ)) rfl (Finsupp.single i 1) = _
    rw [Finsupp.mapRange_single]
    rfl
  rw [map_add, hc, map_add, Realization.rootWeight_simple]
  abel

private theorem lowerWeight_injective : Function.Injective (lowerWeight R Λ) := by
  intro m n h
  have he : R.rootWeight (m.mapRange (fun n : ℕ ↦ (n : ℤ)) rfl) =
      R.rootWeight (n.mapRange (fun n : ℕ ↦ (n : ℤ)) rfl) :=
    sub_right_inj.mp h
  exact (Finsupp.mapRange_injective _ rfl Int.ofNat_injective)
    (Realization.rootWeight_injective R he)

@[simp] private theorem wordVector_nil : wordVector R Λ hχ [] = top R Λ hχ := by
  simp [wordVector]

private theorem wordVector_cons (i : I) (l : List I) :
    wordVector R Λ hχ (i :: l) = (ι ℂ (f R i) : U (Algebra R)) • wordVector R Λ hχ l := by
  simp only [wordVector, List.map_cons, List.prod_cons, mul_smul]

private theorem wordVector_mem_weight (l : List I) :
    wordVector R Λ hχ l ∈ weightSpaceAt R Λ hχ (lowerWeight R Λ (wordMultiplicity l)) := by
  rw [mem_weightSpaceAt]
  intro h
  induction l with
  | nil =>
    change (ι ℂ (cartan R h) : U (Algebra R)) • wordVector R Λ hχ [] =
      lowerWeight R Λ 0 h • wordVector R Λ hχ []
    rw [wordVector_nil, lowerWeight_zero]
    exact (top_isHighest R Λ hχ).1 h
  | cons i l ih =>
    let a : U (Algebra R) := ι ℂ (cartan R h)
    let b : U (Algebra R) := ι ℂ (f R i)
    let z := wordVector R Λ hχ l
    let p := R.α i h
    let q := lowerWeight R Λ (wordMultiplicity l) h
    have he : a * b = (-p) • b + b * a := by
      rw [← sub_eq_iff_eq_add]
      have hm : a * b - b * a = (ι ℂ ⁅cartan R h, f R i⁆ : U (Algebra R)) :=
        ((ι ℂ).map_lie _ _).symm
      rw [hm]
      classical
      rw [(definingRelations R).cartan_f, map_neg, map_smul, neg_smul]
    have hq : a • z = q • z := ih
    have hwt : lowerWeight R Λ (wordMultiplicity (i :: l)) h = -p + q := by
      change lowerWeight R Λ (Finsupp.single i 1 + wordMultiplicity l) h = _
      rw [lowerWeight_single_add, LinearMap.sub_apply]
      change q - p = -p + q
      abel
    rw [wordVector_cons, hwt]
    change a • (b • z) = (-p + q) • (b • z)
    rw [← mul_smul, he, add_smul, smul_assoc, mul_smul, hq, smul_comm b q, ← add_smul]

private theorem negative_eq_lieSpan :
    negative R = LieSubalgebra.lieSpan ℂ (Algebra R) (Set.range (f R)) := by
  change (LieSubalgebra.lieSpan ℂ (Presentation.Algebra R)
    (Set.range (Presentation.f R))).map (quotientMap R) = _
  rw [LieSubalgebra.map_lieSpan, ← Set.range_comp]
  rfl

private theorem span_wordVectors : Submodule.span ℂ (Set.range (wordVector R Λ hχ)) = ⊤ := by
  let g : I → U (Algebra R) := fun i ↦ ι ℂ (f R i)
  let S := Algebra.adjoin ℂ (Set.range g)
  have hneg : negative R ≤ (lieSubalgebraOfSubalgebra ℂ _ S).comap (ι ℂ) := by
    rw [negative_eq_lieSpan]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  have hincl (a : U (negative R)) : inclusion (negative R) a ∈ S := by
    induction a using Shared.Lie.enveloping_induction ℂ (negative R) with
    | scalar c => rw [(inclusion (negative R)).commutes]; exact S.algebraMap_mem c
    | generator x =>
      rw [Shared.Lie.inclusion, inclusion_ι]
      exact hneg x.property
    | mul a b ha hb => rw [map_mul]; exact S.mul_mem ha hb
    | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
  obtain ⟨F, hF⟩ := pbw R Λ hχ
  apply top_unique
  intro z _
  obtain ⟨a, rfl⟩ := F.surjective z
  rw [hF]
  have ha := hincl a
  change inclusion (negative R) a ∈ (Algebra.adjoin ℂ (Set.range g)).toSubmodule at ha
  rw [Algebra.adjoin_eq_span] at ha
  have action_mem (b : U (Algebra R))
      (hb : b ∈ Submodule.span ℂ (Submonoid.closure (Set.range g) : Set (U (Algebra R)))) :
      b • top R Λ hχ ∈ Submodule.span ℂ (Set.range (wordVector R Λ hχ)) := by
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hb
      have hh : ∃ l' : List I, l'.map g = l := by
        clear hb
        induction l with
        | nil => exact ⟨[], rfl⟩
        | cons b l ih =>
          obtain ⟨i, hi⟩ := hl b (by simp)
          obtain ⟨l', hl'⟩ := ih (fun c hc ↦ hl c (List.mem_cons_of_mem _ hc))
          exact ⟨i :: l', by simp only [List.map_cons, hi, hl']⟩
      obtain ⟨l', rfl⟩ := hh
      exact Submodule.subset_span ⟨l', rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_assoc]; exact Submodule.smul_mem _ c ha

  exact action_mem _ ha

open scoped DirectSum

private def wordSpanAt (μ : Module.Dual ℂ H) : Submodule ℂ (Verma R Λ hχ) :=
  Submodule.span ℂ (wordVector R Λ hχ '' {l | lowerWeight R Λ (wordMultiplicity l) = μ})

private theorem weightSpace_eq_wordSpanAt (μ : Module.Dual ℂ H) :
    weightSpaceAt R Λ hχ μ = wordSpanAt R Λ hχ μ := by
  let W := weightSpaceAt R Λ hχ
  let T := wordSpanAt R Λ hχ μ
  let B := ⨆ ν, ⨆ (_ : ν ≠ μ), W ν
  have hle : T ≤ W μ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, rfl⟩
    change lowerWeight R Λ (wordMultiplicity l) = μ at hl
    exact hl ▸ wordVector_mem_weight R Λ hχ l
  have hd : Disjoint (W μ) B :=
    (weightSpace_iSupIndep (cartanAction R (Verma R Λ hχ))).disjoint_biSup
      (show μ ∉ {ν | ν ≠ μ} from fun hn ↦ hn rfl)
  have htop : T ⊔ B = ⊤ := by
    apply top_unique
    rw [← span_wordVectors R Λ hχ]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    by_cases hl : lowerWeight R Λ (wordMultiplicity l) = μ
    · exact (show T ≤ T ⊔ B from le_sup_left) (Submodule.subset_span ⟨l, hl, rfl⟩)
    · exact (show B ≤ T ⊔ B from le_sup_right)
        (Submodule.mem_iSup_of_mem (lowerWeight R Λ (wordMultiplicity l))
          (Submodule.mem_iSup_of_mem hl (wordVector_mem_weight R Λ hχ l)))
  change W μ = T
  calc
    W μ = W μ ⊓ (T ⊔ B) := by rw [htop, inf_top_eq]
    _ = T := by rw [sup_comm, ← inf_sup_assoc_of_le _ hle, hd.eq_bot, bot_sup_eq]

theorem weightDecomposition :
    Specs.LieNotes.Contragredient.VermaModules.WeightDecomposition.{u, v} := by
  classical
  intro I A H _ _ _ R Λ hχ
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (weightSpace_iSupIndep (cartanAction R (Verma R Λ hχ)))
  apply top_unique
  rw [← span_wordVectors R Λ hχ]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact Submodule.mem_iSup_of_mem _ (wordVector_mem_weight R Λ hχ l)

theorem weightSupport : Specs.LieNotes.Contragredient.VermaModules.WeightSupport.{u, v} := by
  intro I A H _ _ _ R Λ hχ μ hμ
  change weightSpaceAt R Λ hχ μ = ⊥
  rw [weightSpace_eq_wordSpanAt]
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  exact (hμ ⟨wordMultiplicity l, hl⟩).elim

theorem weightSpaceWordSpan :
    Specs.LieNotes.Contragredient.VermaModules.WeightSpaceWordSpan.{u, v} := by
  intro I A H _ _ _ R Λ hχ m
  change weightSpaceAt R Λ hχ (lowerWeight R Λ m) = _
  rw [weightSpace_eq_wordSpanAt]
  unfold wordSpanAt
  congr 2
  ext l
  exact (lowerWeight_injective R Λ).eq_iff

private def totalMultiplicity : (I →₀ ℕ) →+ ℕ :=
  Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℕ

omit [Finite I] in
private theorem totalMultiplicity_word (l : List I) :
    totalMultiplicity (wordMultiplicity l) = l.length := by
  induction l with
  | nil => exact map_zero totalMultiplicity
  | cons i l ih =>
    change totalMultiplicity (Finsupp.single i 1 + wordMultiplicity l) = l.length + 1
    rw [map_add, ih, Nat.add_comm]
    congr 1
    simp [totalMultiplicity, Finsupp.sum_single_index]

theorem finiteWeightSpaces :
    Specs.LieNotes.Contragredient.VermaModules.FiniteWeightSpaces.{u, v} := by
  intro I A H _ _ _ R Λ hχ μ
  by_cases hμ : μ ∈ Set.range (lowerWeight R Λ)
  · obtain ⟨m, rfl⟩ := hμ
    rw [weightSpaceWordSpan R Λ hχ m]
    apply FiniteDimensional.span_of_finite
    refine ((List.finite_length_eq I (totalMultiplicity m)).subset ?_).image _
    intro l hl
    change wordMultiplicity l = m at hl
    change l.length = totalMultiplicity m
    rw [← totalMultiplicity_word, hl]
  · rw [weightSupport R Λ hχ μ hμ]
    infer_instance

theorem topWeightSpace : Specs.LieNotes.Contragredient.VermaModules.TopWeightSpace.{u, v} := by
  intro I A H _ _ _ R Λ hχ
  constructor
  · obtain ⟨F, hF⟩ := pbw R Λ hχ
    intro hzero
    have he : (1 : U (negative R)) = 0 := F.injective (by
      rw [hF, map_one, one_smul, hzero, map_zero])
    have he' := congrArg (Shared.Lie.augmentation ℂ (negative R)) he
    exact one_ne_zero (by simpa only [map_one, map_zero] using he')
  · have he := weightSpaceWordSpan R Λ hχ (0 : I →₀ ℕ)
    rw [lowerWeight_zero] at he
    rw [he]
    congr 1
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩
      change wordMultiplicity l = 0 at hl
      have hlen : l.length = 0 := by rw [← totalMultiplicity_word, hl, map_zero]
      rw [List.length_eq_zero_iff.mp hlen]
      exact wordVector_nil R Λ hχ
    · intro hz
      have hz' : z = top R Λ hχ := hz
      subst z
      exact ⟨[], rfl, wordVector_nil R Λ hχ⟩

/-- The highest-weight space has complex dimension one. -/
theorem finrank_topWeightSpace : Module.finrank ℂ (weightSpaceAt R Λ hχ Λ) = 1 := by
  obtain ⟨hne, hspace⟩ := topWeightSpace R Λ hχ
  change Module.finrank ℂ (Specs.LieNotes.Contragredient.VermaModules.weightSpaceAt R Λ hχ Λ) = 1
  rw [hspace]
  exact finrank_span_singleton hne

end Weights

end

end LieNotes.Contragredient.VermaModules
