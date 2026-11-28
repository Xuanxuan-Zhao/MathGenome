import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.WeightBounds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.Category
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BorelInduction
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Weight bounds and local finiteness of the Verma modules in finite category O. -/

noncomputable section

open CategoryTheory Module UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive)
open Shared.Lie.PBW
open scoped Classical ModuleCat.Algebra TensorProduct

namespace RepTheorySurvey.CategoryO

open Specs.RepTheorySurvey.CategoryO.WeightBounds
open BorelInduction (inclusion)

open private exists_negative_basis positiveRoot_mem_cone wordRoot wordRoot_nil wordRoot_cons
  wordRoot_mem_cone exists_word_of_mem_cone finite_wordRoot_fibre positiveRoots_finite
  exists_positive_root_lower_bound length_mul_le_wordRoot
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open private neg_root_mem
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations

universe u v w

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

private theorem direction_nonneg {α : D.Weight} (hα : α ∈ QPlus D) :
    0 ≤ D.direction α := by
  change α ∈ Submodule.span ℕ (Set.range D.alpha) at hα
  induction hα using Submodule.span_induction with
  | mem α hα =>
    obtain ⟨i, rfl⟩ := hα
    exact i.property.1.2.le
  | zero => rw [map_zero]
  | add β γ _ _ hb hc => rw [map_add]; exact add_nonneg hb hc
  | smul n β _ hb => rw [map_nsmul]; exact nsmul_nonneg hb n

private theorem finite_interval (ν lam : D.Weight) :
    {μ | weightLE D ν μ ∧ weightLE D μ lam}.Finite := by
  let P := positive D.cartan D.direction
  let : Finite P := (positiveRoots_finite D.cartan D.direction D.semisimple).to_subtype
  obtain ⟨δ, hδ, hmin⟩ := exists_positive_root_lower_bound D.cartan D.direction D.semisimple
  obtain ⟨n, hn⟩ := exists_nat_gt (D.direction (lam - ν) / δ)
  apply ((List.finite_length_le P n).image (fun l => ν + wordRoot D.cartan D.direction l)).subset
  intro μ hμ
  obtain ⟨l, hl⟩ := exists_word_of_mem_cone D.cartan D.direction (show μ - ν ∈ QPlus D from hμ.1)
  have hnonneg := direction_nonneg D (show lam - μ ∈ QPlus D from hμ.2)
  have hle := length_mul_le_wordRoot D.cartan D.direction δ hmin l
  have hadd : D.direction (lam - ν) =
      D.direction (lam - μ) + D.direction (μ - ν) := by
    rw [← map_add, sub_add_sub_cancel]
  have hlt : (l.length : ℝ) * δ < (n : ℝ) * δ := by
    rw [hl] at hle
    exact lt_of_le_of_lt (hle.trans (by linarith)) ((div_lt_iff₀ hδ).mp hn)
  exact ⟨l, Nat.le_of_lt (by exact_mod_cast lt_of_mul_lt_mul_right hlt hδ.le),
    by change ν + wordRoot D.cartan D.direction l = μ; rw [hl, add_sub_cancel]⟩

theorem finiteUpward : FiniteUpwardType.{u} := by
  intro g _ _ _ D s ν
  apply (s.finite_toSet.biUnion (fun lam _ => finite_interval D ν lam)).subset
  rintro μ ⟨hν, lam, hlam, hμ⟩
  exact Set.mem_iUnion₂.mpr ⟨lam, hlam, hν, hμ⟩

section WeightSpaces

variable (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U g) V]
  [IsScalarTower ℂ (U g) V]

private theorem weightSpace_independent :
    iSupIndep (weightSpace D.cartan V) := by
  let := restrictedLieRingModule V (g := g)
  let := restrictedLieModule V (g := g)
  have hind := (LieSubmodule.iSupIndep_toSubmodule.mpr
    (LieModule.iSupIndep_genWeightSpace ℂ D.cartan V)).comp
      (show Function.Injective (fun a : D.Weight => (a : D.cartan → ℂ)) from
        DFunLike.coe_injective)
  exact hind.mono (fun a => LieModule.weightSpace_le_genWeightSpace V a)

private theorem root_smul_weight (α μ : D.Weight) (x : g) (v : V)
    (hx : x ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan α)
    (hv : v ∈ weightSpace D.cartan V μ) :
    (ι ℂ x) • v ∈ weightSpace D.cartan V (α + μ) := by
  let := restrictedLieRingModule V (g := g)
  let := restrictedLieModule V (g := g)
  rw [add_comm α μ]
  exact LieAlgebrasAndRepresentations.HighestWeight.root_action V D.cartan α μ x v hx hv

private theorem monomial_smul_weight {N : LieSubalgebra ℂ g} {I : Type w}
    (b : Basis I ℂ N) (α : I → D.Weight)
    (hb : ∀ i, (b i : g) ∈
      Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan (α i))
    (μ : D.Weight) (v : V) (hv : v ∈ weightSpace D.cartan V μ) (l : List I) :
    inclusion N (monomial b l) • v ∈ weightSpace D.cartan V (μ + (l.map α).sum) := by
  induction l with
  | nil => simpa [monomial, Shared.Lie.word] using hv
  | cons i l ih =>
    change inclusion N (ι ℂ (b i) * monomial b l) • v ∈ _
    rw [map_mul, mul_smul, BorelInduction.inclusion_ι]
    convert root_smul_weight D V (α i) (μ + (l.map α).sum) (b i : g) _ (hb i) ih using 2
    simp only [List.map_cons, List.sum_cons]
    abel

private theorem weight_fibres {I : Type w} (f : I → V) (wt : I → D.Weight)
    (hw : ∀ i, f i ∈ weightSpace D.cartan V (wt i))
    (hf : Submodule.span ℂ (Set.range f) = ⊤) :
    ∀ μ, weightSpace D.cartan V μ = Submodule.span ℂ (f '' {i | wt i = μ}) := by
  let S (μ : D.Weight) := Submodule.span ℂ (f '' {i | wt i = μ})
  have hS : S ≤ weightSpace D.cartan V := by
    intro μ
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi : wt i = μ, rfl⟩
    exact hi ▸ hw i
  have htop : iSup S = ⊤ := by
    apply top_unique
    rw [← hf]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (wt i) (Submodule.subset_span ⟨i, rfl, rfl⟩)
  have heq : S = weightSpace D.cartan V :=
    ((weightSpace_independent D V).le_iff_eq_of_iSup_eq_top htop).mp hS
  exact fun μ => congrFun heq.symm μ

end WeightSpaces

set_option maxHeartbeats 800000 in
private theorem exists_positive_basis :
    ∃ (b : Basis (positive D.cartan (-D.direction)) ℂ D.nPlus),
      ∀ i, (b i : g) ∈
        Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan (-i.val) := by
  have heq : negative_value D.cartan (-D.direction) = D.nPlus := by
    unfold negative_value Specs.RepTheorySurvey.CategoryO.Setup.nPlus positive_value rootPart
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_Ioi, LinearMap.neg_apply, neg_neg_iff_pos]
  obtain ⟨b, hb⟩ := exists_negative_basis D.cartan (-D.direction) D.semisimple
  refine ⟨b.map (LinearEquiv.ofEq _ _ (congrArg LieSubalgebra.toSubmodule heq)), fun i => ?_⟩
  rw [Basis.map_apply]
  exact hb i

private theorem positive_basis_root_mem_cone (i : positive D.cartan (-D.direction)) :
    -i.val ∈ QPlus D := by
  have hs := LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral
    D.semisimple D.cartan
  apply positiveRoot_mem_cone D.cartan D.direction D.semisimple
    ⟨-i.val, neg_root_mem D.cartan D.semisimple hs i.property.1, ?_⟩
  have hi := i.property.2
  simpa only [LinearMap.neg_apply, map_neg] using hi

section Orbits

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [Module (U g) V]
  [IsScalarTower ℂ (U g) V]

omit [FiniteDimensional ℂ g] in
private theorem orbit_eq_span {N : LieSubalgebra ℂ g} {I : Type w} [LinearOrder I]
    (b : Basis I ℂ N) (v : V) :
    orbit N V v = Submodule.span ℂ
      (Set.range (fun l : OrderedWord I => inclusion N (orderedMonomial b l) • v)) := by
  change LinearMap.range _ = _
  rw [← Submodule.map_top]
  rw [← (orderedBasis b).span_eq, Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, orderedBasis_apply]
  rfl

end Orbits

private theorem sum_roots_mem_cone {I : Type*} (α : I → D.Weight)
    (hα : ∀ i, α i ∈ QPlus D) (l : List I) : (l.map α).sum ∈ QPlus D := by
  induction l with
  | nil => exact (QPlus D).zero_mem
  | cons i l ih => exact (QPlus D).add_mem (hα i) ih

private theorem homogeneous_span (X : ModuleCat.{v} (U g))
    (h : DirectSum.IsInternal (weightSpace D.cartan X)) :
    Submodule.span ℂ {x : X | ∃ μ, x ∈ weightSpace D.cartan X μ} = ⊤ := by
  rw [← h.submodule_iSup_eq_top, eq_comm]
  refine le_antisymm (iSup_le fun μ x hx => Submodule.subset_span ⟨μ, hx⟩) ?_
  apply Submodule.span_le.mpr
  rintro x ⟨μ, hx⟩
  exact Submodule.mem_iSup_of_mem μ hx

private theorem local_finite_of_bounds (X : ModuleCat.{v} (U g))
    (hi : DirectSum.IsInternal (weightSpace D.cartan X)) (hb : HasWeightBounds D X) :
    ∀ x : X, FiniteDimensional ℂ (orbit D.nPlus X x) := by
  let P := positive D.cartan (-D.direction)
  let : LinearOrder P := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨b, hbasis⟩ := exists_positive_basis D
  obtain ⟨hfin, s, hs⟩ := hb
  have hhom (ν : D.Weight) (x : X) (hx : x ∈ weightSpace D.cartan X ν) :
      FiniteDimensional ℂ (orbit D.nPlus X x) := by
    let T := {μ | weightLE D ν μ ∧ μ ∈ support D X}
    let : Finite T := ((finiteUpward D s ν).subset
      (show T ⊆ _ from fun μ hμ => ⟨hμ.1, hs μ hμ.2⟩)).to_subtype
    let S := ⨆ μ : T, weightSpace D.cartan X μ.val
    let (μ : T) : FiniteDimensional ℂ (weightSpace D.cartan X μ.val) := hfin μ.val
    let : FiniteDimensional ℂ S := Submodule.finite_iSup _
    suffices hle : orbit D.nPlus X x ≤ S from
      FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)
    rw [orbit_eq_span b]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    let μ := ν + (l.val.map (fun i : P => -i.val)).sum
    have hm : inclusion D.nPlus (orderedMonomial b l) • x ∈ weightSpace D.cartan X μ :=
      monomial_smul_weight D X b (fun i => -i.val) hbasis ν x hx l.val
    change inclusion D.nPlus (orderedMonomial b l) • x ∈ S
    by_cases hμ : weightSpace D.cartan X μ = ⊥
    · rw [hμ, Submodule.mem_bot] at hm
      rw [hm]
      exact S.zero_mem
    · have hν : weightLE D ν μ := by
        change μ - ν ∈ QPlus D
        simpa only [μ, add_sub_cancel_left] using
          sum_roots_mem_cone D (fun i : P => -i.val) (positive_basis_root_mem_cone D) l.val
      exact Submodule.mem_iSup_of_mem (⟨μ, hν, hμ⟩ : T) hm
  intro x
  have hx : x ∈ Submodule.span ℂ {x : X | ∃ μ, x ∈ weightSpace D.cartan X μ} := by
    rw [homogeneous_span D X hi]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ⟩ := hx
    exact hhom μ x hμ
  | zero =>
    have heq : orbit D.nPlus X 0 = ⊥ := by
      apply bot_unique
      intro y hy
      obtain ⟨a, rfl⟩ := (mem_orbit D.nPlus X 0 y).mp hy
      simp
    rw [heq]
    infer_instance
  | add x y _ _ ihx ihy =>
    let := ihx
    let := ihy
    have hle : orbit D.nPlus X (x + y) ≤ orbit D.nPlus X x ⊔ orbit D.nPlus X y := by
      intro z hz
      obtain ⟨a, rfl⟩ := (mem_orbit D.nPlus X (x + y) z).mp hz
      rw [smul_add]
      exact Submodule.add_mem_sup
        ((mem_orbit D.nPlus X x _).mpr ⟨a, rfl⟩)
        ((mem_orbit D.nPlus X y _).mpr ⟨a, rfl⟩)
    exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)
  | smul c x _ ih =>
    let := ih
    have hle : orbit D.nPlus X (c • x) ≤ orbit D.nPlus X x := by
      intro y hy
      obtain ⟨a, rfl⟩ := (mem_orbit D.nPlus X (c • x) y).mp hy
      rw [smul_comm]
      exact (orbit D.nPlus X x).smul_mem c ((mem_orbit D.nPlus X x _).mpr ⟨a, rfl⟩)
    exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)

/-- The original Verma module lies in category O, with its canonical highest line. -/
theorem verma_mem_O : VermaType.{u} := by
  intro g _ _ _ D lam
  let X := M D lam
  let w : X := highestVector_value D.cartan D.direction (character D lam)
  have hchar := (character_unique D lam).1
  have hweights := LieAlgebrasAndRepresentations.VermaWeightsUniversal.verma_weights
    D.semisimple D.cartan D.direction D.regular lam (character D lam) hchar
  have h :
      DirectSum.IsInternal (weightSpace D.cartan X) ∧
      (∀ μ, FiniteDimensional ℂ (weightSpace D.cartan X μ)) ∧
      (∀ μ, μ ∈ support D X ↔ weightLE D μ lam) ∧
      weightSpace D.cartan X lam = ℂ ∙ w := hweights
  obtain ⟨E, hE, hw⟩ := LieAlgebrasAndRepresentations.VermaModules.induced_free
    D.semisimple D.cartan D.direction D.regular (character D lam)
  have hcyc : Submodule.span (U g) ({w} : Set X) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a, rfl⟩ := E.surjective x
    rw [hE a]
    exact (Submodule.span (U g) ({w} : Set X)).smul_mem _
      (Submodule.subset_span (Set.mem_singleton w))
  have hfg : Module.Finite (U g) X :=
    Module.Finite.of_fg_top ⟨{w}, by simpa using hcyc⟩
  have hbound : HasWeightBounds D X :=
    ⟨h.2.1, {lam}, fun μ hm => ⟨lam, Finset.mem_singleton_self _, (h.2.2.1 μ).mp hm⟩⟩
  exact ⟨⟨hfg, h.1, local_finite_of_bounds D X h.1 hbound⟩, hw, hcyc, h.2⟩

private theorem finite_weight_generators (X : ModuleCat.{v} (U g))
    (hf : Module.Finite (U g) X) (hi : DirectSum.IsInternal (weightSpace D.cartan X)) :
    ∃ (n : ℕ) (x : Fin n → X) (μ : Fin n → D.Weight),
      (∀ j, x j ∈ weightSpace D.cartan X (μ j)) ∧ Submodule.span (U g) (Set.range x) = ⊤ := by
  let T := {x : X | ∃ μ, x ∈ weightSpace D.cartan X μ}
  have hspan : Submodule.span (U g) T = ⊤ := by
    have hle : Submodule.span ℂ T ≤ (Submodule.span (U g) T).restrictScalars ℂ :=
      Submodule.span_le.mpr fun _ hx => Submodule.subset_span hx
    rw [homogeneous_span D X hi] at hle
    exact top_unique fun x _ => hle (Submodule.mem_top (R := ℂ))
  have hfg : (Submodule.span (U g) T).FG := hspan ▸ hf.fg_top
  obtain ⟨s, hs, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset T).mp hfg
  obtain ⟨n, x, hx⟩ := s.finite_toSet.fin_embedding
  have hw (j : Fin n) : ∃ μ, x j ∈ weightSpace D.cartan X μ :=
    hs (hx ▸ Set.mem_range_self j)
  choose μ hμ using hw
  exact ⟨n, x, μ, hμ, by rw [hx, ← he, hspan]⟩

section GeneratingModule

open BorelInduction (Induced induceTensor extend extend_tensor)

variable (X : ModuleCat.{v} (U g))

local instance : Module (U D.borel) X := restrictedBorelAction D X
local instance : IsScalarTower ℂ (U D.borel) X := restrictedBorelTower D X

private theorem cartan_preserves_orbit (h : D.cartan) (x : X) (μ : D.Weight)
    (hx : x ∈ weightSpace D.cartan X μ) :
    ∀ y ∈ orbit D.nPlus X x, ι ℂ (h : g) • y ∈ orbit D.nPlus X x := by
  let P := positive D.cartan (-D.direction)
  let : LinearOrder P := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨b, hb⟩ := exists_positive_basis D
  let f : Module.End ℂ X := Algebra.lsmul ℂ ℂ X (ι ℂ (h : g))
  suffices hle : orbit D.nPlus X x ≤ (orbit D.nPlus X x).comap f from
    fun y hy => hle hy
  rw [orbit_eq_span b]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  let F (l : OrderedWord P) : X := inclusion D.nPlus (orderedMonomial b l) • x
  have hw : F l ∈ weightSpace D.cartan X (μ + (l.val.map (fun i : P => -i.val)).sum) :=
    monomial_smul_weight D X b (fun i => -i.val) hb μ x hx l.val
  change (ι ℂ (h : g)) • F l ∈ Submodule.span ℂ (Set.range F)
  rw [(mem_weightSpace D.cartan X _ _).mp hw h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))

private def generatingBorelSubmodule {n : ℕ} (x : Fin n → X) (μ : Fin n → D.Weight)
    (hx : ∀ j, x j ∈ weightSpace D.cartan X (μ j)) : Submodule (U D.borel) X := by
  let S : Submodule ℂ X := ⨆ j, orbit D.nPlus X (x j)
  refine { S with smul_mem' := ?_ }
  intro a
  change ∀ y ∈ S, (inclusion D.borel) a • y ∈ S
  induction a using Shared.Lie.enveloping_induction ℂ D.borel with
  | scalar c =>
    intro y hy
    rw [AlgHom.commutes, algebraMap_smul]
    exact S.smul_mem c hy
  | generator z =>
    rw [Shared.Lie.inclusion, BorelInduction.inclusion_ι]
    have hz : (z : g) ∈ D.cartan.toSubmodule ⊔ D.nPlus.toSubmodule :=
      (cartan_borel D).1 ▸ z.property
    obtain ⟨h, hh, p, hp, hzp⟩ := Submodule.mem_sup.mp hz
    have hh' : ∀ y ∈ S, ι ℂ h • y ∈ S := by
      let f : Module.End ℂ X := Algebra.lsmul ℂ ℂ X (ι ℂ h)
      suffices hle : S ≤ S.comap f from fun y hy => hle hy
      refine iSup_le fun j y hy => ?_
      exact Submodule.mem_iSup_of_mem j (cartan_preserves_orbit D X ⟨h, hh⟩ (x j) (μ j) (hx j) y hy)
    have hp' : ∀ y ∈ S, ι ℂ p • y ∈ S := by
      let pn : D.nPlus := ⟨p, hp⟩
      let f : Module.End ℂ X := Algebra.lsmul ℂ ℂ X (ι ℂ p)
      suffices hle : S ≤ S.comap f from fun y hy => hle hy
      refine iSup_le fun j y hy => ?_
      obtain ⟨b, hb⟩ := (mem_orbit D.nPlus X (x j) y).mp hy
      apply Submodule.mem_iSup_of_mem j
      apply (mem_orbit D.nPlus X (x j) _).mpr
      refine ⟨ι ℂ pn * b, ?_⟩
      rw [map_mul, mul_smul, BorelInduction.inclusion_ι, hb]
      rfl
    intro y hy
    rw [← hzp, map_add, add_smul]
    exact S.add_mem (hh' y hy) (hp' y hy)
  | mul a b ha hb =>
    intro y hy
    rw [map_mul, mul_smul]
    exact ha _ (hb _ hy)
  | add a b ha hb =>
    intro y hy
    rw [map_add, add_smul]
    exact S.add_mem (ha _ hy) (hb _ hy)

private theorem generatingBorelSubmodule_basis {n : ℕ} (x : Fin n → X) (μ : Fin n → D.Weight)
    (hx : ∀ j, x j ∈ weightSpace D.cartan X (μ j))
    (hfin : ∀ y : X, FiniteDimensional ℂ (orbit D.nPlus X y)) :
    let E := generatingBorelSubmodule D X x μ hx
    ∃ (m : ℕ) (b : Basis (Fin m) ℂ E) (η : Fin m → D.Weight),
      ∀ j, (b j : X) ∈ weightSpace D.cartan X (η j) := by
  let E := generatingBorelSubmodule D X x μ hx
  let P := positive D.cartan (-D.direction)
  let : LinearOrder P := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨b, hb⟩ := exists_positive_basis D
  let f := E.subtype.restrictScalars ℂ
  let T := {e : E | ∃ η, f e ∈ weightSpace D.cartan X η}
  have hspan : Submodule.span ℂ T = ⊤ := by
    apply Submodule.map_injective_of_injective (f := f) E.injective_subtype
    rw [Submodule.map_span, Submodule.map_top]
    have hf : LinearMap.range f = E.restrictScalars ℂ := by
      dsimp [f]
      rw [LinearMap.range_restrictScalars, Submodule.range_subtype]
    rw [hf]
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨e, _, rfl⟩; exact e.property)
    · change (⨆ j, orbit D.nPlus X (x j)) ≤ _
      refine iSup_le fun j => ?_
      rw [orbit_eq_span b]
      apply Submodule.span_le.mpr
      rintro _ ⟨l, rfl⟩
      let y := inclusion D.nPlus (orderedMonomial b l) • x j
      have hy : y ∈ E := Submodule.mem_iSup_of_mem j
        ((mem_orbit D.nPlus X (x j) y).mpr ⟨orderedMonomial b l, rfl⟩)
      refine Submodule.subset_span ⟨⟨y, hy⟩, ?_, rfl⟩
      exact ⟨_, monomial_smul_weight D X b (fun i => -i.val) hb _ _ (hx j) l.val⟩
  let (j : Fin n) : FiniteDimensional ℂ (orbit D.nPlus X (x j)) := hfin (x j)
  let : FiniteDimensional ℂ E := Submodule.finite_iSup (fun j => orbit D.nPlus X (x j))
  let B := Basis.ofSpan hspan.ge
  let := FiniteDimensional.fintypeBasisIndex B
  let B' := B.reindex (Fintype.equivFin _)
  have h (j : Fin _) : ∃ η, (B' j : X) ∈ weightSpace D.cartan X η := by
    change B' j ∈ T
    apply Basis.ofSpan_subset hspan.ge
    exact ⟨(Fintype.equivFin _).symm j, (Basis.reindex_apply B _ j).symm⟩
  choose η hη using h
  exact ⟨_, B', η, hη⟩

/-- The sum of the positive enveloping orbits of weight generators induces onto X. -/
theorem generatingBorelModule : GeneratingBorelModuleType.{u, v} := by
  intro g _ _ _ D X hX
  let := restrictedBorelAction D X
  let := restrictedBorelTower D X
  obtain ⟨n, x, μ, hx, hgen⟩ := finite_weight_generators D X hX.1 hX.2.1
  let E := generatingBorelSubmodule D X x μ hx
  let (j : Fin n) : FiniteDimensional ℂ (orbit D.nPlus X (x j)) := hX.2.2 (x j)
  let : FiniteDimensional ℂ E := Submodule.finite_iSup (fun j => orbit D.nPlus X (x j))
  let q : Induced (inclusion D.borel) E →ₗ[U g] X := extend (inclusion D.borel) E.subtype
  have hq (a : U g) (e : E) : q (induceTensor (inclusion D.borel) a e) = a • (e : X) := extend_tensor (inclusion D.borel) _ a e
  refine ⟨n, x, μ, E, hx, hgen, rfl, inferInstance,
    generatingBorelSubmodule_basis D X x μ hx hX.2.2, q, ?_, hq⟩
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hgen, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : x j ∈ E := Submodule.mem_iSup_of_mem j
    ((mem_orbit D.nPlus X (x j) (x j)).mpr ⟨1, by simp⟩)
  exact ⟨induceTensor (inclusion D.borel) 1 ⟨x j, hj⟩, by rw [hq, one_smul]⟩

end GeneratingModule

section PBWBounds

local notation "P" => (positive D.cartan D.direction)

private theorem bounds_of_pbw_span [LinearOrder P] (X : ModuleCat.{v} (U g))
    {m : ℕ} (η : Fin m → D.Weight) (f : OrderedWord P × Fin m → X)
    (hgen : Submodule.span ℂ (Set.range f) = ⊤)
    (hf : ∀ p, f p ∈ weightSpace D.cartan X (η p.2 - wordRoot D.cartan D.direction p.1.val)) :
    HasWeightBounds D X := by
  let wt (p : OrderedWord P × Fin m) := η p.2 - wordRoot D.cartan D.direction p.1.val
  have hW := weight_fibres D X f wt hf hgen
  constructor
  · intro μ
    change FiniteDimensional ℂ (weightSpace D.cartan X μ)
    rw [hW μ]
    have hfinite : {p | wt p = μ}.Finite := by
      apply ((Set.finite_univ : (Set.univ : Set (Fin m)).Finite).biUnion (fun j _ =>
        (finite_wordRoot_fibre D.cartan D.direction D.semisimple (η j - μ)).image
          (fun l => (l, j)))).subset
      rintro ⟨l, j⟩ (hl : η j - wordRoot D.cartan D.direction l.val = μ)
      refine Set.mem_iUnion₂.mpr ⟨j, Set.mem_univ _, l, ?_, rfl⟩
      change wordRoot D.cartan D.direction l.val = η j - μ
      rw [← hl, sub_sub_cancel]
    exact FiniteDimensional.span_of_finite ℂ (hfinite.image f)
  · refine ⟨Finset.univ.image η, fun μ hμ => ?_⟩
    have hfibre : {p | wt p = μ}.Nonempty := by
      by_contra hn
      rw [Set.not_nonempty_iff_eq_empty] at hn
      apply hμ
      change weightSpace D.cartan X μ = ⊥
      rw [hW μ, hn, Set.image_empty, Submodule.span_empty]
    obtain ⟨⟨l, j⟩, (hl : η j - wordRoot D.cartan D.direction l.val = μ)⟩ := hfibre
    refine ⟨η j, Finset.mem_image_of_mem η (Finset.mem_univ _), ?_⟩
    change η j - μ ∈ QPlus D
    rw [← hl, sub_sub_cancel]
    exact wordRoot_mem_cone D.cartan D.direction D.semisimple l.val

open BorelInduction (Induced induceTensor balance balance_tensor smul_tensor)

variable {X : ModuleCat.{v} (U g)}
local instance : Module (U D.borel) X := restrictedBorelAction D X
local instance : IsScalarTower ℂ (U D.borel) X := restrictedBorelTower D X

private theorem induced_unit_weight (E : Submodule (U D.borel) X) (e : E) (η : D.Weight)
    (he : (e : X) ∈ weightSpace D.cartan X η) :
    let Y := ModuleCat.of (U g) (Induced (inclusion D.borel) E)
    (induceTensor (inclusion D.borel) 1 e : Y) ∈ weightSpace D.cartan Y η := by
  let i := inclusion D.borel
  let Y := ModuleCat.of (U g) (Induced i E)
  apply (mem_weightSpace D.cartan Y η (induceTensor i 1 e)).mpr
  intro h
  let hB : D.borel := ⟨h, (le_sup_left : D.cartan ≤ D.borel) h.property⟩
  have hι : i (ι ℂ hB) = ι ℂ (h : g) := BorelInduction.inclusion_ι D.borel hB
  have he' : (ι ℂ hB) • e = η h • e := by
    apply Subtype.ext
    change i (ι ℂ hB) • (e : X) = η h • (e : X)
    rw [hι]
    exact (mem_weightSpace D.cartan X η (e : X)).mp he h
  change (ι ℂ (h : g)) • induceTensor i 1 e = η h • (induceTensor i 1 e : Y)
  rw [smul_tensor, mul_one, ← hι, ← one_mul (i (ι ℂ hB)), balance_tensor, he']
  change (balance i E).mkQ ((1 : U g) ⊗ₜ[ℂ] (η h • e)) =
    η h • (balance i E).mkQ ((1 : U g) ⊗ₜ[ℂ] e)
  rw [TensorProduct.tmul_smul]
  exact ((balance i E).mkQ.restrictScalars ℂ).map_smul (η h) _

private theorem pbw_basis_weights [LinearOrder P] {m : ℕ} {E : Submodule (U D.borel) X}
    (b : Basis (Fin m) ℂ E) (η : Fin m → D.Weight)
    (hb : ∀ j, (b j : X) ∈ weightSpace D.cartan X (η j)) :
    let Y := ModuleCat.of (U g) (Induced (inclusion D.borel) E)
    ∃ B : Basis (OrderedWord P × Fin m) ℂ Y,
      ∀ p, B p ∈ weightSpace D.cartan Y (η p.2 - wordRoot D.cartan D.direction p.1.val) := by
  let i := inclusion D.borel
  let Y := ModuleCat.of (U g) (Induced i E)
  obtain ⟨bNeg, hbNeg⟩ := exists_negative_basis D.cartan D.direction D.semisimple
  obtain ⟨F, hF⟩ := BorelInduction.inducedPBW D.nMinus D.borel (E := E)
    ((cartan_borel D).2.2)
  let B : Basis (OrderedWord P × Fin m) ℂ Y := ((orderedBasis bNeg).tensorProduct b).map F
  refine ⟨B, fun ⟨l, j⟩ => ?_⟩
  have hB : B (l, j) = induceTensor i (inclusion D.nMinus (orderedMonomial bNeg l)) (b j) := by
    simp only [B, Basis.map_apply, Basis.tensorProduct_apply, orderedBasis_apply, hF, i]
  rw [hB]
  have hword : (l.val.map (fun a : P => -a.val)).sum = -wordRoot D.cartan D.direction l.val := by
    induction l.val with
    | nil => simp only [List.map_nil, List.sum_nil, wordRoot_nil, neg_zero]
    | cons a k ih => simp only [wordRoot_cons, List.map_cons, List.sum_cons, ih, neg_add]
  have h := monomial_smul_weight D Y bNeg (fun a => -a.val) hbNeg (η j)
    (induceTensor i 1 (b j)) (induced_unit_weight D E (b j) (η j) (hb j)) l.val
  rw [hword, ← sub_eq_add_neg, smul_tensor, mul_one] at h
  exact h

/-- A finite homogeneous basis of the inducing submodule yields weight bounds for induction. -/
theorem inducedWeightBounds : InducedBoundsType.{u, v} := by
  intro g _ _ _ D X E m b η hb
  let := restrictedBorelAction D X
  let := restrictedBorelTower D X
  let : LinearOrder (positive D.cartan D.direction) := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨B, hB⟩ := pbw_basis_weights D b η hb
  exact bounds_of_pbw_span D _ η B B.span_eq hB

/-- Category O objects have finite weight multiplicities and finitely many upper bounds. -/
theorem weightBounds : BoundsType.{u, v} := by
  intro g _ _ _ D X hX
  let := restrictedBorelAction D X
  let := restrictedBorelTower D X
  obtain ⟨_, _, _, E, _, _, _, _, ⟨m, b, η, hb⟩, q, hq, _⟩ := generatingBorelModule D X hX
  let : LinearOrder (positive D.cartan D.direction) := WellOrderingRel.isWellOrder.linearOrder
  let Y := ModuleCat.of (U g) (Induced (inclusion D.borel) E)
  obtain ⟨B, hB⟩ := pbw_basis_weights D b η hb
  let qC : Y →ₗ[ℂ] X := q.restrictScalars ℂ
  have hmap : Submodule.span ℂ (Set.range (q ∘ B)) = ⊤ := by
    change Submodule.span ℂ (Set.range (qC ∘ B)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span qC, B.span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hq
  refine bounds_of_pbw_span D X η (q ∘ B) hmap (fun p => ?_)
  apply (mem_weightSpace D.cartan X _ _).mpr
  intro h
  change ι ℂ (h : g) • q (B p) = _ • q (B p)
  rw [← map_smul q, (mem_weightSpace D.cartan Y _ _).mp (hB p) h]
  exact qC.map_smul _ _

end PBWBounds

end RepTheorySurvey.CategoryO
