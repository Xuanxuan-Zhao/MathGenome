import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.WeightStringsConvexity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteModuleWeights
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RepresentationJordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightClassification
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DominantFundamentalDomain
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.LinearCombination

noncomputable section
universe u v

namespace LieAlgebrasAndRepresentations.WeightStringsConvexity

open Module
open Specs.LieAlgebrasAndRepresentations.WeightStringsConvexity
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F)
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules (IsStandardBasis)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open RepresentationJordan (weightSpace)
attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1000000

theorem multiplicities : multiplicities_type.{u,v} :=
  FiniteModuleWeights.multiplicities_weyl_invariant

theorem saturation : saturation_type.{u,v} :=
  FiniteModuleWeights.saturated_weights

section Strings

open FiniteModuleWeights (mem_weightSpace transverseWeightSpace transverse_weight_iff
  coroot_normalized)
open Specs.LieAlgebrasAndRepresentations.Sl2Model (H)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]

private theorem root_shifts_weight (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (T : LieSubalgebra ℂ L) (β ν : Module.Dual ℂ T)
    {y : L} (hy : y ∈ rootSpace T β) {x : V} (hx : x ∈ weightSpace ρ T ν) :
    ρ y x ∈ weightSpace ρ T (ν + β) := by
  apply (mem_weightSpace ρ T).mpr
  intro h
  have hb : ⁅ρ (h : L), ρ y⁆ = β h • ρ y := by
    rw [← ρ.map_lie, (mem_rootSpace T β y).mp hy h, map_smul]
  have hb' : ρ (h : L) (ρ y x) - ρ y (ρ (h : L) x) = β h • ρ y x :=
    congrArg (fun A : Module.End ℂ V => A x) hb
  rw [(mem_weightSpace ρ T).mp hx h, map_smul, sub_eq_iff_eq_add] at hb'
  simpa [add_smul, add_comm] using hb'

private theorem weightReflection_apply {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] {T : LieSubalgebra ℂ L}
    {α : Module.Dual ℂ T} (hc : α (coroot_value T α) = 2) (ν : Module.Dual ℂ T) :
    weightReflection T α ν = ν - ν (coroot_value T α) • α := by
  rw [weightReflection, dite_eq_left hc]
  exact Module.reflection_apply ν (show corootEvaluation T α α = 2 from hc)

theorem root_coset_strings : root_coset_strings_type.{u,v} := by
  classical
  intro L _ _ _ V _ _ _ hss ρ T hT μ α hα
  obtain ⟨e, f, he, hf, _, _, hef, hhe, hhf⟩ := exists_root_triple hss T hT α hα
  refine ⟨e, f, he, hf, hef, ?_⟩
  dsimp only
  let h := coroot_value T α
  have ha : α h = 2 := coroot_normalized T α hss hT hα
  let ν (j : ℤ) := μ + j • α
  let K := cosetSpace ρ T μ α
  have hν : Function.Injective ν := by
    intro i j hij
    have hc := congrArg (fun a : Module.Dual ℂ T => a h) hij
    change (μ + i • α) h = (μ + j • α) h at hc
    simp only [LinearMap.add_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply, ha, smul_eq_mul] at hc
    exact Int.cast_injective (α := ℂ) (by linear_combination hc / 2)
  have hi : iSupIndep (weightSpace ρ T) :=
    (RepresentationJordan.toral_weight_decomposition ℂ L V hss ρ T
      (fun a b => hT.1.1.trivial a b)
      (fun a => (absolutely_semisimple_iff _).mpr (hT.1.2 a))).submodule_iSupIndep
  refine ⟨hi.comp hν, ?_⟩
  have hK : K ≤ transverseWeightSpace ρ T α μ := by
    apply iSup_le
    intro j x hx z hz
    simpa [ν, hz] using (mem_weightSpace ρ T).mp hx z
  have hstable (y : L) (hy : ∀ j, ∃ i, ∀ x ∈ weightSpace ρ T (ν j),
      ρ y x ∈ weightSpace ρ T (ν i)) :
      ∀ x ∈ K, ρ y x ∈ K := by
    have hm : K.map (ρ y) ≤ K := by
      change (⨆ j : ℤ, weightSpace ρ T (ν j)).map (ρ y) ≤ K
      rw [Submodule.map_iSup]
      refine iSup_le fun j => ?_
      obtain ⟨i, hi'⟩ := hy j
      exact (Submodule.map_le_iff_le_comap.mpr hi').trans (le_iSup (fun j => weightSpace ρ T (ν j)) i)
    exact fun x hx => hm ⟨x, hx, rfl⟩
  have hplus (j : ℤ) : ν j + α = ν (j+1) := by
    simp [ν, add_zsmul, add_assoc]
  have hminus (j : ℤ) : ν j + -α = ν (j-1) := by
    simp only [ν, sub_eq_add_neg, add_zsmul, neg_zsmul, one_zsmul, add_assoc]
  let A := (ρ e).restrict (hstable e (fun j => ⟨j+1, fun x hx =>
    hplus j ▸ root_shifts_weight ρ T α (ν j) he hx⟩))
  let B := (ρ f).restrict (hstable f (fun j => ⟨j-1, fun x hx =>
    hminus j ▸ root_shifts_weight ρ T (-α) (ν j) hf hx⟩))
  let D := (ρ (h : L)).restrict (hstable h (fun j => ⟨j, fun x hx => by
    rw [(mem_weightSpace ρ T).mp hx h]
    exact (weightSpace ρ T (ν j)).smul_mem _ hx⟩))
  have relA : ⁅D, A⁆ = (2 : ℂ) • A := by
    ext x
    change (⁅ρ (h : L), ρ e⁆) x.val = _
    rw [← ρ.map_lie, hhe, map_smul]
    rfl
  have relB : ⁅D, B⁆ = (-2 : ℂ) • B := by
    ext x
    change (⁅ρ (h : L), ρ f⁆) x.val = _
    rw [← ρ.map_lie, hhf, map_smul]
    rfl
  have relAB : ⁅A, B⁆ = D := by
    ext x
    change (⁅ρ e, ρ f⁆) x.val = _
    rw [← ρ.map_lie, hef]
    rfl
  let σ := Sl2SimpleModules.representationOfOperators ℂ K A B D relA relB relAB
  have hσ (x : K) : (σ (E ℂ) x : V) = ρ e x ∧
      (σ (F ℂ) x : V) = ρ f x ∧ (σ (H ℂ) x : V) = ρ (h : L) x := by
    change ((Sl2SimpleModules.operatorAction ℂ K A B D (E ℂ) x : K) : V) = _ ∧
      ((Sl2SimpleModules.operatorAction ℂ K A B D (F ℂ) x : K) : V) = _ ∧
      ((Sl2SimpleModules.operatorAction ℂ K A B D (H ℂ) x : K) : V) = _
    rw [Sl2SimpleModules.operatorAction_e, Sl2SimpleModules.operatorAction_f,
      Sl2SimpleModules.operatorAction_h]
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨σ, hσ, ?_⟩
  letI := LieRingModule.compLieHom K σ
  letI := LieModule.compLieHom K σ
  obtain ⟨S, hS, hsum, hbasis⟩ := ClebschGordan.finite_standard_decomposition ℂ K
  refine ⟨S, hS, hsum, ?_⟩
  have hindex {a : Module.Dual ℂ T} {x : K} (hx : x ≠ 0)
      (hxw : (x : V) ∈ weightSpace ρ T a) : ∃ j, ν j = a := by
    by_contra! hnot
    have hd := hi a
    have hdis : Disjoint (weightSpace ρ T a) K :=
      hd.mono_right (iSup_le fun j => le_iSup_of_le (ν j)
        (le_iSup (fun _ : ν j ≠ a => weightSpace ρ T (ν j)) (hnot j)))
    exact hx (Subtype.ext (Submodule.disjoint_def.mp hdis x.val hxw x.property))
  intro W hW
  obtain ⟨n, b, hb⟩ := hbasis W hW
  let x (j : Fin (n+1)) : K := b j
  have hdiag (j : Fin (n+1)) :
      ρ (h : L) (x j : V) = ((n : ℂ) - 2 * (j.val : ℂ)) • (x j : V) := by
    have heq := congrArg (fun y : W => ((y : K) : V)) (hb j).1
    change (σ (H ℂ) (x j) : V) = _ at heq
    rw [(hσ (x j)).2.2] at heq
    exact heq
  let c : ℂ := ((n : ℂ) - μ h) / 2
  have hx0 : (x (0 : Fin (n+1)) : V) ∈ weightSpace ρ T (μ + c • α) := by
    apply (transverse_weight_iff ρ T α μ h ha c (hK (x 0).property)).mpr
    rw [hdiag]
    congr 1
    simp [c]
    ring
  have hnonzero : x (0 : Fin (n+1)) ≠ 0 := fun heq => b.ne_zero _ (Subtype.ext heq)
  obtain ⟨k, hk⟩ := hindex hnonzero hx0
  have htop : μ h + 2 * (k : ℂ) = (n : ℂ) := by
    have heval := congrArg (fun a : Module.Dual ℂ T => a h) hk
    change (μ + k • α) h = (μ + c • α) h at heval
    simp only [LinearMap.add_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply,
      smul_eq_mul, ha] at heval
    dsimp [c] at heval
    linear_combination heval
  have hj (j : Fin (n+1)) :
      ν (k - (j.val : ℤ)) h = (n : ℂ) - 2 * (j.val : ℂ) := by
    change (μ + (k - (j.val : ℤ)) • α) h = _
    simp only [LinearMap.add_apply, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply, smul_eq_mul, ha]
    push_cast
    linear_combination htop
  refine ⟨n, b, k, hb, Sl2SimpleModules.isIrreducible_of_standardBasis b hb, ?_, ?_⟩
  · intro j
    change (x j : V) ∈ weightSpace ρ T (ν (k - (j.val : ℤ)))
    have hc : ν (k - (j.val : ℤ)) h = μ h + 2 * ((k - (j.val : ℤ) : ℤ) : ℂ) := by
      simp [ν, ha, ← Int.cast_smul_eq_zsmul ℂ, mul_comm]
    have heq := hdiag j
    rw [← hj j, hc] at heq
    change (x j : V) ∈ weightSpace ρ T (μ + (k - (j.val : ℤ)) • α)
    rw [← Int.cast_smul_eq_zsmul ℂ]
    exact (transverse_weight_iff ρ T α μ h ha _ (hK (x j).property)).mpr heq
  · intro j
    rw [weightReflection_apply ha]
    change ν (k - (j.val : ℤ)) - ν (k - (j.val : ℤ)) h • α = _
    rw [hj j]
    have hc : (n : ℂ) - 2 * (j.val : ℂ) = (((n : ℤ) - 2 * (j.val : ℤ) : ℤ) : ℂ) := by
      push_cast
      rfl
    rw [hc, Int.cast_smul_eq_zsmul]
    dsimp [ν]
    have hrev : (k - (j.val : ℤ)) - ((n : ℤ) - 2 * (j.val : ℤ)) =
        k - ((j.rev).val : ℤ) := by
      have hjn : j.val ≤ n := Nat.le_of_lt_succ j.isLt
      simp only [Fin.val_rev]
      omega
    rw [add_sub_assoc, ← sub_smul, hrev]
    rfl

end Strings

section ConvexBound

open Specs.LieAlgebrasAndRepresentations.RealRootSpace (Realization realRoots)
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (coroots)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)

open private direction_vector simple_equiv vector_regular from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private cartan_lattice_comparison_of_realization from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData
open private weight_in_verma_cone from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

/-- Test orbit inequalities on the closed positive chamber by moving the
separating functional there with the same orthogonal Weyl action. -/
private theorem mem_convexHull_weyl_orbit
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {R : Set X} (hR : IsRootSystem R) (dir lam μ : X)
    (hbelow : ∀ w : rootWeylGroup R, lam - w.val μ ∈ simpleRootCone R dir) :
    μ ∈ convexHull ℝ (Set.range fun w : rootWeylGroup R => w.val lam) := by
  letI := rootWeylGroup_finite hR
  let O := Set.range fun w : rootWeylGroup R => w.val lam
  by_contra hm
  obtain ⟨f, c, hc, hμ⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ O) ((Set.finite_range _).isClosed_convexHull ℝ) hm
  let x := (InnerProductSpace.toDual ℝ X).symm f
  have hf (y : X) : f y = inner ℝ x y := by
    rw [← InnerProductSpace.toDual_apply_apply]
    exact (DFunLike.congr_fun ((InnerProductSpace.toDual ℝ X).apply_symm_apply f) y).symm
  obtain ⟨w, hw⟩ := exists_weyl_into_closedSimpleChamber hR dir x
  obtain ⟨a, ha, heq⟩ := hbelow w
  have hnonneg : 0 ≤ inner ℝ (w.val x) (lam - w.val μ) := by
    rw [← heq]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, real_inner_smul_right]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (ha r) (hw r r.property)
  have hupper : f μ ≤ f (w.val.symm lam) := by
    rw [inner_sub_right, rootWeylGroup_inner w.property] at hnonneg
    rw [hf, hf, ← rootWeylGroup_inner w.property x (w.val.symm lam), LinearEquiv.apply_symm_apply]
    exact sub_nonneg.mp hnonneg
  have hc' := hc (w.val.symm lam) (subset_convexHull ℝ O ⟨w⁻¹, rfl⟩)
  exact (not_lt_of_ge hupper) (hc'.trans hμ)

theorem highest_weight_convex_bound : highest_weight_convex_bound_type.{u} := by
  classical
  intro L _ _ _ hss T _ φ hφ lam χ hχ hlam
  letI := inducedLieRingModule T φ χ
  letI := inducedLieModule T φ χ
  let V := simpleQuotient_value T φ χ
  letI : FiniteDimensional ℂ V :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss T φ hφ lam χ hχ).mpr hlam).1
  let W := weightSpace_value V T
  let p := quotientMap T φ χ
  have hp : Function.Surjective p := LieSubmodule.Quotient.surjective_mk' _
  have hbelow (ν : Module.Dual ℂ T) (hν : W ν ≠ ⊥) :
      lam - ν ∈ positiveRootCone_value (fun i : simple T φ => i.val) := by
    obtain ⟨y, hy, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hν
    exact weight_in_verma_cone T φ χ hss hφ lam hχ p hp ν y hy hy₀
  let Q := integralRootLattice_value (fun i : simple T φ => i.val)
  have hQ : positiveRootCone_value (fun i : simple T φ => i.val) ≤ Q.restrictScalars ℕ :=
    Submodule.span_le.mpr (fun _ h => Submodule.subset_span h)
  intro μ hμ
  refine ⟨?_, ?_⟩
  · exact (neg_sub lam μ) ▸ Q.neg_mem (hQ (hbelow μ hμ))
  let ρ := LieModule.toEnd ℂ L V
  have hWt (ν : Module.Dual ℂ T) : W ν = weightSpace ρ T ν := by
    ext x
    rw [HighestWeight.mem_weightSpace V T ν x, FiniteModuleWeights.mem_weightSpace]
    rfl
  let hT := RealRootSpace.cartan_isMaximalToral hss T
  let d := RealRootSpace.realization hss T
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  letI : Fact (Realization T) := ⟨d⟩
  obtain ⟨hrealWt, hmult⟩ := FiniteModuleWeights.real_weight_multiplicities hss ρ T hT d
  obtain ⟨x, hx⟩ := hrealWt μ (hWt μ ▸ hμ)
  obtain ⟨dir, hdir⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hdir
  have hreg := vector_regular d φ hdir hφ
  have hcomp := cartan_lattice_comparison_of_realization d dir hreg s
  dsimp only at hcomp
  simp only [hs] at hcomp
  obtain ⟨b, _, _, _, hb, _, hj, _, hcone, _, _, hreal, _⟩ := hcomp
  have hlam' : lam ∈ integralWeights_value (coroots T φ) := by
    intro i
    obtain ⟨n, hn⟩ := hlam i
    exact ⟨n, by simpa using hn⟩
  obtain ⟨l, _, hl, _⟩ := hreal lam hlam'
  have hpre {ν : Module.Dual ℂ T} (hν : W ν ≠ ⊥) :
      ∃ z ∈ Submodule.span ℕ (Set.range b), d.j z = lam - ν :=
    Submodule.mem_map.mp (by rw [hcone]; exact hbelow ν hν)
  have hspan {z : _} (hz : z ∈ Submodule.span ℕ (Set.range b)) :
      z ∈ simpleRootCone (realRoots T) dir := by
    refine Submodule.span_induction ?_ (simpleRootCone_zero _ _) ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      rw [(hb i).1]
      exact positive_mem_simpleRootCone d.root_system.toRootAxioms (s i).property.1
    · exact fun _ _ _ _ ha hb => simpleRootCone_add ha hb
    · intro n y _ hy
      change n • y ∈ _
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      exact simpleRootCone_smul (Nat.cast_nonneg n) hy
  have hrealBelow (w : rootWeylGroup (realRoots T)) : l - w.val x ∈ simpleRootCone (realRoots T) dir := by
    have hwx : W (d.j (w.val x)) ≠ ⊥ := by
      simp only [hWt, ne_eq, ← Submodule.finrank_eq_zero] at hμ ⊢
      rwa [hmult w x, hx]
    obtain ⟨y, hy, hyj⟩ := hpre hwx
    have he : l - w.val x = y := hj (by rw [map_sub, hl, hyj])
    rw [he]
    exact hspan hy
  have hxconv := mem_convexHull_weyl_orbit d.root_system dir l x hrealBelow
  have hmap : μ ∈ d.j '' convexHull ℝ (Set.range fun w : rootWeylGroup (realRoots T) => w.val l) :=
    ⟨x, hxconv, hx⟩
  rw [d.j.image_convexHull] at hmap
  obtain ⟨_, e, he⟩ := FiniteModuleWeights.weyl_complexification T d
  refine convexHull_mono ?_ hmap
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  exact ⟨e w, by rw [he w l, hl]⟩

end ConvexBound
end LieAlgebrasAndRepresentations.WeightStringsConvexity
