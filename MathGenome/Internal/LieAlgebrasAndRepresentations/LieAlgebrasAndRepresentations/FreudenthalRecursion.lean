import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FreudenthalRecursion
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightCasimir
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace LieAlgebrasAndRepresentations.FreudenthalRecursion

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.FreudenthalRecursion
open Specs.LieAlgebrasAndRepresentations.HighestWeightCasimir
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Module UniversalEnvelopingAlgebra
open scoped Classical BigOperators

open private opposite_bracket from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightCasimir
open private exists_raisingVectors weight_in_verma_cone from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
variable {H : LieSubalgebra ℂ L} {φ : Direction H}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

section Trace

local notation "W" => weightSpace_value V H
local notation "m" => multiplicity V H

private def raisingMap {α μ : Module.Dual ℂ H} {x : L}
    (hx : x ∈ RootDecomposition.rootSpace_value H α) : W μ →ₗ[ℂ] W (μ + α) :=
  ((LieModule.toEnd ℂ L V x).comp (W μ).subtype).codRestrict _ fun v =>
    HighestWeight.root_action V H α μ x v hx v.property

private def loweringMap {α μ : Module.Dual ℂ H} {y : L}
    (hy : y ∈ RootDecomposition.rootSpace_value H (-α)) : W (μ + α) →ₗ[ℂ] W μ :=
  ((LieModule.toEnd ℂ L V y).comp (W (μ + α)).subtype).codRestrict _ fun v => by
    have h := HighestWeight.root_action V H (-α) (μ + α) y v hy v.property
    rwa [add_neg_cancel_right] at h

private def rootTrace [FiniteDimensional ℂ V] {α : Module.Dual ℂ H} {x y : L}
    (hx : x ∈ RootDecomposition.rootSpace_value H α)
    (hy : y ∈ RootDecomposition.rootSpace_value H (-α)) (μ : Module.Dual ℂ H) : ℂ :=
  LinearMap.trace ℂ (W μ) ((loweringMap (V := V) hy).comp (raisingMap hx))

private theorem rootTrace_step [FiniteDimensional ℂ V] {α μ : Module.Dual ℂ H} {x y : L}
    (hx : x ∈ RootDecomposition.rootSpace_value H α)
    (hy : y ∈ RootDecomposition.rootSpace_value H (-α))
    (t : H) (ht : ⁅x, y⁆ = (t : L)) :
    rootTrace (V := V) hx hy μ =
      rootTrace (V := V) hx hy (μ + α) + (μ + α) t * (m (μ + α) : ℂ) := by
  let e := raisingMap (V := V) (μ := μ) hx
  let f := loweringMap (V := V) (μ := μ) hy
  let e' := raisingMap (V := V) (μ := μ + α) hx
  let f' := loweringMap (V := V) (μ := μ + α) hy
  have hmaps : e.comp f = f'.comp e' + (μ + α) t • LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ⁅x, ⁅y, (v : V)⁆⁆ = ⁅y, ⁅x, (v : V)⁆⁆ + (μ + α) t • (v : V)
    rw [leibniz_lie, ht, (HighestWeight.mem_weightSpace V H _ v).mp v.property t, add_comm]
  change LinearMap.trace ℂ (W μ) (f.comp e) = _
  rw [LinearMap.trace_comp_comm', hmaps, map_add, map_smul, LinearMap.trace_id]
  rfl

private theorem finite_root_ray [FiniteDimensional ℂ V] {α : Module.Dual ℂ H}
    (hα : α ≠ 0) (μ : Module.Dual ℂ H) :
    Set.Finite {n : ℕ | m (μ + n • α) ≠ 0} := by
  obtain ⟨a, ha⟩ : ∃ a, α a ≠ 0 := by
    by_contra! h
    exact hα (LinearMap.ext h)
  let A := LieModule.toEnd ℂ L V (a : L)
  let g (n : ℕ) := (μ + n • α) a
  have hg : Function.Injective g := by
    intro j k hjk
    apply Nat.cast_injective (R := ℂ)
    apply mul_right_cancel₀ ha
    apply add_left_cancel (a := μ a)
    simpa [g, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul] using hjk
  refine (A.finite_hasEigenvalue.preimage hg.injOn).subset ?_
  intro n hn
  have hW : W (μ + n • α) ≠ ⊥ := by
    simpa [Submodule.finrank_eq_zero] using hn
  obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    (Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr ((HighestWeight.mem_weightSpace V H _ v).mp hv a), hv₀⟩)

private theorem rootTrace_eq_sum [FiniteDimensional ℂ V] {α : Module.Dual ℂ H} {x y : L}
    (hα : α ≠ 0) (hx : x ∈ RootDecomposition.rootSpace_value H α)
    (hy : y ∈ RootDecomposition.rootSpace_value H (-α))
    (t : H) (ht : ⁅x, y⁆ = (t : L)) (μ : Module.Dual ℂ H) :
    rootTrace (V := V) hx hy μ = ∑ᶠ n : ℕ, (μ + (n + 1) • α) t *
      (m (μ + (n + 1) • α) : ℂ) := by
  let ν (n : ℕ) := μ + n • α
  let T (n : ℕ) := rootTrace (V := V) hx hy (ν n)
  have hs := finite_root_ray (V := V) hα μ
  obtain ⟨N, hN⟩ := hs.bddAbove
  have hz (n : ℕ) (hn : N < n) : m (ν n) = 0 := by
    by_contra hm
    exact (not_le_of_gt hn) (hN hm)
  have hT : T (N + 1) = 0 := by
    have hbot := Submodule.finrank_eq_zero.mp (hz (N + 1) (Nat.lt_succ_self N))
    haveI : Subsingleton (W (ν (N + 1))) :=
      ⟨fun a b => Subtype.ext ((show (a : V) = 0 by simpa [hbot] using a.property).trans
        (show (b : V) = 0 by simpa [hbot] using b.property).symm)⟩
    have hzero : (loweringMap (V := V) (μ := ν (N + 1)) hy).comp (raisingMap hx) = 0 :=
      Subsingleton.elim _ _
    simp [T, rootTrace, hzero]
  have step (n : ℕ) : T n - T (n + 1) = ν (n + 1) t * (m (ν (n + 1)) : ℂ) := by
    have h := rootTrace_step (V := V) (μ := ν n) hx hy t ht
    have hn : ν n + α = ν (n + 1) := by simp [ν, add_nsmul, add_assoc]
    rw [hn] at h
    exact sub_eq_of_eq_add (h.trans (add_comm _ _))
  have hstart : T 0 = rootTrace (V := V) hx hy μ := by simp [T, ν]
  rw [← hstart]
  change T 0 = ∑ᶠ n : ℕ, ν (n + 1) t * (m (ν (n + 1)) : ℂ)
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))]
  · simp_rw [← step]
    rw [Finset.sum_range_sub', hT, sub_zero]
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra! h
    apply hn
    change (ν (n + 1)) t * (m (ν (n + 1)) : ℂ) = 0
    rw [hz _ (by omega), Nat.cast_zero, mul_zero]

end Trace

section CasimirTrace

open HighestWeightCasimir (normal_order eigenvalue_action representative_pairing normalized_exists
  eigenvalue_difference)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open ModuleCasimir (action)

variable [FiniteDimensional ℂ L] [FiniteDimensional ℂ V] [H.IsCartanSubalgebra]

private theorem quadratic_pairing (B : Form (L := L))
    (hpair : ∀ α : Module.Dual ℂ H, ∀ h : H, B (weightRepresentative_value H B α : L) h = α h)
    (α β : Module.Dual ℂ H) :
    weightForm_value H B α β = α (weightRepresentative_value H B β) :=
  hpair α _

set_option maxHeartbeats 1000000 in
private theorem casimir_trace (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (B : Form (L := L)) (hB : B.Nondegenerate) (hInv : B.lieInvariant L)
    (lam μ : Module.Dual ℂ H) (w : V)
    (hw : ∀ h : H, ⁅(h : L), w⁆ = lam h • w)
    (hpos : ∀ x ∈ positive_value H φ, ⁅x, w⁆ = 0)
    (hcyc : LieSubmodule.lieSpan ℂ L ({w} : Set V) = ⊤)
    [Fintype (PositiveRoot H φ)] :
    (eigenvalue_value H φ B lam - eigenvalue_value H φ B μ) * (multiplicity V H μ : ℂ) =
      2 * ∑ α : PositiveRoot H φ, ∑ᶠ n : ℕ,
        weightForm_value H B (μ + (n + 1) • α.val) α.val *
          (multiplicity V H (μ + (n + 1) • α.val) : ℂ) := by
  classical
  let W := weightSpace_value V H μ
  let b := Module.finBasis ℂ L
  let h := Module.finBasis ℂ H
  letI : DecidableEq (Fin (finrank ℂ H)) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨hC, hpair⟩ := representative_pairing H hss B hInv hB
  let d := (B.restrict H.toSubmodule).dualBasis hC h
  obtain ⟨x, y, hn⟩ := normalized_exists H hss φ B hInv hB
  let T (α : PositiveRoot H φ) : Module.End ℂ W :=
    (loweringMap (V := V) (μ := μ) (hn α).2.1).comp (raisingMap (hn α).1)
  have hrep : weightRepresentative_value H B μ = ∑ a, μ (h a) • d a := by
    conv_lhs => rw [← d.sum_repr (weightRepresentative_value H B μ)]
    apply Finset.sum_congr rfl
    intro a _
    rw [show d.repr (weightRepresentative_value H B μ) a = μ (h a) by
      dsimp only [d]
      rw [LinearMap.BilinForm.dualBasis_repr_apply]
      exact hpair μ (h a)]
  have hcartan : ∑ a, μ (h a) * μ (d a) = weightForm_value H B μ μ := by
    rw [quadratic_pairing B hpair, hrep, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hact (z : L) (v : V) : action ℂ L V (ι ℂ z) v = ⁅z, v⁆ := by
    change (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ L V)) (ι ℂ z) v = _
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  have hop :
      (eigenvalue_value H φ B lam - eigenvalue_value H φ B μ) •
        (LinearMap.id : Module.End ℂ W) = (2 : ℂ) • ∑ α, T α := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hv := (HighestWeight.mem_weightSpace V H μ v).mp v.property
    have hh (a : Fin (finrank ℂ H)) :
        action ℂ L V (ι ℂ (h a : L) * ι ℂ (((B.restrict H.toSubmodule).dualBasis hC h a : H) : L)) v =
          (μ (h a) * μ (d a)) • (v : V) := by
      change action ℂ L V (ι ℂ (h a : L) * ι ℂ (d a : L)) v = _
      rw [map_mul, Module.End.mul_apply, hact (d a : L) (v : V), hv, map_smul, hact, hv,
        smul_smul, mul_comm]
    have hyx (α : PositiveRoot H φ) :
        action ℂ L V (ι ℂ (y α) * ι ℂ (x α)) v = (T α v : V) := by
      rw [map_mul, Module.End.mul_apply, hact, hact]
      rfl
    have hvΩ := eigenvalue_action H hss φ hφ B hB hInv b V lam w hw hpos hcyc (v : V)
    rw [normal_order H hss φ hφ B hB hInv hC b h x y hn, finsum_eq_sum_of_fintype] at hvΩ
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      map_sum, LinearMap.sum_apply, hyx, hact, hv] at hvΩ
    have hCartanSum :
        (∑ a, action ℂ L V
          (ι ℂ (h a : L) * ι ℂ (((B.restrict H.toSubmodule).dualBasis hC h a : H) : L)) v) =
        weightForm_value H B μ μ • (v : V) := by
      calc
        _ = ∑ a, (μ (h a) * μ (d a)) • (v : V) :=
          Finset.sum_congr rfl (fun a _ => hh a)
        _ = _ := by rw [← Finset.sum_smul, hcartan]
    rw [hCartanSum] at hvΩ
    have hc : weightForm_value H B μ μ • (v : V) +
        (2 : ℂ) • (μ (weightRepresentative_value H B (rho_value H φ)) • (v : V)) =
        eigenvalue_value H φ B μ • (v : V) := by
      simp only [eigenvalue_value, quadratic_pairing B hpair, map_add, map_smul,
        smul_eq_mul, smul_smul, add_smul]
    rw [hc] at hvΩ
    have hs : ((∑ α, T α) v : V) = ∑ α, (T α v : V) := by
      rw [LinearMap.sum_apply]
      exact map_sum W.subtype (fun α => T α v) _
    change (eigenvalue_value H φ B lam - eigenvalue_value H φ B μ) • (v : V) =
      (2 : ℂ) • ((∑ α, T α) v : V)
    rw [hs, sub_smul, ← hvΩ, add_comm, add_sub_cancel_right]
  have htrace := congrArg (LinearMap.trace ℂ W) hop
  simp only [map_smul, LinearMap.trace_id, map_sum, smul_eq_mul] at htrace
  change _ = 2 * ∑ α, rootTrace (V := V) (hn α).1 (hn α).2.1 μ at htrace
  rw [htrace]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  have hb := opposite_bracket H B hss (RealRootSpace.cartan_isMaximalToral hss H)
    hInv hC (hn α).1 (hn α).2.1 (hn α).2.2
  rw [rootTrace_eq_sum α.property.1.1 _ _ _ hb]
  simp only [quadratic_pairing B hpair]

end CasimirTrace

open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (IsDominant coroots)
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)

private theorem finite_positive_roots [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
    (hss : IsSemisimple_value ℂ L) : Finite (PositiveRoot H φ) :=
  ((rootSet_finite H (RealRootSpace.cartan_isMaximalToral hss H).1).subset
    (fun _ h => h.1)).to_subtype

theorem recursion : recursion_type := by
  intro L _ _ _ hss H _ φ hφ B hB hInv _ lam χ hχ hdom
  classical
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let V := simpleQuotient_value H φ χ
  letI : FiniteDimensional ℂ V :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ lam χ hχ).mpr hdom).1
  letI : Finite (PositiveRoot H φ) := finite_positive_roots hss
  letI := Fintype.ofFinite (PositiveRoot H φ)
  obtain ⟨e, he⟩ := exists_raisingVectors (H := H) (φ := φ)
  let w := quotientHighestVector H φ χ
  have hw := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2
  obtain ⟨_, hw, hpos, hcyc⟩ :=
    (SimpleHighestWeightQuotient.highest_weight_iff_positive hss H φ e he V lam w).mp hw
  refine ⟨inferInstance, fun μ => ⟨fun α => ?_, ?_⟩⟩
  · exact (finite_root_ray (V := V) α.property.1.1 μ).preimage Nat.succ_injective.injOn
  · have h := casimir_trace hss hφ B hB hInv lam μ w hw (fun x hx => hpos ⟨x, hx⟩) hcyc
    have heq := congrArg Complex.re h
    have heigen (ν : Module.Dual ℂ H) :
        (eigenvalue_value H φ B ν).re =
          squaredNorm H B (ν + rho_value H φ) - squaredNorm H B (rho_value H φ) := by
      rw [HighestWeightCasimir.eigenvalue_difference H hss φ B hInv, Complex.sub_re]
    have hRe (α : PositiveRoot H φ) :
        (∑ᶠ n : ℕ, weightForm_value H B (μ + (n + 1) • α.val) α.val *
          (multiplicity V H (μ + (n + 1) • α.val) : ℂ)).re =
        ∑ᶠ n : ℕ, (weightForm_value H B (μ + (n + 1) • α.val) α.val).re *
          (multiplicity V H (μ + (n + 1) • α.val) : ℝ) := by
      let F (n : ℕ) := weightForm_value H B (μ + (n + 1) • α.val) α.val *
          (multiplicity V H (μ + (n + 1) • α.val) : ℂ)
      have hf := (finite_root_ray (V := V) α.property.1.1 μ).preimage Nat.succ_injective.injOn
      have hF : (Function.support F).Finite := hf.subset (fun n hn hz => hn (by simp [F, hz]))
      change Complex.reAddGroupHom (∑ᶠ n, F n) = _
      rw [Complex.reAddGroupHom.map_finsum hF]
      simp [F, Complex.mul_re]
    unfold recursionSum
    rw [finsum_eq_sum_of_fintype]
    have h2r : (2 : ℂ).re = 2 := by norm_num
    have h2i : (2 : ℂ).im = 0 := by norm_num
    change ((eigenvalue_value H φ B lam - eigenvalue_value H φ B μ) *
      (multiplicity V H μ : ℂ)).re =
      ((2 : ℂ) * ∑ α : PositiveRoot H φ, ∑ᶠ n : ℕ,
        weightForm_value H B (μ + (n + 1) • α.val) α.val *
          (multiplicity V H (μ + (n + 1) • α.val) : ℂ)).re at heq
    simp only [Complex.mul_re, Complex.sub_re, Complex.natCast_re, Complex.natCast_im,
      mul_zero, sub_zero, heigen, h2r, h2i, zero_mul, Complex.re_sum, hRe] at heq
    unfold denominator
    rw [sub_sub_sub_cancel_right] at heq
    exact heq


section Geometry

open Specs.LieAlgebrasAndRepresentations.RealRootSpace (Realization E realRoots rootRestriction)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights (weightWeylGroup weightReflection)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)

open private invariant_assoc from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightCasimir
open private weightReflection_apply from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
open private direction_vector simple_equiv vector_regular extension_injective from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private cartan_lattice_comparison_of_realization from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData

variable [FiniteDimensional ℂ L]

private theorem weyl_polytope_real (d : Realization H) (l : E H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    polytope H (d.j l) ⊆
      d.j '' convexHull ℝ (Set.range fun w : rootWeylGroup (realRoots H) => w.val l) := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨_, e, he⟩ := FiniteModuleWeights.weyl_complexification H d
  rw [d.j.image_convexHull]
  apply convexHull_mono
  rintro _ ⟨w, rfl⟩
  refine ⟨(e.symm w).val l, ⟨e.symm w, rfl⟩, ?_⟩
  rw [he, e.apply_symm_apply]

private theorem coroot_proportional [H.IsCartanSubalgebra] (hss : IsSemisimple_value ℂ L)
    (B : Form (L := L)) (hInv : B.lieInvariant L) (hB : B.Nondegenerate)
    {α : Module.Dual ℂ H} (ha : α ∈ rootSet_value H) :
    ∃ c : ℂ, coroot_value H α = c • weightRepresentative_value H B α ∧
      c * weightForm_value H B α α = 2 := by
  have hT := RealRootSpace.cartan_isMaximalToral hss H
  obtain ⟨x, y, _, hy, _, _, hxy, _, _⟩ := exists_root_triple hss H hT α ha
  obtain ⟨hC, hpair⟩ := HighestWeightCasimir.representative_pairing H hss B hInv hB
  let c := B x y
  have hc : coroot_value H α = c • weightRepresentative_value H B α := by
    apply ((B.restrict H.toSubmodule).toDual hC).injective
    ext a
    change B (coroot_value H α : L) (a : L) =
      B ((c • weightRepresentative_value H B α : H) : L) (a : L)
    rw [← hxy, invariant_assoc B hInv, ← lie_skew y (a : L), (mem_rootSpace H (-α) y).mp hy a]
    simp [c, hpair α a, mul_comm]
  refine ⟨c, hc, ?_⟩
  have h := FiniteModuleWeights.coroot_normalized H α hss hT ha
  change α (coroot_value H α) = 2 at h
  rw [hc, map_smul, smul_eq_mul, ← quadratic_pairing B hpair] at h
  exact h

private theorem weyl_preserves_square [H.IsCartanSubalgebra]
    (hss : IsSemisimple_value ℂ L) (B : Form (L := L))
    (hInv : B.lieInvariant L) (hB : B.Nondegenerate)
    (g : weightWeylGroup H) (μ : Module.Dual ℂ H) :
    squaredNorm H B (g.val μ) = squaredNorm H B μ := by
  have hT := RealRootSpace.cartan_isMaximalToral hss H
  obtain ⟨_, hpair⟩ := HighestWeightCasimir.representative_pairing H hss B hInv hB
  let F := weightForm_value H B
  have hsym (a b : Module.Dual ℂ H) : F a b = F b a :=
    (HighestWeightCasimir.symmetry hss B hInv).eq _ _
  rcases g with ⟨g, hg⟩
  revert μ
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ μ, squaredNorm H B (g μ) = squaredNorm H B μ) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨α, ha, rfl⟩ μ
    obtain ⟨c, hc, htwo⟩ := coroot_proportional hss B hInv hB ha
    rw [weightReflection_apply (FiniteModuleWeights.coroot_normalized H α hss hT ha), hc,
      map_smul, smul_eq_mul, ← quadratic_pairing B hpair]
    change (F (μ - (c * F μ α) • α) (μ - (c * F μ α) • α)).re = (F μ μ).re
    congr 1
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hsym α μ]
    linear_combination (c * (F μ α)^2) * htwo
  · intro μ
    rfl
  · intro a b _ _ ha hb μ
    change squaredNorm H B (a (b μ)) = _
    rw [ha, hb]
  · intro a _ ha μ
    change squaredNorm H B (a.symm μ) = _
    rw [← ha (a.symm μ), LinearEquiv.apply_symm_apply]

private theorem convex_square_bound [H.IsCartanSubalgebra] (hss : IsSemisimple_value ℂ L)
    (B : Form (L := L)) (hInv : B.lieInvariant L) (hB : B.Nondegenerate)
    (hP : PositiveOnRealRoots H B) {lam μ : Module.Dual ℂ H}
    (hreal : ∀ w : weightWeylGroup H, w.val lam ∈ Submodule.span ℝ (rootSet_value H))
    (hμ : μ ∈ polytope H lam) :
    squaredNorm H B μ ≤ squaredNorm H B lam := by
  let S := Submodule.span ℝ (rootSet_value H)
  let q := squaredNorm H B
  let F := weightForm_value H B
  have hsym (x y : Module.Dual ℂ H) : F x y = F y x :=
    (HighestWeightCasimir.symmetry hss B hInv).eq _ _
  have hq (x : Module.Dual ℂ H) (hx : x ∈ S) : 0 ≤ q x := by
    by_cases h : x = 0
    · simp [h, q, squaredNorm]
    · exact (hP x hx h).1.le
  have hc : Convex ℝ {x ∈ S | q x ≤ q lam} := by
    intro x hx y hy a b ha hb hab
    refine ⟨S.add_mem (S.smul_mem _ hx.1) (S.smul_mem _ hy.1), ?_⟩
    have hnonneg := hq (x - y) (S.sub_mem hx.1 hy.1)
    have hmul := mul_nonneg (mul_nonneg ha hb) hnonneg
    have hid : q (a • x + b • y) + a * b * q (x - y) = a * q x + b * q y := by
      simp only [q, squaredNorm, ← Complex.coe_smul, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hsym y x]
      have habx : (a + b - 1) * (a * (F x x).re + b * (F y y).re) = 0 := by rw [hab]; ring
      linear_combination habx
    calc
      q (a • x + b • y) ≤ a * q x + b * q y := by linarith
      _ ≤ a * q lam + b * q lam :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = q lam := by rw [← add_mul, hab, one_mul]
  have horbit : Set.range (fun w : weightWeylGroup H => w.val lam) ⊆ {x ∈ S | q x ≤ q lam} := by
    rintro _ ⟨w, rfl⟩
    exact ⟨hreal w, (weyl_preserves_square hss B hInv hB w lam).le⟩
  exact (convexHull_min horbit hc hμ).2


private theorem rho_extension (d : Realization H) (v : E H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    (∀ x, φ (d.j x) = inner ℝ v x) →
      d.j (rootRho (realRoots H) v) = rho_value H φ := by
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  intro hv
  have hpos (x : E H) : x ∈ positiveRoots (realRoots H) v ↔
      d.j x ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ := by
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hp⟩
      exact ⟨by simpa only [d.extension_root a ha] using ha, by rwa [hv]⟩
    · intro ha
      exact ⟨⟨d.j x, ha.1, extension_injective d (d.extension_root _ ha.1)⟩, by
        rw [← hv]; exact ha.2⟩
  let j (a : positiveRoots (realRoots H) v) : PositiveRoot H φ :=
    ⟨d.j a, (hpos a).mp a.property⟩
  have hj : Function.Bijective j := by
    refine ⟨fun a b h => Subtype.ext (extension_injective d (congrArg Subtype.val h)), ?_⟩
    intro a
    have he := d.extension_root a.val a.property.1
    exact ⟨⟨rootRestriction H a.val, (hpos _).mpr (he.symm ▸ a.property)⟩, Subtype.ext he⟩
  let e := Equiv.ofBijective j hj
  letI : Fintype (positiveRoots (realRoots H) v) :=
    (positiveRoots_finite d.root_system.toRootAxioms v).fintype
  letI : Fintype (PositiveRoot H φ) := Fintype.ofEquiv _ e
  rw [rootRho, rho_value, map_smul, ← finsum_set_coe_eq_finsum_mem,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  rw [← Equiv.sum_comp e (fun a : PositiveRoot H φ => a.val), ← Complex.coe_smul]
  norm_num
  rfl

private theorem positive_rho_pairing [H.IsCartanSubalgebra] (hss : IsSemisimple_value ℂ L)
    (hφ : Regular H φ) (B : Form (L := L)) (hB : B.Nondegenerate)
    (hInv : B.lieInvariant L) (hP : PositiveOnRealRoots H B) (i : simple H φ) :
    0 < (weightForm_value H B (rho_value H φ) i.val).re := by
  let d := RealRootSpace.realization hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  letI : Fact (Realization H) := ⟨d⟩
  obtain ⟨v, hv⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hv
  have hreg := vector_regular d φ hv hφ
  have hi := i.property.1.1
  have hsi : rootRestriction H i.val = (s i : E H) :=
    extension_injective d ((d.extension_root _ hi).trans (hs i).symm)
  have hρ : rho_value H φ (coroot_value H i.val) = 1 := by
    rw [← rho_extension d v hv, d.coroot_evaluation _ _ hi, hsi,
      rho_simple_coroot_pairing _ d.root_system v hreg _ (s i).property, Complex.ofReal_one]
  obtain ⟨_, hpair⟩ := HighestWeightCasimir.representative_pairing H hss B hInv hB
  obtain ⟨c, hc, htwo⟩ := coroot_proportional hss B hInv hB hi
  rw [hc, map_smul, smul_eq_mul, ← quadratic_pairing B hpair] at hρ
  have he : weightForm_value H B (rho_value H φ) i.val =
      weightForm_value H B i.val i.val / 2 := by
    have hc0 : c ≠ 0 := by rintro rfl; norm_num at htwo
    apply mul_left_cancel₀ hc0
    rw [hρ, ← mul_div_assoc, htwo]
    norm_num
  obtain ⟨hp, _⟩ := hP _ (Submodule.subset_span hi) hi.1
  rw [he, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re]
  positivity

private theorem strict_denominator [H.IsCartanSubalgebra] (hss : IsSemisimple_value ℂ L)
    (hφ : Regular H φ) (B : Form (L := L)) (hB : B.Nondegenerate)
    (hInv : B.lieInvariant L) (hP : PositiveOnRealRoots H B)
    {lam μ : Module.Dual ℂ H} (hpoly : μ ∈ polytope H lam)
    (hcone : inCone H φ lam μ) (hne : μ ≠ lam)
    (hreal : ∀ w : weightWeylGroup H, w.val lam ∈ Submodule.span ℝ (rootSet_value H)) :
    0 < denominator H φ B lam μ := by
  let F := weightForm_value H B
  have hsym (x y : Module.Dual ℂ H) : F x y = F y x :=
    (HighestWeightCasimir.symmetry hss B hInv).eq _ _
  let g := Complex.reLm.comp ((F (rho_value H φ)).restrictScalars ℝ)
  have hg (x : Module.Dual ℂ H) : g x = (F (rho_value H φ) x).re := rfl
  have hcone_pos : 0 ≤ g (lam - μ) ∧ (g (lam - μ) = 0 → lam - μ = 0) := by
    refine Submodule.span_induction (p := fun x _ => 0 ≤ g x ∧ (g x = 0 → x = 0))
      ?_ ?_ ?_ ?_ hcone
    · rintro _ ⟨i, rfl⟩
      have hi : 0 < g i.val := positive_rho_pairing hss hφ B hB hInv hP i
      exact ⟨hi.le, fun h => (hi.ne' h).elim⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      refine ⟨add_nonneg hx.1 hy.1, fun h => ?_⟩
      rw [hx.2 (by linarith [hy.1]), hy.2 (by linarith [hx.1]), add_zero]
    · intro n x _ hx
      rw [map_nsmul]
      cases n with
      | zero => simp
      | succ n =>
        rw [nsmul_eq_mul]
        refine ⟨mul_nonneg (by positivity) hx.1, fun h => ?_⟩
        rw [hx.2 ((mul_eq_zero.mp h).resolve_left (by positivity)), smul_zero]
  have hpos : 0 < g (lam - μ) :=
    lt_of_le_of_ne hcone_pos.1 (fun h => hne ((sub_eq_zero.mp (hcone_pos.2 h.symm)).symm))
  have hbound := convex_square_bound hss B hInv hB hP hreal hpoly
  have heq : denominator H φ B lam μ =
      squaredNorm H B lam - squaredNorm H B μ + 2 * g (lam - μ) := by
    simp only [denominator, squaredNorm, hg, map_add, map_sub, LinearMap.add_apply,
      Complex.add_re, Complex.sub_re]
    change _ = _ + 2 * ((F (rho_value H φ) lam) - (F (rho_value H φ) μ)).re
    simp only [Complex.sub_re]
    rw [hsym lam (rho_value H φ), hsym μ (rho_value H φ)]
    ring
  rw [heq]
  linarith

private theorem finite_candidates [H.IsCartanSubalgebra] (hss : IsSemisimple_value ℂ L)
    (hφ : Regular H φ) {lam : Module.Dual ℂ H} (hdom : IsDominant H φ lam) :
    (candidates H φ lam).Finite ∧
      ∀ w : weightWeylGroup H, w.val lam ∈ Submodule.span ℝ (rootSet_value H) := by
  classical
  let d := RealRootSpace.realization hss H
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  letI : Fact (Realization H) := ⟨d⟩
  obtain ⟨v, hv⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hv
  have hcomp := cartan_lattice_comparison_of_realization d v (vector_regular d φ hv hφ) s
  dsimp only at hcomp
  simp only [hs] at hcomp
  obtain ⟨b, _, _, _, _, _, hj, hQ, _, _, _, hreal, _⟩ := hcomp
  have hInt := (HighestWeight.dominant_iff (coroots H φ) lam).mp hdom |>.1
  obtain ⟨l, _, hl, _⟩ := hreal lam hInt
  letI := rootWeylGroup_finite d.root_system
  letI : Finite (simple H φ) := ((rootSet_finite H
    (RealRootSpace.cartan_isMaximalToral hss H).1).subset (fun _ h => h.1.1)).to_subtype
  let P := convexHull ℝ (Set.range fun w : rootWeylGroup (realRoots H) => w.val l)
  let T := (fun x : E H => x - l) '' P
  have hP : IsCompact P := (Set.finite_range _).isCompact_convexHull ℝ
  have hT : Bornology.IsBounded T := (hP.image (continuous_id.sub continuous_const)).isBounded
  have hfin := ZSpan.setFinite_inter b hT
  have hpoly : polytope H lam ⊆ d.j '' P := hl ▸ weyl_polytope_real d l
  constructor
  · refine (hfin.image (fun z : E H => d.j (z + l))).subset ?_
    intro μ hμ
    obtain ⟨x, hx, hxm⟩ := hpoly hμ.2
    have hm := hμ.1
    change μ - lam ∈ integralRootLattice_value (fun i : simple H φ => i.val) at hm
    rw [← hQ] at hm
    obtain ⟨y, hy, hyq⟩ := Submodule.mem_map.mp hm
    have hxy : x - l = y := hj (by rw [map_sub, hxm, hl]; exact hyq.symm)
    refine ⟨x - l, ⟨⟨x, hx, rfl⟩, hxy.symm ▸ hy⟩, ?_⟩
    change d.j (x - l + l) = μ
    rw [sub_add_cancel, hxm]
  · intro w
    have hw : w.val lam ∈ polytope H lam := subset_convexHull ℝ _ ⟨w, rfl⟩
    obtain ⟨x, _, hxj⟩ := hpoly hw
    rw [← hxj]
    have hr : Submodule.span ℝ (realRoots H) = ⊤ := d.root_system.span_eq_top
    have hx : x ∈ Submodule.span ℝ (realRoots H) := by rw [hr]; trivial
    refine Submodule.span_induction (p := fun z _ => d.j z ∈ Submodule.span ℝ (rootSet_value H))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, rfl⟩
      rw [d.extension_root _ ha]
      exact Submodule.subset_span ha
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    · intro a y _ hy
      rw [map_smul]
      exact Submodule.smul_mem _ _ hy

private theorem raises_wellFounded {lam : Module.Dual ℂ H} (hf : (candidates H φ lam).Finite) :
    (candidates H φ lam).WellFoundedOn (raises H φ) := by
  let r (ν μ : Module.Dual ℂ H) := φ μ < φ ν
  letI : IsStrictOrder (Module.Dual ℂ H) r :=
    { irrefl := fun _ => lt_irrefl _
      trans := fun _ _ _ h₁ h₂ => h₂.trans h₁ }
  have hw : (candidates H φ lam).WellFoundedOn r := hf.wellFoundedOn
  apply hw.mono (fun ν μ h => ?_) Set.Subset.rfl
  obtain ⟨a, n, rfl⟩ := h
  have ha := a.property.2
  change φ μ < φ (μ + (n + 1) • a.val)
  rw [map_add, map_nsmul, nsmul_eq_mul]
  exact lt_add_of_pos_right _ (mul_pos (by positivity) ha)

end Geometry

section InitialMultiplicity

open private weight_independent from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightSubmodules

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem highest_multiplicity (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
    (hχ : IsWeightCharacter H φ lam χ) :
    letI := inducedLieRingModule H φ χ
    letI := inducedLieModule H φ χ
    multiplicity (simpleQuotient_value H φ χ) H lam = 1 := by
  classical
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let M := induced_value H φ χ
  let V := simpleQuotient_value H φ χ
  let A := weightSpace_value M H
  let W := weightSpace_value V H
  let p := quotientMap H φ χ
  let F : M →ₗ[ℂ] V := p
  obtain ⟨hint, _, _, hline⟩ := VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ
  letI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  have hind : iSupIndep W := weight_independent
  have hmap : (fun μ => (A μ).map F) ≤ W := by
    intro μ
    rintro _ ⟨x, hx, rfl⟩
    apply (HighestWeight.mem_weightSpace V H μ (p x)).mpr
    intro h
    change ⁅(h : L), p x⁆ = μ h • p x
    rw [← p.map_lie, (HighestWeight.mem_weightSpace M H μ x).mp hx h, map_smul]
  have hspan : (⨆ μ, (A μ).map F) = ⊤ := by
    rw [← Submodule.map_iSup, hint.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (LieSubmodule.Quotient.surjective_mk' _)
  have heq := congrFun ((hind.le_iff_eq_of_iSup_eq_top hspan).mp hmap) lam
  have hW : W lam = ℂ ∙ (quotientHighestVector H φ χ) := by
    rw [← heq]
    change (weightSpace_value M H lam).map F = _
    rw [hline, Submodule.map_span, Set.image_singleton]
    rfl
  obtain ⟨e, he⟩ := exists_raisingVectors (H := H) (φ := φ)
  have hw := (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e he).2.1
  change finrank ℂ (W lam) = 1
  rw [hW, finrank_span_singleton hw]

end InitialMultiplicity

theorem termination : termination_type := by
  intro L _ _ _ hss H _ φ hφ B hB hInv hP lam χ hχ hdom
  classical
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let V := simpleQuotient_value H φ χ
  letI : FiniteDimensional ℂ V :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ lam χ hχ).mpr hdom).1
  obtain ⟨hf, hreal⟩ := finite_candidates hss hφ hdom
  refine ⟨highest_multiplicity hss hφ lam χ hχ, ?_, ?_, hf, raises_wellFounded hf⟩
  · intro μ hμ
    by_contra h
    have hW : weightSpace_value V H μ ≠ ⊥ := by
      simpa [Submodule.finrank_eq_zero] using h
    have hc := WeightStringsConvexity.highest_weight_convex_bound hss H φ hφ lam χ hχ hdom μ hW
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hcone := weight_in_verma_cone H φ χ hss hφ lam hχ (quotientMap H φ χ)
      (LieSubmodule.Quotient.surjective_mk' _) μ x hx hx0
    exact hμ ⟨hcone, hc⟩
  · intro μ hμ hc hne
    exact strict_denominator hss hφ B hB hInv hP hμ.2 hc hne hreal

theorem unique_solution : unique_solution_type := by
  intro L _ _ _ hss H _ φ hφ B hB hInv hP lam χ hχ hdom
  classical
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let m := multiplicity (simpleQuotient_value H φ χ) H
  obtain ⟨hm, hzero, hpos, _, hwf⟩ := termination hss H φ hφ B hB hInv hP lam χ hχ hdom
  have hrec := (recursion hss H φ hφ B hB hInv hP lam χ hχ hdom).2
  refine ⟨m, ⟨hm, hzero, fun μ _ _ _ => (hrec μ).2⟩, ?_⟩
  intro f ⟨hf, hfzero, hfstep⟩
  have heq (μ : Module.Dual ℂ H) (hμ : μ ∈ candidates H φ lam) : f μ = m μ := by
    refine hwf.induction hμ (P := fun ν => f ν = m ν) ?_
    intro μ hμ ih
    by_cases hc : inCone H φ lam μ
    · by_cases htop : μ = lam
      · subst μ
        exact hf.trans hm.symm
      · have hsum : recursionSum H φ B f μ = recursionSum H φ B m μ := by
          unfold recursionSum
          apply congrArg (fun t : ℝ => 2 * t)
          apply finsum_congr
          intro α
          apply finsum_congr
          intro n
          let ν := μ + (n + 1) • α.val
          have hν : f ν = m ν := by
            by_cases hn : ν ∈ candidates H φ lam
            · exact ih ν hn ⟨α, n, rfl⟩
            · have hout : ¬ (inCone H φ lam ν ∧ ν ∈ candidates H φ lam) :=
                fun h => hn h.2
              exact (hfzero ν hout).trans (hzero ν hout).symm
          change _ * (f ν : ℝ) = _ * (m ν : ℝ)
          rw [hν]
        have h := (hfstep μ hμ hc htop).trans (hsum.trans (hrec μ).2.symm)
        exact Nat.cast_injective (R := ℝ) (mul_left_cancel₀ (hpos μ hμ hc htop).ne' h)
    · have hout : ¬ (inCone H φ lam μ ∧ μ ∈ candidates H φ lam) :=
        fun h => hc h.1
      exact (hfzero μ hout).trans (hzero μ hout).symm
  funext μ
  by_cases hμ : μ ∈ candidates H φ lam
  · exact heq μ hμ
  · have hout : ¬ (inCone H φ lam μ ∧ μ ∈ candidates H φ lam) :=
      fun h => hμ h.2
    exact (hfzero μ hout).trans (hzero μ hout).symm

end LieAlgebrasAndRepresentations.FreudenthalRecursion
