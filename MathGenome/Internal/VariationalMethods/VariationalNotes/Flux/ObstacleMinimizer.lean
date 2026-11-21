import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.ObstacleMinimizer
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.Stampacchia
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory TopologicalSpace Set Filter
open scoped InnerProductSpace NNReal
namespace VariationalNotes.Flux
open Sobolev

/-- The scalar representative is the coordinate of the original Euclidean
value representative outside a null set. -/
theorem scalarValue_ae {d : ℕ} (Ω : Opens (Domain d)) (u : H1Zero Ω 1) :
    (scalarValue Ω u : Domain d → ℝ) =ᵐ[domainMeasure Ω]
      fun x => value Ω 1 Exponent.two u.val x (0 : Fin 1) :=
  coordinateLp_ae Ω Exponent.two 0 (value Ω 1 Exponent.two u.val)

theorem obstacle_closed_convex : ObstacleExpected.ClosedConvex := by
  intro d Ω ψ _
  constructor
  · apply IsSeqClosed.isClosed
    intro u u₀ hu ht
    have hLp := (scalarValue Ω).continuous.tendsto u₀ |>.comp ht
    obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae
    have hall : ∀ᵐ x ∂domainMeasure Ω, ∀ n, ψ x ≤ scalarValue Ω (u (φ n)) x :=
      eventually_countable_forall.mpr (fun n => hu (φ n))
    filter_upwards [hall, hφ] with x hx hlim
    exact ge_of_tendsto' hlim hx
  · intro u hu v hv a b ha hb hab
    change ∀ᵐ x ∂domainMeasure Ω, ψ x ≤ scalarValue Ω (a • u + b • v) x
    rw [map_add, map_smul, map_smul]
    filter_upwards [hu, hv,
      Lp.coeFn_add (a • scalarValue Ω u) (b • scalarValue Ω v),
      Lp.coeFn_smul a (scalarValue Ω u), Lp.coeFn_smul b (scalarValue Ω v)] with x hx hy hs hsa hsb
    rw [hs, Pi.add_apply, hsa, hsb]
    change ψ x ≤ a * scalarValue Ω u x + b * scalarValue Ω v x
    calc
      ψ x = a * ψ x + b * ψ x := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)

/-- A bounded-below linear map identifies the original Banach space with
its closed Hilbert range. Transport Stampacchia along this equivalence. -/
private theorem pullback_stampacchia
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (G : X →L[ℝ] Y) (C : ℝ≥0) (hcontrol : ∀ u, ‖u‖ ≤ (C : ℝ) * ‖G u‖)
    (K : Set X) (hne : K.Nonempty) (hc : IsClosed K) (hv : Convex ℝ K)
    (ℓ : X →L[ℝ] ℝ) :
    (∃! u : X, u ∈ K ∧ ∀ v ∈ K,
      inner ℝ (G u) (G u) / 2 - ℓ u ≤ inner ℝ (G v) (G v) / 2 - ℓ v) ∧
    (∀ u ∈ K,
      ((∀ v ∈ K, ℓ (v-u) ≤ inner ℝ (G u) (G (v-u))) ↔
       ∀ v ∈ K, inner ℝ (G u) (G u) / 2 - ℓ u ≤
         inner ℝ (G v) (G v) / 2 - ℓ v)) := by
  have hanti : AntilipschitzWith C G := AntilipschitzWith.of_le_mul_dist fun u v => by
    rw [dist_eq_norm, dist_eq_norm, ← G.map_sub]
    exact hcontrol (u-v)
  have hr : IsClosed (G.range : Set Y) := hanti.isClosed_range G.uniformContinuous
  let : CompleteSpace G.range := hr.completeSpace_coe
  let e := G.equivRange hanti.injective hr
  let T : Set G.range := e.symm ⁻¹' K
  have ht : IsClosed T := hc.preimage e.symm.continuous
  have htc : Convex ℝ T := hv.linear_preimage e.symm.toLinearMap
  have htn : T.Nonempty := by
    obtain ⟨u, hu⟩ := hne
    exact ⟨e u, by simpa [T] using hu⟩
  let L : G.range →L[ℝ] ℝ := ℓ.comp e.symm.toContinuousLinearMap
  have hK (u : X) : e u ∈ T ↔ u ∈ K := by simp [T]
  have hL (u : X) : L (e u) = ℓ u := by simp [L]
  have hinner (u v : X) : inner ℝ (e u) (e v) = inner ℝ (G u) (G v) := rfl
  have hVI (u : X) :
      (∀ w ∈ T, L (w-e u) ≤ inner ℝ (e u) (w-e u)) ↔
      ∀ v ∈ K, ℓ (v-u) ≤ inner ℝ (G u) (G (v-u)) := by
    rw [e.surjective.forall]
    simp only [← e.map_sub, hL, hK, hinner]
  have hmin (u : X) :
      (∀ w ∈ T, inner ℝ (e u) (e u) / 2 - L (e u) ≤ inner ℝ w w / 2 - L w) ↔
      ∀ v ∈ K, inner ℝ (G u) (G u) / 2 - ℓ u ≤
        inner ℝ (G v) (G v) / 2 - ℓ v := by
    rw [e.surjective.forall]
    simp only [hK, hL, hinner]
  have hbound (u v : G.range) : |innerₗ G.range u v| ≤ 1 * ‖u‖ * ‖v‖ := by
    simpa only [innerₗ_apply_apply, one_mul] using abs_real_inner_le_norm u v
  have hco (v : G.range) : 1 * ‖v‖ ^ 2 ≤ innerₗ G.range v v := by
    simp only [innerₗ_apply_apply, real_inner_self_eq_norm_sq, one_mul, le_refl]
  have heq (w : G.range) (hw : w ∈ T) :=
    Existence.stampacchia_minimization_iff T htn ht htc (innerₗ G.range) 1 1 hbound
      zero_lt_one hco (fun u v => real_inner_comm v u) L w hw
  have hex := Existence.stampacchia_existsUnique T htn ht htc (innerₗ G.range) 1 1
    hbound zero_lt_one hco L
  have hexmin : ∃! w : G.range, w ∈ T ∧ ∀ z ∈ T,
      inner ℝ w w / 2 - L w ≤ inner ℝ z z / 2 - L z := by
    obtain ⟨w, hw, huniq⟩ := hex
    exact ⟨w, ⟨hw.1, (heq w hw.1).mp hw.2⟩,
      fun z hz => huniq z ⟨hz.1, (heq z hz.1).mpr hz.2⟩⟩
  constructor
  · obtain ⟨w, hw, huniq⟩ := hexmin
    refine ⟨e.symm w, ⟨hw.1, (hmin (e.symm w)).mp ?_⟩, ?_⟩
    · simpa only [e.apply_symm_apply] using hw.2
    · intro v hvv
      apply e.injective
      rw [e.apply_symm_apply]
      exact huniq (e v) ⟨(hK v).mpr hvv.1, (hmin v).mpr hvv.2⟩
  · intro u hu
    exact (hVI u).symm.trans ((heq (e u) ((hK u).mpr hu)).trans (hmin u))

/-- Every bounded open domain in positive dimension fits in a coordinate
strip, including the empty domain. -/
private theorem bounded_coordinate_strip {n : ℕ} (Ω : Opens (Domain (n+1)))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain (n+1)))) :
    ∃ a b : ℝ, a < b ∧ InCoordinateStrip Ω (0 : Fin (n+1)) a b := by
  obtain ⟨R, hR, hb⟩ := hΩ.exists_pos_norm_lt
  refine ⟨-R, R, by linarith, ?_⟩
  intro x hx
  have hh : |x (0 : Fin (n+1))| < R := by
    exact (PiLp.norm_apply_le x 0).trans_lt (hb x hx)
  exact abs_lt.mp hh

set_option backward.isDefEq.respectTransparency false in
private theorem obstacle_variational {n : ℕ} (Ω : Opens (Domain (n+1)))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain (n+1))))
    (ℓ : H1Zero Ω 1 →L[ℝ] ℝ) (ψ : Domain (n+1) → ℝ) (hψ : AEMeasurable ψ (domainMeasure Ω))
    (hne : (obstacleSet Ω ψ).Nonempty) :
    (∃! u : H1Zero Ω 1, u ∈ obstacleSet Ω ψ ∧
      ∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v) ∧
    (∀ u ∈ obstacleSet Ω ψ,
      ((∀ v ∈ obstacleSet Ω ψ, ℓ (v-u) ≤ dirichletPairing Ω u (v-u)) ↔
       ∀ v ∈ obstacleSet Ω ψ, dirichletEnergy Ω ℓ u ≤ dirichletEnergy Ω ℓ v)) := by
  obtain ⟨a, b, hab, hstrip⟩ := bounded_coordinate_strip Ω hΩ
  let : CompleteSpace (H1Zero Ω 1) :=
    (smoothSubmodule Ω 1 Exponent.two).isClosed_topologicalClosure.completeSpace_coe
  have htwo : Exponent.two.ennreal = 2 := by norm_num [Exponent.two, Exponent.ennreal]
  let e : GradientLp Ω 1 Exponent.two ≃ₗᵢ[ℝ]
      Lp (Gradient 1 (n+1)) 2 (domainMeasure Ω) := lpExponentEquiv (domainMeasure Ω) htwo
  let D : H1Zero Ω 1 →L[ℝ] GradientLp Ω 1 Exponent.two :=
    (gradient Ω 1 Exponent.two).comp (zeroSubmodule Ω 1 Exponent.two).subtypeL
  let G : H1Zero Ω 1 →L[ℝ] Lp (Gradient 1 (n+1)) 2 (domainMeasure Ω) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp D
  let C : ℝ≥0 := ⟨b-a+1, by linarith⟩
  have hcontrol (u : H1Zero Ω 1) : ‖u‖ ≤ (C : ℝ) * ‖G u‖ := by
    have hnorm : ‖G u‖ = ‖gradient Ω 1 Exponent.two u.val‖ := e.norm_map (D u)
    rw [hnorm]
    exact (slab_norm_equivalence Ω Exponent.two 0 a b hab hstrip u).2
  have hrep (u : H1Zero Ω 1) : (G u : Domain (n+1) → Gradient 1 (n+1)) =
      (gradient Ω 1 Exponent.two u.val : Domain (n+1) → Gradient 1 (n+1)) :=
    lpExponentEquiv_coe (domainMeasure Ω) htwo (D u)
  have hinner (u v : H1Zero Ω 1) :
      inner ℝ (G u) (G v) = dirichletPairing Ω u v := by
    rw [L2.inner_def]
    simp only [hrep, dirichletPairing, Sobolev.frobenius]
  have hdiag (u : H1Zero Ω 1) :
      dirichletPairing Ω u u / 2 - ℓ u = dirichletEnergy Ω ℓ u := by
    simp only [dirichletPairing, Sobolev.frobenius, real_inner_self_eq_norm_sq, dirichletEnergy]
  obtain ⟨hc, hv⟩ := obstacle_closed_convex Ω ψ hψ
  have hp := pullback_stampacchia G C hcontrol (obstacleSet Ω ψ) hne hc hv ℓ
  simp only [hinner, hdiag] at hp
  exact hp

theorem obstacle_unique_minimizer : ObstacleExpected.UniqueMinimizer := by
  intro n Ω hΩ ℓ ψ hψ hne
  exact (obstacle_variational Ω hΩ ℓ ψ hψ hne).1

theorem obstacle_minimization_iff : ObstacleExpected.MinimizationIff := by
  intro n Ω hΩ ℓ ψ hψ u hu
  exact ((obstacle_variational Ω hΩ ℓ ψ hψ ⟨u, hu⟩).2 u hu).symm

end VariationalNotes.Flux
