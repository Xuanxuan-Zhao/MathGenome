import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.ConjugacyTransport
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.DiscreteDefinitions

/-! Transport of the complete forward dynamics by a conjugacy. -/
namespace D13Unified.Ch15.ConjugacyTransport
universe u v
open Function Set Filter
open scoped Topology
open D13Unified.Ch15.DiscreteDefinitions

theorem iterate_transport :
    Specs.D13Unified.Ch15.ConjugacyTransport.iterate_transportStatement.{u,v} := by
  intro X Y F G h hh n
  exact Function.semiconj_iff_comp_eq.mp
    ((Function.semiconj_iff_comp_eq.mpr hh).iterate_right n)

section Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (F : X → X) (G : Y → Y) (h : X ≃ₜ Y)

/-- Reversing the homeomorphism reverses the conjugacy identity. -/
theorem conjugacy_symm (hh : IsConjugacy F G h) : IsConjugacy G F h.symm := by
  intro y
  apply h.injective
  simpa only [h.apply_symm_apply] using (hh (h.symm y)).symm

theorem periodicPt_iff (hh : IsConjugacy F G h) (x : X) (n : ℕ) :
    IsPeriodicPt F n x ↔ IsPeriodicPt G n (h x) := by
  change F^[n] x = x ↔ G^[n] (h x) = h x
  rw [← hh.iterate_right n x]
  exact h.injective.eq_iff.symm

theorem leastPeriod_iff (hh : IsConjugacy F G h) (x : X) (n : ℕ) :
    HasLeastPeriod F x n ↔ HasLeastPeriod G (h x) n := by
  change (0 < n ∧ IsPeriodicPt F n x ∧
    ∀ m, 0 < m → m < n → ¬IsPeriodicPt F m x) ↔
    (0 < n ∧ IsPeriodicPt G n (h x) ∧
    ∀ m, 0 < m → m < n → ¬IsPeriodicPt G m (h x))
  simp only [periodicPt_iff F G h hh x]

theorem periodic_points_bijOn (hh : IsConjugacy F G h) :
    Set.BijOn h {x | ∃ n : ℕ, 0 < n ∧ IsPeriodicPt F n x}
      {y | ∃ n : ℕ, 0 < n ∧ IsPeriodicPt G n y} := by
  refine ⟨?_, h.injective.injOn, ?_⟩
  · rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, (periodicPt_iff F G h hh x n).mp hx⟩
  · intro y hy
    rcases h.surjective y with ⟨x, rfl⟩
    rcases hy with ⟨n, hn, hx⟩
    exact ⟨x, ⟨n, hn, (periodicPt_iff F G h hh x n).mpr hx⟩, rfl⟩

private theorem image_intertwine (hh : IsConjugacy F G h) (A : Set X) :
    G '' (h '' A) = h '' (F '' A) := by
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1
  exact (isConjugacy_iff F G h).mp hh |>.symm

theorem invariant_image_iff (hh : IsConjugacy F G h) (A : Set X) :
    Invariant F A ↔ Invariant G (h '' A) := by
  change F '' A = A ↔ G '' (h '' A) = h '' A
  rw [image_intertwine F G h hh A]
  exact h.injective.image_injective.eq_iff.symm

theorem invariant_sets_bijOn (hh : IsConjugacy F G h) :
    Set.BijOn (fun A : Set X => h '' A) {A | Invariant F A} {B | Invariant G B} := by
  refine ⟨fun A hA => (invariant_image_iff F G h hh A).mp hA,
    h.injective.image_injective.injOn, ?_⟩
  intro B hB
  have himage : h '' (h ⁻¹' B) = B := Set.image_preimage_eq B h.surjective
  refine ⟨h ⁻¹' B, ?_, himage⟩
  apply (invariant_image_iff F G h hh _).mpr
  rwa [himage]

theorem orbitSet_image (hh : IsConjugacy F G h) (x : X) :
    h '' orbitSet F x = orbitSet G (h x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (hh.iterate_right n x).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨F^[n] x, ⟨n, rfl⟩, hh.iterate_right n x⟩

theorem dense_orbit_iff (hh : IsConjugacy F G h) (x : X) :
    Dense (orbitSet F x) ↔ Dense (orbitSet G (h x)) := by
  rw [← orbitSet_image F G h hh x]
  rw [dense_iff_closure_eq, dense_iff_closure_eq]
  rw [← h.image_closure, ← Set.image_univ_of_surjective h.surjective]
  exact h.injective.image_injective.eq_iff.symm

theorem dense_orbit_points_bijOn (hh : IsConjugacy F G h) :
    Set.BijOn h {x | Dense (orbitSet F x)} {y | Dense (orbitSet G y)} := by
  refine ⟨fun x hx => (dense_orbit_iff F G h hh x).mp hx, h.injective.injOn, ?_⟩
  intro y hy
  rcases h.surjective y with ⟨x, rfl⟩
  exact ⟨x, (dense_orbit_iff F G h hh x).mpr hy, rfl⟩

theorem fixed_point (hh : IsConjugacy F G h) (p : X) (hp : F p = p) :
    G (h p) = h p := by
  rw [← hh p, hp]
end Topology

section Metric
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable (F : X → X) (G : Y → Y) (h : X ≃ₜ Y)

/-- The neighborhood proof uses only continuity of the coordinate change. -/
private theorem stable_forward (hh : IsConjugacy F G h) (p : X)
    (hs : LyapunovStable F p) : LyapunovStable G (h p) := by
  apply (lyapunovStable_iff_neighborhoods G (h p)).mpr
  intro V hV
  have hpull : h ⁻¹' V ∈ 𝓝 p := h.continuous.continuousAt.preimage_mem_nhds hV
  rcases (lyapunovStable_iff_neighborhoods F p).mp hs (h ⁻¹' V) hpull with
    ⟨U, hU, hiter⟩
  refine ⟨h '' U, h.isOpenMap.image_mem_nhds hU, ?_⟩
  rintro y ⟨x, hx, rfl⟩ n
  rw [← hh.iterate_right n x]
  exact hiter x hx n

/-- Convergence is transported pointwise; no uniform estimate is used. -/
private theorem attracts_forward (hh : IsConjugacy F G h) (p : X)
    (hs : AttractsNeighborhood F p) : AttractsNeighborhood G (h p) := by
  apply (attractsNeighborhood_iff G (h p)).mpr
  rcases (attractsNeighborhood_iff F p).mp hs with ⟨U, hU, hconv⟩
  refine ⟨h '' U, h.isOpenMap.image_mem_nhds hU, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have ht := h.continuous.continuousAt.tendsto.comp (hconv x hx)
  have heq : (fun n : ℕ => h (F^[n] x)) = (fun n : ℕ => G^[n] (h x)) :=
    funext fun n => hh.iterate_right n x
  rw [← heq]
  exact ht

theorem lyapunovStable_iff (hh : IsConjugacy F G h)
    (_hF : Continuous F) (_hG : Continuous G) (p : X) (_hp : F p = p) :
    LyapunovStable F p ↔ LyapunovStable G (h p) := by
  constructor
  · exact stable_forward F G h hh p
  · intro hs
    simpa only [h.symm_apply_apply] using
      stable_forward G F h.symm (conjugacy_symm F G h hh) (h p) hs

theorem asymptoticallyStable_iff (hh : IsConjugacy F G h)
    (hF : Continuous F) (hG : Continuous G) (p : X) (hp : F p = p) :
    AsymptoticallyStable F p ↔ AsymptoticallyStable G (h p) := by
  change (LyapunovStable F p ∧ AttractsNeighborhood F p) ↔
    (LyapunovStable G (h p) ∧ AttractsNeighborhood G (h p))
  rw [lyapunovStable_iff F G h hh hF hG p hp]
  constructor
  · rintro ⟨hs, ha⟩
    exact ⟨hs, attracts_forward F G h hh p ha⟩
  · rintro ⟨hs, ha⟩
    refine ⟨hs, ?_⟩
    simpa only [h.symm_apply_apply] using
      attracts_forward G F h.symm (conjugacy_symm F G h hh) (h p) ha
end Metric

end D13Unified.Ch15.ConjugacyTransport
