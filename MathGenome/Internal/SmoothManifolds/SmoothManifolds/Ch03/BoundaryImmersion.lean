import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.BoundaryImmersion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace SmoothManifolds.BoundaryImmersion
open ModelData AtlasData MapData BoundaryData FiniteRegularityData Set Filter
open scoped Topology ContDiff
universe u v

/-- Extend an injective linear map by complementary coordinates. -/
theorem complementary_coordinates {m n : ℕ}
    (L : Euclidean m →L[ℝ] Euclidean n) (hi : Function.Injective L) :
    m ≤ n ∧ ∃ E : (Euclidean m × Euclidean (n - m)) ≃L[ℝ] Euclidean n,
      ∀ x, E (x, 0) = L x := by
  classical
  have hmn : m ≤ n := by
    simpa using LinearMap.finrank_le_finrank_of_injective hi
  obtain ⟨q, hq⟩ := (LinearMap.range L.toLinearMap).exists_isCompl
  let A := LinearEquiv.ofInjective L.toLinearMap hi
  let B := (LinearMap.range L.toLinearMap).prodEquivOfIsCompl q hq
  have hdim : Module.finrank ℝ q = n - m := by
    have hh := B.finrank_eq
    rw [Module.finrank_prod, ← A.finrank_eq] at hh
    simp only [Module.finrank_pi, Fintype.card_fin] at hh
    omega
  let C : Euclidean (n - m) ≃ₗ[ℝ] q := LinearEquiv.ofFinrankEq _ _ (by simpa using hdim.symm)
  let E := ((LinearEquiv.prodCongr A C).trans B).toContinuousLinearEquiv
  refine ⟨hmn, E, ?_⟩
  intro x
  simp [E, B, A]

/-- The inverse of a transverse Euclidean thickening straightens an immersion
without changing any of its source coordinates. -/
theorem euclidean_immersion {m n : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (g : Euclidean m → Euclidean n) (U : Set (Euclidean m))
    (hU : IsOpen U) (hg : ContDiffOn ℝ r g U) (x : Euclidean m) (hx : x ∈ U)
    (L : Euclidean m →L[ℝ] Euclidean n) (hd : HasFDerivAt g L x)
    (hi : Function.Injective L) :
    m ≤ n ∧ ∃ h : OpenPartialHomeomorph (Euclidean n) (Euclidean m × Euclidean (n - m)),
      ContDiffOn ℝ r h h.source ∧ ContDiffOn ℝ r h.symm h.target ∧
      ∃ O : Set (Euclidean m), IsOpen O ∧ x ∈ O ∧
        ∀ u ∈ O, g u ∈ h.source ∧ h (g u) = (u, 0) := by
  obtain ⟨hmn, E, hE⟩ := complementary_coordinates L hi
  let A : Euclidean (n - m) →L[ℝ] Euclidean n :=
    E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)
  let P : Euclidean n →L[ℝ] Euclidean m :=
    (ContinuousLinearMap.fst ℝ _ _).comp E.symm.toContinuousLinearMap
  let Q : Euclidean n →L[ℝ] Euclidean (n - m) :=
    (ContinuousLinearMap.snd ℝ _ _).comp E.symm.toContinuousLinearMap
  let Φ : Euclidean n → Euclidean n := fun z => g (P z) + A (Q z)
  let W := P ⁻¹' U
  let z := E (x, 0)
  have hPz : P z = x := by simp [P, z]
  have hW : IsOpen W := hU.preimage P.continuous
  have hzW : z ∈ W := by simpa [W, hPz] using hx
  have hΦ : ContDiffOn ℝ r Φ W :=
    (hg.comp P.contDiff.contDiffOn (fun _ hz => hz)).add
      ((A.contDiff.comp Q.contDiff).contDiffOn)
  have hD : L.comp P + A.comp Q = ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply ContinuousLinearMap.ext
    intro v
    change L (E.symm v).1 + E (0, (E.symm v).2) = v
    rw [← hE]
    rw [← map_add]
    simp
  have hdΦ : HasFDerivAt Φ (ContinuousLinearMap.id ℝ (Euclidean n)) z := by
    rw [← hD]
    exact ((hPz.symm ▸ hd).comp z P.hasFDerivAt).add
      (A.hasFDerivAt.comp z Q.hasFDerivAt)
  obtain ⟨j₀, hzj₀, hj₀, hji₀⟩ := InteriorInverse.euclidean_inverse r hr Φ W hW hΦ z hzW
    (ContinuousLinearMap.id ℝ _) hdΦ Function.bijective_id
  let j := j₀.restrOpen W hW
  have hzj : z ∈ j.source := ⟨hzj₀, hzW⟩
  have hj : (j : Euclidean n → Euclidean n) = Φ := hj₀
  have hji : ContDiffOn ℝ r j.symm j.target := hji₀.mono (by
    intro v hv; exact hv.1)
  have hjf : ContDiffOn ℝ r j j.source := by
    rw [hj]
    exact hΦ.mono (fun _ hv => hv.2)
  let h := j.symm.trans E.symm.toHomeomorph.toOpenPartialHomeomorph
  have hforward : ContDiffOn ℝ r h h.source := by
    intro v hv
    exact E.symm.contDiff.contDiffAt.comp_contDiffWithinAt v
      ((hji v hv.1).mono (fun _ hv => hv.1))
  have hinverse : ContDiffOn ℝ r h.symm h.target := by
    intro v hv
    exact (hjf.contDiffAt (j.open_source.mem_nhds hv.2)).comp_contDiffWithinAt v
      E.contDiff.contDiffAt.contDiffWithinAt
  let O := (fun u => E (u, 0)) ⁻¹' j.source
  have hO : IsOpen O := j.open_source.preimage
    (E.continuous.comp (continuous_id.prodMk continuous_const))
  have hxO : x ∈ O := hzj
  refine ⟨hmn, h, hforward, hinverse, O, hO, hxO, ?_⟩
  intro u hu
  have hjEu : j (E (u, 0)) = g u := by
    rw [hj]
    simp [Φ, P, Q, A]
  have hgu : g u ∈ j.target := hjEu ▸ j.map_source hu
  refine ⟨⟨hgu, Set.mem_univ _⟩, ?_⟩
  change E.symm (j.symm (g u)) = (u, 0)
  rw [← hjEu, j.left_inv hu, E.symm_apply_apply]

/-- The boundary immersion theorem, with the original half-space condition and
an actual two-sided C^r change of target coordinates. -/
theorem boundary_immersion :
    Specs.SmoothManifolds.Ch03.BoundaryImmersion.boundary_immersionType.{u,v} := by
  intro m n a b M N _ _ r hr S T f hf p hpb hfpi F G
  let := F.group; let := F.module; let := G.group; let := G.module
  intro L hL hi
  obtain ⟨e, he, hp, hface⟩ := hpb
  obtain ⟨d, hd, hfp, hfpei⟩ := hfpi
  have ha : a = .halfSpace := by
    cases a with
    | halfSpace => rfl
    | euclidean => exact (Set.notMem_empty _ hface).elim
  have hm : 0 < m := by
    cases m with
    | zero => simp [BoundaryData.modelFace, ha, ModelData.halfSpaceFace] at hface
    | succ m => exact Nat.zero_lt_succ m
  obtain ⟨U, hU, hepU, g, hg, heq⟩ := (hf p).2 e he d hd hp hfp
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr))
  have hdg := ((hg.contDiffAt (hU.mem_nhds hepU)).differentiableAt hr0).hasFDerivAt
  have hderiv : chartDerivative e d f p = fderiv ℝ g (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨g, hdg, heq⟩
  have hlin := MapClasses.differential_chart_invariants S T f p F G
    e d he hd hp hfp L hL
  have hgi : Function.Injective (fderiv ℝ g (e p).val) := by
    rw [← hderiv]
    exact hlin.2.1.mp hi
  obtain ⟨hmn, h, hhs, hhi, O, hO, hepO, hform⟩ :=
    euclidean_immersion r hr g U hU hg (e p).val hepU _ hdg hgi
  let D := InteriorInverse.ambientChart d
  let c := D.trans h
  have hfpD : f p ∈ D.source := ⟨hfp, hfpei⟩
  have hfpc : f p ∈ c.source := by
    refine ⟨hfpD, ?_⟩
    change (d (f p)).val ∈ h.source
    rw [← heq.eq_of_nhds]
    exact (hform _ hepO).1
  have hecont : ContinuousAt (fun y => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hnhds : ∀ᶠ y in 𝓝 p, y ∈ e.source ∧ f y ∈ c.source ∧
      (e y).val ∈ O ∧ g (e y).val = (d (f y)).val := by
    filter_upwards [e.open_source.mem_nhds hp,
      (hf p).1.preimage_mem_nhds (c.open_source.mem_nhds hfpc),
      hecont.preimage_mem_nhds (hO.mem_nhds hepO), heq] with y hy hfy hyO heqy
    exact ⟨hy, hfy, hyO, heqy⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  refine ⟨hmn, hm, ha, e, he, hp, hface, c, hfpc, ?_, d, hd, ?_, h,
    hhs, hhi, ?_, ?_, V, hV, hpV, ?_, ?_⟩
  · intro y hy
    exact ⟨d, hd, hy.1.1, hy.1.2⟩
  · intro y hy
    exact hy.1.1
  · intro y hy
    exact ⟨hy.2, rfl⟩
  · intro z hz
    change h.symm z = D (D.symm (h.symm z))
    exact (D.right_inv hz.2).symm
  · intro x hx
    exact (hVsub hx).1
  · intro x hx
    obtain ⟨_, hfxc, hxO, heqx⟩ := hVsub hx
    refine ⟨hfxc, ?_⟩
    change h (d (f x)).val = ((e x).val, 0)
    rw [← heqx]
    exact (hform _ hxO).2

end SmoothManifolds.BoundaryImmersion
