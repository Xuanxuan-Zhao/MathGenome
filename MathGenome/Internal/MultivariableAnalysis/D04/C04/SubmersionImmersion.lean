import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.SubmersionImmersion
import MathGenome.Internal.MultivariableAnalysis.D04.C04.ConstantRank
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04

def SubmersionAt : Specs.D04.C04.SubmersionImmersion.SubmersionAtType :=
  @Specs.D04.C04.SubmersionImmersion.SubmersionAtValue

def ImmersionAt : Specs.D04.C04.SubmersionImmersion.ImmersionAtType :=
  @Specs.D04.C04.SubmersionImmersion.ImmersionAtValue

def EmbeddingOn : Specs.D04.C04.SubmersionImmersion.EmbeddingOnType :=
  @Specs.D04.C04.SubmersionImmersion.EmbeddingOnValue

namespace SubmersionImmersion
open Specs.D04.C04.ConstantRank

/-- Scalar component derivatives are the rows of the same total derivative. -/
theorem component_differential {n m : ℕ} (f : E n → E m) (a : E n)
    (hf : DifferentiableAt ℝ f a) (i : Fin m) :
    (fderiv ℝ (fun x => f x i) a).toLinearMap =
      (fderiv ℝ f a).toLinearMap.dualMap ((standardBasis m).dualBasis i) := by
  have hd := (PiLp.hasFDerivAt_apply 2 (f a) i).comp a hf.hasFDerivAt
  change (fderiv ℝ ((fun y : E m => y i) ∘ f) a).toLinearMap = _
  rw [hd.fderiv]
  apply LinearMap.ext
  intro v
  change fderiv ℝ f a v i = (standardBasis m).dualBasis i (fderiv ℝ f a v)
  simp [standardBasis]

theorem submersion_iff_components {n m : ℕ} (f : E n → E m) (a : E n)
    (hf : DifferentiableAt ℝ f a) :
    SubmersionAt f a ↔ LinearIndependent ℝ
      (fun i : Fin m => (totalDerivative (fun x => f x i) a).toLinearMap) := by
  let L := (fderiv ℝ f a).toLinearMap
  have he : (fun i : Fin m => (totalDerivative (fun x => f x i) a).toLinearMap) =
      L.dualMap ∘ (standardBasis m).dualBasis := by
    funext i
    exact component_differential f a hf i
  rw [he]
  change Function.Surjective L ↔ _
  constructor
  · intro h
    exact (standardBasis m).dualBasis.linearIndependent.map' L.dualMap
      (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective h))
  · intro h
    exact LinearMap.dualMap_injective_iff.mp
      (LinearMap.injective_of_linearIndependent (standardBasis m).dualBasis.span_eq h)

/-- Full column rank is open, including the empty-column case. -/
theorem immersion_persists {n m : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E m)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U) (h : ImmersionAt f a) :
    ∀ᶠ x in 𝓝 a, ImmersionAt f x := by
  have hc := (hf.continuousOn_fderiv_of_isOpen hU hr).continuousAt (hU.mem_nhds ha)
  exact hc.preimage_mem_nhds (ContinuousLinearMap.isOpen_injective.mem_nhds h)

/-- A right inverse reduces persistence of full row rank to openness of
invertibility on the target space. This also works for a zero target. -/
theorem submersion_persists {n m : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E m)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U) (h : SubmersionAt f a) :
    ∀ᶠ x in 𝓝 a, SubmersionAt f x := by
  let L := fderiv ℝ f a
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr h)
  let R' := R.toContinuousLinearMap
  have hLR : L.comp R' = ContinuousLinearMap.id ℝ (E m) := by
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun hR y
  have hc := (hf.continuousOn_fderiv_of_isOpen hU hr).continuousAt (hU.mem_nhds ha)
  have hcomp : ContinuousAt (fun x => (fderiv ℝ f x).comp R') a :=
    hc.clm_comp continuousAt_const
  have hn : {x | ∃ B : E m ≃L[ℝ] E m,
      B.toContinuousLinearMap = (fderiv ℝ f x).comp R'} ∈ 𝓝 a := by
    have ht := hcomp.preimage_mem_nhds (by
      change {A | ∃ B : E m ≃L[ℝ] E m, B.toContinuousLinearMap = A} ∈ 𝓝 (L.comp R')
      rw [hLR]
      exact (ContinuousLinearEquiv.refl ℝ (E m)).nhds)
    exact ht
  filter_upwards [hn] with x hx
  obtain ⟨B, hB⟩ := hx
  intro y
  obtain ⟨z, hz⟩ := B.surjective y
  exact ⟨R' z, (DFunLike.congr_fun hB z).symm.trans hz⟩

/-- Surjectivity fixes the derivative rank at the target dimension. -/
theorem rank_of_submersion {n m : ℕ} (f : E n → E m) (a : E n)
    (h : SubmersionAt f a) :
    Module.finrank ℝ (LinearMap.range (totalDerivative f a).toLinearMap) = m := by
  change Module.finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap) = m
  change Function.Surjective (fderiv ℝ f a).toLinearMap at h
  rw [LinearMap.range_eq_top.mpr h, finrank_top, finrank_euclideanSpace_fin]

/-- Injectivity fixes the derivative rank at the source dimension. -/
theorem rank_of_immersion {n m : ℕ} (f : E n → E m) (a : E n)
    (h : ImmersionAt f a) :
    Module.finrank ℝ (LinearMap.range (totalDerivative f a).toLinearMap) = n := by
  change Module.finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap) = n
  change Function.Injective (fderiv ℝ f a).toLinearMap at h
  simpa only [finrank_euclideanSpace_fin] using LinearMap.finrank_range_of_inj h

theorem submersion_normal_form {n m : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E m)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U) (h : SubmersionAt f a) :
    m ≤ n ∧ RankNormalForm r U f a m ∧ ∀ᶠ x in 𝓝 a, SubmersionAt f x := by
  have hp := submersion_persists r hr U hU f hf a ha h
  have hk : NeighborhoodRank f a m := hp.mono (fun x hx => rank_of_submersion f x hx)
  exact ⟨((constant_rank_bounds f a m hk).2).trans (min_le_left _ _),
    ConstantRank.rankNormalForm r hr U hU f hf a ha m hk, hp⟩

theorem immersion_normal_form {n m : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E m)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U) (h : ImmersionAt f a) :
    n ≤ m ∧ RankNormalForm r U f a n ∧ ∀ᶠ x in 𝓝 a, ImmersionAt f x := by
  have hp := immersion_persists r hr U hU f hf a ha h
  have hk : NeighborhoodRank f a n := hp.mono (fun x hx => rank_of_immersion f x hx)
  exact ⟨((constant_rank_bounds f a n hk).2).trans (min_le_right _ _),
    ConstantRank.rankNormalForm r hr U hU f hf a ha n hk, hp⟩

/-- The first m coordinates, bundled as a continuous linear map. -/
def firstCoordinates (n m : ℕ) (h : m ≤ n) : E n →L[ℝ] E m :=
  (ContinuousLinearMap.fst ℝ (E m) (E (n-m))).comp
    (ConstantRank.coordinateSplit n m h).toContinuousLinearMap

theorem firstCoordinates_apply (n m : ℕ) (h : m ≤ n) (u : E n) (i : Fin m) :
    firstCoordinates n m h u i = u ⟨i.val, lt_of_lt_of_le i.isLt h⟩ := rfl

theorem firstCoordinates_eq_projection (n m : ℕ) (h : m ≤ n) (u : E n) :
    firstCoordinates n m h u = normalProjection n m m u := by
  ext i
  simp only [normalProjection, PiLp.toLp_apply, firstCoordinates_apply]
  rw [dite_eq_left ⟨i.isLt, lt_of_lt_of_le i.isLt h⟩]

theorem firstCoordinates_surjective (n m : ℕ) (h : m ≤ n) :
    Function.Surjective (firstCoordinates n m h) := by
  intro y
  refine ⟨(ConstantRank.coordinateSplit n m h).symm (y, 0), ?_⟩
  change ((ConstantRank.coordinateSplit n m h)
    ((ConstantRank.coordinateSplit n m h).symm (y, 0))).1 = y
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem firstCoordinates_inclusion (n m : ℕ) (h : n ≤ m) (u : E n) :
    firstCoordinates m n h (normalProjection n m n u) = u := by
  ext i
  simp only [firstCoordinates_apply, normalProjection]
  rw [dite_eq_left ⟨i.isLt, i.isLt⟩]

/-- The inclusion normal form is an embedding on the chart's source.
Projection of the target coordinates recovers the source coordinates
continuously; all continuity assertions use the displayed chart domains. -/
theorem embedding_of_normal_form {n m : ℕ} (r : ℕ∞ω) (U : Set (E n))
    (f : E n → E m) (a : E n) (h : n ≤ m)
    (hc : ContinuousOn f U) (hn : RankNormalForm r U f a n) :
    ∃ X : Set (E n), IsOpen X ∧ a ∈ X ∧ X ⊆ U ∧ EmbeddingOn f X := by
  obtain ⟨Φ, Ψ, ha, hsub, hΦa, hfa, hΨa, hΦ, hΦi, hΨ, hΨi, hmap, hnormal⟩ := hn
  let F : Φ.source → E m := fun x => f x
  let G : Φ.source → E m := fun x => Ψ (f x)
  have hF : Continuous F := (hc.mono hsub).domRestrict
  have hG : Continuous G := Ψ.continuousOn.comp_continuous hF (fun x => hmap x.property)
  have heq : (fun x : Φ.source => firstCoordinates m n h (G x)) =
      Φ.source.domRestrict Φ := by
    funext x
    have hi := hnormal (Φ x) (Φ.map_source x.property)
    rw [Φ.left_inv x.property] at hi
    change firstCoordinates m n h (Ψ (f x)) = Φ x
    rw [hi, firstCoordinates_inclusion]
  have hEmbG : Topology.IsEmbedding G := by
    apply Topology.IsEmbedding.of_comp hG (firstCoordinates m n h).continuous
    change Topology.IsEmbedding (fun x : Φ.source => firstCoordinates m n h (G x))
    rw [heq]
    exact Φ.isEmbedding_restrict
  have hEmbF : Topology.IsEmbedding F := by
    let H : Ψ.source → E m := Ψ.source.domRestrict Ψ
    let F' : Φ.source → Ψ.source := fun x => ⟨f x, hmap x.property⟩
    have hF' : Continuous F' := hF.subtype_mk _
    have hEmbF' : Topology.IsEmbedding F' :=
      Topology.IsEmbedding.of_comp hF' Ψ.continuousOn.domRestrict hEmbG
    exact Topology.IsEmbedding.subtypeVal.comp hEmbF'
  exact ⟨Φ.source, Φ.open_source, ha, hsub, hEmbF⟩

/-- Projection is open; transporting it through the two coordinate charts
proves openness on an arbitrary open subset of a submersion's domain. -/
theorem open_image_of_submersion {n m : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E m)
    (hf : ContDiffOn ℝ r f U) (h : ∀ a ∈ U, SubmersionAt f a)
    (X : Set (E n)) (hX : IsOpen X) (hXU : X ⊆ U) : IsOpen (f '' X) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨a, haX, rfl⟩
  obtain ⟨hmn, hn, hp⟩ := submersion_normal_form r hr U hU f hf a (hXU haX) (h a (hXU haX))
  obtain ⟨Φ, Ψ, ha, hsub, hΦa, hfa, hΨa, hΦ, hΦi, hΨ, hΨi, hmap, hnormal⟩ := hn
  let O := Φ.source ∩ X
  let S := Φ '' O
  let P := firstCoordinates n m hmn
  have hO : IsOpen O := Φ.open_source.inter hX
  have hS : IsOpen S := Φ.isOpen_image_of_subset_source hO inter_subset_left
  have hP : IsOpen (P '' S) :=
    (LinearMap.isOpenMap_of_finiteDimensional P.toLinearMap (firstCoordinates_surjective n m hmn)) S hS
  have htarget : P '' S ⊆ Ψ.target := by
    rintro z ⟨u, ⟨x, hx, rfl⟩, rfl⟩
    have hn := hnormal (Φ x) (Φ.map_source hx.1)
    rw [Φ.left_inv hx.1] at hn
    rw [firstCoordinates_eq_projection, ← hn]
    exact Ψ.map_source (hmap hx.1)
  have heq : Ψ.symm '' (P '' S) = f '' O := by
    ext z
    constructor
    · rintro ⟨v, ⟨u, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      have hn := hnormal (Φ x) (Φ.map_source hx.1)
      rw [Φ.left_inv hx.1] at hn
      rw [firstCoordinates_eq_projection, ← hn, Ψ.left_inv (hmap hx.1)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨P (Φ x), ⟨Φ x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      have hn := hnormal (Φ x) (Φ.map_source hx.1)
      rw [Φ.left_inv hx.1] at hn
      rw [firstCoordinates_eq_projection, ← hn, Ψ.left_inv (hmap hx.1)]
  have hopen : IsOpen (f '' O) := heq ▸ Ψ.isOpen_image_symm_of_subset_target hP htarget
  exact mem_of_superset (hopen.mem_nhds ⟨a, ⟨ha, haX⟩, rfl⟩)
    (image_mono inter_subset_right)

end SubmersionImmersion

theorem embeddingOn_homeomorph :
    Specs.D04.C04.SubmersionImmersion.embeddingOn_homeomorphType := by
  intro n m f X h
  change Topology.IsEmbedding (fun x : X => f x) at h
  have heq : Set.range (fun x : X => f x) = f '' X := by
    ext y
    simp
  exact ⟨h.toHomeomorph.trans (Homeomorph.setCongr heq), fun x => rfl⟩

theorem submersion_iff_components :
    Specs.D04.C04.SubmersionImmersion.submersion_iff_componentsType := by
  intro n m f a hf
  exact SubmersionImmersion.submersion_iff_components f a hf

theorem submersion_finite : Specs.D04.C04.SubmersionImmersion.submersion_finiteType := by
  intro n m r U f a hr hU hf ha h
  exact SubmersionImmersion.submersion_normal_form r (by exact_mod_cast hr)
    U hU f ((crOn_iff_contDiffOn r U f hU).mp hf) a ha h

theorem submersion_smooth : Specs.D04.C04.SubmersionImmersion.submersion_smoothType := by
  intro n m U f a hU hf ha h
  exact SubmersionImmersion.submersion_normal_form ∞ (by simp)
    U hU f ((smoothOn_iff_contDiffOn U f hU).mp hf) a ha h

theorem immersion_finite : Specs.D04.C04.SubmersionImmersion.immersion_finiteType := by
  intro n m r U f a hr hU hf ha h
  have hf' := (crOn_iff_contDiffOn r U f hU).mp hf
  obtain ⟨hnm, hn, hp⟩ := SubmersionImmersion.immersion_normal_form r (by exact_mod_cast hr)
    U hU f hf' a ha h
  exact ⟨hnm, hn, hp, SubmersionImmersion.embedding_of_normal_form r U f a hnm hf'.continuousOn hn⟩

theorem immersion_smooth : Specs.D04.C04.SubmersionImmersion.immersion_smoothType := by
  intro n m U f a hU hf ha h
  have hf' := (smoothOn_iff_contDiffOn U f hU).mp hf
  obtain ⟨hnm, hn, hp⟩ := SubmersionImmersion.immersion_normal_form ∞ (by simp)
    U hU f hf' a ha h
  exact ⟨hnm, hn, hp, SubmersionImmersion.embedding_of_normal_form ∞ U f a hnm hf'.continuousOn hn⟩

theorem submersion_open_finite : Specs.D04.C04.SubmersionImmersion.submersion_open_finiteType := by
  intro n m r U f hr hU hf h X hX hXU
  exact SubmersionImmersion.open_image_of_submersion r (by exact_mod_cast hr)
    U hU f ((crOn_iff_contDiffOn r U f hU).mp hf) h X hX hXU

theorem submersion_open_smooth : Specs.D04.C04.SubmersionImmersion.submersion_open_smoothType := by
  intro n m U f hU hf h X hX hXU
  exact SubmersionImmersion.open_image_of_submersion ∞ (by simp)
    U hU f ((smoothOn_iff_contDiffOn U f hU).mp hf) h X hX hXU

end D04
