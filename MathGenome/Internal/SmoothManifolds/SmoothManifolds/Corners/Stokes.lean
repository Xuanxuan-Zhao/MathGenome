import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.Stokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.LocalStokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.StructureAndFaces
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Topology Classical

namespace SmoothManifolds.CornerStokesResults
open ModelData LocalStokesData CornerStokesData LocalStokesResults MeasureTheory Set Filter

/-- Orthants have unique within derivatives, including at their corners. -/
theorem orthant_uniqueDiffOn {n : ℕ} (k : Fin (n+1)) :
    UniqueDiffOn ℝ (orthantSet n k) := by
  change UniqueDiffOn ℝ (Set.pi {i : Fin n | i.val < k.val} (fun _ => Ici (0 : ℝ)))
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Ici 0)

theorem orthant_isClosed {n : ℕ} (k : Fin (n+1)) :
    IsClosed (orthantSet n k) := by
  have he : ModelData.orthantSet n k =
      ⋂ i : Fin n, ⋂ (_ : i.val < k.val), {x : Euclidean n | 0 ≤ x i} := by
    ext x
    simp [ModelData.orthantSet]
  change IsClosed (ModelData.orthantSet n k)
  rw [he]
  exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
    isClosed_le (continuous_const : Continuous (fun _ : Euclidean n => (0 : ℝ)))
      (continuous_apply i)))

/-- Scalar divergence on an orthant with compact relative support.
Apply the rectangle divergence theorem to a large box whose constrained lower
bounds are zero. Every artificial face vanishes by the support bound. -/
theorem orthant_divergence {n : ℕ} (k : Fin (n+2))
    (f : Fin (n+1) → Euclidean (n+1) → ℝ)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (orthantSet (n+1) k))
    (K : Set (Euclidean (n+1))) (hK : IsCompact K)
    (hKH : K ⊆ orthantSet (n+1) k)
    (hz : ∀ i x, x ∈ orthantSet (n+1) k → x ∉ K → f i x = 0) :
    IntegrableOn (fun x => ∑ i, fderivWithin ℝ (f i) (orthantSet (n+1) k) x
      (frame (n+1) i)) (orthantSet (n+1) k) ∧
    (∀ i : Fin (n+1), i.val < k.val →
      IntegrableOn (fun y => f i (i.insertNth 0 y)) (orthantFaceSet k i)) ∧
    (∫ x in orthantSet (n+1) k, ∑ i,
      fderivWithin ℝ (f i) (orthantSet (n+1) k) x (frame (n+1) i)) =
      ∑ i : Fin (n+1), if i.val < k.val then
        -(∫ y in orthantFaceSet k i, f i (i.insertNth 0 y)) else 0 := by
  let H := orthantSet (n+1) k
  have hHc : IsClosed H := orthant_isClosed k
  have hud : UniqueDiffOn ℝ H := orthant_uniqueDiffOn k
  let D (i : Fin (n+1)) := fderivWithin ℝ (f i) H
  let d (x : Euclidean (n+1)) := ∑ i, D i x (frame (n+1) i)
  have hdcont : ContinuousOn d H :=
    continuousOn_finsetSum _ (fun i _ =>
      ((hf i).continuousOn_fderivWithin hud (by norm_num)).clm_apply continuousOn_const)
  have hd0 (x : Euclidean (n+1)) (hx : x ∈ H) (hxK : x ∉ K) : d x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    dsimp only [D]
    rw [fderivWithin_zero_off_compact hK (f i) (hz i) hx hxK]
    rfl
  have hdi : IntegrableOn d H :=
    ((hdcont.mono hKH).integrableOn_compact hK).of_forall_sdiff_eq_zero hHc.measurableSet
      (fun x hx => hd0 x hx.1 hx.2)
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 0
  have hbnd (x : Euclidean (n+1)) (hx : x ∈ K) (i : Fin (n+1)) : |x i| < R :=
    (norm_le_pi_norm x i).trans_lt (by simpa using hR hx)
  let a : Euclidean (n+1) := fun i => if i.val < k.val then 0 else -R
  let b : Euclidean (n+1) := fun _ => R
  let B := Icc a b
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    split_ifs <;> linarith
  have hBH : B ⊆ H := by
    intro x hx i hi
    simpa [a, hi] using hx.1 i
  have hKB : K ⊆ B := by
    intro x hx
    constructor
    · intro i
      dsimp [a]
      split_ifs with hi
      · exact hKH hx i hi
      · exact (abs_lt.mp (hbnd x hx i)).1.le
    · intro i
      exact (abs_lt.mp (hbnd x hx i)).2.le
  have hdeq : (∫ x in H, d x) = ∫ x in B, d x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hHc.measurableSet hBH
      (fun x hx => hd0 x hx.1 (fun h => hx.2 (hKB h)))
  have hdf (x : Euclidean (n+1))
      (hx : x ∈ (pi univ fun i => Ioo (a i) (b i)) \ (∅ : Set (Euclidean (n+1))))
      (i : Fin (n+1)) : HasFDerivAt (f i) (D i x) x := by
    have hopen : IsOpen {y : Euclidean (n+1) | ∀ j, j.val < k.val → 0 < y j} :=
      by
        simp only [Set.ofPred_forall]
        exact isOpen_iInter_of_finite (fun j =>
          isOpen_iInter_of_finite (fun _ => isOpen_lt continuous_const (continuous_apply j)))
    have hxpos : x ∈ {y : Euclidean (n+1) | ∀ j, j.val < k.val → 0 < y j} := by
      intro j hj
      simpa [a, hj] using (hx.1 j (mem_univ _)).1
    have hnhds : H ∈ 𝓝 x := mem_of_superset (hopen.mem_nhds hxpos)
      (fun y hy j hj => (hy j hj).le)
    dsimp only [D]
    rw [fderivWithin_of_mem_nhds hnhds]
    exact ((hf i).differentiableOn (by norm_num) x
      (fun j hj => (hxpos j hj).le)).differentiableAt hnhds |>.hasFDerivAt
  have hbox := integral_divergence_of_hasFDerivAt_off_countable' a b hab f D ∅ countable_empty
    (fun i => (hf i).continuousOn.mono hBH) hdf (hdi.mono_set hBH)
  have hfront (i : Fin (n+1)) (x : Euclidean n)
      (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      f i (i.insertNth (b i) x) = 0 := by
    apply hz i
    · apply hBH
      constructor <;> intro j <;> refine Fin.succAboveCases i ?_ (fun r => ?_) j
      · simp only [Fin.insertNth_apply_same]; exact hab i
      · simpa using hx.1 r
      · simp
      · simpa using hx.2 r
    · intro hm
      have ht := (abs_lt.mp (hbnd _ hm i)).2
      simp [b] at ht
  have hback (i : Fin (n+1)) (hi : ¬ i.val < k.val) (x : Euclidean n)
      (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      f i (i.insertNth (a i) x) = 0 := by
    apply hz i
    · apply hBH
      constructor <;> intro j <;> refine Fin.succAboveCases i ?_ (fun r => ?_) j
      · simp
      · simpa using hx.1 r
      · simp only [Fin.insertNth_apply_same]; exact hab i
      · simpa using hx.2 r
    · intro hm
      have ht := (abs_lt.mp (hbnd _ hm i)).1
      simp [a, hi] at ht
  have hface (i : Fin (n+1)) (hi : i.val < k.val) :
      Icc (a ∘ i.succAbove) (b ∘ i.succAbove) ⊆ orthantFaceSet k i := by
    intro y hy
    change i.insertNth (0 : ℝ) y ∈ H
    apply hBH
    simpa [a, hi] using (show i.insertNth (a i) y ∈ B from by
      constructor <;> intro j <;> refine Fin.succAboveCases i ?_ (fun r => ?_) j
      · simp
      · simpa using hy.1 r
      · simp only [Fin.insertNth_apply_same]; exact hab i
      · simpa using hy.2 r)
  have htrace0 (i : Fin (n+1)) (hi : i.val < k.val) (y : Euclidean n)
      (hy : y ∈ orthantFaceSet k i)
      (hyB : y ∉ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) : f i (i.insertNth 0 y) = 0 := by
    apply hz i _ hy
    intro hm
    have hmem := hKB hm
    exact hyB ⟨fun r => by simpa using hmem.1 (i.succAbove r),
      fun r => by simpa using hmem.2 (i.succAbove r)⟩
  have hins (i : Fin (n+1)) : Continuous (fun y : Euclidean n => i.insertNth (α := fun _ => ℝ) (0 : ℝ) y) := by
    apply continuous_pi
    intro j
    refine Fin.succAboveCases i ?_ (fun r => ?_) j
    · simpa using (continuous_const : Continuous (fun _ : Euclidean n => (0 : ℝ)))
    · simpa using (continuous_apply r : Continuous (fun y : Euclidean n => y r))
  have hfaceClosed (i : Fin (n+1)) : IsClosed (orthantFaceSet k i) :=
    hHc.preimage (hins i)
  have htracecont (i : Fin (n+1)) :
      ContinuousOn (fun y : Euclidean n => f i (i.insertNth 0 y)) (orthantFaceSet k i) :=
    (hf i).continuousOn.comp
      (hins i).continuousOn (fun _ hy => hy)
  have htracei (i : Fin (n+1)) (hi : i.val < k.val) :
      IntegrableOn (fun y => f i (i.insertNth 0 y)) (orthantFaceSet k i) :=
    (((htracecont i).mono (hface i hi)).integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero (hfaceClosed i).measurableSet
        (fun y hy => htrace0 i hi y hy.1 hy.2)
  refine ⟨hdi, htracei, ?_⟩
  change (∫ x in H, d x) = _
  rw [hdeq]
  change (∫ x in Icc a b, ∑ i, D i x (Pi.single i 1)) = _
  rw [hbox]
  apply Finset.sum_congr rfl
  intro i _
  rw [setIntegral_eq_zero_of_forall_eq_zero (hfront i), zero_sub]
  split_ifs with hi
  · simp only [a, hi, ite_eq_left]
    congr 1
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hfaceClosed i).measurableSet (hface i hi)
      (fun y hy => htrace0 i hi y hy.1 hy.2)).symm
  · rw [setIntegral_eq_zero_of_forall_eq_zero (hback i hi), neg_zero]

/-- The form coefficient on each outward-oriented coordinate face is -a_i. -/
theorem face_coefficient :
    Specs.SmoothManifolds.Corners.Stokes.face_coefficientType := by
  intro n ω i y
  simp only [orthantBoundaryCoefficient, signedOmittedCoefficient, pow_succ]
  ring

/-- Local Stokes on genuine alternating covectors with local ambient C¹
extensions and compact support in the relative model. -/
theorem local_orthant_stokes :
    Specs.SmoothManifolds.Corners.Stokes.local_orthant_stokesType := by
  intro n k ω hlocal hs
  let H := orthantSet (n+1) k
  have hω : ContDiffOn ℝ 1 ω H := localExtensions_contDiffOn hlocal
  have hud : UniqueDiffOn ℝ H := orthant_uniqueDiffOn k
  let g (i : Fin (n+1)) (x : Euclidean (n+1)) := ω x (i.removeNth (frame (n+1)))
  let f (i : Fin (n+1)) := signedOmittedCoefficient ω i
  have hg (i : Fin (n+1)) : ContDiffOn ℝ 1 (g i) H :=
    (ContinuousAlternatingMap.apply ℝ (Euclidean (n+1)) ℝ
      (i.removeNth (frame (n+1)))).contDiff.comp_contDiffOn hω
  have hf (i : Fin (n+1)) : ContDiffOn ℝ 1 (f i) H :=
    contDiffOn_const.mul (hg i)
  obtain ⟨K, hK, hKH, hz⟩ := relative_support_image H ω hs
  have hzero (i : Fin (n+1)) (x : Euclidean (n+1)) (hx : x ∈ H) (hxK : x ∉ K) :
      f i x = 0 := by
    simp [f, signedOmittedCoefficient, hz x hx hxK]
  obtain ⟨hdi, htri, hstokes⟩ := orthant_divergence k f hf K hK hKH hzero
  have hd (x : Euclidean (n+1)) (hx : x ∈ H) : orthantBulkCoefficient k ω x =
      ∑ i, fderivWithin ℝ (f i) H x (frame (n+1) i) := by
    rw [orthantBulkCoefficient,
      extDerivWithin_apply (hω.differentiableOn (by norm_num) x hx) (hud x hx)]
    apply Finset.sum_congr rfl
    intro i _
    change ((-1 : ℤ)^i.val) • fderivWithin ℝ (g i) H x (frame (n+1) i) =
      fderivWithin ℝ (fun y => (-1 : ℝ)^i.val * g i y) H x (frame (n+1) i)
    rw [fderivWithin_const_mul (hud x hx) ((hg i).differentiableOn (by norm_num) x hx)]
    simp [zsmul_eq_mul]
  have htrace (i : Fin (n+1)) (y : Euclidean n) :
      orthantBoundaryCoefficient ω i y = - f i (i.insertNth 0 y) :=
    face_coefficient n ω i y
  refine ⟨?_, ?_, ?_⟩
  · exact hdi.congr_fun (fun x hx => (hd x hx).symm) (orthant_isClosed k).measurableSet
  · intro i hi
    have he : orthantBoundaryCoefficient ω i = fun y => - f i (i.insertNth 0 y) :=
      funext (htrace i)
    rw [he]
    exact (htri i hi).neg
  · calc
      (∫ x in H, orthantBulkCoefficient k ω x) =
          ∫ x in H, ∑ i, fderivWithin ℝ (f i) H x (frame (n+1) i) :=
        setIntegral_congr_fun (orthant_isClosed k).measurableSet hd
      _ = ∑ i : Fin (n+1), if i.val < k.val then
          -(∫ y in orthantFaceSet k i, f i (i.insertNth 0 y)) else 0 := hstokes
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs
        · simp_rw [htrace]
          rw [integral_neg]
        · rfl

universe u v


open CornerData CornerOrientationData

/-- Multiplication by a scalar function preserves the coordinate gluing law. -/
def weightForm {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ρ : M → ℝ) (ω : CornerStokesData.Form S r) :
    CornerStokesData.Form S r where
  field := fun c hc p => ρ p.val • ω.field c hc p
  compatible := by
    intro c e hc he p hp hq H
    rw [ω.compatible c e hc he p hp hq H]
    ext v
    simp

/-- The closed support of a weighted form is contained in both original
closed supports, on the full corner manifold. -/
theorem weightForm_support {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ρ : M → ℝ) (ω : CornerStokesData.Form S r) :
    formSupport (weightForm ρ ω) ⊆ sectionSupport ρ ∩ formSupport ω := by
  apply closure_minimal _ (isClosed_closure.inter isClosed_closure)
  rintro p ⟨c, hc, hp, h⟩
  constructor
  · apply subset_closure
    intro hz
    exact h (by simp [weightForm, hz])
  · apply subset_closure
    refine ⟨c, hc, hp, ?_⟩
    intro hz
    exact h (by simp [weightForm, hz])

/-- Continuous weights give actual compact continuous top forms. -/
def weightTopForm {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ρ : M → ℝ) (hρ : Continuous ρ)
    (ω : CornerStokesData.CompactTopForm S) : CornerStokesData.CompactTopForm S where
  form := weightForm ρ ω.form
  continuous := fun c hc => (hρ.comp continuous_subtype_val).smul (ω.continuous c hc)
  compact_support := by
    letI := S.hausdorff
    exact ω.compact_support.of_isClosed_subset isClosed_closure
      (fun _ hp => (weightForm_support ρ ω.form hp).2)

/-- Finite sums of continuous weights commute with every linear integral. -/
theorem integral_weight_sum {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {o : CornerOrientation S}
    (I : CornerStokesData.CompactTopForm S → ℝ) (hI : CornerStokesData.IsIntegral o I)
    (ω : CornerStokesData.CompactTopForm S) {ι : Type*}
    (ρ : ι → M → ℝ) (hρ : ∀ i, Continuous (ρ i)) (s : Finset ι) :
    I (weightTopForm (fun p => ∑ i ∈ s, ρ i p)
      (continuous_finsetSum s (fun i _ => hρ i)) ω) =
      ∑ i ∈ s, I (weightTopForm (ρ i) (hρ i) ω) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using hI.2.1 0 ω
      (weightTopForm (fun _ => 0) continuous_const ω) (by intros; rfl)
  | @insert i s hi ih =>
    have he := hI.1 (weightTopForm (ρ i) (hρ i) ω)
      (weightTopForm (fun p => ∑ j ∈ s, ρ j p)
        (continuous_finsetSum s (fun j _ => hρ j)) ω)
      (weightTopForm (fun p => ∑ j ∈ insert i s, ρ j p)
        (continuous_finsetSum _ (fun j _ => hρ j)) ω) (by
          intro c hc p
          change (∑ j ∈ insert i s, ρ j p.val) • ω.form.field c hc p = _
          rw [Finset.sum_insert hi, add_smul]
          rfl)
    rw [he, ih, Finset.sum_insert hi]

/-- Full finite localization on corner forms, conditional only on the defining
linearity and coordinate compatibility of the integral. -/
theorem finite_localization :
    Specs.SmoothManifolds.Corners.Stokes.finite_localizationType.{u} := by
  intro d M _ S o I hI m c hc ρ hρ hsub ω hsum
  let α := fun i => weightTopForm (ρ i) (hρ i) ω
  refine ⟨α, (by intros; rfl), ?_, ?_⟩
  · intro i p hp
    exact hsub i (weightForm_support (ρ i) ω.form hp).1
  · let σ : M → ℝ := fun p => ∑ i : Fin m, ρ i p
    have hσ : Continuous σ := continuous_finsetSum _ (fun i _ => hρ i)
    let ζ := weightTopForm σ hσ ω
    have hsame : I ζ = I ω := by
      have ht := hI.2.1 1 ω ζ (by
        intro e he p
        change σ p.val • ω.form.field e he p = 1 • ω.form.field e he p
        by_cases hz : ω.form.field e he p = 0
        · simp [hz]
        · have hp : p.val ∈ formSupport ω.form := subset_closure ⟨e, he, p.property, hz⟩
          rw [show σ p.val = 1 from hsum p.val hp])
      simpa using ht
    calc
      I ω = I ζ := hsame.symm
      _ = ∑ i : Fin m, I (α i) := integral_weight_sum I hI ω ρ hρ Finset.univ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply hI.2.2 (c i) (hc i) (α i)
        intro p hp
        exact hsub i (weightForm_support (ρ i) ω.form hp).1

/-- A compact subset admits a finite continuous chart localization.
This uses only the full locally-compact conclusion supplied by the frozen
geometry interface. Smooth localizers are still needed for global Stokes. -/
theorem finite_chart_localizers
    {d : ℕ} {M : Type u} [TopologicalSpace M] (S : CornerManifold d M)
    (K : Set M) (hK : IsCompact K) :
    ∃ (m : ℕ) (c : Fin m → CornerChart d M) (hc : ∀ i, c i ∈ S.atlas)
      (ρ : Fin m → M → ℝ), (∀ i, Continuous (ρ i)) ∧
      (∀ i, sectionSupport (ρ i) ⊆ (c i).2.source) ∧
      ∀ p ∈ K, ∑ i, ρ i p = 1 := by
  letI := S.hausdorff
  letI : LocallyCompactSpace M := Corners.locally_compact S
  let A := {c : CornerChart d M // c ∈ S.atlas}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : A => c.val.2.source) (fun c => c.val.2.open_source) (by
      intro p _
      obtain ⟨c, hc, hp⟩ := S.maximal.1.1 p
      exact mem_iUnion.mpr ⟨⟨c,hc⟩,hp⟩)
  let m := Fintype.card t
  let e : Fin m ≃ t := (Fintype.equivFin t).symm
  let c : Fin m → CornerChart d M := fun i => (e i).val.val
  have hcov : K ⊆ ⋃ i : Fin m, (c i).2.source := by
    intro p hp
    obtain ⟨a, ha, hap⟩ := mem_iUnion₂.mp (ht hp)
    refine mem_iUnion.mpr ⟨e.symm ⟨a,ha⟩, ?_⟩
    change p ∈ (e (e.symm ⟨a,ha⟩)).val.val.2.source
    rw [e.apply_symm_apply]
    exact hap
  obtain ⟨ρ, hsub, hsum, _, _⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun i : Fin m => (c i).2.open_source) hK hcov
  refine ⟨m, c, (fun i => (e i).val.property), (fun i p => ρ i p),
    (fun i => (ρ i).continuous), hsub, ?_⟩
  intro p hp
  simpa using hsum hp

/-- Any two coordinate-compatible integrals agree by finite localization. -/
theorem unique_integral :
    Specs.SmoothManifolds.Corners.Stokes.unique_integralType.{u} := by
  intro d M _ S o I J hI hJ
  funext ω
  obtain ⟨m, c, hc, ρ, hρ, hsub, hsum⟩ :=
    finite_chart_localizers S (formSupport ω.form) ω.compact_support
  let α := fun i => weightTopForm (ρ i) (hρ i) ω
  let σ : M → ℝ := fun p => ∑ i : Fin m, ρ i p
  have hσ : Continuous σ := continuous_finsetSum _ (fun i _ => hρ i)
  let ζ := weightTopForm σ hσ ω
  have hsame : ∀ L : CornerStokesData.CompactTopForm S → ℝ,
      CornerStokesData.IsIntegral o L → L ζ = L ω := by
    intro L hL
    have ht := hL.2.1 1 ω ζ (by
      intro a ha p
      change σ p.val • ω.form.field a ha p = 1 • ω.form.field a ha p
      by_cases hz : ω.form.field a ha p = 0
      · simp [hz]
      · have hp : p.val ∈ formSupport ω.form := subset_closure ⟨a,ha,p.property,hz⟩
        rw [show σ p.val = 1 from hsum p.val hp])
    simpa using ht
  have hterm (i : Fin m) : I (α i) = J (α i) := by
    have hsupp : formSupport (α i).form ⊆ (c i).2.source :=
      fun p hp => hsub i (weightForm_support (ρ i) ω.form hp).1
    exact (hI.2.2 (c i) (hc i) (α i) hsupp).trans
      (hJ.2.2 (c i) (hc i) (α i) hsupp).symm
  calc
    I ω = I ζ := (hsame I hI).symm
    _ = ∑ i : Fin m, I (α i) := integral_weight_sum I hI ω ρ hρ Finset.univ
    _ = ∑ i : Fin m, J (α i) := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = J ζ := (integral_weight_sum J hJ ω ρ hρ Finset.univ).symm
    _ = J ω := hsame J hJ



/-- Signed coefficients at points in the actual chart domain. -/
theorem chartCoefficient_at {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (ω : CornerStokesData.Form S d)
    (p : M) (hp : p ∈ c.2.source) :
    chartCoefficient o c hc ω (c.2 p).val =
      OrientationData.signValue (o.sign c hc ⟨p,hp⟩) * ω.field c hc ⟨p,hp⟩ (frame d) := by
  simp only [chartCoefficient, (c.2 p).property, dite_true, c.2.map_source hp]
  have hpoint : (⟨c.2.symm (c.2 p), c.2.map_target (c.2.map_source hp)⟩ : c.2.source) =
      ⟨p,hp⟩ := Subtype.ext (c.2.left_inv hp)
  rw [hpoint]

/-- All nonzero signed coordinate values lie in the image of the closed support. -/
theorem chartCoefficient_support {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (ω : CornerStokesData.Form S d) :
    Function.support (chartCoefficient o c hc ω) ⊆
      (fun p : M => (c.2 p).val) '' formSupport ω := by
  intro x hx
  by_cases hm : x ∈ orthantSet d c.1
  · by_cases ht : (⟨x,hm⟩ : Orthant d c.1) ∈ c.2.target
    · refine ⟨c.2.symm ⟨x,hm⟩, subset_closure ⟨c,hc,c.2.map_target ht,?_⟩, ?_⟩
      · intro hz
        exact hx (by simp [chartCoefficient, hm, ht, hz])
      · exact congrArg Subtype.val (c.2.right_inv ht)
    · exact (hx (by simp [chartCoefficient, hm, ht])).elim
  · exact (hx (by simp [chartCoefficient, hm])).elim

/-- Continuous coefficients on the source become continuous coefficients on
compact subsets of its image, including the genuine coordinate faces. -/
theorem chartCoefficient_continuousOn_image
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (ω : CornerStokesData.CompactTopForm S)
    (K : Set M) (hKc : K ⊆ c.2.source) :
    ContinuousOn (chartCoefficient o c hc ω.form) ((fun p : M => (c.2 p).val) '' K) := by
  let C := (fun p : M => (c.2 p).val) '' K
  have hm (x : C) : x.val ∈ orthantSet d c.1 := by
    obtain ⟨p, hp, heq⟩ := x.property
    rw [← heq]
    exact (c.2 p).property
  have ht (x : C) : (⟨x.val,hm x⟩ : Orthant d c.1) ∈ c.2.target := by
    obtain ⟨p, hp, heq⟩ := x.property
    have he : (⟨x.val,hm x⟩ : Orthant d c.1) = c.2 p := Subtype.ext heq.symm
    rw [he]
    exact c.2.map_source (hKc hp)
  let y : C → c.2.target := fun x => ⟨⟨x.val,hm x⟩,ht x⟩
  have hy : Continuous y := (continuous_subtype_val.subtype_mk _).subtype_mk _
  let f : c.2.source → ℝ := fun p =>
    OrientationData.signValue (o.sign c hc p) * ω.form.field c hc p (frame d)
  have hf : Continuous f :=
    ((o.locallyConstant c hc).comp OrientationData.signValue).continuous.mul
      ((ContinuousAlternatingMap.apply ℝ (Euclidean d) ℝ (frame d)).continuous.comp
        (ω.continuous c hc))
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hf.comp (c.2.toHomeomorphSourceTarget.symm.continuous.comp hy) using 1
  funext x
  simp only [Set.domRestrict_apply, chartCoefficient, hm x, dite_true, ht x,
    Function.comp_apply]
  rfl

/-- Compact support in the full manifold gives integrability of the zero
extended coefficient; support on true corner faces is allowed. -/
theorem coordinate_integrable :
    Specs.SmoothManifolds.Corners.Stokes.coordinate_integrableType.{u} := by
  intro d M _ S o c hc ω hω
  have hC : IsCompact ((fun p : M => (c.2 p).val) '' formSupport ω.form) :=
    ω.compact_support.image_of_continuousOn
      (continuous_subtype_val.comp_continuousOn (c.2.continuousOn.mono hω))
  exact (integrableOn_iff_integrable_of_support_subset
    (chartCoefficient_support o c hc ω.form)).mp
    ((chartCoefficient_continuousOn_image o c hc ω _ hω).integrableOn_compact hC)


/-- Ambient image of a relatively open orthant patch. -/
def cornerAmbientDomain {d : ℕ} {k : Fin (d+1)} (U : Set (Orthant d k)) :
    Set (Euclidean d) := Subtype.val '' U

/-- The actual transition, represented as a total ambient function. -/
def cornerAmbientTransition {d : ℕ} {k l : Fin (d+1)}
    (e : OpenPartialHomeomorph (Orthant d k) (Orthant d l)) (x : Euclidean d) :
    Euclidean d := if hx : x ∈ orthantSet d k then (e ⟨x,hx⟩).val else 0

theorem cornerAmbientTransition_at {d : ℕ} {k l : Fin (d+1)}
    (e : OpenPartialHomeomorph (Orthant d k) (Orthant d l)) (x : Orthant d k) :
    cornerAmbientTransition e x.val = (e x).val := by
  simp [cornerAmbientTransition, x.property]

theorem cornerAmbientDomain_measurable {d : ℕ} {k : Fin (d+1)}
    {U : Set (Orthant d k)} (hU : IsOpen U) :
    MeasurableSet (cornerAmbientDomain U) := by
  obtain ⟨V,hV,he⟩ := hU.image_val
  change MeasurableSet (Subtype.val '' U)
  rw [he]
  exact hV.measurableSet.inter (orthant_isClosed k).measurableSet

theorem cornerAmbientDomain_uniqueDiffOn {d : ℕ} {k : Fin (d+1)}
    {U : Set (Orthant d k)} (hU : IsOpen U) :
    UniqueDiffOn ℝ (cornerAmbientDomain U) := by
  obtain ⟨V,hV,he⟩ := hU.image_val
  change UniqueDiffOn ℝ (Subtype.val '' U)
  rw [he, inter_comm]
  exact (orthant_uniqueDiffOn k).inter hV

theorem cornerAmbientTransition_injective {d : ℕ} {k l : Fin (d+1)}
    (e : OpenPartialHomeomorph (Orthant d k) (Orthant d l)) :
    InjOn (cornerAmbientTransition e) (cornerAmbientDomain e.source) := by
  rintro x ⟨p,hp,rfl⟩ y ⟨q,hq,rfl⟩ he
  rw [cornerAmbientTransition_at, cornerAmbientTransition_at] at he
  exact congrArg Subtype.val (e.injOn hp hq (Subtype.ext he))

theorem cornerAmbientTransition_image {d : ℕ} {k l : Fin (d+1)}
    (e : OpenPartialHomeomorph (Orthant d k) (Orthant d l)) :
    cornerAmbientTransition e '' cornerAmbientDomain e.source =
      cornerAmbientDomain e.target := by
  ext y
  constructor
  · rintro ⟨x,⟨p,hp,rfl⟩,rfl⟩
    rw [cornerAmbientTransition_at]
    exact ⟨e p,e.map_source hp,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    refine ⟨(e.symm q).val,⟨e.symm q,e.map_target hq,rfl⟩,?_⟩
    rw [cornerAmbientTransition_at,e.right_inv hq]

/-- The local ambient extension differentiates the genuine transition within
its actual domain, without deleting the lower dimensional strata. -/
theorem cornerAmbientTransition_hasFDerivWithinAt {d : ℕ} {k l : Fin (d+1)}
    (e : OpenPartialHomeomorph (Orthant d k) (Orthant d l))
    (x : Orthant d k) (hx : x ∈ e.source) (H : OrthantExtension e.source e x) :
    HasFDerivWithinAt (cornerAmbientTransition e) (fderiv ℝ H.map x.val)
      (cornerAmbientDomain e.source) x.val := by
  have hd := ((H.smooth.differentiableOn (by simp) x.val H.mem_domain).differentiableAt
    (H.isOpen_domain.mem_nhds H.mem_domain)).hasFDerivAt.hasFDerivWithinAt
      (s := cornerAmbientDomain e.source)
  refine hd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (H.isOpen_domain.mem_nhds H.mem_domain)] with y hy hyU
    obtain ⟨z,hz,rfl⟩ := hy
    rw [cornerAmbientTransition_at, H.agrees z hz hyU]
  · rw [cornerAmbientTransition_at, H.agrees x hx H.mem_domain]

theorem cornerAmbientTransition_differentiable {d : ℕ} {k l : Fin (d+1)}
    (e : OpenPartialHomeomorph (Orthant d k) (Orthant d l))
    (he : OrthantMapContDiffOn (⊤ : ℕ∞) e.source (fun x => e x.val)) :
    DifferentiableOn ℝ (cornerAmbientTransition e) (cornerAmbientDomain e.source) := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨U,hU,hyU,F,hF,heq⟩ := he ⟨y,hy⟩
  let H : OrthantExtension e.source e y :=
    ⟨U,hU,hyU,F,hF,fun z hz hzU => heq ⟨z,hz⟩ hzU⟩
  exact (cornerAmbientTransition_hasFDerivWithinAt e y hy H).differentiableWithinAt

/-- The determinant law for a genuine top alternating covector. -/
theorem evaluate_frame_comp {d : ℕ}
    (α : (Euclidean d) [⋀^Fin d]→L[ℝ] ℝ)
    (L : Euclidean d →L[ℝ] Euclidean d) :
    α (fun i => L (frame d i)) = α (frame d) * L.det := by
  have hframe : frame d = Pi.basisFun ℝ (Fin d) := by
    funext i
    simp [frame, Pi.basisFun_apply]
  rw [hframe]
  change α.toAlternatingMap (L.toLinearMap ∘ (Pi.basisFun ℝ (Fin d))) = _
  rw [α.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin d))]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one]
  rfl

/-- Form and orientation transformation laws cancel the absolute Jacobian. -/
theorem chartCoefficient_transition {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c e : CornerChart d M) (hc : c ∈ S.atlas) (he : e ∈ S.atlas)
    (ω : CornerStokesData.Form S d) (p : M) (hp : p ∈ c.2.source) (hq : p ∈ e.2.source)
    (H : OrthantExtension (c.2.symm.trans e.2).source (c.2.symm.trans e.2) (c.2 p)) :
    |(fderiv ℝ H.map (c.2 p).val).det| * chartCoefficient o e he ω (e.2 p).val =
      chartCoefficient o c hc ω (c.2 p).val := by
  rw [chartCoefficient_at o e he ω p hq, chartCoefficient_at o c hc ω p hp]
  have hω : ω.field c hc ⟨p,hp⟩ (frame d) =
      ω.field e he ⟨p,hq⟩ (frame d) * (fderiv ℝ H.map (c.2 p).val).det := by
    rw [ω.compatible c e hc he p hp hq H]
    exact evaluate_frame_comp _ _
  rw [hω]
  have hs := o.compatible c e hc he p hp hq H
  rw [CornerFaceOrientations.real_sign_eq_signType] at hs
  rw [hs]
  calc
    _ = OrientationData.signValue (o.sign c hc ⟨p,hp⟩) *
        (ω.field e he ⟨p,hq⟩ (frame d) *
          ((SignType.sign (fderiv ℝ H.map (c.2 p).val).det : ℝ) *
            |(fderiv ℝ H.map (c.2 p).val).det|)) := by ring
    _ = _ := by rw [sign_mul_abs]


/-- Nonzero coefficients lie in an overlap if the form is supported there. -/
theorem chartCoefficient_support_overlap {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c e : CornerChart d M) (hc : c ∈ S.atlas) (ω : CornerStokesData.Form S d)
    (hω : formSupport ω ⊆ c.2.source ∩ e.2.source) :
    Function.support (chartCoefficient o c hc ω) ⊆
      cornerAmbientDomain (c.2.symm.trans e.2).source := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := chartCoefficient_support o c hc ω hx
  refine ⟨c.2 p,⟨c.2.map_source (hω hp).1,?_⟩,rfl⟩
  change c.2.symm (c.2 p) ∈ e.2.source
  rw [c.2.left_inv (hω hp).1]
  exact (hω hp).2

/-- Signed coordinate integration agrees on corner chart overlaps. This uses
measurable-set substitution and therefore retains the genuine corner faces. -/
theorem chartIntegral_eq {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c e : CornerChart d M) (hc : c ∈ S.atlas) (he : e ∈ S.atlas)
    (ω : CornerStokesData.Form S d)
    (hcω : formSupport ω ⊆ c.2.source) (heω : formSupport ω ⊆ e.2.source) :
    chartIntegral o c hc ω = chartIntegral o e he ω := by
  let t := c.2.symm.trans e.2
  let U := cornerAmbientDomain t.source
  let V := cornerAmbientDomain t.target
  let ψ := cornerAmbientTransition t
  let D := fderivWithin ℝ ψ U
  let f := chartCoefficient o c hc ω
  let g := chartCoefficient o e he ω
  have hU : MeasurableSet U := cornerAmbientDomain_measurable t.open_source
  have hD : ∀ x ∈ U, HasFDerivWithinAt ψ (D x) U x :=
    fun x hx => (cornerAmbientTransition_differentiable t
      (S.maximal.1.2 c hc e he).1 x hx).hasFDerivWithinAt
  have hfg : ∀ x ∈ U, |(D x).det| * g (ψ x) = f x := by
    rintro x ⟨y,hy,rfl⟩
    have hp : c.2.symm y ∈ c.2.source := c.2.map_target hy.1
    have hq : c.2.symm y ∈ e.2.source := hy.2
    let p := c.2.symm y
    have hcy : c.2 p = y := c.2.right_inv hy.1
    obtain ⟨W,hW,hyW,F,hF,heq⟩ := (S.maximal.1.2 c hc e he).1 ⟨y,hy⟩
    let H : OrthantExtension t.source t y :=
      ⟨W,hW,hyW,F,hF,fun z hz hzW => heq ⟨z,hz⟩ hzW⟩
    have hDy : D y.val = fderiv ℝ H.map y.val :=
      (cornerAmbientTransition_hasFDerivWithinAt t y hy H).fderivWithin
        (cornerAmbientDomain_uniqueDiffOn t.open_source y.val ⟨y,hy,rfl⟩)
    have hψy : ψ y.val = (e.2 p).val := cornerAmbientTransition_at t y
    rw [hDy,hψy]
    change |(fderiv ℝ H.map y.val).det| * chartCoefficient o e he ω (e.2 p).val =
      chartCoefficient o c hc ω y.val
    let Hc : OrthantExtension t.source t (c.2 p) :=
      ⟨W,hW,(by rw [hcy]; exact hyW),F,hF,fun z hz hzW => heq ⟨z,hz⟩ hzW⟩
    have ht := chartCoefficient_transition o c e hc he ω p hp hq Hc
    change |(fderiv ℝ F (c.2 p).val).det| * chartCoefficient o e he ω (e.2 p).val =
      chartCoefficient o c hc ω (c.2 p).val at ht
    rw [hcy] at ht
    exact ht
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hD
    (cornerAmbientTransition_injective t) g
  rw [cornerAmbientTransition_image t] at hsub
  have hfU : Function.support f ⊆ U :=
    chartCoefficient_support_overlap o c e hc ω (fun p hp => ⟨hcω hp,heω hp⟩)
  have hgV : Function.support g ⊆ V := by
    have hh := chartCoefficient_support_overlap o e c he ω (fun p hp => ⟨heω hp,hcω hp⟩)
    have ht : t.symm = e.2.symm.trans c.2 := by
      simp only [t, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
    rw [← ht] at hh
    exact hh
  have hfint : (∫ x in U, f x) = ∫ x, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (hfU hn)))
  have hgint : (∫ x in V, g x) = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (hgV hn)))
  change ∫ x, f x = ∫ x, g x
  rw [← hfint,← hgint,hsub]
  exact setIntegral_congr_fun hU (fun x hx => (hfg x hx).symm)


theorem chartIntegral_congr {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (α β : CornerStokesData.Form S d)
    (h : ∀ e he p, α.field e he p = β.field e he p) :
    chartIntegral o c hc α = chartIntegral o c hc β := by
  unfold chartIntegral
  congr 1
  funext x
  unfold chartCoefficient
  split_ifs <;> simp [h]

theorem chartIntegral_add {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (α β γ : CompactTopForm S)
    (hα : formSupport α.form ⊆ c.2.source) (hβ : formSupport β.form ⊆ c.2.source)
    (h : ∀ e he p, γ.form.field e he p = α.form.field e he p + β.form.field e he p) :
    chartIntegral o c hc γ.form = chartIntegral o c hc α.form + chartIntegral o c hc β.form := by
  have heq : chartCoefficient o c hc γ.form =
      fun x => chartCoefficient o c hc α.form x + chartCoefficient o c hc β.form x := by
    funext x
    unfold chartCoefficient
    split_ifs <;> simp [h, mul_add]
  unfold chartIntegral
  rw [heq]
  exact integral_add (coordinate_integrable S o c hc α hα) (coordinate_integrable S o c hc β hβ)

theorem chartIntegral_smul {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (a : ℝ) (α β : CompactTopForm S)
    (h : ∀ e he p, β.form.field e he p = a • α.form.field e he p) :
    chartIntegral o c hc β.form = a * chartIntegral o c hc α.form := by
  have heq : chartCoefficient o c hc β.form =
      fun x => a * chartCoefficient o c hc α.form x := by
    funext x
    unfold chartCoefficient
    split_ifs <;> simp [h, mul_left_comm]
  unfold chartIntegral
  rw [heq, integral_const_mul]

/-- Finite continuous localization inside one chart commutes with its Lebesgue integral. -/
theorem chartIntegral_localization {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (ω : CompactTopForm S)
    (hω : formSupport ω.form ⊆ c.2.source) {m : ℕ}
    (ρ : Fin m → M → ℝ) (hρ : ∀ i, Continuous (ρ i))
    (hsum : ∀ p ∈ formSupport ω.form, ∑ i, ρ i p = 1) :
    chartIntegral o c hc ω.form =
      ∑ i, chartIntegral o c hc (weightTopForm (ρ i) (hρ i) ω).form := by
  have heq : chartCoefficient o c hc ω.form = fun x =>
      ∑ i, chartCoefficient o c hc (weightTopForm (ρ i) (hρ i) ω).form x := by
    funext x
    unfold chartCoefficient
    split_ifs with hx ht
    · let p : c.2.source := ⟨c.2.symm ⟨x,hx⟩, c.2.map_target ht⟩
      change OrientationData.signValue (o.sign c hc p) * ω.form.field c hc p (frame d) =
        ∑ i, OrientationData.signValue (o.sign c hc p) *
          (ρ i p.val • ω.form.field c hc p) (frame d)
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      by_cases hz : ω.form.field c hc p = 0
      · simp [hz]
      · have hs := hsum p.val (subset_closure ⟨c,hc,p.property,hz⟩)
        rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, hs, one_mul]
    · simp
    · simp
  unfold chartIntegral
  rw [heq]
  exact integral_finsetSum _ (fun i _ => coordinate_integrable S o c hc _
    (fun p hp => hω (weightForm_support (ρ i) ω.form hp).2))

/-- A finite chart localization, specified on a compact set in the full base. -/
structure FiniteChartLocalization {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (K : Set M) where
  count : ℕ
  chart : Fin count → CornerChart d M
  mem_atlas : ∀ i, chart i ∈ S.atlas
  weight : Fin count → M → ℝ
  continuous : ∀ i, Continuous (weight i)
  support : ∀ i, sectionSupport (weight i) ⊆ (chart i).2.source
  sum_one : ∀ p ∈ K, ∑ i, weight i p = 1

def chooseLocalization {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (K : Set M) (hK : IsCompact K) :
    FiniteChartLocalization S K := Classical.choice <| by
  obtain ⟨m,c,hc,ρ,hρ,hsub,hsum⟩ := finite_chart_localizers S K hK
  exact ⟨⟨m,c,hc,ρ,hρ,hsub,hsum⟩⟩

def localizationIntegral {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {K : Set M} (o : CornerOrientation S)
    (L : FiniteChartLocalization S K) (ω : CompactTopForm S) : ℝ :=
  ∑ i, chartIntegral o (L.chart i) (L.mem_atlas i)
    (weightTopForm (L.weight i) (L.continuous i) ω).form

/-- Common refinement proves independence from all finite localizing choices. -/
theorem localizationIntegral_eq {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {K H : Set M} (o : CornerOrientation S)
    (L : FiniteChartLocalization S K) (R : FiniteChartLocalization S H)
    (ω : CompactTopForm S) (hK : formSupport ω.form ⊆ K) (hH : formSupport ω.form ⊆ H) :
    localizationIntegral o L ω = localizationIntegral o R ω := by
  let α (i : Fin L.count) := weightTopForm (L.weight i) (L.continuous i) ω
  let β (j : Fin R.count) := weightTopForm (R.weight j) (R.continuous j) ω
  have hα (i : Fin L.count) : formSupport (α i).form ⊆ (L.chart i).2.source :=
    fun _ hp => L.support i (weightForm_support _ _ hp).1
  have hβ (j : Fin R.count) : formSupport (β j).form ⊆ (R.chart j).2.source :=
    fun _ hp => R.support j (weightForm_support _ _ hp).1
  unfold localizationIntegral
  change (∑ i, chartIntegral o (L.chart i) (L.mem_atlas i) (α i).form) =
    ∑ j, chartIntegral o (R.chart j) (R.mem_atlas j) (β j).form
  calc
    _ = ∑ i, ∑ j, chartIntegral o (L.chart i) (L.mem_atlas i)
        (weightTopForm (R.weight j) (R.continuous j) (α i)).form := by
      apply Finset.sum_congr rfl
      intro i _
      exact chartIntegral_localization o _ _ _ (hα i) R.weight R.continuous
        (fun p hp => R.sum_one p (hH (weightForm_support _ _ hp).2))
    _ = ∑ i, ∑ j, chartIntegral o (R.chart j) (R.mem_atlas j)
        (weightTopForm (L.weight i) (L.continuous i) (β j)).form := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have heq := chartIntegral_eq o (L.chart i) (R.chart j) (L.mem_atlas i) (R.mem_atlas j)
        (weightTopForm (R.weight j) (R.continuous j) (α i)).form
        (fun p hp => hα i (weightForm_support _ _ hp).2)
        (fun p hp => R.support j (weightForm_support _ _ hp).1)
      refine heq.trans (chartIntegral_congr o _ _ _ _ ?_)
      intro e he p
      change R.weight j p.val • L.weight i p.val • ω.form.field e he p =
        L.weight i p.val • R.weight j p.val • ω.form.field e he p
      exact smul_comm _ _ _
    _ = ∑ j, ∑ i, chartIntegral o (R.chart j) (R.mem_atlas j)
        (weightTopForm (L.weight i) (L.continuous i) (β j)).form := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (chartIntegral_localization o _ _ _ (hβ j) L.weight L.continuous
        (fun p hp => L.sum_one p (hK (weightForm_support _ _ hp).2))).symm

theorem localizationIntegral_add {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {K : Set M} (o : CornerOrientation S)
    (L : FiniteChartLocalization S K) (α β γ : CompactTopForm S)
    (h : ∀ e he p, γ.form.field e he p = α.form.field e he p + β.form.field e he p) :
    localizationIntegral o L γ = localizationIntegral o L α + localizationIntegral o L β := by
  unfold localizationIntegral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply chartIntegral_add
  · exact fun p hp => L.support i (weightForm_support _ _ hp).1
  · exact fun p hp => L.support i (weightForm_support _ _ hp).1
  · intro e he p
    change L.weight i p.val • γ.form.field e he p =
      L.weight i p.val • α.form.field e he p + L.weight i p.val • β.form.field e he p
    rw [h, smul_add]

theorem localizationIntegral_smul {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {K : Set M} (o : CornerOrientation S)
    (L : FiniteChartLocalization S K) (a : ℝ) (α β : CompactTopForm S)
    (h : ∀ e he p, β.form.field e he p = a • α.form.field e he p) :
    localizationIntegral o L β = a * localizationIntegral o L α := by
  unfold localizationIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply chartIntegral_smul
  intro e he p
  change L.weight i p.val • β.form.field e he p = a • L.weight i p.val • α.form.field e he p
  rw [h, smul_comm]

theorem localizationIntegral_coordinate {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {K : Set M} (o : CornerOrientation S)
    (L : FiniteChartLocalization S K) (ω : CompactTopForm S)
    (hK : formSupport ω.form ⊆ K) (c : CornerChart d M) (hc : c ∈ S.atlas)
    (hω : formSupport ω.form ⊆ c.2.source) :
    localizationIntegral o L ω = chartIntegral o c hc ω.form := by
  unfold localizationIntegral
  calc
    _ = ∑ i, chartIntegral o c hc (weightTopForm (L.weight i) (L.continuous i) ω).form := by
      apply Finset.sum_congr rfl
      intro i _
      apply chartIntegral_eq
      · exact fun p hp => L.support i (weightForm_support _ _ hp).1
      · exact fun p hp => hω (weightForm_support _ _ hp).2
    _ = _ := (chartIntegral_localization o c hc ω hω L.weight L.continuous
      (fun p hp => L.sum_one p (hK hp))).symm

/-- The integral is defined by finite chart localization of the full compact support. -/
def cornerIntegral {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : CompactTopForm S) : ℝ :=
  localizationIntegral o (chooseLocalization S (formSupport ω.form) ω.compact_support) ω

theorem cornerIntegral_eq_localization {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {K : Set M} (o : CornerOrientation S)
    (L : FiniteChartLocalization S K) (ω : CompactTopForm S)
    (hK : formSupport ω.form ⊆ K) : cornerIntegral o ω = localizationIntegral o L ω :=
  localizationIntegral_eq o _ L ω Subset.rfl hK

/-- Existence uses common refinement, while uniqueness uses the established finite localization. -/
theorem exists_integral : Specs.SmoothManifolds.Corners.Stokes.exists_integralType.{u} := by
  intro d M _ S o
  have hI : IsIntegral o (cornerIntegral o) := by
    constructor
    · intro α β γ hγ
      let K := (formSupport α.form ∪ formSupport β.form) ∪ formSupport γ.form
      have hK : IsCompact K := (α.compact_support.union β.compact_support).union γ.compact_support
      let L := chooseLocalization S K hK
      have hα : formSupport α.form ⊆ K := fun p hp => Or.inl (Or.inl hp)
      have hβ : formSupport β.form ⊆ K := fun p hp => Or.inl (Or.inr hp)
      have hγK : formSupport γ.form ⊆ K := fun p hp => Or.inr hp
      rw [cornerIntegral_eq_localization o L α hα, cornerIntegral_eq_localization o L β hβ,
        cornerIntegral_eq_localization o L γ hγK]
      exact localizationIntegral_add o L α β γ hγ
    · constructor
      · intro a α β hβ
        let K := formSupport α.form ∪ formSupport β.form
        let L := chooseLocalization S K (α.compact_support.union β.compact_support)
        rw [cornerIntegral_eq_localization o L α (fun _ hp => Or.inl hp),
          cornerIntegral_eq_localization o L β (fun _ hp => Or.inr hp)]
        exact localizationIntegral_smul o L a α β hβ
      · intro c hc ω hω
        exact localizationIntegral_coordinate o _ ω Subset.rfl c hc hω
  exact ⟨cornerIntegral o, hI, fun J hJ => unique_integral S o J (cornerIntegral o) hJ hI⟩


theorem chart_independence :
    Specs.SmoothManifolds.Corners.Stokes.chart_independenceType.{u} := by
  intro d M _ S o c e hc he ω hωc hωe
  exact chartIntegral_eq o c e hc he ω hωc hωe

theorem ambientForm_at {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (p : c.2.source) :
    ambientForm ω c hc (c.2 p.val).val = ω.field c hc p := by
  simp only [ambientForm, (c.2 p.val).property, dite_true,
    c.2.map_source p.property]
  congr 1
  exact Subtype.ext (c.2.left_inv p.property)

theorem regularForm_continuous {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (s : ℕ∞) (hω : IsRegularForm s ω)
    (c : CornerChart n M) (hc : c ∈ S.atlas) : Continuous (ω.field c hc) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U,hU,hpU,F,hF,he⟩ := hω c hc p
  have hcoord : ContinuousAt (fun q : c.2.source => (c.2 q.val).val) p :=
    (continuous_subtype_val.continuousAt.comp (c.2.continuousAt p.property)).comp
      continuousAt_subtype_val
  apply ((hF.continuousOn.continuousAt (hU.mem_nhds hpU)).comp
    (f := fun q : c.2.source => (c.2 q.val).val) hcoord).congr
  filter_upwards [hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hq
  exact he q hq

theorem ambientForm_contDiffOn {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (s : ℕ∞) (hω : IsRegularForm s ω)
    (c : CornerChart n M) (hc : c ∈ S.atlas) :
    ContDiffOn ℝ s (ambientForm ω c hc) (Subtype.val '' c.2.target) := by
  apply localExtensions_contDiffOn
  rintro ⟨x, q, hq, rfl⟩
  obtain ⟨U,hU,hpU,F,hF,he⟩ := hω c hc ⟨c.2.symm q,c.2.map_target hq⟩
  refine ⟨U,hU,?_,F,hF,?_⟩
  · simpa only [c.2.right_inv hq] using hpU
  · rintro ⟨y,z,hz,rfl⟩ hyU
    simp only [ambientForm,z.property,dite_true,hz]
    simpa only [c.2.right_inv hz] using
      he ⟨c.2.symm z,c.2.map_target hz⟩ (by simpa only [c.2.right_inv hz] using hyU)

theorem uniqueDiffOn_orthantDomain {n : ℕ} {c : Fin (n+1)}
    {s : Set (Orthant n c)} (hs : IsOpen s) :
    UniqueDiffOn ℝ (Subtype.val '' s : Set (Euclidean n)) := by
  obtain ⟨U,hU,hEq⟩ := hs.image_val
  rw [hEq,inter_comm]
  have horth : UniqueDiffOn ℝ (orthantSet n c) := by
    change UniqueDiffOn ℝ (Set.pi {i : Fin n | i.val < c.val} (fun _ => Ici (0 : ℝ)))
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Ici 0)
  exact horth.inter hU

theorem ambientForm_extension_derivative {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r)
    (c : CornerChart n M) (hc : c ∈ S.atlas) (p : c.2.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c.2 p.val).val ∈ U)
    (F : Euclidean n → (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ)
    (hF : ContDiffOn ℝ 1 F U)
    (he : ∀ q : c.2.source, (c.2 q.val).val ∈ U → F (c.2 q.val).val = ω.field c hc q) :
    extDerivWithin (ambientForm ω c hc) (Subtype.val '' c.2.target) (c.2 p.val).val =
      extDeriv F (c.2 p.val).val := by
  have hmem : (c.2 p.val).val ∈ Subtype.val '' c.2.target :=
    ⟨c.2 p.val,c.2.map_source p.property,rfl⟩
  have hloc : ambientForm ω c hc =ᶠ[𝓝[Subtype.val '' c.2.target] (c.2 p.val).val] F := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hU.mem_nhds hpU)] with x hx hxU
    obtain ⟨q,hq,rfl⟩ := hx
    simp only [ambientForm,q.property,dite_true,hq]
    simpa only [c.2.right_inv hq] using
      (he ⟨c.2.symm q,c.2.map_target hq⟩ (by simpa only [c.2.right_inv hq] using hxU)).symm
  unfold extDerivWithin extDeriv
  rw [hloc.fderivWithin_eq_of_mem hmem]
  rw [((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num)).fderivWithin
    (uniqueDiffOn_orthantDomain c.2.open_target _ hmem)]

theorem derivative_continuous {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (hω : IsRegularForm 1 ω)
    (η : Form S (r+1)) (hη : HasDerivative ω η)
    (c : CornerChart n M) (hc : c ∈ S.atlas) : Continuous (η.field c hc) := by
  have hcω := ambientForm_contDiffOn ω 1 hω c hc
  have hcont := hcω.continuousOn_fderivWithin
    (uniqueDiffOn_orthantDomain c.2.open_target) (by norm_num)
  have hchart : Continuous (fun p : c.2.source => (c.2 p.val).val) :=
    continuous_subtype_val.comp c.2.continuousOn.domRestrict
  have hderiv : Continuous (fun p : c.2.source =>
      fderivWithin ℝ (ambientForm ω c hc) (Subtype.val '' c.2.target) (c.2 p.val).val) :=
    continuousOn_iff_continuous_domRestrict.mp hcont |>.comp
      (hchart.subtype_mk (fun p => ⟨c.2 p.val,c.2.map_source p.property,rfl⟩))
  have hh := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean n) ℝ).continuous.comp hderiv
  convert hh using 1
  funext p
  exact hη c hc p

theorem derivative_zero_off_support {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (η : Form S (r+1))
    (hη : HasDerivative ω η) (c : CornerChart n M) (hc : c ∈ S.atlas)
    (p : c.2.source) (hp : p.val ∉ formSupport ω) : η.field c hc p = 0 := by
  have htend : Tendsto c.2.symm (𝓝 (c.2 p.val)) (𝓝 p.val) := by
    simpa only [ContinuousAt,c.2.left_inv p.property] using
      c.2.symm.continuousAt (c.2.map_source p.property)
  have hzero : ∀ᶠ q in 𝓝 p.val, q ∉ formSupport ω :=
    isClosed_closure.isOpen_compl.mem_nhds hp
  have heModel : (fun x : Orthant n c.1 => ambientForm ω c hc x.val)
      =ᶠ[𝓝 (c.2 p.val)] fun _ => 0 := by
    filter_upwards [c.2.open_target.mem_nhds (c.2.map_source p.property),
      htend.eventually hzero] with x hx hx0
    simp only [ambientForm,x.property,dite_true,hx]
    by_contra hfield
    exact hx0 (subset_closure ⟨c,hc,c.2.map_target hx,hfield⟩)
  have heAmbient : ambientForm ω c hc =ᶠ[𝓝[orthantSet n c.1] (c.2 p.val).val] fun _ => 0 := by
    rw [← map_nhds_subtype_val (c.2 p.val)]
    exact heModel
  have hsub : (Subtype.val '' c.2.target : Set (Euclidean n)) ⊆ orthantSet n c.1 := by
    rintro _ ⟨z,hz,rfl⟩
    exact z.property
  have he := heAmbient.filter_mono (nhdsWithin_mono _ hsub)
  rw [hη c hc p,extDerivWithin,he.fderivWithin_eq_of_mem
    ⟨c.2 p.val,c.2.map_source p.property,rfl⟩]
  simp
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean n) ℝ).map_zero

theorem derivative_support {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (η : Form S (r+1))
    (hη : HasDerivative ω η) : formSupport η ⊆ formSupport ω := by
  apply closure_minimal _ isClosed_closure
  rintro p ⟨c,hc,hp,h⟩
  by_contra hpω
  exact h (derivative_zero_off_support ω η hη c hc ⟨p,hp⟩ hpω)

theorem coordinate_derivative_compatible {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (hω : IsRegularForm 1 ω)
    (c d : CornerChart n M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p)) :
    extDerivWithin (ambientForm ω c hc) (Subtype.val '' c.2.target) (c.2 p).val =
      (extDerivWithin (ambientForm ω d hd) (Subtype.val '' d.2.target) (d.2 p).val).compContinuousLinearMap (fderiv ℝ H.map (c.2 p).val) := by
  obtain ⟨V,hV,hpV,G,hG,heG⟩ := hω d hd ⟨p,hq⟩
  have hx : c.2 p ∈ (c.2.symm.trans d.2).source := by
    refine ⟨c.2.map_source hp,?_⟩
    change c.2.symm (c.2 p) ∈ d.2.source
    rwa [c.2.left_inv hp]
  have hHpoint : H.map (c.2 p).val = (d.2 p).val := by
    simpa only [OpenPartialHomeomorph.trans_apply,OpenPartialHomeomorph.symm_symm,
      c.2.left_inv hp] using H.agrees (c.2 p) hx H.mem_domain
  let Φ : Euclidean n → (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ := fun z =>
    (G (H.map z)).compContinuousLinearMap (fderiv ℝ H.map z)
  have hH := H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)
  have hGdiff : DifferentiableAt ℝ G (H.map (c.2 p).val) := by
    rw [hHpoint]
    exact (hG.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by norm_num)
  have hΦ : DifferentiableAt ℝ Φ (c.2 p).val :=
    (hGdiff.comp _ (hH.differentiableAt (by simp))).continuousAlternatingMapCompContinuousLinearMap
      ((hH.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num))
  have htend : Tendsto c.2.symm (𝓝 (c.2 p)) (𝓝 p) := by
    simpa only [ContinuousAt,c.2.left_inv hp] using c.2.symm.continuousAt (c.2.map_source hp)
  have hdcoord : Tendsto (fun y : Orthant n c.1 => (d.2 (c.2.symm y)).val)
      (𝓝 (c.2 p)) (𝓝 (d.2 p).val) :=
    (show Tendsto (fun z : M => (d.2 z).val) (𝓝 p) (𝓝 (d.2 p).val) from
      continuous_subtype_val.continuousAt.comp (d.2.continuousAt hq)).comp htend
  have heModel : (fun y : Orthant n c.1 => ambientForm ω c hc y.val)
      =ᶠ[𝓝 (c.2 p)] fun y => Φ y.val := by
    filter_upwards [c.2.open_target.mem_nhds (c.2.map_source hp),
      htend.eventually (d.2.open_source.mem_nhds hq),
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (H.isOpen_domain.mem_nhds H.mem_domain),
      hdcoord.eventually (hV.mem_nhds hpV)] with y hy hyD hyH hyG
    change y.val ∈ H.domain at hyH
    let z : c.2.source := ⟨c.2.symm y,c.2.map_target hy⟩
    have hytrans : y ∈ (c.2.symm.trans d.2).source := ⟨hy,hyD⟩
    have hHy : H.map y.val = (d.2 (c.2.symm y)).val := by
      exact H.agrees y hytrans hyH
    let Hy : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2)
        (c.2 z.val) := {
      domain := H.domain
      isOpen_domain := H.isOpen_domain
      mem_domain := by simpa only [z,c.2.right_inv hy] using hyH
      map := H.map
      smooth := H.smooth
      agrees := H.agrees }
    calc
      ambientForm ω c hc y.val = ω.field c hc z := by
        simpa only [z,c.2.right_inv hy] using ambientForm_at ω c hc z
      _ = (ω.field d hd ⟨z.val,hyD⟩).compContinuousLinearMap
          (fderiv ℝ H.map y.val) := by
        simpa only [Hy,z,c.2.right_inv hy] using ω.compatible c d hc hd z.val z.property hyD Hy
      _ = Φ y.val := by
        dsimp only [Φ]
        rw [hHy,heG ⟨z.val,hyD⟩ hyG]
  have heAmbient : ambientForm ω c hc =ᶠ[𝓝[orthantSet n c.1] (c.2 p).val] Φ := by
    rw [← map_nhds_subtype_val (c.2 p)]
    exact heModel
  have hsub : (Subtype.val '' c.2.target : Set (Euclidean n)) ⊆ orthantSet n c.1 := by
    rintro _ ⟨z,hz,rfl⟩
    exact z.property
  have he := heAmbient.filter_mono (nhdsWithin_mono _ hsub)
  have hmem : (c.2 p).val ∈ Subtype.val '' c.2.target := ⟨c.2 p,c.2.map_source hp,rfl⟩
  have hleft : extDerivWithin (ambientForm ω c hc) (Subtype.val '' c.2.target) (c.2 p).val =
      extDeriv Φ (c.2 p).val := by
    unfold extDerivWithin extDeriv
    rw [he.fderivWithin_eq_of_mem hmem,hΦ.fderivWithin
      (uniqueDiffOn_orthantDomain c.2.open_target _ hmem)]
  rw [hleft,ambientForm_extension_derivative ω d hd ⟨p,hq⟩ V hV hpV G hG heG]
  have hnat := extDeriv_pullback hGdiff hH (by simp)
  simpa only [Φ,hHpoint] using hnat

/-- The chartwise exterior derivative is a genuinely compatible corner form. -/
def derivativeForm {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (hω : IsRegularForm 1 ω) : Form S (r+1) where
  field := fun c hc p => extDerivWithin (ambientForm ω c hc)
    (Subtype.val '' c.2.target) (c.2 p.val).val
  compatible := coordinate_derivative_compatible ω hω

/-- Existence, continuity, and support for the exterior derivative on a corner manifold. -/
theorem derivative_exists {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold n M} (ω : Form S r) (hω : IsRegularForm 1 ω) :
    ∃ η : Form S (r+1), HasDerivative ω η ∧
      (∀ c hc, Continuous (η.field c hc)) ∧ formSupport η ⊆ formSupport ω := by
  let η := derivativeForm ω hω
  have hη : HasDerivative ω η := by intro c hc p; rfl
  exact ⟨η,hη,derivative_continuous ω hω η hη,derivative_support ω η hη⟩

def derivativeTopForm {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (ω : Form S n) (hω : IsRegularForm 1 ω)
    (hcompact : IsCompact (formSupport ω)) : CompactTopForm S where
  form := derivativeForm ω hω
  continuous := derivative_continuous ω hω _ (by intro c hc p; rfl)
  compact_support := by
    letI := S.hausdorff
    exact hcompact.of_isClosed_subset isClosed_closure
      (derivative_support ω _ (by intro c hc p; rfl))


def RegularScalar {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (r : ℕ∞) (f : M → ℝ) : Prop :=
  ∀ c : CornerChart d M, c ∈ S.atlas →
    LocallyContDiffAlong r (fun p : c.2.source => (c.2 p.val).val) (fun p => f p.val)

/-- An eventual ambient coordinate formula gives an exact local extension
on all points of the chart whose coordinates lie in a sufficiently small open set. -/
theorem extension_of_eventual {d : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart d M) {r : ℕ∞} {f : M → ℝ} (p : c.2.source)
    (U : Set (Euclidean d)) (hU : IsOpen U) (hpU : (c.2 p.val).val ∈ U)
    (F : Euclidean d → ℝ) (hF : ContDiffOn ℝ r F U)
    (he : (fun y => F (c.2 y).val) =ᶠ[𝓝 p.val] f) :
    HasLocalContDiffExtensionAt r (fun q : c.2.source => (c.2 q.val).val)
      (fun q => f q.val) p := by
  obtain ⟨W, hWsub, hWo, hpW⟩ := mem_nhds_iff.mp he
  let Q := c.2.symm ⁻¹' W ∩ c.2.target
  have hQo : IsOpen Q := by
    simpa [Q, inter_comm] using c.2.symm.isOpen_inter_preimage hWo
  obtain ⟨V, hVo, hVQ⟩ := isOpen_induced_iff.mp hQo
  have hpQ : c.2 p.val ∈ Q :=
    ⟨by simpa [c.2.left_inv p.property] using hpW, c.2.map_source p.property⟩
  have hpV : (c.2 p.val).val ∈ V := by
    change c.2 p.val ∈ Subtype.val ⁻¹' V
    rwa [hVQ]
  refine ⟨U ∩ V, hU.inter hVo, ⟨hpU,hpV⟩, F, hF.mono inter_subset_left, ?_⟩
  intro q hq
  have hqQ : c.2 q.val ∈ Q := by
    rw [← hVQ]
    exact hq.2
  have hqW : q.val ∈ W := by
    have hh := hqQ.1
    change c.2.symm (c.2 q.val) ∈ W at hh
    rwa [c.2.left_inv q.property] at hh
  exact hWsub hqW

/-- Scalar extension regularity is preserved by scalar multiplication of forms. -/
theorem regular_weight {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {s : ℕ∞} (ρ : M → ℝ) (ω : Form S r)
    (hρ : RegularScalar S s ρ) (hω : IsRegularForm s ω) :
    ∀ c hc p, HasLocalContDiffExtensionAt s
      (fun q : c.2.source => (c.2 q.val).val)
      (fun q => ρ q.val • ω.field c hc q) p := by
  intro c hc p
  obtain ⟨U,hU,hpU,F,hF,hFe⟩ := hρ c hc p
  obtain ⟨V,hV,hpV,G,hG,hGe⟩ := hω c hc p
  refine ⟨U ∩ V,hU.inter hV,⟨hpU,hpV⟩,fun x => F x • G x,
    (hF.mono inter_subset_left).smul (hG.mono inter_subset_right),?_⟩
  intro q hq
  change F (c.2 q.val).val • G (c.2 q.val).val = _
  rw [hFe q hq.1,hGe q hq.2]

/-- A smooth ambient function composed with one chart, and cut off inside
that chart, is smooth in every corner chart. -/
theorem regular_indicator_chart {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (c : CornerChart d M) (hc : c ∈ S.atlas)
    (b : Euclidean d → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (C : Set M) (hC : IsClosed C) (hCc : C ⊆ c.2.source)
    (hs : Function.support (c.2.source.indicator (fun y => b (c.2 y).val)) ⊆ C) :
    RegularScalar S ⊤ (c.2.source.indicator (fun y => b (c.2 y).val)) := by
  let f := c.2.source.indicator (fun y => b (c.2 y).val)
  intro e he p
  by_cases hp : p.val ∈ c.2.source
  · let t := e.2.symm.trans c.2
    have hpt : e.2 p.val ∈ t.source := by
      refine ⟨e.2.map_source p.property,?_⟩
      change e.2.symm (e.2 p.val) ∈ c.2.source
      rwa [e.2.left_inv p.property]
    obtain ⟨U,hU,hpU,H,hH,hHe⟩ := (S.maximal.1.2 e he c hc).1 ⟨e.2 p.val,hpt⟩
    apply extension_of_eventual e p U hU hpU (fun x => b (H x))
      (hb.comp_contDiffOn hH)
    have hcoord : ContinuousAt (fun y : M => (e.2 y).val) p.val :=
      continuous_subtype_val.continuousAt.comp (e.2.continuousAt p.property)
    filter_upwards [e.2.open_source.mem_nhds p.property,
      c.2.open_source.mem_nhds hp,
      hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hqe hqc hqU
    have hqt : e.2 q ∈ t.source := by
      refine ⟨e.2.map_source hqe,?_⟩
      change e.2.symm (e.2 q) ∈ c.2.source
      rwa [e.2.left_inv hqe]
    have hh := hHe ⟨e.2 q,hqt⟩ hqU
    change H (e.2 q).val = (t (e.2 q)).val at hh
    simp only [t, OpenPartialHomeomorph.trans_apply, e.2.left_inv hqe] at hh
    simp only [hh, f, Set.indicator_of_mem hqc]
  · apply extension_of_eventual e p univ isOpen_univ (mem_univ _)
      (fun _ => 0) contDiffOn_const
    have hpC : p.val ∉ C := fun h => hp (hCc h)
    filter_upwards [hC.compl_mem_nhds hpC] with q hq
    exact (Function.notMem_support.mp (fun h => hq (hs h))).symm

/-- The chart cover turns scalar extension regularity into continuity. -/
theorem regularScalar_continuous {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) {r : ℕ∞} {f : M → ℝ} (hf : RegularScalar S r f) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨c,hc,hxc⟩ := S.maximal.1.1 x
  obtain ⟨U,hU,hxU,F,hF,hFe⟩ := hf c hc ⟨x,hxc⟩
  have hcoord : ContinuousAt (fun y : M => (c.2 y).val) x :=
    continuous_subtype_val.continuousAt.comp (c.2.continuousAt hxc)
  have heq : (fun y => F (c.2 y).val) =ᶠ[𝓝 x] f := by
    filter_upwards [c.2.open_source.mem_nhds hxc,
      hcoord.preimage_mem_nhds (hU.mem_nhds hxU)] with y hyc hyU
    exact hFe ⟨y,hyc⟩ hyU
  have hFc : ContinuousAt F (c.2 x).val := hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  have hcomp : ContinuousAt (fun y : M => F (c.2 y).val) x :=
    hFc.comp (f := fun y : M => (c.2 y).val) hcoord
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- Compact smooth bumps exist inside any prescribed corner chart patch. -/
theorem exists_corner_bump {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (c : CornerChart d M) (hc : c ∈ S.atlas)
    (x : M) (hxc : x ∈ c.2.source) (U : Set M) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ f : M → ℝ, Continuous f ∧ RegularScalar S ⊤ f ∧
      (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 x] (fun _ => 1) ∧ sectionSupport f ⊆ U ∩ c.2.source ∧
      IsCompact (sectionSupport f) := by
  letI := S.hausdorff
  let V := c.2.symm ⁻¹' U ∩ c.2.target
  have hV : IsOpen V := by
    simpa [V, inter_comm] using c.2.symm.isOpen_inter_preimage hU
  have hxV : c.2 x ∈ V := ⟨by simpa [c.2.left_inv hxc] using hxU,c.2.map_source hxc⟩
  obtain ⟨W,hW,hWV⟩ := isOpen_induced_iff.mp hV
  have hxW : (c.2 x).val ∈ W := by
    change c.2 x ∈ Subtype.val ⁻¹' W
    rwa [hWV]
  obtain ⟨δ,hδ,hδW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hxW)
  let b : ContDiffBump (c.2 x).val := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  let β : Orthant d c.1 → ℝ := fun y => b y.val
  have hβball : sectionSupport β ⊆ Subtype.val ⁻¹' Metric.closedBall (c.2 x).val δ := by
    apply closure_minimal
    · intro y hy
      have hyb : y.val ∈ Function.support b := hy
      rw [b.support_eq] at hyb
      exact Metric.ball_subset_closedBall hyb
    · exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  have hβV : sectionSupport β ⊆ V := by
    intro y hy
    rw [←hWV]
    exact hδW (hβball hy)
  have horth : IsClosed (orthantSet d c.1) := by
    have he : orthantSet d c.1 =
        ⋂ i : Fin d, ⋂ (_ : i.val < c.1.val), {y : Euclidean d | 0 ≤ y i} := by
      ext y; simp [orthantSet]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (continuous_apply i)))
  have hβcp : IsCompact (sectionSupport β) :=
    (horth.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall (c.2 x).val δ)).of_isClosed_subset isClosed_closure hβball
  let C : Set M := c.2.symm '' sectionSupport β
  have hβt : sectionSupport β ⊆ c.2.target := fun y hy => (hβV hy).2
  have hCcp : IsCompact C := hβcp.image_of_continuousOn (c.2.symm.continuousOn.mono hβt)
  have hCc : C ⊆ c.2.source := by
    rintro y ⟨z,hz,rfl⟩
    exact c.2.map_target (hβt hz)
  have hCU : C ⊆ U := by
    rintro y ⟨z,hz,rfl⟩
    exact (hβV hz).1
  let f : M → ℝ := c.2.source.indicator (fun y => b (c.2 y).val)
  have hfC : Function.support f ⊆ C := by
    intro y hy
    have hyc : y ∈ c.2.source := by
      by_contra hyc
      exact hy (by simp [f,hyc])
    have hby : β (c.2 y) ≠ 0 := by simpa [β,f,hyc] using hy
    exact ⟨c.2 y,subset_closure hby,c.2.left_inv hyc⟩
  have hfsupp : sectionSupport f ⊆ C := closure_minimal hfC hCcp.isClosed
  have hfreg : RegularScalar S ⊤ f := regular_indicator_chart S c hc b b.contDiff C hCcp.isClosed hCc hfC
  refine ⟨f,regularScalar_continuous S hfreg,hfreg,?_,?_,?_,
    hCcp.of_isClosed_subset isClosed_closure hfsupp⟩
  · intro y
    by_cases hy : y ∈ c.2.source
    · simpa [f,hy] using (show b (c.2 y).val ∈ Icc (0 : ℝ) 1 from ⟨b.nonneg,b.le_one⟩)
    · simp [f,hy]
  · have heq : f =ᶠ[𝓝 x] (fun y => b (c.2 y).val) := by
      filter_upwards [c.2.open_source.mem_nhds hxc] with y hy
      simp [f,hy]
    exact heq.trans (b.eventuallyEq_one.comp_tendsto
      (continuous_subtype_val.continuousAt.comp (c.2.continuousAt hxc)))
  · intro y hy
    exact ⟨hCU (hfsupp hy),hCc (hfsupp hy)⟩

theorem regularScalar_const {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (r : ℕ∞) (a : ℝ) : RegularScalar S r (fun _ => a) := by
  intro c hc p
  exact ⟨univ,isOpen_univ,mem_univ _,fun _ => a,contDiffOn_const,by intros; rfl⟩

theorem regularScalar_mul {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {r : ℕ∞} {f g : M → ℝ}
    (hf : RegularScalar S r f) (hg : RegularScalar S r g) :
    RegularScalar S r (fun x => f x * g x) := by
  intro c hc p
  obtain ⟨U,hU,hpU,F,hF,hFe⟩ := hf c hc p
  obtain ⟨V,hV,hpV,G,hG,hGe⟩ := hg c hc p
  refine ⟨U ∩ V,hU.inter hV,⟨hpU,hpV⟩,fun x => F x * G x,
    (hF.mono inter_subset_left).mul (hG.mono inter_subset_right),?_⟩
  intro q hq
  change F (c.2 q.val).val * G (c.2 q.val).val = _
  rw [hFe q hq.1,hGe q hq.2]

theorem regularScalar_sub {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {r : ℕ∞} {f g : M → ℝ}
    (hf : RegularScalar S r f) (hg : RegularScalar S r g) :
    RegularScalar S r (fun x => f x - g x) := by
  intro c hc p
  obtain ⟨U,hU,hpU,F,hF,hFe⟩ := hf c hc p
  obtain ⟨V,hV,hpV,G,hG,hGe⟩ := hg c hc p
  refine ⟨U ∩ V,hU.inter hV,⟨hpU,hpV⟩,fun x => F x - G x,
    (hF.mono inter_subset_left).sub (hG.mono inter_subset_right),?_⟩
  intro q hq
  change F (c.2 q.val).val - G (c.2 q.val).val = _
  rw [hFe q hq.1,hGe q hq.2]

theorem regularScalar_prod {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {r : ℕ∞} {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    (hf : ∀ i ∈ t, RegularScalar S r (f i)) :
    RegularScalar S r (fun x => ∏ i ∈ t, f i x) := by
  induction t using Finset.induction_on with
  | empty => simpa using regularScalar_const S r 1
  | @insert i t hi ih =>
    have h := regularScalar_mul (hf i (Finset.mem_insert_self i t))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa [Finset.prod_insert hi] using h

/-- A compact subset has finite smooth localization whose sum is one on an
open neighborhood of the set. Each entire closed support is compact and lies
inside its selected corner chart, including all actual model faces. -/
theorem finite_smooth_chart_localizers {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (K : Set M) (hK : IsCompact K) :
    ∃ (m : ℕ) (c : Fin m → CornerChart d M) (hc : ∀ i, c i ∈ S.atlas)
      (ρ : Fin m → M → ℝ),
      (∀ i, Continuous (ρ i)) ∧ (∀ i, RegularScalar S ⊤ (ρ i)) ∧
      (∀ i, sectionSupport (ρ i) ⊆ (c i).2.source) ∧
      (∀ i, IsCompact (sectionSupport (ρ i))) ∧
      ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ ∀ p ∈ V, ∑ i, ρ i p = 1 := by
  choose a ha hpa using S.maximal.1.1
  have hb : ∀ p : M, ∃ f : M → ℝ, Continuous f ∧ RegularScalar S ⊤ f ∧
      (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 p] (fun _ => 1) ∧ sectionSupport f ⊆ (a p).2.source ∧
      IsCompact (sectionSupport f) := by
    intro p
    obtain ⟨f,hfc,hfr,hf01,hf1,hfs,hfcp⟩ :=
      exists_corner_bump S (a p) (ha p) p (hpa p) (a p).2.source (a p).2.open_source (hpa p)
    exact ⟨f,hfc,hfr,hf01,hf1,fun q hq => (hfs hq).1,hfcp⟩
  choose b hbc hbr hb01 hb1 hbs hbcp using hb
  have hW : ∀ p : M, ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, b p q = 1 := by
    intro p
    obtain ⟨W,hWsub,hWo,hpW⟩ := mem_nhds_iff.mp (hb1 p)
    exact ⟨W,hWo,hpW,fun q hq => hWsub hq⟩
  choose W hWo hpW hW1 using hW
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover W hWo (by
    intro p hp
    exact mem_iUnion.mpr ⟨p,hpW p⟩)
  let m := Fintype.card t
  let e : Fin m ≃ t := (Fintype.equivFin t).symm
  let V : Set M := ⋃ p ∈ t, W p
  have hVo : IsOpen V := isOpen_iUnion (fun p => isOpen_iUnion (fun _ => hWo p))
  let B : BumpCovering (Fin m) M V := {
    toFun := fun i => ⟨b (e i).val,hbc _⟩
    locallyFinite' := locallyFinite_of_finite _
    nonneg' := fun i p => (hb01 _ p).1
    le_one' := fun i p => (hb01 _ p).2
    eventuallyEq_one' := by
      intro q hq
      obtain ⟨p,hpt,hqp⟩ := mem_iUnion₂.mp hq
      refine ⟨e.symm ⟨p,hpt⟩,?_⟩
      filter_upwards [(hWo p).mem_nhds hqp] with y hy
      change b (e (e.symm ⟨p,hpt⟩)).val y = 1
      rw [e.apply_symm_apply]
      exact hW1 p y hy }
  let ρ : Fin m → M → ℝ := fun i p => B.toPartitionOfUnity i p
  refine ⟨m,fun i => a (e i).val,fun i => ha _,ρ,
    fun i => (B.toPartitionOfUnity i).continuous,?_,?_,?_,V,hVo,ht,?_⟩
  · intro i
    have hh := regularScalar_mul (hbr (e i).val)
      (regularScalar_prod (Finset.univ.filter (fun j => WellOrderingRel j i))
        (fun j p => 1-b (e j).val p)
        (fun j _ => regularScalar_sub (regularScalar_const S ⊤ 1) (hbr (e j).val)))
    convert hh using 1
    funext p
    exact B.toPartitionOfUnity_eq_mul_prod i p Finset.univ (by simp)
  · intro i
    exact (closure_mono (B.support_toPartitionOfUnity_subset i)).trans (hbs (e i).val)
  · intro i
    exact (hbcp (e i).val).of_isClosed_subset isClosed_closure
      (closure_mono (B.support_toPartitionOfUnity_subset i))
  · intro p hp
    simpa [ρ,finsum_eq_sum_of_fintype] using B.toPartitionOfUnity.sum_eq_one hp

/-- The zero extension cannot be nonzero away from the coordinate image of
its original closed support. -/
theorem ambientForm_support {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas) :
    Function.support (ambientForm ω c hc) ⊆
      (fun p : M => (c.2 p).val) '' formSupport ω := by
  intro x hx
  by_cases hm : x ∈ orthantSet d c.1
  · by_cases ht : (⟨x,hm⟩ : Orthant d c.1) ∈ c.2.target
    · refine ⟨c.2.symm ⟨x,hm⟩, subset_closure ⟨c,hc,c.2.map_target ht,?_⟩,?_⟩
      · intro hz
        exact hx (by simp [ambientForm,hm,ht,hz])
      · exact congrArg Subtype.val (c.2.right_inv ht)
    · exact (hx (by simp [ambientForm,hm,ht])).elim
  · exact (hx (by simp [ambientForm,hm])).elim

/-- A chart-supported regular form extends by zero across artificial chart
edges with its full C^r local ambient regularity on the closed orthant. -/
theorem ambientForm_regular {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas) {s : ℕ∞}
    (hω : IsRegularForm s ω) (hK : IsCompact (formSupport ω))
    (hs : formSupport ω ⊆ c.2.source) :
    LocallyContDiffOn s (orthantSet d c.1) (fun x => ambientForm ω c hc x.val) := by
  let C := (fun p : M => (c.2 p).val) '' formSupport ω
  have hC : IsCompact C := hK.image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn (c.2.continuousOn.mono hs))
  intro x
  by_cases hx : x ∈ c.2.target
  · let p : c.2.source := ⟨c.2.symm x,c.2.map_target hx⟩
    obtain ⟨U,hU,hpU,F,hF,hFe⟩ := hω c hc p
    obtain ⟨V,hV,hVt⟩ := isOpen_induced_iff.mp c.2.open_target
    have hxV : x.val ∈ V := by
      change x ∈ Subtype.val ⁻¹' V
      rwa [hVt]
    have hxU : x.val ∈ U := by
      have he : c.2 p.val = x := c.2.right_inv hx
      simpa only [he] using hpU
    refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,F,hF.mono inter_subset_left,?_⟩
    intro y hy
    have hyt : y ∈ c.2.target := by
      rw [←hVt]
      exact hy.2
    let q : c.2.source := ⟨c.2.symm y,c.2.map_target hyt⟩
    have he : c.2 q.val = y := c.2.right_inv hyt
    have hqU : (c.2 q.val).val ∈ U := by rw [he]; exact hy.1
    have hval := hFe q hqU
    change F (c.2 q.val).val = _ at hval
    rw [he] at hval
    simpa only [ambientForm,y.property,dite_true,hyt,q] using hval
  · have hxC : x.val ∉ C := by
      rintro ⟨p,hp,he⟩
      have hxp : c.2 p = x := Subtype.ext he
      exact hx (hxp ▸ c.2.map_source (hs hp))
    refine ⟨Cᶜ,hC.isClosed.isOpen_compl,hxC,fun _ => 0,contDiffOn_const,?_⟩
    intro y hy
    symm
    exact Function.notMem_support.mp (fun h => hy (ambientForm_support ω c hc h))

/-- Compact support of the original form becomes compact support relative to
the entire closed orthant, including every true coordinate face. -/
theorem ambientForm_hasCompactSupport {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas)
    (hK : IsCompact (formSupport ω)) (hs : formSupport ω ⊆ c.2.source) :
    HasCompactSupport (fun x : Orthant d c.1 => ambientForm ω c hc x.val) := by
  have hC : IsCompact (c.2 '' formSupport ω) :=
    hK.image_of_continuousOn (c.2.continuousOn.mono hs)
  have hsub : Function.support (fun x : Orthant d c.1 => ambientForm ω c hc x.val) ⊆
      c.2 '' formSupport ω := by
    intro x hx
    obtain ⟨p,hp,he⟩ := ambientForm_support ω c hc hx
    exact ⟨p,hp,Subtype.ext he⟩
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

/-- The relatively open chart image and the full orthant have the same
within derivative at each chart point, including multiple corners. -/
theorem extDerivWithin_chart_eq_orthant {d r : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart d M) (p : M) (hp : p ∈ c.2.source)
    (ω : Euclidean d → (Euclidean d) [⋀^Fin r]→L[ℝ] ℝ) :
    extDerivWithin ω (Subtype.val '' c.2.target) (c.2 p).val =
      extDerivWithin ω (orthantSet d c.1) (c.2 p).val := by
  obtain ⟨U,hU,hUt⟩ := isOpen_induced_iff.mp c.2.open_target
  have hset : Subtype.val '' c.2.target = orthantSet d c.1 ∩ U := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,by change y ∈ Subtype.val ⁻¹' U; rwa [hUt]⟩
    · rintro ⟨hxH,hxU⟩
      refine ⟨⟨x,hxH⟩,?_,rfl⟩
      rw [←hUt]
      exact hxU
  have hpU : (c.2 p).val ∈ U := by
    change c.2 p ∈ Subtype.val ⁻¹' U
    rw [hUt]
    exact c.2.map_source hp
  rw [hset]
  simp only [extDerivWithin,fderivWithin_inter (hU.mem_nhds hpU)]

open CornerOrientationData OrientationData

/-- The coordinate orientation sign, zero away from the actual chart image. -/
def chartSign {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (x : Euclidean d) : ℝ :=
  if hx : x ∈ orthantSet d c.1 then
    if ht : (⟨x,hx⟩ : Orthant d c.1) ∈ c.2.target then
      signValue (o.sign c hc ⟨c.2.symm ⟨x,hx⟩,c.2.map_target ht⟩)
    else 0
  else 0

/-- The coordinate r-form carrying the locally constant orientation sign. -/
def signedAmbientForm {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (x : Euclidean d) :
    (Euclidean d) [⋀^Fin r]→L[ℝ] ℝ :=
  chartSign o c hc x • ambientForm ω c hc x

/-- A locally constant chart-source function is constant on a relative
coordinate neighborhood which also lies inside the actual chart target. -/
theorem chart_source_constant_neighborhood {d : ℕ} {M : Type u} [TopologicalSpace M]
    (c : CornerChart d M) {α : Type*} (σ : c.2.source → α)
    (hσ : IsLocallyConstant σ) (p : c.2.source) :
    ∃ V : Set (Euclidean d), IsOpen V ∧ (c.2 p.val).val ∈ V ∧
      ∀ y : Orthant d c.1, y.val ∈ V →
        ∃ hy : y ∈ c.2.target, σ ⟨c.2.symm y,c.2.map_target hy⟩ = σ p := by
  let E := c.2.toHomeomorphSourceTarget
  let A : Set c.2.source := {q | σ q = σ p}
  let Q : Set (Orthant d c.1) := Subtype.val '' (E '' A)
  have hQo : IsOpen Q := c.2.open_target.isOpenMap_subtype_val _
    (E.isOpenMap _ (hσ.isOpen_fiber (σ p)))
  obtain ⟨V,hVo,hVQ⟩ := isOpen_induced_iff.mp hQo
  have hpQ : c.2 p.val ∈ Q := ⟨E p,⟨p,rfl,rfl⟩,rfl⟩
  refine ⟨V,hVo,?_,?_⟩
  · change c.2 p.val ∈ Subtype.val ⁻¹' V
    rwa [hVQ]
  · intro y hyV
    have hyQ : y ∈ Q := by rw [←hVQ]; exact hyV
    obtain ⟨z,⟨q,hq,rfl⟩,rfl⟩ := hyQ
    refine ⟨(E q).property,?_⟩
    have he : (⟨c.2.symm (E q).val,c.2.map_target (E q).property⟩ : c.2.source) = q := by
      apply Subtype.ext
      exact c.2.left_inv q.property
    simpa only [he,A,Set.mem_setOf_eq] using hq

/-- The orientation sign is constant on a full relative coordinate neighborhood. -/
theorem chartSign_neighborhood {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (p : c.2.source) :
    ∃ V : Set (Euclidean d), IsOpen V ∧ (c.2 p.val).val ∈ V ∧
      ∀ y : Orthant d c.1, y.val ∈ V →
        chartSign o c hc y.val = signValue (o.sign c hc p) := by
  obtain ⟨V,hV,hpV,hsign⟩ := chart_source_constant_neighborhood c
    (fun q => signValue (o.sign c hc q)) ((o.locallyConstant c hc).comp signValue) p
  refine ⟨V,hV,hpV,?_⟩
  intro y hy
  obtain ⟨hyt,he⟩ := hsign y hy
  simpa only [chartSign,y.property,dite_true,hyt] using he

/-- Multiplication by the variable chart sign preserves compact relative support. -/
theorem signedAmbientForm_hasCompactSupport {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas)
    (hK : IsCompact (formSupport ω)) (hs : formSupport ω ⊆ c.2.source) :
    HasCompactSupport (fun x : Orthant d c.1 => signedAmbientForm o ω c hc x.val) := by
  have hC := ambientForm_hasCompactSupport ω c hc hK hs
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx hz
  exact hx (by simp [signedAmbientForm,hz])

/-- The signed coordinate form remains regular at chart edges and all true faces. -/
theorem signedAmbientForm_regular {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas) {s : ℕ∞}
    (hω : IsRegularForm s ω) (hK : IsCompact (formSupport ω))
    (hs : formSupport ω ⊆ c.2.source) :
    LocallyContDiffOn s (orthantSet d c.1) (fun x => signedAmbientForm o ω c hc x.val) := by
  intro x
  by_cases hx : x ∈ c.2.target
  · let p : c.2.source := ⟨c.2.symm x,c.2.map_target hx⟩
    obtain ⟨V,hV,hpV,hsgn⟩ := chartSign_neighborhood o c hc p
    have he : c.2 p.val = x := c.2.right_inv hx
    have hxV : x.val ∈ V := by simpa only [he] using hpV
    obtain ⟨U,hU,hxU,F,hF,hFe⟩ := ambientForm_regular ω c hc hω hK hs x
    refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,
      fun y => signValue (o.sign c hc p) • F y,
      (hF.mono inter_subset_left).const_smul (signValue (o.sign c hc p)),?_⟩
    intro y hy
    change signValue (o.sign c hc p) • F y.val = _
    rw [hFe y hy.1]
    simp only [signedAmbientForm,hsgn y hy.2]
  · let C := (fun p : M => (c.2 p).val) '' formSupport ω
    have hC : IsCompact C := hK.image_of_continuousOn
      (continuous_subtype_val.comp_continuousOn (c.2.continuousOn.mono hs))
    have hxC : x.val ∉ C := by
      rintro ⟨p,hp,he⟩
      have hxp : c.2 p = x := Subtype.ext he
      exact hx (hxp ▸ c.2.map_source (hs hp))
    refine ⟨Cᶜ,hC.isClosed.isOpen_compl,hxC,fun _ => 0,contDiffOn_const,?_⟩
    intro y hy
    have hz : ambientForm ω c hc y.val = 0 :=
      Function.notMem_support.mp (fun h => hy (ambientForm_support ω c hc h))
    simp [signedAmbientForm,hz]

theorem orthantUniqueDiff {d : ℕ} (k : Fin (d+1)) : UniqueDiffOn ℝ (orthantSet d k) := by
  change UniqueDiffOn ℝ (Set.pi {i : Fin d | i.val < k.val} (fun _ => Ici (0 : ℝ)))
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Ici 0)

/-- Exterior differentiation sees the chart sign as a constant at each point. -/
theorem signedAmbientForm_derivative {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (p : c.2.source) :
    extDerivWithin (signedAmbientForm o ω c hc) (orthantSet d c.1) (c.2 p.val).val =
      signValue (o.sign c hc p) •
        extDerivWithin (ambientForm ω c hc) (orthantSet d c.1) (c.2 p.val).val := by
  obtain ⟨V,hV,hpV,hsgn⟩ := chartSign_neighborhood o c hc p
  have hVevent : ∀ᶠ x in 𝓝 (c.2 p.val).val, x ∈ V := hV.mem_nhds hpV
  have heq : signedAmbientForm o ω c hc =ᶠ[𝓝[orthantSet d c.1] (c.2 p.val).val]
      (fun x => signValue (o.sign c hc p) • ambientForm ω c hc x) := by
    filter_upwards [eventually_mem_nhdsWithin,
      hVevent.filter_mono nhdsWithin_le_nhds] with x hxH hxV
    simp only [signedAmbientForm,hsgn ⟨x,hxH⟩ hxV]
  rw [heq.extDerivWithin_eq_of_mem (c.2 p.val).property,
    extDerivWithin_fun_smul _ _ (orthantUniqueDiff c.1 _ (c.2 p.val).property)]

/-- The local signed bulk coefficient is the signed coefficient of the actual
exterior derivative, with the chart image/full orthant bridge made explicit. -/
theorem signedAmbientForm_bulk {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S) (ω : Form S n)
    (η : Form S (n+1)) (hη : HasDerivative ω η)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas) (p : c.2.source) :
    orthantBulkCoefficient c.1 (signedAmbientForm o ω c hc) (c.2 p.val).val =
      signValue (o.sign c hc p) * η.field c hc p (LocalStokesData.frame (n+1)) := by
  rw [orthantBulkCoefficient,signedAmbientForm_derivative o ω c hc p]
  rw [←extDerivWithin_chart_eq_orthant c p.val p.property (ambientForm ω c hc),←hη c hc p]
  rfl

/-- Outside the compact coordinate support image the signed extension and
all its within exterior derivatives vanish on a neighborhood. -/
theorem signedAmbientForm_derivative_zero {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas)
    (hK : IsCompact (formSupport ω)) (hs : formSupport ω ⊆ c.2.source)
    (x : Euclidean d) (hx : x ∉ (fun p : M => (c.2 p).val) '' formSupport ω) :
    extDerivWithin (signedAmbientForm o ω c hc) (orthantSet d c.1) x = 0 := by
  let C := (fun p : M => (c.2 p).val) '' formSupport ω
  have hC : IsCompact C := hK.image_of_continuousOn
    (continuous_subtype_val.comp_continuousOn (c.2.continuousOn.mono hs))
  have he : signedAmbientForm o ω c hc =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hC.isClosed.compl_mem_nhds hx] with y hy
    have hz : ambientForm ω c hc y = 0 :=
      Function.notMem_support.mp (fun h => hy (ambientForm_support ω c hc h))
    simp [signedAmbientForm,hz]
  rw [he.extDerivWithin_eq_nhds]
  simp only [extDerivWithin,fderivWithin_const_apply]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean d) ℝ) 0 = 0
  exact map_zero _

/-- The signed local Stokes bulk integrand equals the actual chart integral
coefficient throughout the whole orthant, including outside the chart image. -/
theorem signedAmbientForm_bulk_eq_chartCoefficient {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S) (ω : Form S n)
    (η : Form S (n+1)) (hη : HasDerivative ω η)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (hK : IsCompact (formSupport ω)) (hs : formSupport ω ⊆ c.2.source)
    (x : Euclidean (n+1)) (hx : x ∈ orthantSet (n+1) c.1) :
    orthantBulkCoefficient c.1 (signedAmbientForm o ω c hc) x =
      chartCoefficient o c hc η x := by
  by_cases ht : (⟨x,hx⟩ : Orthant (n+1) c.1) ∈ c.2.target
  · let p : c.2.source := ⟨c.2.symm ⟨x,hx⟩,c.2.map_target ht⟩
    have he : (c.2 p.val).val = x := congrArg Subtype.val (c.2.right_inv ht)
    have hb := signedAmbientForm_bulk o ω η hη c hc p
    rw [he] at hb
    simpa only [chartCoefficient,hx,dite_true,ht,p] using hb
  · have hxC : x ∉ (fun p : M => (c.2 p).val) '' formSupport ω := by
      rintro ⟨p,hp,he⟩
      have hxp : c.2 p = (⟨x,hx⟩ : Orthant (n+1) c.1) := Subtype.ext he
      exact ht (hxp ▸ c.2.map_source (hs hp))
    simp [orthantBulkCoefficient,signedAmbientForm_derivative_zero o ω c hc hK hs x hxC,
      chartCoefficient,hx,ht]

/-- Signed local integration on a chart is exactly the orthant integral of
the local exterior derivative coefficient. -/
theorem chartIntegral_derivative_eq_orthant {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S) (ω : Form S n)
    (η : Form S (n+1)) (hη : HasDerivative ω η)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (hK : IsCompact (formSupport ω)) (hs : formSupport ω ⊆ c.2.source) :
    chartIntegral o c hc η = ∫ x in orthantSet (n+1) c.1,
      orthantBulkCoefficient c.1 (signedAmbientForm o ω c hc) x := by
  rw [chartIntegral,←MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := orthantSet (n+1) c.1) (fun x hx => by simp [chartCoefficient,hx])]
  apply MeasureTheory.setIntegral_congr_fun
  · have he : orthantSet (n+1) c.1 =
        ⋂ i : Fin (n+1), ⋂ (_ : i.val < c.1.val), {y : Euclidean (n+1) | 0 ≤ y i} := by
      ext y; simp [orthantSet]
    rw [he]
    exact (isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (continuous_apply i)))).measurableSet
  · intro x hx
    exact (signedAmbientForm_bulk_eq_chartCoefficient o ω η hη c hc hK hs x hx).symm

theorem ambientForm_at_source {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ω : Form S r)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (p : c.2.source) :
    ambientForm ω c hc (c.2 p.val).val = ω.field c hc p := by
  simp only [ambientForm,(c.2 p.val).property,dite_true,c.2.map_source p.property]
  congr 1
  apply Subtype.ext
  exact c.2.left_inv p.property

theorem chartSign_at_source {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (p : c.2.source) :
    chartSign o c hc (c.2 p.val).val = signValue (o.sign c hc p) := by
  simp only [chartSign,(c.2 p.val).property,dite_true,c.2.map_source p.property]
  congr 1
  congr 1
  apply Subtype.ext
  exact c.2.left_inv p.property

theorem chartCoefficient_at_source {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S) (ω : Form S d)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (p : c.2.source) :
    chartCoefficient o c hc ω (c.2 p.val).val =
      signValue (o.sign c hc p) * ω.field c hc p (LocalStokesData.frame d) := by
  simp only [chartCoefficient,(c.2 p.val).property,dite_true,c.2.map_source p.property]
  have hpoint : (⟨c.2.symm (c.2 p.val),c.2.map_target (c.2.map_source p.property)⟩ : c.2.source) = p :=
    Subtype.ext (c.2.left_inv p.property)
  rw [hpoint]

/-- The deleted ambient standard frame is exactly the insertion of the face frame. -/
theorem faceInsertion_frame {n : ℕ} (i : Fin (n+1)) :
    (fun j => faceInsertion i (LocalStokesData.frame n j)) =
      i.removeNth (LocalStokesData.frame (n+1)) := by
  funext j
  ext l
  refine Fin.succAboveCases i ?_ (fun k => ?_) l
  · simp [faceInsertion,LocalStokesData.frame,Fin.removeNth,Pi.single_apply,Fin.succAbove_ne]
  · simp [faceInsertion,LocalStokesData.frame,Fin.removeNth,Pi.single_apply]

/-- In each actual resolved chart, outward-first sign and actual restriction
identify the local face coefficient at every sheet point, including corners. -/
theorem signedAmbientForm_face_at_source {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    {T : CornerManifold n (ResolvedFaceSpace S)} (b : CornerOrientation T)
    (hOb : IsResolvedOrientation o b) (ω : Form S n) (β : Form T n)
    (hβ : CornerStokesData.IsFaceRestriction ω β)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (i : Fin (n+1)) (hi : i.val < c.1.val)
    (e : CornerChart n (ResolvedFaceSpace S)) (he : e ∈ T.atlas)
    (hek : e.1 = faceConstraintCount c.1)
    (hes : e.2.source = faceSheet S c i univ)
    (hecoord : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (q : e.2.source) :
    orthantBoundaryCoefficient (signedAmbientForm o ω c hc) i (e.2 q.val).val =
      chartCoefficient b e he β (e.2 q.val).val := by
  have hqsheet : q.val ∈ faceSheet S c i univ := hes ▸ q.property
  have hp : q.val.1 ∈ c.2.source := hqsheet.2.1
  have hz : (c.2 q.val.1).val i = 0 := hqsheet.2.2.1
  have hins : i.insertNth (0 : ℝ) (e.2 q.val).val = (c.2 q.val.1).val := by
    rw [hecoord q.val q.property,←hz]
    exact Fin.insertNth_self_removeNth i _
  rw [orthantBoundaryCoefficient,hins,chartCoefficient_at_source b β e he q]
  simp only [signedAmbientForm,chartSign_at_source o c hc ⟨q.val.1,hp⟩,
    ambientForm_at_source ω c hc ⟨q.val.1,hp⟩]
  rw [hOb.2 c hc i hi e he hek hes hecoord q.val q.property hp,
    hβ c hc i hi e he hek hes hecoord q.val q.property hp (LocalStokesData.frame n),
    faceInsertion_frame]
  simp only [faceSign,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  ring

/-- The complete zero-extended resolved-chart coefficient is exactly the
signed orthant face coefficient; both vanish away from the true face image. -/
theorem signedAmbientForm_face_eq_chartCoefficient {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    {T : CornerManifold n (ResolvedFaceSpace S)} (b : CornerOrientation T)
    (hOb : IsResolvedOrientation o b) (ω : Form S n) (β : Form T n)
    (hβ : CornerStokesData.IsFaceRestriction ω β)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (i : Fin (n+1)) (hi : i.val < c.1.val)
    (e : CornerChart n (ResolvedFaceSpace S)) (he : e ∈ T.atlas)
    (hek : e.1 = faceConstraintCount c.1)
    (hes : e.2.source = faceSheet S c i univ)
    (hecoord : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (y : Euclidean n) :
    orthantBoundaryCoefficient (signedAmbientForm o ω c hc) i y =
      chartCoefficient b e he β y := by
  by_cases hy : ∃ q : e.2.source, (e.2 q.val).val = y
  · obtain ⟨q,rfl⟩ := hy
    exact signedAmbientForm_face_at_source o b hOb ω β hβ c hc i hi e he hek hes hecoord q
  · have hcoef : chartCoefficient b e he β y = 0 := by
      by_cases hm : y ∈ orthantSet n e.1
      · by_cases ht : (⟨y,hm⟩ : Orthant n e.1) ∈ e.2.target
        · exact (hy ⟨⟨e.2.symm ⟨y,hm⟩,e.2.map_target ht⟩,
            congrArg Subtype.val (e.2.right_inv ht)⟩).elim
        · simp [chartCoefficient,hm,ht]
      · simp [chartCoefficient,hm]
    rw [hcoef]
    by_cases hxH : i.insertNth (0 : ℝ) y ∈ orthantSet (n+1) c.1
    · by_cases hxt : (⟨i.insertNth (0 : ℝ) y,hxH⟩ : Orthant (n+1) c.1) ∈ c.2.target
      · let x : Orthant (n+1) c.1 := ⟨i.insertNth (0 : ℝ) y,hxH⟩
        let p := c.2.symm x
        have hp : p ∈ c.2.source := c.2.map_target hxt
        have hcp : c.2 p = x := c.2.right_inv hxt
        have hz : (c.2 p).val i = 0 := by rw [hcp]; simp [x]
        have hia : i ∈ activeCoordinates (c.2 p) := by
          simp [activeCoordinates,hi,hz]
        let q : ResolvedFaceSpace S := ⟨p,chartFaceAt S c hc p hp ⟨i,hia⟩⟩
        have hq : q ∈ e.2.source := by
          rw [hes]
          exact ⟨mem_univ _,hp,hz,rfl⟩
        apply (hy ⟨⟨q,hq⟩,?_⟩).elim
        rw [hecoord q hq]
        change i.removeNth (c.2 p).val = y
        rw [hcp]
        simpa only [x] using (Fin.removeNth_insertNth (α := fun _ => ℝ) i (0 : ℝ) y)
      · simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hxH,hxt]
    · simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hxH]


/-- The genuine transition derivative intertwines the two face inclusions.
It is essential that the face germs agree, also at a multiple corner. -/
theorem faceInsertion_transition {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (c d : CornerChart (n+1) M)
    (hc : c ∈ S.atlas) (hd : d ∈ S.atlas) (p : M)
    (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p))
    (i : activeCoordinates (c.2 p)) (j : activeCoordinates (d.2 p))
    (hij : chartFaceGerm c p i.val = chartFaceGerm d p j.val) :
    (fderiv ℝ H.map (c.2 p).val).toLinearMap.comp (faceInsertion i.val) =
      (faceInsertion j.val).comp
        (faceDerivative (fderiv ℝ H.map (c.2 p).val).toLinearMap i.val j.val) := by
  obtain ⟨a,_,ha⟩ := CornerFaceOrientations.chart_face_germ_normal_row
    S c d hc hd p hp hq H i j hij
  apply LinearMap.ext
  intro v
  funext s
  refine Fin.succAboveCases j.val ?_ (fun t => ?_) s
  · have hz := ha (faceInsertion i.val v)
    simpa [faceInsertion] using hz
  · change fderiv ℝ H.map (c.2 p).val (i.val.insertNth 0 v) (j.val.succAbove t) =
      j.val.insertNth (0 : ℝ)
        (j.val.removeNth (fderiv ℝ H.map (c.2 p).val (i.val.insertNth 0 v))) (j.val.succAbove t)
    rw [Fin.insertNth_apply_succAbove]
    rfl

/-- Restriction of a genuine bulk form to any two representing face sheets
obeys the actual derivative law of the resolved chart transition. -/
theorem face_covector_compatible {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (ω : CornerStokesData.Form S r)
    (c d : CornerChart (n+1) M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (i j : Fin (n+1)) (hi : i.val < c.1.val) (hj : j.val < d.1.val)
    (e f : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : f.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ f.2.source, (f.2 q).val = j.removeNth ((d.2 q.1).val))
    (q : ResolvedFaceSpace S) (hqe : q ∈ e.2.source) (hqf : q ∈ f.2.source)
    (hp : q.1 ∈ c.2.source) (hq : q.1 ∈ d.2.source)
    (K : OrthantExtension (e.2.symm.trans f.2).source (e.2.symm.trans f.2) (e.2 q)) :
    (ω.field c hc ⟨q.1,hp⟩).compContinuousLinearMap (faceInsertion i).toContinuousLinearMap =
      ((ω.field d hd ⟨q.1,hq⟩).compContinuousLinearMap (faceInsertion j).toContinuousLinearMap).compContinuousLinearMap
        (fderiv ℝ K.map (e.2 q).val) := by
  have hqec : q ∈ faceSheet S c i univ := hes ▸ hqe
  have hqfd : q ∈ faceSheet S d j univ := hfs ▸ hqf
  let I : activeCoordinates (c.2 q.1) := ⟨i, by simp [activeCoordinates,hi,hqec.2.2.1]⟩
  let J : activeCoordinates (d.2 q.1) := ⟨j, by simp [activeCoordinates,hj,hqfd.2.2.1]⟩
  have hIJ : chartFaceGerm c q.1 I.val = chartFaceGerm d q.1 J.val :=
    hqec.2.2.2.symm.trans hqfd.2.2.2
  let H := CornerFaceOrientations.cornerTransitionExtension c d (S.maximal.1.2 c hc d hd)
    q.1 hp hq
  have hL := faceInsertion_transition S c d hc hd q.1 hp hq H I J hIJ
  have hK := CornerFaceOrientations.resolved_face_transition_derivative S c d i j e f
    hes hfs hec hfc q hqe hqf H K
  rw [ω.compatible c d hc hd q.1 hp hq H]
  ext v
  change ω.field d hd ⟨q.1,hq⟩
      (fun t => fderiv ℝ H.map (c.2 q.1).val (faceInsertion i (v t))) =
    ω.field d hd ⟨q.1,hq⟩
      (fun t => faceInsertion j (fderiv ℝ K.map (e.2 q).val (v t)))
  congr 1
  funext t
  have hLt := DFunLike.congr_fun hL (v t)
  change fderiv ℝ H.map (c.2 q.1).val (faceInsertion i (v t)) =
    faceInsertion j (faceDerivative (fderiv ℝ H.map (c.2 q.1).val).toLinearMap i j (v t)) at hLt
  rw [← hK] at hLt
  exact hLt

/-- A face chart represented in two bulk charts gives exactly the same
restricted covector; no representation of a local face is chosen in the result. -/
theorem face_covector_representation_independent {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (ω : CornerStokesData.Form S r)
    (c d : CornerChart (n+1) M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (i j : Fin (n+1)) (hi : i.val < c.1.val) (hj : j.val < d.1.val)
    (e : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : e.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ e.2.source, (e.2 q).val = j.removeNth ((d.2 q.1).val))
    (q : ResolvedFaceSpace S) (hqe : q ∈ e.2.source)
    (hp : q.1 ∈ c.2.source) (hq : q.1 ∈ d.2.source) :
    (ω.field c hc ⟨q.1,hp⟩).compContinuousLinearMap (faceInsertion i).toContinuousLinearMap =
      (ω.field d hd ⟨q.1,hq⟩).compContinuousLinearMap (faceInsertion j).toContinuousLinearMap := by
  let K : OrthantExtension (e.2.symm.trans e.2).source (e.2.symm.trans e.2) (e.2 q) := {
    domain := univ
    isOpen_domain := isOpen_univ
    mem_domain := mem_univ _
    map := id
    smooth := contDiffOn_id
    agrees := by
      intro z hz _
      change z.val = (e.2 (e.2.symm z)).val
      rw [e.2.right_inv hz.1] }
  have h := face_covector_compatible S ω c d hc hd i j hi hj e e hes hfs hec hfc
    q hqe hqe hp hq K
  ext v
  simpa [K] using congrArg (fun A : (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ => A v) h


def zeroCornerForm {d r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) : Form S r where
  field := fun _ _ _ => 0
  compatible := by intros; ext v; simp

def addCornerForm {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (α β : Form S r) : Form S r where
  field := fun c hc p => α.field c hc p + β.field c hc p
  compatible := by
    intro c e hc he p hp hq H
    rw [α.compatible c e hc he p hp hq H, β.compatible c e hc he p hp hq H]
    ext v
    simp

theorem addCornerForm_support {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (α β : Form S r) :
    formSupport (addCornerForm α β) ⊆ formSupport α ∪ formSupport β := by
  apply closure_minimal _ (isClosed_closure.union isClosed_closure)
  rintro p ⟨c,hc,hp,h⟩
  by_cases hα : α.field c hc ⟨p,hp⟩ = 0
  · right
    apply subset_closure
    refine ⟨c,hc,hp,?_⟩
    simpa only [addCornerForm,hα,zero_add] using h
  · exact Or.inl (subset_closure ⟨c,hc,hp,hα⟩)

def zeroTopForm {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) : CompactTopForm S where
  form := zeroCornerForm S
  continuous := by intros; exact continuous_const
  compact_support := by simp [formSupport,zeroCornerForm]

def addTopForm {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (α β : CompactTopForm S) : CompactTopForm S where
  form := addCornerForm α.form β.form
  continuous := fun c hc => (α.continuous c hc).add (β.continuous c hc)
  compact_support := (α.compact_support.union β.compact_support).of_isClosed_subset
    isClosed_closure (addCornerForm_support α.form β.form)

theorem exists_sumTopForm {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {ι : Type*} (s : Finset ι) (α : ι → CompactTopForm S) :
    ∃ ζ : CompactTopForm S, ∀ c hc p, ζ.form.field c hc p = ∑ i ∈ s, (α i).form.field c hc p := by
  induction s using Finset.induction_on with
  | empty => exact ⟨zeroTopForm S, by intros; simp [zeroTopForm,zeroCornerForm]⟩
  | @insert i s hi ih =>
    obtain ⟨ζ,hζ⟩ := ih
    refine ⟨addTopForm (α i) ζ,?_⟩
    intro c hc p
    simp [addTopForm,addCornerForm,hζ,hi]

theorem integral_congr {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {o : CornerOrientation S}
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) (α β : CompactTopForm S)
    (h : ∀ c hc p, β.form.field c hc p = α.form.field c hc p) : I β = I α := by
  simpa using hI.2.1 1 α β (by intro c hc p; simpa using h c hc p)

theorem integral_sum {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {o : CornerOrientation S}
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) {ι : Type*}
    (s : Finset ι) (α : ι → CompactTopForm S) (ζ : CompactTopForm S)
    (hζ : ∀ c hc p, ζ.form.field c hc p = ∑ i ∈ s, (α i).form.field c hc p) :
    I ζ = ∑ i ∈ s, I (α i) := by
  induction s using Finset.induction_on generalizing ζ with
  | empty =>
    simpa using hI.2.1 0 ζ ζ (by intro c hc p; simp [hζ])
  | @insert i s hi ih =>
    obtain ⟨ξ,hξ⟩ := exists_sumTopForm s α
    have heq := hI.1 (α i) ξ ζ (by
      intro c hc p
      rw [hζ,hξ,Finset.sum_insert hi])
    rw [heq,ih ξ hξ,Finset.sum_insert hi]

/-- Exterior differentiation commutes with any finite sum of regular corner forms. -/
theorem derivative_sum {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {ι : Type*} (s : Finset ι) (ω : Form S r)
    (α : ι → Form S r) (η : Form S (r+1)) (δ : ι → Form S (r+1))
    (hα : ∀ i ∈ s, IsRegularForm 1 (α i))
    (hη : HasDerivative ω η) (hδ : ∀ i ∈ s, HasDerivative (α i) (δ i))
    (hsum : ∀ c hc p, ω.field c hc p = ∑ i ∈ s, (α i).field c hc p) :
    ∀ c hc p, η.field c hc p = ∑ i ∈ s, (δ i).field c hc p := by
  intro c hc p
  have heq : ambientForm ω c hc = ∑ i ∈ s, ambientForm (α i) c hc := by
    funext x
    by_cases hx : x ∈ orthantSet d c.1
    · by_cases ht : (⟨x,hx⟩ : Orthant d c.1) ∈ c.2.target
      · simpa only [Finset.sum_apply,ambientForm,hx,dite_true,ht] using
          hsum c hc ⟨c.2.symm ⟨x,hx⟩,c.2.map_target ht⟩
      · simp only [Finset.sum_apply,ambientForm,hx,dite_true,ht,dite_false,Finset.sum_const_zero]
    · simp only [Finset.sum_apply,ambientForm,hx,dite_false,Finset.sum_const_zero]
  have hmem : (c.2 p.val).val ∈ Subtype.val '' c.2.target :=
    ⟨c.2 p.val,c.2.map_source p.property,rfl⟩
  rw [hη c hc p,heq]
  simp only [extDerivWithin]
  rw [fderivWithin_sum (uniqueDiffOn_orthantDomain c.2.open_target _ hmem)
    (fun i hi => (ambientForm_contDiffOn (α i) 1 (hα i hi) c hc).differentiableOn
      (by norm_num) _ hmem)]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean d) ℝ)
    (∑ i ∈ s, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (hδ i hi c hc p).symm


end SmoothManifolds.CornerStokesResults

namespace SmoothManifolds.CornerFormDescent
open ModelData CornerData CornerStokesData CornerFaceOrientations Set Filter
universe u

/-- The actual transition derivative varies continuously on the overlap. -/
theorem transitionDerivative_continuous {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d) :
    Continuous (fun p : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
      cornerTransitionDerivative c d h p.val p.property.1 p.property.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := cornerTransitionExtension c d h p.val p.property.1 p.property.2
  have hcoord : ContinuousAt (fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
      (c.2 q.val).val) p :=
    continuous_subtype_val.continuousAt.comp
      ((c.2.continuousAt p.property.1).comp continuous_subtype_val.continuousAt)
  have hder : ContinuousAt (fderiv ℝ H.map) (c.2 p.val).val :=
    (H.smooth.continuousOn_fderiv_of_isOpen H.isOpen_domain (by simp)).continuousAt
      (H.isOpen_domain.mem_nhds H.mem_domain)
  have hdercoord : ContinuousAt (fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
      fderiv ℝ H.map (c.2 q.val).val) p :=
    hder.comp (f := fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} => (c.2 q.val).val) hcoord
  apply hdercoord.congr
  filter_upwards [hcoord.eventually (H.isOpen_domain.mem_nhds H.mem_domain)] with q hqU
  let G : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 q.val) :=
    ⟨H.domain,H.isOpen_domain,hqU,H.map,H.smooth,H.agrees⟩
  exact (cornerTransitionDerivative_eq c d h q.val q.property.1 q.property.2 G).symm

/-- Continuous compatible alternating covectors descend from any covering subatlas. -/
theorem form_extension {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (A : Set (CornerChart n M)) (hsub : A ⊆ S.atlas)
    (hcover : ∀ p : M, ∃ c ∈ A, p ∈ c.2.source)
    (F : ∀ c : CornerChart n M, c ∈ A → c.2.source →
      (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ)
    (hFcont : ∀ c hc, Continuous (F c hc))
    (hFcomp : ∀ (c d : CornerChart n M) (hc : c ∈ A) (hd : d ∈ A)
      (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
      (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p)),
      F c hc ⟨p,hp⟩ = (F d hd ⟨p,hq⟩).compContinuousLinearMap
        (fderiv ℝ H.map (c.2 p).val)) :
    ∃ ω : Form S r, (∀ c hc, Continuous (ω.field c hc)) ∧
      ∀ c (hc : c ∈ A) (p : c.2.source), ω.field c (hsub hc) p = F c hc p := by
  have hcover0 := hcover
  choose a ha hpa using hcover0
  let compat := fun c (hc : c ∈ S.atlas) d (hd : d ∈ S.atlas) => S.maximal.1.2 c hc d hd
  let f : ChartField S r := fun c hc p =>
    (F (a p.val) (ha p.val) ⟨p.val,hpa p.val⟩).compContinuousLinearMap
      (cornerTransitionDerivative c (a p.val) (compat c hc _ (hsub (ha p.val)))
        p.val p.property (hpa p.val))
  have hanchor : ∀ (c : CornerChart n M) (hc : c ∈ S.atlas) (p : c.2.source)
      (d : CornerChart n M) (hd : d ∈ A) (hpd : p.val ∈ d.2.source),
      f c hc p = (F d hd ⟨p.val,hpd⟩).compContinuousLinearMap
        (cornerTransitionDerivative c d (compat c hc d (hsub hd)) p.val p.property hpd) := by
    intro c hc p d hd hpd
    have had := hFcomp d (a p.val) hd (ha p.val) p.val hpd (hpa p.val)
      (cornerTransitionExtension d (a p.val) (compat d (hsub hd) _ (hsub (ha p.val)))
        p.val hpd (hpa p.val))
    change F d hd ⟨p.val,hpd⟩ = (F (a p.val) (ha p.val) ⟨p.val,hpa p.val⟩).compContinuousLinearMap (cornerTransitionDerivative d (a p.val)
        (compat d (hsub hd) _ (hsub (ha p.val))) p.val hpd (hpa p.val)) at had
    rw [had]
    dsimp only [f]
    rw [cornerTransitionDerivative_comp c d (a p.val) (compat c hc d (hsub hd))
      (compat d (hsub hd) _ (hsub (ha p.val))) (compat c hc _ (hsub (ha p.val)))
      p.val p.property hpd (hpa p.val)]
    ext v
    rfl
  have hcont : ∀ c hc, Continuous (f c hc) := by
    intro c hc
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨d,hd,hpd⟩ := hcover p.val
    let U : Set c.2.source := {q | q.val ∈ d.2.source}
    have hU : IsOpen U := d.2.open_source.preimage continuous_subtype_val
    let inc : U → {q : M // q ∈ c.2.source ∧ q ∈ d.2.source} :=
      fun q => ⟨q.val.val,q.val.property,q.property⟩
    have hinc : Continuous inc := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hFd : Continuous (fun q : U => F d hd ⟨q.val.val,q.property⟩) :=
      (hFcont d hd).comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    have hD : Continuous (fun q : U => cornerTransitionDerivative c d
        (compat c hc d (hsub hd)) q.val.val q.val.property q.property) :=
      (transitionDerivative_continuous c d (compat c hc d (hsub hd))).comp hinc
    have hh : Continuous (fun q : U => f c hc q.val) := by
      have heq : (fun q : U => f c hc q.val) =
          (fun q : U => (F d hd ⟨q.val.val,q.property⟩).compContinuousLinearMap
            (cornerTransitionDerivative c d (compat c hc d (hsub hd))
              q.val.val q.val.property q.property)) :=
        funext fun q => hanchor c hc q.val d hd q.property
      rw [heq]
      exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp hD).clm_apply hFd
    apply (hU.isOpenEmbedding_subtypeVal.continuousAt_iff (g := f c hc)
      (x := ⟨p,hpd⟩)).mp
    convert hh.continuousAt (x := (⟨p,hpd⟩ : U)) using 1
    rfl
  let ω : Form S r := {
    field := f
    compatible := by
      intro c d hc hd p hp hq H
      obtain ⟨e,he,hpe⟩ := hcover p
      rw [hanchor c hc ⟨p,hp⟩ e he hpe,hanchor d hd ⟨p,hq⟩ e he hpe,
        cornerTransitionDerivative_comp c d e (compat c hc d hd)
          (compat d hd e (hsub he)) (compat c hc e (hsub he)) p hp hq hpe,
        cornerTransitionDerivative_eq c d (compat c hc d hd) p hp hq H]
      ext v
      rfl }
  refine ⟨ω,hcont,?_⟩
  intro c hc p
  change f c (hsub hc) p = _
  rw [hanchor c (hsub hc) p c hc p.property,cornerTransitionDerivative_self]
  ext v
  rfl

end SmoothManifolds.CornerFormDescent

namespace SmoothManifolds.CornerFaceForms
open ModelData CornerData CornerOrientationData CornerStokesData CornerFaceOrientations
  CornerStokesResults CornerFormDescent Set Filter
universe u

theorem face_restriction_exists {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (T : CornerManifold n (ResolvedFaceSpace S))
    (hT : T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e})
    (ω : Form S n) (hω : ∀ c hc, Continuous (ω.field c hc))
    (hcompact : IsCompact (formSupport ω)) :
    ∃ β : CompactTopForm T, CornerStokesData.IsFaceRestriction ω β.form ∧
      formSupport β.form ⊆ faceProjection S ⁻¹' formSupport ω := by
  let A : Set (CornerChart n (ResolvedFaceSpace S)) := {e | IsResolvedFaceChart S e}
  choose c hc i hi hek hes hec using (fun e : A => e.property)
  let incl (e : A) : e.val.2.source → (c e).2.source :=
    fun q => ⟨q.val.1, by
      have hq' : q.val ∈ faceSheet S (c e) (i e) univ :=
        Eq.mp (congrArg (fun U : Set (ResolvedFaceSpace S) => q.val ∈ U) (hes e)) q.property
      exact hq'.2.1⟩
  let F : ∀ e : CornerChart n (ResolvedFaceSpace S), e ∈ A → e.2.source →
      (Euclidean n) [⋀^Fin n]→L[ℝ] ℝ := fun e he q =>
    (ω.field (c ⟨e,he⟩) (hc ⟨e,he⟩) (incl ⟨e,he⟩ q)).compContinuousLinearMap
      (faceInsertion (i ⟨e,he⟩)).toContinuousLinearMap
  have hFcont : ∀ e he, Continuous (F e he) := by
    intro e he
    have hinc : Continuous (incl ⟨e,he⟩) :=
      ((Corners.face_projection_continuous S).comp continuous_subtype_val).subtype_mk _
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (faceInsertion (i ⟨e,he⟩)).toContinuousLinearMap).continuous.comp
        ((hω _ _).comp hinc)
  have hFcomp : ∀ (e f : CornerChart n (ResolvedFaceSpace S)) (he : e ∈ A) (hf : f ∈ A)
      (q : ResolvedFaceSpace S) (hp : q ∈ e.2.source) (hq : q ∈ f.2.source)
      (H : OrthantExtension (e.2.symm.trans f.2).source (e.2.symm.trans f.2) (e.2 q)),
      F e he ⟨q,hp⟩ = (F f hf ⟨q,hq⟩).compContinuousLinearMap
        (fderiv ℝ H.map (e.2 q).val) := by
    intro e f he hf q hp hq H
    let ee : A := ⟨e,he⟩
    let ff : A := ⟨f,hf⟩
    exact face_covector_compatible S ω (c ee) (c ff) (hc ee) (hc ff) (i ee) (i ff)
      (hi ee) (hi ff) e f (hes ee) (hes ff) (hec ee) (hec ff) q hp hq
      (incl ee ⟨q,hp⟩).property (incl ff ⟨q,hq⟩).property H
  have hsub : A ⊆ T.atlas := by
    rw [hT]
    exact Corners.cornerAtlas_subset_maximalExtension (Corners.resolved_face_atlas S)
  obtain ⟨β,hβcont,hβ⟩ := form_extension T A hsub (Corners.resolved_face_atlas S).1 F hFcont hFcomp
  have hrestrict : CornerStokesData.IsFaceRestriction ω β := by
    intro d hd j hj e he hek' hes' hec' q hq hp v
    have heA : e ∈ A := ⟨d,hd,j,hj,hek',hes',hec'⟩
    rw [hβ e heA ⟨q,hq⟩]
    let ee : A := ⟨e,heA⟩
    have hsame := face_covector_representation_independent S ω (c ee) d (hc ee) hd
      (i ee) j (hi ee) hj e (hes ee) hes' (hec ee) hec' q hq
      (incl ee ⟨q,hq⟩).property hp
    exact congrArg (fun a : (Euclidean n) [⋀^Fin n]→L[ℝ] ℝ => a v) hsame
  have hsupp : formSupport β ⊆ faceProjection S ⁻¹' formSupport ω := by
    apply closure_minimal _ (isClosed_closure.preimage (Corners.face_projection_continuous S))
    rintro q ⟨f,hf,hq,hne⟩
    by_contra hn
    obtain ⟨e,he,hqe⟩ := (Corners.resolved_face_atlas S).1 q
    let ee : A := ⟨e,he⟩
    have hz : ω.field (c ee) (hc ee) (incl ee ⟨q,hqe⟩) = 0 := by
      by_contra hz
      exact hn (subset_closure ⟨c ee,hc ee,(incl ee ⟨q,hqe⟩).property,hz⟩)
    have hβ0 : β.field e (hsub he) ⟨q,hqe⟩ = 0 := by
      rw [hβ e he ⟨q,hqe⟩]
      dsimp only [F]
      rw [hz]
      ext v
      rfl
    have htrans := β.compatible f e hf (hsub he) q hq hqe
      (cornerTransitionExtension f e (T.maximal.1.2 f hf e (hsub he)) q hq hqe)
    rw [hβ0] at htrans
    exact hne (by rw [htrans]; ext v; rfl)
  have hβcompact : IsCompact (formSupport β) := by
    letI := T.hausdorff
    exact ((Corners.face_projection_proper S).isCompact_preimage hcompact).of_isClosed_subset
      isClosed_closure hsupp
  exact ⟨⟨β,hβcont,hβcompact⟩,hrestrict,hsupp⟩

theorem faceRestriction_field_unique {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (T : CornerManifold n (ResolvedFaceSpace S))
    (hT : T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e})
    (ω : Form S n) (β γ : Form T n)
    (hβ : CornerStokesData.IsFaceRestriction ω β)
    (hγ : CornerStokesData.IsFaceRestriction ω γ)
    (f : CornerChart n (ResolvedFaceSpace S)) (hf : f ∈ T.atlas) (p : f.2.source) :
    β.field f hf p = γ.field f hf p := by
  obtain ⟨e,he,hpe⟩ := (Corners.resolved_face_atlas S).1 p.val
  obtain ⟨c,hc,i,hi,hek,hes,hec⟩ := he
  have heT : e ∈ T.atlas := by
    rw [hT]
    exact Corners.cornerAtlas_subset_maximalExtension (Corners.resolved_face_atlas S)
      ⟨c,hc,i,hi,hek,hes,hec⟩
  have hpface : p.val ∈ faceSheet S c i univ := hes ▸ hpe
  have hpbase : p.val.1 ∈ c.2.source := hpface.2.1
  have heq : β.field e heT ⟨p.val,hpe⟩ = γ.field e heT ⟨p.val,hpe⟩ := by
    ext v
    rw [hβ c hc i hi e heT hek hes hec p.val hpe hpbase v,
      hγ c hc i hi e heT hek hes hec p.val hpe hpbase v]
  let K := cornerTransitionExtension f e (T.maximal.1.2 f hf e heT) p.val p.property hpe
  rw [β.compatible f e hf heT p.val p.property hpe K,
    γ.compatible f e hf heT p.val p.property hpe K,heq]

theorem faceRestriction_support {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (T : CornerManifold n (ResolvedFaceSpace S))
    (hT : T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e})
    (ω : Form S n) (β : Form T n)
    (hβ : CornerStokesData.IsFaceRestriction ω β) :
    formSupport β ⊆ faceProjection S ⁻¹' formSupport ω := by
  apply closure_minimal _ (isClosed_closure.preimage (Corners.face_projection_continuous S))
  rintro q ⟨f,hf,hq,hne⟩
  by_contra hn
  obtain ⟨e,he,hqe⟩ := (Corners.resolved_face_atlas S).1 q
  obtain ⟨c,hc,i,hi,hek,hes,hec⟩ := he
  have heT : e ∈ T.atlas := by
    rw [hT]
    exact Corners.cornerAtlas_subset_maximalExtension (Corners.resolved_face_atlas S)
      ⟨c,hc,i,hi,hek,hes,hec⟩
  have hqface : q ∈ faceSheet S c i univ := hes ▸ hqe
  have hp : q.1 ∈ c.2.source := hqface.2.1
  have hz : ω.field c hc ⟨q.1,hp⟩ = 0 := by
    by_contra hz
    exact hn (subset_closure ⟨c,hc,hp,hz⟩)
  have hβ0 : β.field e heT ⟨q,hqe⟩ = 0 := by
    ext v
    rw [hβ c hc i hi e heT hek hes hec q hqe hp v,hz]
    rfl
  let K := cornerTransitionExtension f e (T.maximal.1.2 f hf e heT) q hq hqe
  have htrans := β.compatible f e hf heT q hq hqe K
  rw [hβ0] at htrans
  exact hne (by rw [htrans]; ext v; rfl)

end SmoothManifolds.CornerFaceForms

namespace SmoothManifolds.CornerStokesResults
open ModelData CornerData CornerOrientationData CornerStokesData CornerFaceForms
universe u

theorem top_forms : Specs.SmoothManifolds.Corners.Stokes.top_formsType.{u} := by
  intro n M _ S o T b hb ω hω hcompact
  let η := derivativeTopForm ω hω hcompact
  obtain ⟨β,hβ,hβsupport⟩ := face_restriction_exists S T hb.1 ω
    (regularForm_continuous ω 1 hω) hcompact
  exact ⟨η,β,(by intro c hc p; rfl),
    derivative_support ω η.form (by intro c hc p; rfl),hβ,hβsupport⟩

end SmoothManifolds.CornerStokesResults

namespace SmoothManifolds.CornerStokesResults
open ModelData CornerData CornerOrientationData CornerStokesData LocalStokesData CornerFaceForms Set MeasureTheory Filter
universe u

/-- Distinct local faces from one bulk chart give disjoint resolved sheets,
including at intersections of coordinate faces. -/
theorem faceSheet_index_unique {d : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold d M) (c : CornerChart d M)
    (i j : Fin d) (hi : i.val < c.1.val) (hj : j.val < c.1.val)
    (q : ResolvedFaceSpace S)
    (hqi : q ∈ faceSheet S c i univ) (hqj : q ∈ faceSheet S c j univ) : i = j := by
  let I : activeCoordinates (c.2 q.1) := ⟨i, by simp [activeCoordinates,hi,hqi.2.2.1]⟩
  let J : activeCoordinates (c.2 q.1) := ⟨j, by simp [activeCoordinates,hj,hqj.2.2.1]⟩
  have hIJ : chartFaceGerm c q.1 I.val = chartFaceGerm c q.1 J.val :=
    hqi.2.2.2.symm.trans hqj.2.2.2
  exact congrArg Subtype.val (Corners.chart_coordinate_germs_injective c q.1 hqi.2.1 hIJ)

/-- Local equality on one chart suffices for equality of its coordinate integrals. -/
theorem chartIntegral_congr_on_chart {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (o : CornerOrientation S)
    (c : CornerChart d M) (hc : c ∈ S.atlas) (α β : CornerStokesData.Form S d)
    (h : ∀ p : c.2.source, α.field c hc p = β.field c hc p) :
    chartIntegral o c hc α = chartIntegral o c hc β := by
  unfold chartIntegral
  congr 1
  funext x
  unfold chartCoefficient
  split_ifs <;> simp [h]

/-- A compact face form supported over a single bulk chart integrates once
on each of that chart's finitely many local sheets. No compactness of support
on the open depth-one stratum occurs in the statement or proof. -/
theorem resolved_integral_over_chart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T)
    (J : CompactTopForm T → ℝ) (hJ : IsIntegral b J)
    (K : Set M) (hKc : K ⊆ c.2.source)
    (β : CompactTopForm T) (hβ : formSupport β.form ⊆ faceProjection S ⁻¹' K)
    (e : {i : Fin (n+1) // i.val < c.1.val} → CornerChart n (ResolvedFaceSpace S))
    (he : ∀ i, e i ∈ T.atlas)
    (hes : ∀ i, (e i).2.source = faceSheet S c i.val univ) :
    J β = ∑ i, chartIntegral b (e i) (he i) β.form := by
  letI := T.hausdorff
  letI : LocallyCompactSpace (ResolvedFaceSpace S) := Corners.locally_compact T
  let A := {i : Fin (n+1) // i.val < c.1.val}
  have hcov : formSupport β.form ⊆ ⋃ i : A, (e i).2.source := by
    intro q hq
    have hp : q.1 ∈ c.2.source := hKc (hβ hq)
    obtain ⟨i,hi⟩ := (Corners.chart_face_germs S c hc q.1 hp).2 q.2
    let a : A := ⟨i.val,(Finset.mem_filter.mp i.property).2.1⟩
    refine mem_iUnion.mpr ⟨a,?_⟩
    rw [hes a]
    refine ⟨mem_univ _,hp,(Finset.mem_filter.mp i.property).2.2,?_⟩
    exact (congrArg Subtype.val hi).symm
  let a : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hcovFin : formSupport β.form ⊆ ⋃ i : Fin (Fintype.card A), (e (a i)).2.source := by
    intro q hq
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcov hq)
    refine mem_iUnion.mpr ⟨a.symm j,?_⟩
    rw [Equiv.apply_symm_apply]
    exact hj
  obtain ⟨ρ0,hsub0,hsum0,_,_⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun i : Fin (Fintype.card A) => (e (a i)).2.open_source) β.compact_support hcovFin
  let ρ : A → C(ResolvedFaceSpace S,ℝ) := fun i => ρ0 (a.symm i)
  have hsub (i : A) : sectionSupport (fun p => ρ i p) ⊆ (e i).2.source := by
    have ht := hsub0 (a.symm i)
    rw [Equiv.apply_symm_apply] at ht
    exact ht
  have hsum {q : ResolvedFaceSpace S} (hq : q ∈ formSupport β.form) :
      ∑ i : A, ρ i q = 1 := by
    rw [← Equiv.sum_comp a]
    simpa only [ρ,Equiv.symm_apply_apply,Finset.sum_apply,Pi.one_apply] using hsum0 hq
  have hρ : ∀ i : A, Continuous (fun p => ρ i p) := fun i => (ρ i).continuous
  have hsingle (i : A) (q : ResolvedFaceSpace S)
      (hq : q ∈ (e i).2.source) (hqβ : q ∈ formSupport β.form) : ρ i q = 1 := by
    have hsumq := hsum hqβ
    have hsumone : (∑ j : A, ρ j q) = ρ i q := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_contra hnonzero
        have hqj : q ∈ (e j).2.source := hsub j (subset_closure hnonzero)
        have hindices := faceSheet_index_unique S c i.val j.val i.property j.property q
          ((hes i) ▸ hq) ((hes j) ▸ hqj)
        exact hji (Subtype.ext hindices.symm)
      · intro hi
        exact (hi (Finset.mem_univ _)).elim
    exact hsumone.symm.trans hsumq
  let α : A → CompactTopForm T := fun i => weightTopForm (fun p => ρ i p) (hρ i) β
  let σ : ResolvedFaceSpace S → ℝ := fun q => ∑ i : A, ρ i q
  have hσ : Continuous σ := continuous_finsetSum _ (fun i _ => hρ i)
  let ζ := weightTopForm σ hσ β
  have hζ : J ζ = J β := by
    have h := hJ.2.1 1 β ζ (by
      intro a ha p
      change σ p.val • β.form.field a ha p = 1 • β.form.field a ha p
      by_cases hz : β.form.field a ha p = 0
      · simp [hz]
      · have hp : p.val ∈ formSupport β.form := subset_closure ⟨a,ha,p.property,hz⟩
        rw [show σ p.val = 1 from hsum hp])
    simpa using h
  calc
    J β = J ζ := hζ.symm
    _ = ∑ i : A, J (α i) := integral_weight_sum J hJ β (fun i p => ρ i p) hρ Finset.univ
    _ = ∑ i : A, chartIntegral b (e i) (he i) (α i).form := by
      apply Finset.sum_congr rfl
      intro i _
      exact hJ.2.2 (e i) (he i) (α i)
        (fun p hp => hsub i (weightForm_support (fun p => ρ i p) β.form hp).1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply chartIntegral_congr_on_chart
      intro p
      change ρ i p.val • β.form.field (e i) (he i) p = β.form.field (e i) (he i) p
      by_cases hz : β.form.field (e i) (he i) p = 0
      · simp [hz]
      · have hp : p.val ∈ formSupport β.form := subset_closure ⟨e i,he i,p.property,hz⟩
        rw [hsingle i p.val p.property hp,one_smul]


/-- Empty local face patches contribute a zero boundary coefficient. -/
theorem boundaryCoefficient_zero_of_empty_patch {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S) (ω : Form S n)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas) (i : Fin (n+1))
    (hpatch : ¬ Nonempty (ChartFacePatch c i)) (y : Euclidean n) :
    orthantBoundaryCoefficient (signedAmbientForm o ω c hc) i y = 0 := by
  by_cases hm : i.insertNth (0 : ℝ) y ∈ orthantSet (n+1) c.1
  · by_cases ht : (⟨i.insertNth 0 y,hm⟩ : Orthant (n+1) c.1) ∈ c.2.target
    · let x : Orthant (n+1) c.1 := ⟨i.insertNth 0 y,hm⟩
      let p := c.2.symm x
      have hp : p ∈ c.2.source := c.2.map_target ht
      have hz : (c.2 p).val i = 0 := by
        rw [c.2.right_inv ht]
        simp [x]
      exact (hpatch ⟨⟨p,hp,hz⟩⟩).elim
    · simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hm,ht]
  · simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hm]

/-- A partial chart with empty source and target, available when the base is
nonempty. It represents a constrained face missed by one bulk chart. -/
def emptyResolvedChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (q : ResolvedFaceSpace S) (k : Fin (n+1)) :
    CornerChart n (ResolvedFaceSpace S) :=
  ⟨k,{
    toPartialEquiv := {
      toFun := fun _ => ⟨0,by intro i hi; exact le_rfl⟩
      invFun := fun _ => q
      source := ∅
      target := ∅
      map_source' := by simp
      map_target' := by simp
      left_inv' := by simp
      right_inv' := by simp }
    continuousOn_toFun := continuous_const.continuousOn
    continuousOn_invFun := continuous_const.continuousOn
    open_source := isOpen_empty
    open_target := isOpen_empty }⟩

theorem exists_resolved_chart_in_canonical_atlas {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (T : CornerManifold n (ResolvedFaceSpace S))
    (hT : T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e})
    (q0 : ResolvedFaceSpace S) (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (i : Fin (n+1)) (hi : i.val < c.1.val) :
    ∃ e : CornerChart n (ResolvedFaceSpace S), e ∈ T.atlas ∧
      e.1 = faceConstraintCount c.1 ∧ e.2.source = faceSheet S c i univ ∧
      ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val) := by
  have hsub : {e | IsResolvedFaceChart S e} ⊆ T.atlas := by
    rw [hT]
    exact (Corners.corner_atlas_extension _ (Corners.resolved_face_atlas S)).2
  by_cases hp : Nonempty (ChartFacePatch c i)
  · obtain ⟨p⟩ := hp
    obtain ⟨e,hes,hec⟩ := Corners.exists_resolvedFaceChart S c hc i hi p
    let E : CornerChart n (ResolvedFaceSpace S) := ⟨faceConstraintCount c.1,e⟩
    exact ⟨E,hsub ⟨c,hc,i,hi,rfl,hes,hec⟩,rfl,hes,hec⟩
  · have hs : faceSheet S c i univ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact hp ⟨⟨q.1,hq.2.1,hq.2.2.1⟩⟩
    let E := emptyResolvedChart S q0 (faceConstraintCount c.1)
    have hEs : E.2.source = faceSheet S c i univ := by
      change ∅ = _
      exact hs.symm
    have hEc : ∀ q ∈ E.2.source, (E.2 q).val = i.removeNth ((c.2 q.1).val) := by
      intro q hq
      exact hq.elim
    exact ⟨E,hsub ⟨c,hc,i,hi,rfl,hEs,hEc⟩,rfl,hEs,hEc⟩

/-- The face chart integral is the local orthant face term, including zero
extension beyond the chart target. -/
theorem chartIntegral_face_eq_orthant {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    {T : CornerManifold n (ResolvedFaceSpace S)} (b : CornerOrientation T)
    (hOb : IsResolvedOrientation o b) (ω : Form S n) (β : Form T n)
    (hβ : CornerStokesData.IsFaceRestriction ω β)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (i : Fin (n+1)) (hi : i.val < c.1.val)
    (e : CornerChart n (ResolvedFaceSpace S)) (he : e ∈ T.atlas)
    (hek : e.1 = faceConstraintCount c.1)
    (hes : e.2.source = faceSheet S c i univ)
    (hecoord : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val)) :
    chartIntegral b e he β = ∫ y in orthantFaceSet c.1 i,
      orthantBoundaryCoefficient (signedAmbientForm o ω c hc) i y := by
  have hcoef := funext (signedAmbientForm_face_eq_chartCoefficient
    o b hOb ω β hβ c hc i hi e he hek hes hecoord)
  rw [chartIntegral,←hcoef]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro y hy
  change i.insertNth (0 : ℝ) y ∉ orthantSet (n+1) c.1 at hy
  simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hy]

/-- Stokes for a compact C¹ corner form whose entire support is in one chart. -/
theorem chart_supported_stokes {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold (n+1) M) (o : CornerOrientation S)
    (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T)
    (hb : IsResolvedOrientation o b)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral b J)
    (c : CornerChart (n+1) M) (hc : c ∈ S.atlas) (ω : Form S n)
    (hω : IsRegularForm 1 ω) (hcompact : IsCompact (formSupport ω))
    (hsource : formSupport ω ⊆ c.2.source)
    (η : CompactTopForm S) (β : CompactTopForm T) (hη : HasDerivative ω η.form)
    (hηsupport : formSupport η.form ⊆ formSupport ω)
    (hβ : CornerStokesData.IsFaceRestriction ω β.form)
    (hβsupport : formSupport β.form ⊆ faceProjection S ⁻¹' c.2.source) : I η = J β := by
  have hloc := local_orthant_stokes n c.1 (signedAmbientForm o ω c hc)
    (signedAmbientForm_regular o ω c hc hω hcompact hsource)
    (signedAmbientForm_hasCompactSupport o ω c hc hcompact hsource)
  have hbulk : I η = ∫ x in orthantSet (n+1) c.1,
      orthantBulkCoefficient c.1 (signedAmbientForm o ω c hc) x := by
    rw [hI.2.2 c hc η (hηsupport.trans hsource)]
    exact chartIntegral_derivative_eq_orthant o ω η.form hη c hc hcompact hsource
  rw [hbulk,hloc.2.2]
  by_cases hfaces : Nonempty (ResolvedFaceSpace S)
  · obtain ⟨q0⟩ := hfaces
    let A := {i : Fin (n+1) // i.val < c.1.val}
    choose e he hek hes hecoord using
      (fun i : A => exists_resolved_chart_in_canonical_atlas S T hb.1 q0 c hc i.val i.property)
    rw [resolved_integral_over_chart S c hc T b J hJ c.2.source Subset.rfl β hβsupport e he hes]
    have hterm (i : A) : chartIntegral b (e i) (he i) β.form =
        ∫ y in orthantFaceSet c.1 i.val,
          orthantBoundaryCoefficient (signedAmbientForm o ω c hc) i.val y :=
      chartIntegral_face_eq_orthant o b hb ω β.form hβ c hc i.val i.property (e i) (he i)
        (hek i) (hes i) (hecoord i)
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro i; simp) _
  · have hpatch (i : Fin (n+1)) (hi : i.val < c.1.val) : ¬ Nonempty (ChartFacePatch c i) := by
      rintro ⟨p⟩
      have hia : i ∈ activeCoordinates (c.2 p.val) := by simp [activeCoordinates,hi,p.property.2]
      exact hfaces ⟨⟨p.val,chartFaceAt S c hc p.val p.property.1 ⟨i,hia⟩⟩⟩
    have hzero : J β = 0 := by
      have h := hJ.2.1 0 β β (by
        intro e he p
        exact (hfaces ⟨p.val⟩).elim)
      simpa using h
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro y _
      exact boundaryCoefficient_zero_of_empty_patch o ω c hc i (hpatch i hi) y
    · rfl


theorem regularScalar_mono {d : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {s t : ℕ∞} {ρ : M → ℝ}
    (hρ : RegularScalar S t ρ) (hst : s ≤ t) : RegularScalar S s ρ := by
  intro c hc p
  obtain ⟨U,hU,hpU,F,hF,he⟩ := hρ c hc p
  exact ⟨U,hU,hpU,F,hF.of_le (by exact_mod_cast hst),he⟩

theorem regular_weightForm {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} {s : ℕ∞} (ρ : M → ℝ) (ω : Form S r)
    (hρ : RegularScalar S s ρ) (hω : IsRegularForm s ω) :
    IsRegularForm s (weightForm ρ ω) := regular_weight ρ ω hρ hω

theorem weightForm_compact {d r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold d M} (ρ : M → ℝ) (ω : Form S r)
    (hω : IsCompact (formSupport ω)) : IsCompact (formSupport (weightForm ρ ω)) :=
  hω.of_isClosed_subset isClosed_closure (fun _ hp => (weightForm_support ρ ω hp).2)

theorem scalar_comp_support {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (ρ : Y → ℝ) :
    sectionSupport (fun x => ρ (f x)) ⊆ f ⁻¹' sectionSupport ρ := by
  apply closure_minimal _ (isClosed_closure.preimage hf)
  intro x hx
  exact subset_closure hx

theorem weight_face_restriction {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} {T : CornerManifold n (ResolvedFaceSpace S)}
    (ρ : M → ℝ) (ω : Form S n) (β : Form T n) (hβ : CornerStokesData.IsFaceRestriction ω β) :
    CornerStokesData.IsFaceRestriction (weightForm ρ ω) (weightForm (fun q => ρ (faceProjection S q)) β) := by
  intro c hc i hi e he hek hes hecoords q hq hp v
  change (ρ q.1 • β.field e he ⟨q,hq⟩) v =
    (ρ q.1 • ω.field c hc ⟨q.1,hp⟩) (fun j => faceInsertion i (v j))
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [hβ c hc i hi e he hek hes hecoords q hq hp v]

/-- Finite smooth localization assembles global Stokes from its chart-supported case. -/
theorem global_stokes_of_local
    (hlocal : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      (S : CornerManifold (n+1) M) (o : CornerOrientation S)
      (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T),
      IsResolvedOrientation o b →
      ∀ (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
      IsIntegral o I → IsIntegral b J →
      ∀ (c : CornerChart (n+1) M) (hc : c ∈ S.atlas) (ω : Form S n),
      IsRegularForm 1 ω → IsCompact (formSupport ω) → formSupport ω ⊆ c.2.source →
      ∀ (η : CompactTopForm S) (β : CompactTopForm T), HasDerivative ω η.form →
      formSupport η.form ⊆ formSupport ω → CornerStokesData.IsFaceRestriction ω β.form →
      formSupport β.form ⊆ faceProjection S ⁻¹' c.2.source → I η = J β) :
    Specs.SmoothManifolds.Corners.Stokes.stokesType.{u} := by
  intro n M _ S o T b hb I J hI hJ ω hω hcompact
  obtain ⟨η,β,hη,hηsupport,hβ,hβsupport⟩ := top_forms S o T b hb ω hω hcompact
  obtain ⟨m,c,hc,ρ,hρ,hρreg,hρsupport,_,V,hV,hKV,hsum⟩ :=
    finite_smooth_chart_localizers S (formSupport ω) hcompact
  let α (i : Fin m) := weightForm (ρ i) ω
  have hαreg (i : Fin m) : IsRegularForm 1 (α i) :=
    regular_weightForm (ρ i) ω (regularScalar_mono (hρreg i) le_top) hω
  have hαcompact (i : Fin m) : IsCompact (formSupport (α i)) :=
    weightForm_compact (ρ i) ω hcompact
  have hαsource (i : Fin m) : formSupport (α i) ⊆ (c i).2.source :=
    fun _ hp => hρsupport i (weightForm_support _ _ hp).1
  let δ (i : Fin m) := derivativeTopForm (α i) (hαreg i) (hαcompact i)
  have hδ (i : Fin m) : HasDerivative (α i) (δ i).form := by intro e he p; rfl
  have hδsupport (i : Fin m) : formSupport (δ i).form ⊆ formSupport (α i) :=
    derivative_support (α i) (δ i).form (hδ i)
  let γ (i : Fin m) := weightTopForm (fun q => ρ i (faceProjection S q))
    ((hρ i).comp (Corners.face_projection_continuous S)) β
  have hγ (i : Fin m) : CornerStokesData.IsFaceRestriction (α i) (γ i).form :=
    weight_face_restriction (ρ i) ω β.form hβ
  have hγsource (i : Fin m) :
      formSupport (γ i).form ⊆ faceProjection S ⁻¹' (c i).2.source := by
    intro q hq
    exact hρsupport i (scalar_comp_support (Corners.face_projection_continuous S)
      (ρ i) (weightForm_support _ _ hq).1)
  have hωsum : ∀ e he p, ω.field e he p = ∑ i ∈ (Finset.univ : Finset (Fin m)), (α i).field e he p := by
    intro e he p
    change ω.field e he p = ∑ i ∈ (Finset.univ : Finset (Fin m)), ρ i p.val • ω.field e he p
    by_cases hz : ω.field e he p = 0
    · simp [hz]
    · rw [← Finset.sum_smul]
      rw [hsum p.val (hKV (subset_closure ⟨e,he,p.property,hz⟩)),one_smul]
  have hηsum := derivative_sum Finset.univ ω α η.form (fun i => (δ i).form)
    (fun i _ => hαreg i) hη (fun i _ => hδ i) hωsum
  have hβsum : ∀ e he p, β.form.field e he p =
      ∑ i ∈ (Finset.univ : Finset (Fin m)), (γ i).form.field e he p := by
    intro e he p
    change β.form.field e he p =
      ∑ i ∈ (Finset.univ : Finset (Fin m)), ρ i (faceProjection S p.val) • β.form.field e he p
    by_cases hz : β.form.field e he p = 0
    · simp [hz]
    · rw [← Finset.sum_smul]
      rw [hsum (faceProjection S p.val)
        (hKV (hβsupport (subset_closure ⟨e,he,p.property,hz⟩))),one_smul]
  refine ⟨η,β,hη,hηsupport,hβ,hβsupport,?_⟩
  calc
    I η = ∑ i ∈ (Finset.univ : Finset (Fin m)), I (δ i) := integral_sum I hI _ δ η hηsum
    _ = ∑ i ∈ (Finset.univ : Finset (Fin m)), J (γ i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hlocal S o T b hb I J hI hJ (c i) (hc i) (α i) (hαreg i) (hαcompact i)
        (hαsource i) (δ i) (γ i) (hδ i) (hδsupport i) (hγ i) (hγsource i)
    _ = J β := (integral_sum J hJ _ γ β hβsum).symm


/-- Stokes on every oriented positive-dimensional smooth manifold with corners,
with compact support in the full base and every resolved local face counted once. -/
theorem stokes : Specs.SmoothManifolds.Corners.Stokes.stokesType.{u} :=
  global_stokes_of_local chart_supported_stokes

/-- The source theorem with the face structure and integral constructions supplied. -/
theorem canonical_stokes : Specs.SmoothManifolds.Corners.Stokes.canonical_stokesType.{u} := by
  intro n M _ S o ω hω hcompact
  obtain ⟨T,b,hb⟩ := CornerFaceOrientations.resolved_orientation o
  obtain ⟨I,hI,_⟩ := exists_integral S o
  obtain ⟨J,hJ,_⟩ := exists_integral T b
  exact ⟨T,b,hb,I,J,hI,hJ,stokes S o T b hb I J hI hJ ω hω hcompact⟩

end SmoothManifolds.CornerStokesResults
