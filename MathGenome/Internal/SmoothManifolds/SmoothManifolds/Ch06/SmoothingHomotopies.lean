import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.SmoothingHomotopies
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.RelativeManifoldApproximation
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.InteriorHomotopyEquivalence

namespace SmoothManifolds.SmoothingHomotopies
open ModelData AtlasData BoundaryData InteriorHomotopyData Set Filter
open scoped Topology
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- Add the time coordinate to an ambient extension. This is an extension on
an open Euclidean set, so it also applies at all cylinder corners. -/
theorem LocalCoordinateExtension.with_time {n m : ℕ} {X : Type u}
    [TopologicalSpace X] {ι : X → Euclidean n} {f : X → Euclidean m} {x : X}
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) ι f x)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (t : HomotopyTime) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z : HomotopyTime × X => Fin.cons z.1.val (ι z.2))
      (fun z => Fin.cons (φ z.1.val) (f z.2)) (t, x) := by
  obtain ⟨U, hU, hx, F, hF, heq⟩ := hf
  have htail : ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean (n + 1) => Fin.tail y) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) i.succ)
  have hFt := hF.comp htail.contDiffOn (fun _ hy => hy)
  refine ⟨Fin.tail ⁻¹' U, hU.preimage htail.continuous, by simpa using hx,
    fun y => Fin.cons (φ (y 0)) (F (Fin.tail y)), ?_, ?_⟩
  · apply contDiffOn_pi.mpr
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact (hφ.comp (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0)).contDiffOn
    | succ j =>
      simp only [Fin.cons_succ]
      exact (contDiffOn_pi.mp hFt) j
  · filter_upwards [heq.comp_tendsto (continuous_snd.continuousAt (x := (t, x)))] with z hz
    change F (ι z.2) = f z.2 at hz
    simpa only [Fin.tail_cons, Fin.cons_zero] using
      congrArg (fun v : Euclidean m => (@Fin.cons m (fun _ => ℝ) (φ z.1.val) v)) hz

/-- Reparameterize time and pull a smooth homotopy back by a smooth map. -/
theorem smoothHomotopy_precomp {n m l : ℕ} {a b c : ModelKind}
    {P : Type u} {N : Type v} {Y : Type w}
    [TopologicalSpace P] [TopologicalSpace N] [TopologicalSpace Y]
    (S : SmoothManifold n a P) (T : SmoothManifold m b N)
    (U : SmoothManifold l c Y) {H : HomotopyTime × N → Y}
    (hH : SmoothHomotopy T.smoothStructure.val U.smoothStructure.val H)
    {f : P → N} (hf : IsSmoothMap S T f)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφI : ∀ t : HomotopyTime, φ t.val ∈ Icc (0 : ℝ) 1) :
    SmoothHomotopy S.smoothStructure.val U.smoothStructure.val
      (fun z => H (⟨φ z.1.val, hφI z.1⟩, f z.2)) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  have hτ : Continuous (fun t : HomotopyTime => (⟨φ t.val, hφI t⟩ : HomotopyTime)) :=
    (hφ.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨hH.1.comp ((hτ.comp continuous_fst).prodMk (hfc.comp continuous_snd)), ?_⟩
  intro e he d hd z hx hHz
  obtain ⟨j, hj, hxj⟩ := T.smoothStructure.property.1.1 (f z.2)
  have hpair := LocalCoordinateExtension.with_time
    ((hf z.2).2 e he j hj hx hxj) φ hφ z.1
  have hmap : Continuous (fun z : HomotopyTime × P =>
      ((⟨φ z.1.val, hφI z.1⟩ : HomotopyTime), f z.2)) :=
    (hτ.comp continuous_fst).prodMk (hfc.comp continuous_snd)
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp
      (ι := fun w : HomotopyTime × N => Fin.cons w.1.val (j w.2).val)
      (f := fun w => (d (H w)).val)
      (h := fun z : HomotopyTime × P => (⟨φ z.1.val, hφI z.1⟩, f z.2))
      (hH.2 j hj d hd _ hxj hHz) hmap.continuousAt rfl) hpair

/-- Postcomposition preserves the ambient smooth cylinder test. -/
theorem smoothHomotopy_postcomp {n m l : ℕ} {a b c : ModelKind}
    {P : Type u} {N : Type v} {Y : Type w}
    [TopologicalSpace P] [TopologicalSpace N] [TopologicalSpace Y]
    (S : SmoothManifold n a P) (T : SmoothManifold m b N)
    (U : SmoothManifold l c Y) {H : HomotopyTime × P → N}
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H)
    {f : N → Y} (hf : IsSmoothMap T U f) :
    SmoothHomotopy S.smoothStructure.val U.smoothStructure.val (f ∘ H) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  refine ⟨hfc.comp hH.1, ?_⟩
  intro e he d hd z hx hfHz
  obtain ⟨j, hj, hHj⟩ := T.smoothStructure.property.1.1 (H z)
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp (ι := fun y : N => (j y).val)
      (f := fun y => (d (f y)).val) (h := H)
      ((hf (H z)).2 j hj d hd hHj hfHz) hH.1.continuousAt rfl)
    (hH.2 e he j hj z hx hHj)

/-- Smooth concatenation with a constant interval at the join. Both time
changes are globally smooth and take values in the closed interval. -/
theorem smoothHomotopy_trans {n m : ℕ} {a b : ModelKind}
    {P : Type u} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold n a P) (T : SmoothManifold m b N)
    {F₀ F₁ F₂ : P → N} {H J : HomotopyTime × P → N}
    (hH : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val H)
    (hJ : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val J)
    (hH0 : ∀ x, H (timeZero, x) = F₀ x) (hH1 : ∀ x, H (timeOne, x) = F₁ x)
    (hJ0 : ∀ x, J (timeZero, x) = F₁ x) (hJ1 : ∀ x, J (timeOne, x) = F₂ x) :
    ∃ K : HomotopyTime × P → N,
      SmoothHomotopy S.smoothStructure.val T.smoothStructure.val K ∧
      (∀ x, K (timeZero, x) = F₀ x) ∧ (∀ x, K (timeOne, x) = F₂ x) := by
  let φ : ℝ → ℝ := fun t => Real.smoothTransition (4 * t)
  let ψ : ℝ → ℝ := fun t => Real.smoothTransition (4 * t - 3)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hφI (t : HomotopyTime) : φ t.val ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hψI (t : HomotopyTime) : ψ t.val ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  let A : HomotopyTime × P → N := fun z => H (⟨φ z.1.val, hφI z.1⟩, z.2)
  let B : HomotopyTime × P → N := fun z => J (⟨ψ z.1.val, hψI z.1⟩, z.2)
  have hA : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val A :=
    smoothHomotopy_precomp S S T hH
    (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1) φ hφ hφI
  have hB : SmoothHomotopy S.smoothStructure.val T.smoothStructure.val B :=
    smoothHomotopy_precomp S S T hJ
    (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1) ψ hψ hψI
  have hAB (z : HomotopyTime × P) (hlo : 1 / 4 < z.1.val) (hhi : z.1.val < 3 / 4) :
      A z = B z := by
    have hφ1 : (⟨φ z.1.val, hφI z.1⟩ : HomotopyTime) = timeOne := by
      apply Subtype.ext
      exact Real.smoothTransition.one_of_one_le (by linarith)
    have hψ0 : (⟨ψ z.1.val, hψI z.1⟩ : HomotopyTime) = timeZero := by
      apply Subtype.ext
      exact Real.smoothTransition.zero_of_nonpos (by linarith)
    simp only [A, B, hφ1, hψ0, hH1, hJ0]
  let K : HomotopyTime × P → N := fun z => if z.1.val ≤ 1 / 2 then A z else B z
  have htc : Continuous (fun z : HomotopyTime × P => z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hK : Continuous K := continuous_if_le htc continuous_const
    hA.1.continuousOn hB.1.continuousOn (fun z hz => hAB z (by linarith) (by linarith))
  refine ⟨K, ⟨hK, ?_⟩, ?_, ?_⟩
  · intro e he d hd z hx hKz
    have hlocal : (A =ᶠ[𝓝 z] K) ∨ (B =ᶠ[𝓝 z] K) := by
      by_cases hz : z.1.val < 3 / 4
      · left
        filter_upwards [htc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hz)] with w hw
        dsimp only [K]
        split_ifs with h
        · rfl
        · exact hAB w (by linarith) hw
      · right
        have hz' : 1 / 4 < z.1.val := by linarith
        filter_upwards [htc.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hz')] with w hw
        dsimp only [K]
        split_ifs with h
        · exact (hAB w hw (by linarith)).symm
        · rfl
    rcases hlocal with heq | heq
    · exact SmoothManifolds.LocalCoordinateExtension.congr
        (hA.2 e he d hd z hx (by rw [heq.eq_of_nhds]; exact hKz))
        (heq.fun_comp (fun y => (d y).val))
    · exact SmoothManifolds.LocalCoordinateExtension.congr
        (hB.2 e he d hd z hx (by rw [heq.eq_of_nhds]; exact hKz))
        (heq.fun_comp (fun y => (d y).val))
  · intro x
    have ht : (⟨φ timeZero.val, hφI timeZero⟩ : HomotopyTime) = timeZero := by
      apply Subtype.ext
      change Real.smoothTransition (4 * 0) = 0
      norm_num
    change (if (0 : ℝ) ≤ 1 / 2 then A (timeZero, x) else B (timeZero, x)) = _
    rw [ite_eq_left (by norm_num)]
    change H (⟨φ timeZero.val, hφI timeZero⟩, x) = _
    rw [ht, hH0]
  · intro x
    have ht : (⟨ψ timeOne.val, hψI timeOne⟩ : HomotopyTime) = timeOne := by
      apply Subtype.ext
      change Real.smoothTransition (4 * 1 - 3) = 1
      norm_num
    change (if (1 : ℝ) ≤ 1 / 2 then A (timeOne, x) else B (timeOne, x)) = _
    rw [ite_eq_right (by norm_num)]
    change J (⟨ψ timeOne.val, hψI timeOne⟩, x) = _
    rw [ht, hJ1]

/-- Projection from an ordinary product has the expected smoothness. -/
theorem timeProduct_snd_smooth {n : ℕ} {a k : ModelKind} {P : Type u}
    [TopologicalSpace P] (S : SmoothManifold n a P)
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hR : euclideanChart 1 ∈ R.smoothStructure.val)
    (C : ProductData.ProductCoordinates 1 .euclidean n a k)
    (Q : SmoothManifold (1 + n) k (Euclidean 1 × P))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (ProductData.productAtlas C R.smoothStructure.val S.smoothStructure.val)) :
    IsSmoothMap Q S Prod.snd := by
  have hA := productAtlas_isContDiffAtlas C (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 S.smoothStructure.property.1
  intro z
  obtain ⟨e, he, hze⟩ := S.smoothStructure.property.1.1 z.2
  let c := ProductData.productChart C (euclideanChart 1) e
  have hc : c ∈ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension hA ⟨euclideanChart 1, hR, e, he, rfl⟩
  have hzc : z ∈ c.source := by simpa [c] using hze
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    Q.smoothStructure.property.1 S.smoothStructure.property.1 Prod.snd z).mpr
  refine ⟨continuous_snd.continuousAt, c, hc, e, he, hzc, hze,
    univ, isOpen_univ, mem_univ _, fun y => (C.linearEquiv.symm y).2,
    (contDiff_snd.comp C.linearEquiv.symm.contDiff).contDiffOn, ?_⟩
  exact Eventually.of_forall (fun w => by
    change (C.linearEquiv.symm (C.linearEquiv ((euclideanChart 1 w.1).val, (e w.2).val))).2 = _
    simp)

/-- Restrict a smooth map on the ordinary open-time product to the closed
cylinder. The extension remains ambient at the cylinder's corners. -/
theorem timeProduct_restrict_smooth {n m : ℕ} {a b k : ModelKind}
    {P : Type u} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold n a P) (T : SmoothManifold m b N)
    (R : SmoothManifold 1 .euclidean (Euclidean 1))
    (hR : euclideanChart 1 ∈ R.smoothStructure.val)
    (C : ProductData.ProductCoordinates 1 .euclidean n a k)
    (Q : SmoothManifold (1 + n) k (Euclidean 1 × P))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (ProductData.productAtlas C R.smoothStructure.val S.smoothStructure.val))
    {G : Euclidean 1 × P → N} (hG : IsSmoothMap Q T G) :
    SmoothHomotopy S.smoothStructure.val T.smoothStructure.val
      (fun z => G ((fun _ => z.1.val), z.2)) := by
  let j : HomotopyTime × P → Euclidean 1 × P := fun z => ((fun _ => z.1.val), z.2)
  have hj : Continuous j :=
    (continuous_pi (fun _ => continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  have hGc : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).1)
  have hA := productAtlas_isContDiffAtlas C (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 S.smoothStructure.property.1
  refine ⟨hGc.comp hj, ?_⟩
  intro e he d hd z hx hGz
  let c := ProductData.productChart C (euclideanChart 1) e
  have hc : c ∈ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension hA ⟨euclideanChart 1, hR, e, he, rfl⟩
  have hzc : j z ∈ c.source := by simpa [c, j] using hx
  have hGext := LocalCoordinateExtension.precomp
    (ι := fun y : Euclidean 1 × P => (c y).val)
    (f := fun y => (d (G y)).val) (h := j)
    ((hG (j z)).2 c hc d hd hzc hGz) hj.continuousAt rfl
  apply LocalCoordinateExtension.comp hGext
  have htail : ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean (n + 1) => Fin.tail y) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) i.succ)
  refine ⟨univ, isOpen_univ, mem_univ _,
    fun y : Euclidean (n + 1) => C.linearEquiv ((fun _ => y 0), Fin.tail y),
    (C.linearEquiv.contDiff.comp
      ((contDiff_pi.mpr (fun _ => contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0)).prodMk htail)).contDiffOn,
    Eventually.of_forall ?_⟩
  intro w
  change C.linearEquiv ((fun _ => (Fin.cons w.1.val (e w.2).val : Euclidean (n + 1)) 0),
      Fin.tail (Fin.cons w.1.val (e w.2).val : Euclidean (n + 1))) =
    C.linearEquiv ((euclideanChart 1 (fun _ => w.1.val)).val, (e w.2).val)
  simp

/-- Whitney approximation on the extended cylinder fixes both endpoint maps.
Only the restrictions to the two closed time slices need smooth extensions;
the given homotopy need not be smooth on any endpoint neighborhood. -/
theorem boundaryless_homotopy_smoothing {n m : ℕ} {a : ModelKind}
    {P : Type u} {N : Type v} [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold n a P) (T : SmoothManifold m .euclidean N)
    {F₀ F₁ : P → N} (hF₀ : IsSmoothMap S T F₀) (hF₁ : IsSmoothMap S T F₁)
    {H : HomotopyTime × P → N} (hH : Continuous H)
    (hH0 : ∀ x, H (timeZero, x) = F₀ x) (hH1 : ∀ x, H (timeOne, x) = F₁ x) :
    ∃ K : HomotopyTime × P → N,
      SmoothHomotopy S.smoothStructure.val T.smoothStructure.val K ∧
      (∀ x, K (timeZero, x) = F₀ x) ∧ (∀ x, K (timeOne, x) = F₁ x) := by
  obtain ⟨R, hR⟩ := standardEuclidean_exists 1
  obtain ⟨C, Q, _, hQ⟩ := exists_ordinaryProduct_smoothManifold R S (Or.inl rfl)
  have hsnd := timeProduct_snd_smooth S R hR C Q hQ
  have hF₀c : Continuous F₀ := continuous_iff_continuousAt.mpr (fun x => (hF₀ x).1)
  have hF₁c : Continuous F₁ := continuous_iff_continuousAt.mpr (fun x => (hF₁ x).1)
  let H' : ContinuousMap.Homotopy ⟨F₀, hF₀c⟩ ⟨F₁, hF₁c⟩ := {
    toFun := H
    continuous_toFun := hH
    map_zero_left := hH0
    map_one_left := hH1 }
  let F : Euclidean 1 × P → N := fun z => H' (projIcc 0 1 zero_le_one (z.1 0), z.2)
  let A : Set (Euclidean 1 × P) := {z | z.1 0 = 0 ∨ z.1 0 = 1}
  have htime : Continuous (fun z : Euclidean 1 × P => z.1 0) :=
    (continuous_apply 0).comp continuous_fst
  have hA : IsClosed A := (isClosed_eq htime continuous_const).union
    (isClosed_eq htime continuous_const)
  have hFc : Continuous F := hH.comp
    ((continuous_projIcc.comp htime).prodMk continuous_snd)
  have hF0 (z : Euclidean 1 × P) (hz : z.1 0 = 0) : F z = F₀ z.2 := by
    dsimp only [F]
    rw [hz]
    change H (projIcc 0 1 zero_le_one 0, z.2) = _
    rw [projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩]
    exact hH0 z.2
  have hF1 (z : Euclidean 1 × P) (hz : z.1 0 = 1) : F z = F₁ z.2 := by
    dsimp only [F]
    rw [hz]
    change H (projIcc 0 1 zero_le_one 1, z.2) = _
    rw [projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩]
    exact hH1 z.2
  have hlocal : LocallySmoothOnSubsetToManifold Q.smoothStructure.val T.smoothStructure.val
      A (fun z => F z.val) := by
    intro z
    rcases z.property with hz | hz
    · refine ⟨{w | w.1 0 < 1}, isOpen_Iio.preimage htime, by simp [hz], F₀ ∘ Prod.snd, ?_, ?_⟩
      · intro w _
        exact manifoldContDiffAt_comp S.smoothStructure.property.1.1 (hsnd w) (hF₀ w.2)
      · intro w hw
        rcases w.property with hw0 | hw1
        · exact (hF0 w.val hw0).symm
        · change w.val.1 0 < 1 at hw
          rw [hw1] at hw
          exact False.elim (lt_irrefl _ hw)
    · refine ⟨{w | 0 < w.1 0}, isOpen_Ioi.preimage htime, by simp [hz], F₁ ∘ Prod.snd, ?_, ?_⟩
      · intro w _
        exact manifoldContDiffAt_comp S.smoothStructure.property.1.1 (hsnd w) (hF₁ w.2)
      · intro w hw
        rcases w.property with hw0 | hw1
        · change 0 < w.val.1 0 at hw
          rw [hw0] at hw
          exact False.elim (lt_irrefl _ hw)
        · exact (hF1 w.val hw1).symm
  obtain ⟨G, hG, hGA, _⟩ := RelativeManifoldApproximation.relative_manifold_approximation
    Q T A F univ hA hFc hlocal isOpen_univ (fun _ => mem_univ _)
  refine ⟨fun z => G ((fun _ => z.1.val), z.2),
    timeProduct_restrict_smooth S T R hR C Q hQ hG, ?_, ?_⟩
  · intro x
    exact (hGA (by exact Or.inl rfl)).trans (hF0 _ rfl)
  · intro x
    exact (hGA (by exact Or.inr rfl)).trans (hF1 _ rfl)

/-- The actual interior has a boundaryless smooth structure equivalent to the
restricted atlas. The construction also applies to an empty interior. -/
theorem interior_euclidean_structure {m : ℕ} {b : ModelKind} {N : Type u}
    [TopologicalSpace N] (T : SmoothManifold m b N)
    (hI : IsOpen (manifoldInterior T)) :
    ∃ E : SmoothManifold m .euclidean (manifoldInterior T),
      ManifoldSmooth (openSubsetAtlas T.smoothStructure.val (manifoldInterior T) hI)
        E.smoothStructure.val id ∧ IsSmoothMap E T Subtype.val := by
  let A := openSubsetAtlas T.smoothStructure.val (manifoldInterior T) hI
  have hA := openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _
    T.smoothStructure.property.1 (manifoldInterior T) hI
  obtain ⟨R, _, hR, hRT⟩ := exists_openSubset_smoothManifold T (manifoldInterior T) hI
  have hAR : ManifoldSmooth A R.smoothStructure.val id := by
    intro x
    obtain ⟨c, hc, hx⟩ := hA.1 x
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _ hA
      R.smoothStructure.property.1 id x).mpr
    refine ⟨continuousAt_id, c, hc, c, ?_, hx, hx, ?_⟩
    · rw [hR]
      exact subset_maximalExtension hA hc
    · exact LocalCoordinateExtension.self _ (fun y => (c y).val) x
  have hboundary : intrinsicBoundary R = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨c, hc, hxc, hxi⟩ := x.property
    let d := c.subtypeRestr (s := ⟨manifoldInterior T, hI⟩) ⟨x⟩
    have hd : d ∈ R.smoothStructure.val := by
      rw [hR]
      exact subset_maximalExtension hA ⟨⟨x⟩, c, hc, rfl⟩
    have hxd : x ∈ d.source := by simpa [d] using hxc
    have hf := (intrinsicBoundary_iff_chart R d hd x hxd).mp hx
    exact (mem_modelFace_iff_not_mem_interior (d x)).mp hf hxi
  obtain ⟨E, hRE, hER⟩ := exists_boundaryless_euclidean_smoothManifold R hboundary
  refine ⟨E, ?_, ?_⟩
  · exact manifoldContDiff_comp (⊤ : ℕ∞) A R.smoothStructure.val E.smoothStructure.val
      R.smoothStructure.property.1.1 id id hAR hRE
  · exact manifoldContDiff_comp (⊤ : ℕ∞) E.smoothStructure.val R.smoothStructure.val
      T.smoothStructure.val R.smoothStructure.property.1.1 id Subtype.val hER hRT

/-- Every continuous map into an ordinary manifold is homotopic to a smooth map. -/
theorem continuous_map_homotopic_smooth :
    ∀ {n m : ℕ} {a b : ModelKind} {P : Type v} {N : Type u}
      [TopologicalSpace P] [TopologicalSpace N]
      (S : SmoothManifold n a P) (T : SmoothManifold m b N)
      (F : P → N), Continuous F →
      ∃ G : P → N, IsSmoothMap S T G ∧
        ∃ H : HomotopyTime × P → N, Continuous H ∧
          (∀ x, H (timeZero, x) = F x) ∧
          (∀ x, H (timeOne, x) = G x) := by
  intro n m a b P N _ _ S T F hF
  obtain ⟨R⟩ := InteriorHomotopies.interior_inclusion_homotopy_equivalence T
  obtain ⟨E, hAE, hET⟩ := interior_euclidean_structure T R.isOpen_interior
  have hr : IsSmoothMap T E R.inverse :=
    manifoldContDiff_comp (⊤ : ℕ∞) T.smoothStructure.val _ E.smoothStructure.val
      (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ T.smoothStructure.property.1
        (manifoldInterior T) R.isOpen_interior).1 R.inverse id R.smooth_inverse hAE
  have hrc : Continuous R.inverse := continuous_iff_continuousAt.mpr (fun x => (hr x).1)
  have hEc : Continuous (Subtype.val : manifoldInterior T → N) := continuous_subtype_val
  obtain ⟨g, hg, _, H, hH, hH0, hH1, _⟩ :=
    RelativeManifoldApproximation.relative_manifold_approximation S E ∅ (R.inverse ∘ F)
      univ isClosed_empty (hrc.comp hF) (by intro x; exact False.elim x.property)
      isOpen_univ (fun _ => mem_univ _)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).1)
  let G : P → N := Subtype.val ∘ g
  have hG : IsSmoothMap S T G := manifoldContDiff_comp (⊤ : ℕ∞)
    S.smoothStructure.val E.smoothStructure.val T.smoothStructure.val
    E.smoothStructure.property.1.1 g Subtype.val hg hET
  let H₀ : ContinuousMap.Homotopy ⟨F, hF⟩ ⟨Subtype.val ∘ R.inverse ∘ F, hEc.comp (hrc.comp hF)⟩ := {
    toFun := fun z => R.homotopy (z.1, F z.2)
    continuous_toFun := R.smooth_homotopy.1.comp (continuous_fst.prodMk (hF.comp continuous_snd))
    map_zero_left := fun x => R.homotopy_zero (F x)
    map_one_left := fun x => R.homotopy_one (F x) }
  let H₁ : ContinuousMap.Homotopy
      ⟨Subtype.val ∘ R.inverse ∘ F, hEc.comp (hrc.comp hF)⟩ ⟨G, hEc.comp hgc⟩ := {
    toFun := fun z => (H z).val
    continuous_toFun := hEc.comp hH
    map_zero_left := fun x => congrArg Subtype.val (hH0 x)
    map_one_left := fun x => congrArg Subtype.val (hH1 x) }
  exact ⟨G, hG, H₀.trans H₁, (H₀.trans H₁).continuous_toFun,
    (H₀.trans H₁).map_zero_left, (H₀.trans H₁).map_one_left⟩

/-- Push the given homotopy into the interior, smooth it there relative to
its two endpoint slices, and join the collar homotopies back on both sides.
The smooth concatenation lemma restores the exact original endpoints. -/
theorem continuous_homotopy_smoothing :
    ∀ {n m : ℕ} {a b : ModelKind} {P : Type v} {N : Type u}
      [TopologicalSpace P] [TopologicalSpace N]
      (S : SmoothManifold n a P) (T : SmoothManifold m b N)
      (F₀ F₁ : P → N), IsSmoothMap S T F₀ → IsSmoothMap S T F₁ →
      (∃ H : HomotopyTime × P → N, Continuous H ∧
        (∀ x, H (timeZero, x) = F₀ x) ∧
        (∀ x, H (timeOne, x) = F₁ x)) →
      ∃ K : HomotopyTime × P → N,
        SmoothHomotopy S.smoothStructure.val T.smoothStructure.val K ∧
        (∀ x, K (timeZero, x) = F₀ x) ∧
        (∀ x, K (timeOne, x) = F₁ x) := by
  intro n m a b P N _ _ S T F₀ F₁ hF₀ hF₁ hH
  obtain ⟨H, hH, hH0, hH1⟩ := hH
  obtain ⟨R⟩ := InteriorHomotopies.interior_inclusion_homotopy_equivalence T
  obtain ⟨E, hAE, hET⟩ := interior_euclidean_structure T R.isOpen_interior
  have hr : IsSmoothMap T E R.inverse :=
    manifoldContDiff_comp (⊤ : ℕ∞) T.smoothStructure.val _ E.smoothStructure.val
      (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ T.smoothStructure.property.1
        (manifoldInterior T) R.isOpen_interior).1 R.inverse id R.smooth_inverse hAE
  have hrc : Continuous R.inverse := continuous_iff_continuousAt.mpr (fun x => (hr x).1)
  have hF₀I : IsSmoothMap S E (R.inverse ∘ F₀) :=
    manifoldContDiff_comp (⊤ : ℕ∞) S.smoothStructure.val T.smoothStructure.val
      E.smoothStructure.val T.smoothStructure.property.1.1 F₀ R.inverse hF₀ hr
  have hF₁I : IsSmoothMap S E (R.inverse ∘ F₁) :=
    manifoldContDiff_comp (⊤ : ℕ∞) S.smoothStructure.val T.smoothStructure.val
      E.smoothStructure.val T.smoothStructure.property.1.1 F₁ R.inverse hF₁ hr
  obtain ⟨K, hK, hK0, hK1⟩ := boundaryless_homotopy_smoothing S E hF₀I hF₁I
    (hrc.comp hH) (fun x => congrArg R.inverse (hH0 x))
    (fun x => congrArg R.inverse (hH1 x))
  have hMid := smoothHomotopy_postcomp S E T hK hET
  have hLeft := smoothHomotopy_precomp S T T R.smooth_homotopy hF₀ id contDiff_id
    (fun t => t.property)
  have hRev (t : HomotopyTime) : 1 - t.val ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [t.property.2], by linarith [t.property.1]⟩
  have hRight := smoothHomotopy_precomp S T T R.smooth_homotopy hF₁
    (fun t => 1 - t) (contDiff_const.sub contDiff_id) hRev
  have ht0 : (⟨1 - timeZero.val, hRev timeZero⟩ : HomotopyTime) = timeOne := by
    apply Subtype.ext
    norm_num [timeZero, timeOne]
  have ht1 : (⟨1 - timeOne.val, hRev timeOne⟩ : HomotopyTime) = timeZero := by
    apply Subtype.ext
    norm_num [timeZero, timeOne]
  obtain ⟨L, hL, hL0, hL1⟩ := smoothHomotopy_trans S T hLeft hMid
    (fun x => R.homotopy_zero (F₀ x)) (fun x => R.homotopy_one (F₀ x))
    (fun x => congrArg Subtype.val (hK0 x)) (fun x => congrArg Subtype.val (hK1 x))
  exact smoothHomotopy_trans S T hL hRight hL0 hL1
    (fun x => by dsimp only; rw [ht0]; exact R.homotopy_one (F₁ x))
    (fun x => by dsimp only; rw [ht1]; exact R.homotopy_zero (F₁ x))

end SmoothManifolds.SmoothingHomotopies
