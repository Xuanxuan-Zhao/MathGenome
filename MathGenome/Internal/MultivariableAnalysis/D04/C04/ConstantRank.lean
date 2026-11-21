import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.ConstantRank
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
open Specs.D04.C04.ConstantRank

/-- The dimension bound requires only the rank at the basepoint; no rank
bound is inserted as an additional hypothesis of the normal-form theorem. -/
theorem constant_rank_bounds : Specs.D04.C04.ConstantRank.constant_rank_boundsType := by
  intro n m f a k hk
  have ha : Module.finrank ℝ (LinearMap.range (totalDerivative f a).toLinearMap) = k :=
    (show ∀ᶠ x in 𝓝 a, Module.finrank ℝ
      (LinearMap.range (totalDerivative f x).toLinearMap) = k from hk).self_of_nhds
  have hn := (totalDerivative f a).toLinearMap.finrank_range_le
  have hm := Submodule.finrank_le (LinearMap.range (totalDerivative f a).toLinearMap)
  refine ⟨Nat.zero_le _, le_min ?_ ?_⟩
  · simpa only [ha, finrank_euclideanSpace_fin] using hn
  · simpa only [ha, finrank_euclideanSpace_fin] using hm

/-- Once local constancy is known, translations give compatible coordinates
of every regularity, including finite orders and infinity. -/
theorem rankNormalForm_of_locally_constant {n m : ℕ} (r : ℕ∞ω)
    (U : Set (E n)) (f : E n → E m) (a : E n)
    (hU : IsOpen U) (ha : a ∈ U) (hc : ∀ᶠ x in 𝓝 a, f x = f a) :
    RankNormalForm r U f a 0 := by
  obtain ⟨X, hXsub, hX, haX⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hc)
  let Φ := (Homeomorph.subRight a).toOpenPartialHomeomorphOfImageEq
    X hX ((Homeomorph.subRight a) '' X) rfl
  let Ψ := (Homeomorph.subRight (f a)).toOpenPartialHomeomorph
  have hΦ (x : E n) : Φ x = x - a := rfl
  have hΦi (u : E n) : Φ.symm u = u + a := rfl
  have hΨ (y : E m) : Ψ y = y - f a := rfl
  have hΨi (v : E m) : Ψ.symm v = v + f a := rfl
  refine ⟨Φ, Ψ, haX, (fun x hx => (hXsub hx).1), ?_, mem_univ _, ?_,
    ?_, ?_, ?_, ?_, (fun _ _ => mem_univ _), ?_⟩
  · simp only [hΦ, sub_self]
  · simp only [hΨ, sub_self]
  · exact (contDiff_id.sub contDiff_const).contDiffOn
  · exact (contDiff_id.add contDiff_const).contDiffOn
  · exact (contDiff_id.sub contDiff_const).contDiffOn
  · exact (contDiff_id.add contDiff_const).contDiffOn
  · intro u hu
    have hx : Φ.symm u ∈ X := Φ.map_target hu
    rw [hΨ, (hXsub hx).2, sub_self]
    ext j
    simp [normalProjection]

/-- Rank zero is equivalent to a zero linear derivative. -/
theorem totalDerivative_eq_zero_of_rank_zero {n m : ℕ} (f : E n → E m) (x : E n)
    (h : Module.finrank ℝ (LinearMap.range (totalDerivative f x).toLinearMap) = 0) :
    totalDerivative f x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)) v

/-- The rank-zero branch uses the actual neighborhood rank condition to
obtain local constancy; it does not assume constancy as part of the input. -/
theorem rankNormalForm_zero {n m : ℕ} (r : ℕ∞ω) (U : Set (E n))
    (f : E n → E m) (a : E n) (hr : 1 ≤ r) (hU : IsOpen U)
    (hf : ContDiffOn ℝ r f U) (ha : a ∈ U) (hk : NeighborhoodRank f a 0) :
    RankNormalForm r U f a 0 := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hk)
  have hsub : Metric.ball a ε ⊆ U := fun x hx => (hb hx).1
  have hzero : ∀ x ∈ Metric.ball a ε, totalDerivative f x = 0 :=
    fun x hx => totalDerivative_eq_zero_of_rank_zero f x (hb hx).2
  apply rankNormalForm_of_locally_constant r U f a hU ha
  filter_upwards [Metric.ball_mem_nhds a hε] with x hx
  exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball a ε).isPreconnected
    ((hf.differentiableOn (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))).mono hsub)
    hzero hx (Metric.mem_ball_self hε)

theorem constant_rank_zero_finite :
    Specs.D04.C04.ConstantRank.constant_rank_zero_finiteType := by
  intro n m r U f a hr hU hf ha hk
  exact rankNormalForm_zero r U f a (by exact_mod_cast hr) hU
    ((crOn_iff_contDiffOn r U f hU).mp hf) ha hk

theorem constant_rank_zero_smooth :
    Specs.D04.C04.ConstantRank.constant_rank_zero_smoothType := by
  intro n m U f a hU hf ha hk
  exact rankNormalForm_zero ∞ U f a (by simp) hU
    ((smoothOn_iff_contDiffOn U f hU).mp hf) ha hk

namespace ConstantRank

/-- A version of the inverse-chart construction for the product spaces used
in the rank proof. Shrinking keeps the original C^r domain and gives C^r
regularity of the inverse at every point of its displayed open target. -/
theorem exists_inverse_chart {X Y : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℕ∞ω) (hr : 1 ≤ r) (U : Set X) (hU : IsOpen U)
    (f : X → Y) (hf : ContDiffOn ℝ r f U) (a : X) (ha : a ∈ U)
    (A : X ≃L[ℝ] Y) (hA : HasFDerivAt f A.toContinuousLinearMap a) :
    ∃ e : OpenPartialHomeomorph X Y,
      (∀ x, e x = f x) ∧ a ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ r e e.source ∧ ContDiffOn ℝ r e.symm e.target := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hfa := hf.contDiffAt (hU.mem_nhds ha)
  let e := hfa.toOpenPartialHomeomorph f hA hr0
  have he (x : X) : e x = f x := rfl
  have hae : a ∈ e.source := hfa.mem_toOpenPartialHomeomorph_source hA hr0
  have hcont : ContinuousAt (fderiv ℝ f) a :=
    (hf.continuousOn_fderiv_of_isOpen hU hr).continuousAt (hU.mem_nhds ha)
  have hInv : {x : X | ∃ B : X ≃L[ℝ] Y,
      B.toContinuousLinearMap = fderiv ℝ f x} ∈ 𝓝 a := by
    have ht := hcont.preimage_mem_nhds (by rw [hA.fderiv]; exact A.nhds)
    exact ht
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hInv)
  let e' := e.restrOpen W hW
  have hsub : e'.source ⊆ U := fun x hx => (hWsub hx.2).1
  refine ⟨e', he, ⟨hae, haW⟩, hsub, hf.mono hsub, ?_⟩
  intro y hy
  have hx : e'.symm y ∈ e'.source := e'.map_target hy
  have hxW : e.symm y ∈ W := hx.2
  obtain ⟨B, hB⟩ := (hWsub hxW).2
  have hfx := hf.contDiffAt (hU.mem_nhds (hWsub hxW).1)
  have hd : HasFDerivAt f B.toContinuousLinearMap (e.symm y) := by
    rw [hB]
    exact (hfx.differentiableAt hr0).hasFDerivAt
  exact (e.contDiffAt_symm hy.1 (f₀' := B) hd hfx).contDiffWithinAt


/-- Centering an inverse chart gives the square full-rank normal form. -/
theorem rankNormalForm_of_invertible_derivative {n : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E n)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U)
    (A : E n ≃L[ℝ] E n) (hA : HasFDerivAt f A.toContinuousLinearMap a) :
    RankNormalForm r U f a n := by
  obtain ⟨e, he, hae, hsub, hreg, hregi⟩ := exists_inverse_chart r hr U hU f hf a ha A hA
  let Φ := e.transHomeomorph (Homeomorph.subRight (f a))
  let Ψ := (Homeomorph.subRight (f a)).toOpenPartialHomeomorph
  have hΦ (x : E n) : Φ x = e x - f a := rfl
  have hΦi (u : E n) : Φ.symm u = e.symm (u + f a) := rfl
  have hΨ (x : E n) : Ψ x = x - f a := rfl
  refine ⟨Φ, Ψ, hae, hsub, ?_, mem_univ _, ?_, ?_, ?_, ?_, ?_,
    (fun _ _ => mem_univ _), ?_⟩
  · rw [hΦ, he, sub_self]
  · exact sub_self _
  · exact hreg.sub contDiffOn_const
  · exact hregi.comp (contDiff_id.add contDiff_const).contDiffOn (fun _ hu => hu)
  · exact (contDiff_id.sub contDiff_const).contDiffOn
  · exact (contDiff_id.add contDiff_const).contDiffOn
  · intro u hu
    have hnorm : normalProjection n n n u = u := by
      ext j
      simp [normalProjection]
    rw [hnorm, hΨ, hΦi, ← he]
    have hi : e (e.symm (u + f a)) = u + f a := e.right_inv hu
    rw [hi]
    exact add_sub_cancel_right u (f a)

/-- The square maximal-rank branch, including n = 0. Only rank at the
basepoint is needed in this branch, as expected from the inverse theorem. -/
theorem rankNormalForm_square {n : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E n)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U)
    (hk : Module.finrank ℝ (LinearMap.range (fderiv ℝ f a).toLinearMap) = n) :
    RankNormalForm r U f a n := by
  let L := (fderiv ℝ f a).toLinearMap
  have htop : LinearMap.range L = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa only [finrank_euclideanSpace_fin] using hk)
  have hsurj : Function.Surjective L := LinearMap.range_eq_top.mp htop
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hsurj
  let A := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  apply rankNormalForm_of_invertible_derivative r hr U hU f hf a ha A
  exact (hf.contDiffAt (hU.mem_nhds ha)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr)) |>.hasFDerivAt

/-- The mixed source map straightens the first block. Its derivative at zero
is the identity once the derivative of g is in the algebraic normal form. -/
theorem exists_source_straightening {V W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (r : ℕ∞ω) (hr : 1 ≤ r) (U : Set (V × W)) (hU : IsOpen U)
    (h0 : (0 : V × W) ∈ U) (g : V × W → V × Z)
    (hg : ContDiffOn ℝ r g U) (hg0 : g 0 = 0)
    (hd : HasFDerivAt g
      ((ContinuousLinearMap.fst ℝ V W).prod (0 : V × W →L[ℝ] Z)) 0) :
    ∃ e : OpenPartialHomeomorph (V × W) (V × W),
      (0 : V × W) ∈ e.source ∧ e.source ⊆ U ∧ e 0 = 0 ∧
      ContDiffOn ℝ r e e.source ∧ ContDiffOn ℝ r e.symm e.target ∧
      ∀ p ∈ e.target, (g (e.symm p)).1 = p.1 := by
  let F : V × W → V × W := fun p => ((g p).1, p.2)
  have hF : ContDiffOn ℝ r F U := hg.fst.prodMk contDiffOn_snd
  have hD : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ (V × W)).toContinuousLinearMap 0 := by
    convert hd.fst.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : V × W))) using 1
    ext p <;> rfl
  obtain ⟨e, he, he0, hesub, hreg, hregi⟩ :=
    exists_inverse_chart r hr U hU F hF 0 h0 (ContinuousLinearEquiv.refl ℝ (V × W)) hD
  refine ⟨e, he0, hesub, ?_, hreg, hregi, ?_⟩
  · rw [he]
    change ((g 0).1, (0 : W)) = 0
    rw [hg0]
    rfl
  · intro p hp
    have hi := congrArg Prod.fst (e.right_inv hp)
    simpa only [he] using hi

/-- Invertible linear changes in domain and codomain preserve derivative rank. -/
theorem finrank_range_coordinates {X X' Y Y' : Type}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup X'] [Module ℝ X']
    [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Y'] [Module ℝ Y']
    (L : X →ₗ[ℝ] Y) (P : X' ≃ₗ[ℝ] X) (Q : Y ≃ₗ[ℝ] Y') :
    Module.finrank ℝ (LinearMap.range (Q.toLinearMap.comp (L.comp P.toLinearMap))) =
      Module.finrank ℝ (LinearMap.range L) := by
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top L P.range]
  exact Q.finrank_map_eq _

/-- Algebraic splitting adapted to a linear map. The common first block is
its range, the second source block its kernel, and the second target block
a complement of the range. These are genuine equivalences, also when any
block has dimension zero. -/
theorem exists_adapted_splittings {X Y : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : X →ₗ[ℝ] Y) :
    ∃ Z : Submodule ℝ Y,
    ∃ P : X ≃L[ℝ] (LinearMap.range L × LinearMap.ker L),
    ∃ Q : Y ≃L[ℝ] (LinearMap.range L × Z),
      ∀ v w, Q (L (P.symm (v, w))) = (v, 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker L)
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (LinearMap.range L)
  let R := LinearMap.range L
  let K := LinearMap.ker L
  let e : C ≃ₗ[ℝ] R :=
    ((LinearMap.ker L).quotientEquivOfIsCompl C hC).symm.trans L.quotKerEquivRange
  let P : X ≃ₗ[ℝ] R × K :=
    (C.prodEquivOfIsCompl K hC.symm).symm.trans
      (LinearEquiv.prodCongr e (LinearEquiv.refl ℝ K))
  let Q : Y ≃ₗ[ℝ] R × Z := (R.prodEquivOfIsCompl Z hZ).symm
  refine ⟨Z, P.toContinuousLinearEquiv, Q.toContinuousLinearEquiv, ?_⟩
  intro v w
  have he (c : C) : (e c : Y) = L c := rfl
  have hinv : P.symm (v, w) = (e.symm v : X) + (w : X) := rfl
  change Q (L (P.symm (v, w))) = (v, 0)
  rw [hinv, map_add, show L (w : X) = 0 from w.property, add_zero,
    ← he (e.symm v), e.apply_symm_apply]
  exact R.prodEquivOfIsCompl_symm_apply_left Z hZ v


/-- The rank step in the block argument. The first projection identifies the
range with V: it is surjective, and equality of dimensions makes it injective.
Thus a column in the fiber directions, whose first component is zero, is zero.
No positive-dimension assumption is used on any block. -/
theorem fiber_columns_eq_zero {V W Z : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]
    (A : V × W →ₗ[ℝ] V × Z)
    (hfirst : ∀ p, (A p).1 = p.1)
    (hrank : Module.finrank ℝ (LinearMap.range A) ≤ Module.finrank ℝ V) :
    ∀ w, A (0, w) = 0 := by
  let P : LinearMap.range A →ₗ[ℝ] V :=
    (LinearMap.fst ℝ V Z).comp (LinearMap.range A).subtype
  have hsurj : Function.Surjective P := by
    intro v
    exact ⟨⟨A (v, 0), ⟨(v, 0), rfl⟩⟩, hfirst (v, 0)⟩
  have hinj : Function.Injective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (le_antisymm hrank (LinearMap.finrank_le_finrank_of_surjective hsurj))).mpr hsurj
  intro w
  have heq : (⟨A (0, w), ⟨(0, w), rfl⟩⟩ : LinearMap.range A) = 0 := by
    apply hinj
    change (A (0, w)).1 = 0
    exact hfirst (0, w)
  exact congrArg Subtype.val heq

/-- Differential version of the block lemma. Equality of the first component
is assumed on an open set, so its derivative is the first projection there. -/
theorem fiber_derivative_eq_zero {V W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (g : V × W → V × Z) (S : Set (V × W)) (hS : IsOpen S)
    (p : V × W) (hp : p ∈ S) (hg : DifferentiableAt ℝ g p)
    (hfirst : ∀ q ∈ S, (g q).1 = q.1)
    (hrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ g p).toLinearMap) ≤
      Module.finrank ℝ V) :
    HasFDerivAt (fun w => (g (p.1, w)).2) (0 : W →L[ℝ] Z) p.2 := by
  have heq : (fun q => (g q).1) =ᶠ[𝓝 p] Prod.fst := by
    filter_upwards [hS.mem_nhds hp] with q hq using hfirst q hq
  have hderiv : (ContinuousLinearMap.fst ℝ V Z).comp (fderiv ℝ g p) =
      ContinuousLinearMap.fst ℝ V W :=
    (hg.hasFDerivAt.fst.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_fst (𝕜 := ℝ))
  have hcols := fiber_columns_eq_zero (fderiv ℝ g p).toLinearMap
    (fun q => DFunLike.congr_fun hderiv q) hrank
  have hi : HasFDerivAt (fun w : W => (p.1, w))
      ((0 : W →L[ℝ] V).prod (ContinuousLinearMap.id ℝ W)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h := hg.hasFDerivAt.snd.comp p.2 hi
  have hzero : ((ContinuousLinearMap.snd ℝ V Z).comp (fderiv ℝ g p)).comp
      ((0 : W →L[ℝ] V).prod (ContinuousLinearMap.id ℝ W)) = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    change (fderiv ℝ g p (0, w)).2 = 0
    exact congrArg Prod.snd (hcols w)
  simpa only [Function.comp_def, hzero] using h

/-- On a product with a convex fiber, constant rank forces independence of the
fiber variable after the first components have been straightened. -/
theorem independent_of_fiber {V W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (g : V × W → V × Z) (A : Set V) (B : Set W)
    (hA : IsOpen A) (hB : IsOpen B) (hc : Convex ℝ B)
    (hg : DifferentiableOn ℝ g (A ×ˢ B))
    (hfirst : ∀ p ∈ A ×ˢ B, (g p).1 = p.1)
    (hrank : ∀ p ∈ A ×ˢ B,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g p).toLinearMap) ≤ Module.finrank ℝ V) :
    ∀ v ∈ A, ∀ w ∈ B, ∀ z ∈ B, (g (v, w)).2 = (g (v, z)).2 := by
  intro v hv
  have hd (w : W) (hw : w ∈ B) :
      HasFDerivAt (fun t => (g (v, t)).2) (0 : W →L[ℝ] Z) w :=
    fiber_derivative_eq_zero g (A ×ˢ B) (hA.prod hB) (v, w) ⟨hv, hw⟩
      ((hg (v, w) ⟨hv, hw⟩).differentiableAt ((hA.prod hB).mem_nhds ⟨hv, hw⟩))
      hfirst (hrank (v, w) ⟨hv, hw⟩)
  intro w hw z hz
  exact hB.is_const_of_fderiv_eq_zero hc.isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).fderiv) hw hz

/-- Subtracting a C^r graph is a C^r target coordinate diffeomorphism on
A × Z. The inverse adds the same graph; neither direction loses regularity. -/
theorem exists_target_shear {V Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (r : ℕ∞ω) (A : Set V) (hA : IsOpen A) (h : V → Z)
    (hh : ContDiffOn ℝ r h A) :
    ∃ Ψ : OpenPartialHomeomorph (V × Z) (V × Z),
      Ψ.source = A ×ˢ univ ∧ Ψ.target = A ×ˢ univ ∧
      (∀ p, Ψ p = (p.1, p.2 - h p.1)) ∧
      (∀ p, Ψ.symm p = (p.1, p.2 + h p.1)) ∧
      ContDiffOn ℝ r Ψ Ψ.source ∧ ContDiffOn ℝ r Ψ.symm Ψ.target := by
  have hhfst : ContDiffOn ℝ r (fun p : V × Z => h p.1) (A ×ˢ univ) :=
    hh.comp contDiffOn_fst (fun _ hp => hp.1)
  have hsub : ContDiffOn ℝ r (fun p : V × Z => (p.1, p.2 - h p.1)) (A ×ˢ univ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.sub hhfst)
  have hadd : ContDiffOn ℝ r (fun p : V × Z => (p.1, p.2 + h p.1)) (A ×ˢ univ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add hhfst)
  let Ψ : OpenPartialHomeomorph (V × Z) (V × Z) :=
    { toFun := fun p => (p.1, p.2 - h p.1)
      invFun := fun p => (p.1, p.2 + h p.1)
      source := A ×ˢ univ
      target := A ×ˢ univ
      map_source' := fun _ hp => ⟨hp.1, mem_univ _⟩
      map_target' := fun _ hp => ⟨hp.1, mem_univ _⟩
      left_inv' := by intro p hp; simp
      right_inv' := by intro p hp; simp
      open_source := hA.prod isOpen_univ
      open_target := hA.prod isOpen_univ
      continuousOn_toFun := hsub.continuousOn
      continuousOn_invFun := hadd.continuousOn }
  exact ⟨Ψ, rfl, rfl, fun _ => rfl, fun _ => rfl, hsub, hadd⟩

/-- The complete analytic second half of the rank theorem on straightened
product coordinates. The derivative rank hypothesis is used to prove fiber
independence; the target diffeomorphism then removes the graph. -/
theorem normal_form_after_straightening {V W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (r : ℕ∞ω) (hr : 1 ≤ r) (A : Set V) (B : Set W)
    (hA : IsOpen A) (hB : IsOpen B) (hc : Convex ℝ B) (h0 : (0 : W) ∈ B)
    (g : V × W → V × Z) (hg : ContDiffOn ℝ r g (A ×ˢ B))
    (hfirst : ∀ p ∈ A ×ˢ B, (g p).1 = p.1)
    (hrank : ∀ p ∈ A ×ˢ B,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g p).toLinearMap) ≤ Module.finrank ℝ V) :
    ∃ Ψ : OpenPartialHomeomorph (V × Z) (V × Z),
      Ψ.source = A ×ˢ univ ∧ Ψ.target = A ×ˢ univ ∧
      ContDiffOn ℝ r Ψ Ψ.source ∧ ContDiffOn ℝ r Ψ.symm Ψ.target ∧
      MapsTo g (A ×ˢ B) Ψ.source ∧
      ∀ p ∈ A ×ˢ B, Ψ (g p) = (p.1, 0) := by
  let h : V → Z := fun v => (g (v, 0)).2
  have hh : ContDiffOn ℝ r h A :=
    hg.snd.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hv => ⟨hv, h0⟩)
  obtain ⟨Ψ, hsource, htarget, hΨ, hΨi, hreg, hregi⟩ :=
    exists_target_shear r A hA h hh
  have hind := independent_of_fiber g A B hA hB hc
    (hg.differentiableOn (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))) hfirst hrank
  refine ⟨Ψ, hsource, htarget, hreg, hregi, ?_, ?_⟩
  · intro p hp
    rw [hsource]
    exact ⟨by rw [hfirst p hp]; exact hp.1, mem_univ _⟩
  · intro p hp
    rw [hΨ, hfirst p hp, hind p.1 hp.1 p.2 hp.2 0 h0]
    exact Prod.ext rfl (sub_self _)

/-- The full local construction for a map whose derivative at zero has
already been put in projection form by linear coordinates. -/
theorem normalized_rank_normal_form {V W Z : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (r : ℕ∞ω) (hr : 1 ≤ r) (U : Set (V × W)) (hU : IsOpen U)
    (h0 : (0 : V × W) ∈ U) (g : V × W → V × Z)
    (hg : ContDiffOn ℝ r g U) (hg0 : g 0 = 0)
    (hd : HasFDerivAt g
      ((ContinuousLinearMap.fst ℝ V W).prod (0 : V × W →L[ℝ] Z)) 0)
    (hrank : ∀ p ∈ U,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g p).toLinearMap) ≤ Module.finrank ℝ V) :
    ∃ Φ : OpenPartialHomeomorph (V × W) (V × W),
    ∃ Ψ : OpenPartialHomeomorph (V × Z) (V × Z),
      (0 : V × W) ∈ Φ.source ∧ Φ.source ⊆ U ∧ Φ 0 = 0 ∧
      (0 : V × Z) ∈ Ψ.source ∧ Ψ 0 = 0 ∧
      ContDiffOn ℝ r Φ Φ.source ∧ ContDiffOn ℝ r Φ.symm Φ.target ∧
      ContDiffOn ℝ r Ψ Ψ.source ∧ ContDiffOn ℝ r Ψ.symm Ψ.target ∧
      MapsTo g Φ.source Ψ.source ∧
      ∀ p ∈ Φ.target, Ψ (g (Φ.symm p)) = (p.1, 0) := by
  obtain ⟨e, he0, heU, he00, hreg, hregi, hfirst⟩ :=
    exists_source_straightening r hr U hU h0 g hg hg0 hd
  have htarget : e.target ∈ 𝓝 (0 : V × W) := by
    rw [← he00]
    exact e.open_target.mem_nhds (e.map_source he0)
  obtain ⟨A₀, hA₀, B₀, hB₀, hAB₀⟩ := mem_nhds_prod_iff.mp htarget
  obtain ⟨α, hα, hαsub⟩ := Metric.mem_nhds_iff.mp hA₀
  obtain ⟨β, hβ, hβsub⟩ := Metric.mem_nhds_iff.mp hB₀
  let A := Metric.ball (0 : V) α
  let B := Metric.ball (0 : W) β
  have hAB : A ×ˢ B ⊆ e.target :=
    fun p hp => hAB₀ ⟨hαsub hp.1, hβsub hp.2⟩
  let Φ := (e.symm.restrOpen (A ×ˢ B) (Metric.isOpen_ball.prod Metric.isOpen_ball)).symm
  have hΦ (p : V × W) : Φ p = e p := rfl
  have hΦi (p : V × W) : Φ.symm p = e.symm p := rfl
  have hΦtarget : Φ.target = A ×ˢ B := inter_eq_right.mpr hAB
  have hΦsource : Φ.source = e.source ∩ e ⁻¹' (A ×ˢ B) := rfl
  have hΦU : Φ.source ⊆ U := fun p hp => heU hp.1
  have hΦreg : ContDiffOn ℝ r Φ Φ.source := hreg.mono (fun _ hp => hp.1)
  have hΦregi : ContDiffOn ℝ r Φ.symm Φ.target := hregi.mono (fun _ hp => hp.1)
  let G : V × W → V × Z := g ∘ Φ.symm
  have hG : ContDiffOn ℝ r G (A ×ˢ B) := by
    rw [← hΦtarget]
    exact hg.comp hΦregi (fun p hp => hΦU (Φ.map_target hp))
  have hGfirst : ∀ p ∈ A ×ˢ B, (G p).1 = p.1 :=
    fun p hp => hfirst p (hAB hp)
  have hGrank (p : V × W) (hp : p ∈ A ×ˢ B) :
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G p).toLinearMap) ≤ Module.finrank ℝ V := by
    have hpt : p ∈ Φ.target := hΦtarget.symm ▸ hp
    have hx := hΦU (Φ.map_target hpt)
    have hdiffg := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
    have hdiffi := (hΦregi.contDiffAt (Φ.open_target.mem_nhds hpt)).differentiableAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hr))
    have hcomp : fderiv ℝ G p = (fderiv ℝ g (Φ.symm p)).comp (fderiv ℝ Φ.symm p) :=
      fderiv_comp p hdiffg hdiffi
    rw [hcomp]
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range
      (fderiv ℝ Φ.symm p).toLinearMap (fderiv ℝ g (Φ.symm p)).toLinearMap)).trans (hrank _ hx)
  obtain ⟨Ψ, hΨs, hΨt, hΨreg, hΨregi, hGmap, hnormal⟩ :=
    normal_form_after_straightening r hr A B Metric.isOpen_ball Metric.isOpen_ball
      (convex_ball 0 β) (Metric.mem_ball_self hβ) G hG hGfirst hGrank
  have hΦ0 : (0 : V × W) ∈ Φ.source := by
    rw [hΦsource]
    exact ⟨he0, by rw [mem_preimage, he00]; exact ⟨Metric.mem_ball_self hα, Metric.mem_ball_self hβ⟩⟩
  have h0t : (0 : V × W) ∈ Φ.target := by simpa only [hΦ, he00] using Φ.map_source hΦ0
  have hG0 : G 0 = 0 := by
    change g (Φ.symm 0) = 0
    rw [show Φ.symm 0 = 0 from by simpa only [hΦ, he00] using Φ.left_inv hΦ0]
    exact hg0
  refine ⟨Φ, Ψ, hΦ0, hΦU, he00, ?_, ?_, hΦreg, hΦregi, hΨreg, hΨregi, ?_, ?_⟩
  · rw [hΨs]
    exact ⟨Metric.mem_ball_self hα, mem_univ _⟩
  · have hn := hnormal 0 (hΦtarget ▸ h0t)
    exact (by simpa only [hG0, Prod.fst_zero] using hn : Ψ 0 = (0, 0)).trans (by ext <;> rfl)
  · intro p hp
    have ht := Φ.map_source hp
    have hm := hGmap (hΦtarget ▸ ht)
    change G (Φ p) ∈ Ψ.source at hm
    simpa only [G, Function.comp_apply, Φ.left_inv hp] using hm
  · intro p hp
    exact hnormal p (hΦtarget ▸ hp)

/-- Splitting Euclidean coordinates after the first k entries. The inverse
concatenates the two coordinate vectors, including empty blocks. -/
def coordinateSplit (n k : ℕ) (hk : k ≤ n) : E n ≃L[ℝ] (E k × E (n-k)) := by
  refine LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u =>
        (WithLp.toLp 2 (fun i => u ⟨i.val, lt_of_lt_of_le i.isLt hk⟩),
         WithLp.toLp 2 (fun i => u ⟨k+i.val, by omega⟩))
      invFun := fun p => WithLp.toLp 2 (fun j =>
        if h : j.val < k then p.1 ⟨j.val, h⟩ else p.2 ⟨j.val-k, by omega⟩)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro u
    apply PiLp.ext; intro j
    dsimp
    split
    · rfl
    · rename_i hj
      have hi : (⟨k+(j.val-k), by omega⟩ : Fin n) = j := by
        apply Fin.ext
        exact Nat.add_sub_of_le (Nat.le_of_not_gt hj)
      exact congrArg (fun i : Fin n => u i) hi
  · intro p
    apply Prod.ext
    · apply PiLp.ext; intro j
      change (if h : j.val < k then p.1 ⟨j.val,h⟩ else _) = p.1 j
      simp [j.isLt]
    · apply PiLp.ext; intro j
      simp

theorem coordinateSplit_symm_apply (n k : ℕ) (hk : k ≤ n)
    (p : E k × E (n-k)) (j : Fin n) :
    (coordinateSplit n k hk).symm p j =
      if h : j.val < k then p.1 ⟨j.val,h⟩ else p.2 ⟨j.val-k, by omega⟩ := rfl

/-- Using the same coordinates for the common range block gives precisely
the first-k-coordinate projection specified in the source theorem. -/
theorem coordinateSplit_projection (n m k : ℕ) (hn : k ≤ n) (hm : k ≤ m)
    (u : E n) :
    (coordinateSplit m k hm).symm (((coordinateSplit n k hn) u).1, 0) =
      normalProjection n m k u := by
  ext j
  rw [coordinateSplit_symm_apply]
  simp only [normalProjection, PiLp.toLp_apply]
  by_cases h : j.val < k
  · have hj : j.val < n := lt_of_lt_of_le h hn
    simp only [dite_eq_left h, dite_eq_left (And.intro h hj)]
    rfl
  · simp [h]

/-- Transport a local chart through global coordinate homeomorphisms. -/
def recoordinate {X Y V W : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace V] [TopologicalSpace W]
    (A : X ≃ₜ V) (e : OpenPartialHomeomorph V W) (B : W ≃ₜ Y) :
    OpenPartialHomeomorph X Y :=
  (A.transOpenPartialHomeomorph e).transHomeomorph B

theorem recoordinate_regular {X Y V W : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (r : ℕ∞ω) (A : X ≃ₜ V) (e : OpenPartialHomeomorph V W) (B : W ≃ₜ Y)
    (hA : ContDiff ℝ r A) (hAi : ContDiff ℝ r A.symm)
    (hB : ContDiff ℝ r B) (hBi : ContDiff ℝ r B.symm)
    (he : ContDiffOn ℝ r e e.source) (hei : ContDiffOn ℝ r e.symm e.target) :
    ContDiffOn ℝ r (recoordinate A e B) (recoordinate A e B).source ∧
    ContDiffOn ℝ r (recoordinate A e B).symm (recoordinate A e B).target := by
  constructor
  · exact hB.comp_contDiffOn (he.comp hA.contDiffOn (fun _ hx => hx))
  · exact hAi.comp_contDiffOn (hei.comp hBi.contDiffOn (fun _ hx => hx))

/-- The Euclidean constant-rank theorem, retaining the order of regularity
through every affine, linear, inverse, and shear coordinate change. -/
theorem rankNormalForm {n m : ℕ} (r : ℕ∞ω) (hr : 1 ≤ r)
    (U : Set (E n)) (hU : IsOpen U) (f : E n → E m)
    (hf : ContDiffOn ℝ r f U) (a : E n) (ha : a ∈ U)
    (k : ℕ) (hk : NeighborhoodRank f a k) : RankNormalForm r U f a k := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hbounds := (constant_rank_bounds f a k hk).2
  have hn : k ≤ n := hbounds.trans (min_le_left _ _)
  have hm : k ≤ m := hbounds.trans (min_le_right _ _)
  let L := (fderiv ℝ f a).toLinearMap
  let V := LinearMap.range L
  let W := LinearMap.ker L
  have hdimV : Module.finrank ℝ V = k :=
    (show ∀ᶠ x in 𝓝 a,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = k from hk).self_of_nhds
  obtain ⟨Z, P, Q, hPQ⟩ := exists_adapted_splittings L
  have hdimW : Module.finrank ℝ W = n-k := by
    have h := P.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, finrank_euclideanSpace_fin] at h
    change n = Module.finrank ℝ V + Module.finrank ℝ W at h
    omega
  have hdimZ : Module.finrank ℝ Z = m-k := by
    have h := Q.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod, finrank_euclideanSpace_fin] at h
    change m = Module.finrank ℝ V + Module.finrank ℝ Z at h
    omega
  let cV : V ≃L[ℝ] E k := ContinuousLinearEquiv.ofFinrankEq
    (hdimV.trans (finrank_euclideanSpace_fin.symm))
  let cW : W ≃L[ℝ] E (n-k) := ContinuousLinearEquiv.ofFinrankEq
    (hdimW.trans (finrank_euclideanSpace_fin.symm))
  let cZ : Z ≃L[ℝ] E (m-k) := ContinuousLinearEquiv.ofFinrankEq
    (hdimZ.trans (finrank_euclideanSpace_fin.symm))
  let S : (V × W) ≃L[ℝ] E n :=
    (cV.prodCongr cW).trans (coordinateSplit n k hn).symm
  let T : (V × Z) ≃L[ℝ] E m :=
    (cV.prodCongr cZ).trans (coordinateSplit m k hm).symm
  have hST (p : V × W) : T (p.1, 0) = normalProjection n m k (S p) := by
    have h := coordinateSplit_projection n m k hn hm (S p)
    have hs : coordinateSplit n k hn (S p) = (cV p.1, cW p.2) := by
      exact (coordinateSplit n k hn).apply_symm_apply _
    rw [hs] at h
    simpa only [T, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.prodCongr_apply,
      map_zero] using h
  obtain ⟨O, hOsub, hO, haO⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hk)
  let A : E n ≃ₜ (V × W) := (Homeomorph.subRight a).trans P.toHomeomorph
  let C : E m ≃ₜ (V × Z) := (Homeomorph.subRight (f a)).trans Q.toHomeomorph
  have hA (x : E n) : A x = P (x-a) := rfl
  have hAi (p : V × W) : A.symm p = P.symm p + a := rfl
  have hC (y : E m) : C y = Q (y-f a) := rfl
  have hCi (q : V × Z) : C.symm q = Q.symm q + f a := rfl
  have hAreg : ContDiff ℝ r A := P.contDiff.comp (contDiff_id.sub contDiff_const)
  have hAireg : ContDiff ℝ r A.symm := P.symm.contDiff.add contDiff_const
  have hCreg : ContDiff ℝ r C := Q.contDiff.comp (contDiff_id.sub contDiff_const)
  have hCireg : ContDiff ℝ r C.symm := Q.symm.contDiff.add contDiff_const
  have hAa : A a = 0 := by simp only [hA, sub_self, map_zero]
  have hCa : C (f a) = 0 := by simp only [hC, sub_self, map_zero]
  let D := A.symm ⁻¹' O
  have hD : IsOpen D := hO.preimage A.symm.continuous
  have hD0 : (0 : V × W) ∈ D := by
    change A.symm 0 ∈ O
    rw [← hAa, A.symm_apply_apply]
    exact haO
  let g : V × W → V × Z := fun p => C (f (A.symm p))
  have hg : ContDiffOn ℝ r g D := hCreg.comp_contDiffOn
    ((hf.mono (fun x hx => (hOsub hx).1)).comp hAireg.contDiffOn (fun _ hx => hx))
  have hg0 : g 0 = 0 := by
    change C (f (A.symm 0)) = 0
    rw [← hAa, A.symm_apply_apply, hCa]
  have hder (p : V × W) (hp : p ∈ D) :
      HasFDerivAt g
        (Q.toContinuousLinearMap.comp ((fderiv ℝ f (A.symm p)).comp P.symm.toContinuousLinearMap)) p := by
    have hfp := ((hf.contDiffAt (hU.mem_nhds (hOsub hp).1)).differentiableAt hr0).hasFDerivAt
    have hai := (P.symm.hasFDerivAt (x := p)).add_const a
    have hinner := hfp.comp p hai
    exact Q.hasFDerivAt.comp p (hinner.sub_const (f a))
  have hd : HasFDerivAt g
      ((ContinuousLinearMap.fst ℝ V W).prod (0 : V × W →L[ℝ] Z)) 0 := by
    convert hder 0 hD0 using 1
    apply ContinuousLinearMap.ext
    intro p
    change (p.1, 0) = Q (fderiv ℝ f (A.symm 0) (P.symm p))
    rw [← hAa, A.symm_apply_apply]
    exact (hPQ p.1 p.2).symm
  have hgrank (p : V × W) (hp : p ∈ D) :
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g p).toLinearMap) ≤ Module.finrank ℝ V := by
    rw [(hder p hp).fderiv]
    have h := finrank_range_coordinates (fderiv ℝ f (A.symm p)).toLinearMap
      P.symm.toLinearEquiv Q.toLinearEquiv
    change Module.finrank ℝ (LinearMap.range
      (Q.toLinearMap.comp ((fderiv ℝ f (A.symm p)).toLinearMap.comp P.symm.toLinearMap))) ≤ _
    rw [h, hdimV]
    exact le_of_eq (hOsub hp).2
  obtain ⟨e, d, he0, heD, he00, hd0, hd00, hereg, heireg, hdreg, hdireg, hmap, hnormal⟩ :=
    normalized_rank_normal_form r hr D hD hD0 g hg hg0 hd hgrank
  let Φ := recoordinate A e S.toHomeomorph
  let Ψ := recoordinate C d T.toHomeomorph
  have hΦ (x : E n) : Φ x = S (e (A x)) := rfl
  have hΦi (u : E n) : Φ.symm u = A.symm (e.symm (S.symm u)) := rfl
  have hΨ (y : E m) : Ψ y = T (d (C y)) := rfl
  have hΦs (x : E n) : x ∈ Φ.source ↔ A x ∈ e.source := Iff.rfl
  have hΦt (u : E n) : u ∈ Φ.target ↔ S.symm u ∈ e.target := Iff.rfl
  have hΨs (y : E m) : y ∈ Ψ.source ↔ C y ∈ d.source := Iff.rfl
  have hregs := recoordinate_regular r A e S.toHomeomorph hAreg hAireg
    S.contDiff S.symm.contDiff hereg heireg
  have hregt := recoordinate_regular r C d T.toHomeomorph hCreg hCireg
    T.contDiff T.symm.contDiff hdreg hdireg
  refine ⟨Φ, Ψ, ?_, ?_, ?_, ?_, ?_, hregs.1, hregs.2, hregt.1, hregt.2, ?_, ?_⟩
  · exact (hΦs a).mpr (hAa.symm ▸ he0)
  · intro x hx
    have hdx := heD ((hΦs x).mp hx)
    change A.symm (A x) ∈ O at hdx
    exact (hOsub (by simpa only [A.symm_apply_apply] using hdx)).1
  · rw [hΦ, hAa, he00, map_zero]
  · exact (hΨs (f a)).mpr (hCa.symm ▸ hd0)
  · rw [hΨ, hCa, hd00, map_zero]
  · intro x hx
    apply (hΨs (f x)).mpr
    have h := hmap ((hΦs x).mp hx)
    change C (f (A.symm (A x))) ∈ d.source at h
    simpa only [A.symm_apply_apply] using h
  · intro u hu
    rw [hΨ, hΦi]
    change T (d (g (e.symm (S.symm u)))) = _
    rw [hnormal _ ((hΦt u).mp hu), hST, S.apply_symm_apply]

end ConstantRank

theorem constant_rank_finite : Specs.D04.C04.ConstantRank.constant_rank_finiteType := by
  intro n m r U f a k hr hU hf ha hk
  exact ⟨(constant_rank_bounds f a k hk).1, (constant_rank_bounds f a k hk).2,
    ConstantRank.rankNormalForm r (by exact_mod_cast hr) U hU f
      ((crOn_iff_contDiffOn r U f hU).mp hf) a ha k hk⟩

theorem constant_rank_smooth : Specs.D04.C04.ConstantRank.constant_rank_smoothType := by
  intro n m U f a k hU hf ha hk
  exact ⟨(constant_rank_bounds f a k hk).1, (constant_rank_bounds f a k hk).2,
    ConstantRank.rankNormalForm ∞ (by simp) U hU f
      ((smoothOn_iff_contDiffOn U f hU).mp hf) a ha k hk⟩
theorem constant_rank_square_finite :
    Specs.D04.C04.ConstantRank.constant_rank_square_finiteType := by
  intro n r U f a hr hU hf ha hk
  apply ConstantRank.rankNormalForm_square r (by exact_mod_cast hr) U hU f
    ((crOn_iff_contDiffOn r U f hU).mp hf) a ha
  exact (show ∀ᶠ x in 𝓝 a,
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = n from hk).self_of_nhds

theorem constant_rank_square_smooth :
    Specs.D04.C04.ConstantRank.constant_rank_square_smoothType := by
  intro n U f a hU hf ha hk
  apply ConstantRank.rankNormalForm_square ∞ (by simp) U hU f
    ((smoothOn_iff_contDiffOn U f hU).mp hf) a ha
  exact (show ∀ᶠ x in 𝓝 a,
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = n from hk).self_of_nhds

end D04
