import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.MittagLeffler
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.CompatibleExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.RungeHolomorphicCorrections
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.MeromorphicSeriesGluing
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set Filter
open scoped Topology Classical

namespace D12Complex.MittagLeffler
open LocalQuotientsArithmetic

/-- Finite principal parts, including the zero part. -/
abbrev PrincipalPart := Specs.D12Complex.Ch16.MittagLeffler.Objects.PrincipalPart

/-- The finite sum ∑ cₖ/(z-a)^k. Its value at a is irrelevant. -/
abbrev principalPartValue := Specs.D12Complex.Ch16.MittagLeffler.Objects.principalPartValue

/-- Local finiteness in Ω, in its equivalent compact-subset formulation. -/
abbrev LocallyFiniteIn := Specs.D12Complex.Ch16.MittagLeffler.Objects.LocallyFiniteIn

/-- An analytic remainder at a, with equality of punctured germs. -/
abbrev HasPrincipalPart := Specs.D12Complex.Ch16.MittagLeffler.Objects.HasPrincipalPart

/-- Exactly the prescribed principal parts and no other poles. -/
abbrev IsSolution := Specs.D12Complex.Ch16.MittagLeffler.Objects.IsSolution

/-- Addition of a finite holomorphic function, with removable values filled. -/
abbrev addHolomorphic := Specs.D12Complex.Ch16.MittagLeffler.Objects.addHolomorphic

@[simp] theorem principalPartValue_zero (a z : ℂ) : principalPartValue 0 a z = 0 := by
  simp [principalPartValue, Specs.D12Complex.Ch16.MittagLeffler.Objects.principalPartValue]

/-- Compact local finiteness gives a neighborhood containing no designated
point other than possibly its center, including centers not in A. -/
theorem LocallyFiniteIn.isolating_neighborhood {Ω A : Set ℂ} (hA : LocallyFiniteIn Ω A)
    (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω) :
    ∃ U : Set ℂ, IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧ ∀ z ∈ U, z ∈ A → z = a := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ a ha
  have hKΩ : Metric.closedBall a (r / 2) ⊆ Ω := by
    intro z hz
    apply hball
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith))
  have hfin := hA.2 (Metric.closedBall a (r / 2)) (isCompact_closedBall _ _) hKΩ
  let S := (A ∩ Metric.closedBall a (r / 2)) \ {a}
  have hSc : IsClosed S := hfin.sdiff.isClosed
  refine ⟨Metric.ball a (r / 2) ∩ Sᶜ, Metric.isOpen_ball.inter hSc.isOpen_compl, ?_, ?_, ?_⟩
  · simp [S, Metric.mem_ball, hr]
  · exact fun z hz => hKΩ (Metric.ball_subset_closedBall hz.1)
  · intro z hz hzA
    by_contra hza
    exact hz.2 ⟨⟨hzA, Metric.ball_subset_closedBall hz.1⟩, hza⟩

/-- Removing locally finite data from Ω leaves an open set. -/
theorem LocallyFiniteIn.isOpen_compl {Ω A : Set ℂ} (hA : LocallyFiniteIn Ω A)
    (hΩ : IsOpen Ω) : IsOpen (Ω \ A) := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  obtain ⟨U, hU, haU, hUΩ, hiso⟩ := hA.isolating_neighborhood hΩ ha.1
  apply mem_of_superset (hU.mem_nhds haU)
  intro z hz
  refine ⟨hUΩ hz, ?_⟩
  intro hzA
  exact ha.2 ((hiso z hz hzA) ▸ hzA)

/-- A finite principal part is meromorphic at every point. -/
theorem principalPartValue_meromorphicAt (p : PrincipalPart) (a z : ℂ) :
    MeromorphicAt (principalPartValue p a) z := by
  unfold principalPartValue Specs.D12Complex.Ch16.MittagLeffler.Objects.principalPartValue
    Finsupp.sum
  apply MeromorphicAt.fun_sum
  intro k _
  exact (MeromorphicAt.const _ _).div
    (((MeromorphicAt.id z).sub (MeromorphicAt.const a z)).pow (k : ℕ))

/-- Away from its center a principal part is analytic. -/
theorem principalPartValue_analyticAt (p : PrincipalPart) (a z : ℂ) (hz : z ≠ a) :
    AnalyticAt ℂ (principalPartValue p a) z := by
  unfold principalPartValue Specs.D12Complex.Ch16.MittagLeffler.Objects.principalPartValue
    Finsupp.sum
  apply Finset.analyticAt_fun_sum
  intro k _
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow (k : ℕ))
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

/-- The largest nonzero coefficient gives the exact pole order, even after
adding an arbitrary analytic remainder. -/
theorem principalPart_add_order {p : PrincipalPart} (hp : p ≠ 0) (a : ℂ)
    {h : ℂ → ℂ} (hh : AnalyticAt ℂ h a) :
    ∃ m : ℕ+, meromorphicOrderAt (fun z => principalPartValue p a z + h z) a =
      (-(m : ℤ) : WithTop ℤ) := by
  have hs : p.support.Nonempty := Finsupp.support_nonempty_iff.mpr hp
  let m : ℕ+ := p.support.max' hs
  have hm : m ∈ p.support := Finset.max'_mem _ hs
  have hjm (j : ℕ+) (hj : j ∈ p.support) : (j : ℕ) ≤ (m : ℕ) :=
    Finset.le_max' _ j hj
  let g : ℂ → ℂ := fun z => ∑ j ∈ p.support, p j * (z - a) ^ ((m : ℕ) - j)
  have hg : AnalyticAt ℂ g a := by
    apply Finset.analyticAt_fun_sum
    intro j _
    exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow _)
  have hga : g a = p m := by
    dsimp [g]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j hj hne
      have hlt : (j : ℕ) < (m : ℕ) := lt_of_le_of_ne (hjm j hj)
        (fun he => hne (Subtype.ext he))
      simp [zero_pow (by omega : (m : ℕ) - j ≠ 0)]
    · exact fun hn => (hn hm).elim
  have hg0 : g a ≠ 0 := by simpa [hga] using Finsupp.mem_support_iff.mp hm
  have hscale (z : ℂ) (hz : z ≠ a) :
      (z - a) ^ (m : ℕ) * principalPartValue p a z = g z := by
    simp only [principalPartValue, Specs.D12Complex.Ch16.MittagLeffler.Objects.principalPartValue,
      Finsupp.sum, g, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hpow : (z - a) ^ (m : ℕ) =
        (z - a) ^ ((m : ℕ) - j) * (z - a) ^ (j : ℕ) := by
      rw [← pow_add, Nat.sub_add_cancel (hjm j hj)]
    rw [hpow]
    field_simp
  have hmer : MeromorphicAt (fun z => principalPartValue p a z + h z) a :=
    (principalPartValue_meromorphicAt p a a).add hh.meromorphicAt
  refine ⟨m, (meromorphicOrderAt_eq_int_iff hmer).mpr ?_⟩
  refine ⟨fun z => g z + (z - a) ^ (m : ℕ) * h z,
    hg.add (((analyticAt_id.sub analyticAt_const).pow _).mul hh), ?_, ?_⟩
  · simpa only [sub_self, zero_pow m.pos.ne', zero_mul, add_zero] using hg0
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : z ≠ a := hz
    rw [zpow_neg, zpow_natCast, smul_eq_mul]
    have hpz := hscale z hza
    have hpow0 : (z - a) ^ (m : ℕ) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
    field_simp
    linear_combination hpz

/-- Zero parts are removable, and every nonzero finite part is a genuine pole. -/
theorem solution_pole_iff : Specs.D12Complex.Ch16.MittagLeffler.solution_pole_iff_type := by
  intro Ω A p F hF a ha
  obtain ⟨h, hh, he⟩ := hF.2.2 a
  rw [scalar_eq_fill Ω F hF.1 ha]
  change fill (scalarFinitePart F) a = sphereInfty ↔ _
  rw [fill_eq_infty_iff]
  rw [meromorphicOrderAt_congr he]
  constructor
  · intro hneg hp
    have heq : (fun z => principalPartValue (p a) a z + h z) = h := by
      funext z
      simp [hp]
    rw [heq] at hneg
    exact (not_lt.mpr hh.meromorphicOrderAt_nonneg) hneg
  · intro hp
    obtain ⟨m, hm⟩ := principalPart_add_order hp (a : ℂ) hh
    rw [hm]
    exact WithTop.coe_lt_coe.mpr (by exact_mod_cast (neg_neg_of_pos (by exact_mod_cast m.pos)))

/-- Weak holomorphy supplies an analytic germ at every interior point. -/
theorem analyticAt_of_holomorphicOn {Ω : Set ℂ} {h : ℂ → ℂ}
    (hh : HolomorphicOn Ω h) {a : ℂ} (ha : a ∈ Ω) : AnalyticAt ℂ h a :=
  DifferentiableOn.analyticAt
    (fun z hz => (hh.2 z hz).differentiableWithinAt : DifferentiableOn ℂ h Ω)
    (hh.1.mem_nhds ha)

/-- Global meromorphic normalization restores a given analytic punctured extension. -/
theorem analyticAt_normalize_of_extension {Ω : Set ℂ} {f g : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicOn f Ω) (ha : a ∈ Ω) (hg : AnalyticAt ℂ g a)
    (he : f =ᶠ[𝓝[≠] a] g) : AnalyticAt ℂ (toMeromorphicNFOn f Ω) a := by
  rw [analyticAt_congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf ha)]
  rw [analyticAt_congr (toMeromorphicNFAt_eventuallyEq_nhds_congr he)]
  simpa only [toMeromorphicNFAt_eq_self.mpr hg.meromorphicNFAt] using hg

/-- Changing values outside the domain changes neither solutions nor their parts. -/
theorem IsSolution.congr {Ω A : Set ℂ} {p : A → PrincipalPart}
    {F G : ℂ → RiemannSphere} (hF : IsSolution Ω A p F) (hA : A ⊆ Ω)
    (he : EqOn F G Ω) : IsSolution Ω A p G := by
  refine ⟨scalar_congr hF.1 he, ?_, ?_⟩
  · intro a ha hna
    rw [← he ha]
    exact hF.2.1 a ha hna
  · intro a
    obtain ⟨h, hh, hpart⟩ := hF.2.2 a
    refine ⟨h, hh, ?_⟩
    have hfg : scalarFinitePart F =ᶠ[𝓝[≠] (a : ℂ)] scalarFinitePart G := by
      filter_upwards [nhdsWithin_le_nhds (hF.1.1.mem_nhds (hA a.2))] with z hz
      exact congrArg finiteCoordinate (he hz)
    exact hfg.symm.trans hpart

/-- Adding any holomorphic function preserves every local principal part. -/
theorem IsSolution.addHolomorphic {Ω A : Set ℂ} {p : A → PrincipalPart}
    {F : ℂ → RiemannSphere} {h : ℂ → ℂ} (hF : IsSolution Ω A p F)
    (hA : A ⊆ Ω) (hh : HolomorphicOn Ω h) :
    IsSolution Ω A p (addHolomorphic F h) := by
  have hm : MeromorphicOn (fun z => scalarFinitePart F z + h z) Ω := by
    intro a ha
    exact (scalar_meromorphicAt Ω F hF.1 a ha).add
      (analyticAt_of_holomorphicOn hh ha).meromorphicAt
  refine ⟨scalarMeromorphicOn_fill Ω hh.1 _ hm, ?_, ?_⟩
  · intro a ha hna
    have hfa := scalarMeromorphicOn_finite_analytic Ω F hF.1 a ha (hF.2.1 a ha hna)
    change fill (scalarFinitePart F + h) a ≠ sphereInfty
    rw [fill_of_analyticAt (hfa.add (analyticAt_of_holomorphicOn hh ha))]
    simp [sphereFinite, sphereInfty]
  · intro a
    obtain ⟨g, hg, he⟩ := hF.2.2 a
    refine ⟨fun z => g z + h z, hg.add (analyticAt_of_holomorphicOn hh (hA a.2)), ?_⟩
    have hfill := finitePart_fill_germ (hm a (hA a.2))
    change scalarFinitePart (fill (fun z => scalarFinitePart F z + h z)) =ᶠ[_] _
    apply hfill.trans
    filter_upwards [he] with z hz
    simp only [hz]
    ring

/-- The difference of two solutions has an analytic extension at every point. -/
theorem solutions_difference_extension {Ω A : Set ℂ} {p : A → PrincipalPart}
    {F G : ℂ → RiemannSphere} (hF : IsSolution Ω A p F) (hG : IsSolution Ω A p G)
    (a : ℂ) (ha : a ∈ Ω) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (fun z => scalarFinitePart G z - scalarFinitePart F z) =ᶠ[𝓝[≠] a] g := by
  by_cases hmem : a ∈ A
  · obtain ⟨u, hu, heu⟩ := hG.2.2 ⟨a, hmem⟩
    obtain ⟨v, hv, hev⟩ := hF.2.2 ⟨a, hmem⟩
    refine ⟨fun z => u z - v z, hu.sub hv, ?_⟩
    filter_upwards [heu, hev] with z hzu hzv
    simp only [hzu, hzv]
    ring
  · exact ⟨_, (scalarMeromorphicOn_finite_analytic Ω G hG.1 a ha (hG.2.1 a ha hmem)).sub
      (scalarMeromorphicOn_finite_analytic Ω F hF.1 a ha (hF.2.1 a ha hmem)),
      Filter.EventuallyEq.rfl⟩

/-- Every two solutions differ by a global holomorphic function on Ω. -/
theorem solutions_differ_by_holomorphic {Ω A : Set ℂ} {p : A → PrincipalPart}
    {F G : ℂ → RiemannSphere} (hF : IsSolution Ω A p F) (hG : IsSolution Ω A p G) :
    ∃ h : ℂ → ℂ, HolomorphicOn Ω h ∧ EqOn G (addHolomorphic F h) Ω := by
  let d : ℂ → ℂ := fun z => scalarFinitePart G z - scalarFinitePart F z
  have hd : MeromorphicOn d Ω := fun a ha =>
    (scalar_meromorphicAt Ω G hG.1 a ha).sub (scalar_meromorphicAt Ω F hF.1 a ha)
  let h := toMeromorphicNFOn d Ω
  have hh : HolomorphicOn Ω h := by
    refine ⟨hF.1.1, fun a ha => ?_⟩
    obtain ⟨g, hg, he⟩ := solutions_difference_extension hF hG a ha
    exact (analyticAt_normalize_of_extension hd ha hg he).differentiableAt
  refine ⟨h, hh, fun a ha => ?_⟩
  calc
    G a = fill (scalarFinitePart G) a := scalar_eq_fill Ω G hG.1 ha
    _ = addHolomorphic F h a := by
      apply fill_congr
      have he := hd.toMeromorphicNFOn_eq_self_on_nhdsNE ha
      filter_upwards [he] with z hz
      change h z = scalarFinitePart G z - scalarFinitePart F z at hz
      rw [hz]
      ring

/-- Full affine solution-set description; local finiteness is only needed for existence. -/
theorem solution_affine_of_subset {Ω A : Set ℂ} (hA : A ⊆ Ω)
    (p : A → PrincipalPart) (F G : ℂ → RiemannSphere) (hF : IsSolution Ω A p F) :
    IsSolution Ω A p G ↔ ∃ h : ℂ → ℂ, HolomorphicOn Ω h ∧
      EqOn G (addHolomorphic F h) Ω := by
  constructor
  · exact solutions_differ_by_holomorphic hF
  · rintro ⟨h, hh, he⟩
    exact (hF.addHolomorphic hA hh).congr hA he.symm

/-- Finite data need no approximation: fill the sum of the prescribed parts. -/
theorem mittag_leffler_finite :
    Specs.D12Complex.Ch16.MittagLeffler.mittag_leffler_finite_type := by
  intro Ω A hΩ hA hfin p
  letI : Fintype A := hfin.fintype
  let f : ℂ → ℂ := fun z => ∑ a : A, principalPartValue (p a) a z
  have hm : MeromorphicOn f Ω := by
    intro z _
    exact MeromorphicAt.fun_sum (fun a _ => principalPartValue_meromorphicAt (p a) a z)
  refine ⟨fill f, scalarMeromorphicOn_fill Ω hΩ f hm, ?_, ?_⟩
  · intro z hz hza
    have han : AnalyticAt ℂ f z := by
      exact Finset.analyticAt_fun_sum _ (fun a _ =>
        principalPartValue_analyticAt (p a) a z (fun he => hza (he ▸ a.2)))
    rw [fill_of_analyticAt han]
    simp [sphereFinite, sphereInfty]
  · intro a
    let g : ℂ → ℂ := fun z => ∑ b ∈ (Finset.univ.erase a), principalPartValue (p b) b z
    have hg : AnalyticAt ℂ g (a : ℂ) := by
      apply Finset.analyticAt_fun_sum
      intro b hb
      exact principalPartValue_analyticAt (p b) b a (fun he =>
        (Finset.ne_of_mem_erase hb) (Subtype.ext he.symm))
    refine ⟨g, hg, (finitePart_fill_germ (hm a (hA a.2))).trans ?_⟩
    apply Filter.Eventually.of_forall
    intro z
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm

theorem solution_affine : Specs.D12Complex.Ch16.MittagLeffler.solution_affine_type := by
  intro Ω A p F G hA hF
  exact solution_affine_of_subset hA p F G hF

/-- A finite sum of parts is analytic at every point outside its centers. -/
theorem finite_parts_analyticAt {A : Set ℂ} (p : A → PrincipalPart)
    (s : Finset A) (z : ℂ) (hz : ∀ a ∈ s, z ≠ (a : ℂ)) :
    AnalyticAt ℂ (fun w => ∑ a ∈ s, principalPartValue (p a) a w) z := by
  exact Finset.analyticAt_fun_sum _ (fun a ha =>
    principalPartValue_analyticAt (p a) a z (hz a ha))

/-- Subtracting one designated part from a finite sum removes its singularity. -/
theorem finite_parts_sub_analyticAt {A : Set ℂ} (p : A → PrincipalPart)
    (s : Finset A) (a : A) (ha : a ∈ s) :
    AnalyticAt ℂ (fun w => (∑ b ∈ s, principalPartValue (p b) b w) -
      principalPartValue (p a) a w) (a : ℂ) := by
  have hg := finite_parts_analyticAt p (s.erase a) a (fun b hb he =>
    (Finset.ne_of_mem_erase hb) (Subtype.ext he.symm))
  convert hg using 1
  ext w
  rw [← Finset.add_sum_erase s _ ha]
  ring

/-- Compact stages contain only finitely many designated points. -/
def stagePoints {Ω A : Set ℂ} (hA : LocallyFiniteIn Ω A)
    {K : ℕ → Set ℂ} (hK : Ch15.IsCompatibleExhaustion Ω K) (n : ℕ) : Finset A :=
  ((hA.2 (K n) (hK.1 n).1 (hK.1 n).2.1).preimage
    (fun _ _ _ _ he => Subtype.ext he)).toFinset

@[simp] theorem mem_stagePoints {Ω A : Set ℂ} (hA : LocallyFiniteIn Ω A)
    {K : ℕ → Set ℂ} (hK : Ch15.IsCompatibleExhaustion Ω K) (n : ℕ) (a : A) :
    a ∈ stagePoints hA hK n ↔ (a : ℂ) ∈ K n := by
  simp [stagePoints]

/-- Runge-corrected shell series, with its finite heads identified explicitly. -/
theorem corrected_series {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hA : LocallyFiniteIn Ω A)
    (p : A → PrincipalPart) :
    ∃ (K : ℕ → Set ℂ) (hK : Ch15.IsCompatibleExhaustion Ω K)
      (r : ℕ → ℂ → ℂ) (t : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
      (∀ n, HolomorphicOn Ω (r n)) ∧ MeromorphicOn f Ω ∧
      TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, t n z) f atTop Ω ∧
      (∀ m z, (∑ n ∈ Finset.range m, t n z) =
        (∑ a ∈ stagePoints hA hK m, principalPartValue (p a) a z) -
          ∑ n ∈ Finset.range m, r n z) ∧
      ∀ m, HolomorphicOn (interior (K m))
        (fun z => f z - ∑ n ∈ Finset.range m, t n z) := by
  obtain ⟨K, hzero, hK⟩ := Ch15.compatible_exhaustion Ω hΩ
  have hmono := MeromorphicSeriesGluing.exhaustion_monotone hK
  let s := stagePoints hA hK
  have hsmono : Monotone s := by
    intro i j hij a ha
    exact (mem_stagePoints hA hK j a).mpr
      (hmono hij ((mem_stagePoints hA hK i a).mp ha))
  have hs0 : s 0 = ∅ := by
    ext a
    simp [s, hzero]
  let q : ℕ → ℂ → ℂ := fun n z =>
    ∑ a ∈ s (n + 1) \ s n, principalPartValue (p a) a z
  have hqmero : ∀ n, MeromorphicOn (q n) Ω := by
    intro n z _
    exact MeromorphicAt.fun_sum fun a _ => principalPartValue_meromorphicAt (p a) a z
  have hqhol : ∀ n, ∃ U : Set ℂ, IsOpen U ∧ K n ⊆ U ∧ HolomorphicOn U (q n) := by
    intro n
    let S : Set ℂ := Subtype.val '' (↑(s (n + 1) \ s n) : Set A)
    have hS : S.Finite := (Finset.finite_toSet _).image _
    refine ⟨Sᶜ, hS.isClosed.isOpen_compl, ?_, hS.isClosed.isOpen_compl, ?_⟩
    · intro z hz
      rintro ⟨a, ha, rfl⟩
      exact (Finset.mem_sdiff.mp ha).2 ((mem_stagePoints hA hK n a).mpr hz)
    · intro z hz
      exact (finite_parts_analyticAt p _ z (by
        intro a ha he
        exact hz ⟨a, ha, he.symm⟩)).differentiableAt
  let b : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  obtain ⟨r, hr, herr⟩ := RungeHolomorphicCorrections.holomorphic_corrections
    Ω K q b hΩ hK hqhol (fun n => pow_pos (by norm_num) n)
  let t : ℕ → ℂ → ℂ := fun n z => q n z - r n z
  have htmero : ∀ n, MeromorphicOn (t n) Ω := by
    intro n z hz
    exact (hqmero n z hz).sub (analyticAt_of_holomorphicOn (hr n) hz).meromorphicAt
  have hthol : ∀ n, HolomorphicOn (interior (K n)) (t n) := by
    intro n
    obtain ⟨U, hU, hKU, hq⟩ := hqhol n
    exact ⟨isOpen_interior, fun z hz =>
      (hq.2 z (hKU (interior_subset hz))).sub
        ((hr n).2 z ((hK.1 n).2.1 (interior_subset hz)))⟩
  obtain ⟨f, hf, hlim, htail⟩ := MeromorphicSeriesGluing.meromorphic_series_gluing
    Ω K t b hΩ hzero hK (summable_geometric_of_norm_lt_one (by norm_num))
      (fun n => le_of_lt (pow_pos (by norm_num) n)) htmero hthol
      (fun n z hz => (herr n z hz).le)
  refine ⟨K, hK, r, t, f, hr, hf, hlim, ?_, htail⟩
  intro m z
  induction m with
  | zero =>
    change (0 : ℂ) = (∑ a ∈ s 0, principalPartValue (p a) a z) - 0
    simp [hs0]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hsum := Finset.sum_sdiff (hsmono (Nat.le_succ m))
      (f := fun a : A => principalPartValue (p a) a z)
    dsimp [t, q]
    dsimp [s] at hsum ⊢
    linear_combination hsum

/-- Existence for arbitrary locally finite data on any open plane set. -/
theorem mittag_leffler_exists :
    Specs.D12Complex.Ch16.MittagLeffler.mittag_leffler_exists_type := by
  intro Ω A hΩ hA p
  obtain ⟨K, hK, r, t, f, hr, hf, hlim, hhead, htail⟩ := corrected_series hΩ hA p
  have hR (m : ℕ) (z : ℂ) (hz : z ∈ Ω) :
      AnalyticAt ℂ (fun w => ∑ n ∈ Finset.range m, r n w) z :=
    Finset.analyticAt_fun_sum _ (fun n _ => analyticAt_of_holomorphicOn (hr n) hz)
  refine ⟨fill f, scalarMeromorphicOn_fill Ω hΩ f hf, ?_, ?_⟩
  · intro z hz hzA
    obtain ⟨m, hm⟩ := MeromorphicSeriesGluing.exists_mem_interior_stage hK hz
    have hT := analyticAt_of_holomorphicOn (htail m) hm
    have hP := finite_parts_analyticAt p (stagePoints hA hK m) z (by
      intro a _ he
      exact hzA (he ▸ a.2))
    have han : AnalyticAt ℂ f z := by
      apply ((hT.add hP).sub (hR m z hz)).congr
      apply Filter.Eventually.of_forall
      intro w
      dsimp
      rw [hhead m w]
      ring
    rw [fill_of_analyticAt han]
    simp [sphereFinite, sphereInfty]
  · intro a
    obtain ⟨m, hm⟩ := MeromorphicSeriesGluing.exists_mem_interior_stage hK (hA.1 a.2)
    have ha : a ∈ stagePoints hA hK m :=
      (mem_stagePoints hA hK m a).mpr (interior_subset hm)
    have hT := analyticAt_of_holomorphicOn (htail m) hm
    have hP := finite_parts_sub_analyticAt p (stagePoints hA hK m) a ha
    have han : AnalyticAt ℂ (fun w => f w - principalPartValue (p a) a w) (a : ℂ) := by
      apply ((hT.add hP).sub (hR m a (hA.1 a.2))).congr
      apply Filter.Eventually.of_forall
      intro w
      dsimp
      rw [hhead m w]
      ring
    refine ⟨_, han, (finitePart_fill_germ (hf a (hA.1 a.2))).trans ?_⟩
    apply Filter.Eventually.of_forall
    intro w
    ring

end D12Complex.MittagLeffler
