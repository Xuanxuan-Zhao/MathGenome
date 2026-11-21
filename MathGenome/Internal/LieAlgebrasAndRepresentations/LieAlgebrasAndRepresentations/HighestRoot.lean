import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HighestRoot
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
import Mathlib.Algebra.Group.Irreducible.Indecomposable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
universe u v
namespace LieAlgebrasAndRepresentations.HighestRoot
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

private lemma positive_mem_monoid [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L) (hH : IsToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) {α : Module.Dual ℂ H}
    (hα : α ∈ positiveRoots H φ) : α ∈ positiveRootMonoid H φ := by
  let : Finite (rootSet H) := (rootSet_finite H hH).to_subtype
  have he : (fun a : rootSet H => (a : Module.Dual ℂ H)) ''
      IsAddIndecomposable.baseOf (fun a : rootSet H => (a : Module.Dual ℂ H))
        φ.toAddMonoidHom = simpleRoots H φ := by
    ext a
    constructor
    · rintro ⟨a, ⟨ha, hi⟩, rfl⟩
      refine ⟨⟨a.property, ha⟩, ?_⟩
      intro b hb c hc heq
      rcases hi ⟨b, hb.1⟩ hb.2 ⟨c, hc.1⟩ hc.2 heq with h | h
      · exact (ne_of_gt hb.2) (by rw [show b = 0 from h]; simp)
      · exact (ne_of_gt hc.2) (by rw [show c = 0 from h]; simp)
    · intro ha
      exact ⟨⟨a, ha.1.1⟩, ⟨ha.1.2,
        fun b hb c hc heq => False.elim (ha.2 b ⟨b.property, hb⟩ c ⟨c.property, hc⟩ heq)⟩, rfl⟩
  change α ∈ AddSubmonoid.closure _
  rw [← he, AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
  exact AddSubmonoid.subset_closure ⟨⟨α, hα.1⟩, hα.2, rfl⟩

private lemma monoid_zero_or_positive (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) {α : Module.Dual ℂ H}
    (hα : α ∈ positiveRootMonoid H φ) : α = 0 ∨ 0 < φ α := by
  refine AddSubmonoid.closure_induction (fun a ha => Or.inr ha.1.2)
    (Or.inl rfl) (fun a b _ _ ha hb => ?_) hα
  rcases ha with rfl | ha
  · simpa using hb
  rcases hb with rfl | hb
  · simpa using Or.inr ha
  · exact Or.inr (by simpa using add_pos ha hb)

private lemma monoid_antisymm (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) {α β : Module.Dual ℂ H}
    (hα : α - β ∈ positiveRootMonoid H φ)
    (hβ : β - α ∈ positiveRootMonoid H φ) : α = β := by
  rcases monoid_zero_or_positive H φ hα with hz | hp
  · exact sub_eq_zero.mp hz
  rcases monoid_zero_or_positive H φ hβ with hz | hp'
  · exact (sub_eq_zero.mp hz).symm
  · rw [map_sub] at hp hp'
    linarith

/-- Iterated negative-root operators in the actual adjoint representation. -/
private inductive Lowered (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L) :
    Module.Dual ℂ H → L → Prop
  | base : Lowered H φ θ e θ e
  | step {α γ : Module.Dual ℂ H} {x z : L}
      (hα : α ∈ rootSet H) (hneg : φ α < 0) (hx : x ∈ rootSpace H α)
      (hz : Lowered H φ θ e γ z) : Lowered H φ θ e (α + γ) ⁅x, z⁆

private def loweringSpan (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L) :
    Submodule ℂ L := Submodule.span ℂ {z | ∃ γ, Lowered H φ θ e γ z}

private lemma lowered_mem (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L)
    {γ : Module.Dual ℂ H} {z : L} (hz : Lowered H φ θ e γ z) :
    z ∈ loweringSpan H φ θ e := Submodule.subset_span ⟨γ, hz⟩

private lemma lowered_weight (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L)
    (he : e ∈ rootSpace H θ) {γ : Module.Dual ℂ H} {z : L}
    (hz : Lowered H φ θ e γ z) : z ∈ rootSpace H γ := by
  induction hz with
  | base => exact he
  | step hα hneg hx hz ih => exact rootSpace_bracket H _ _ _ _ hx ih

private lemma loweringSpan_negative (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L)
    {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) (hneg : φ α < 0)
    {x : L} (hx : x ∈ rootSpace H α) {z : L} (hz : z ∈ loweringSpan H φ θ e) :
    ⁅x, z⁆ ∈ loweringSpan H φ θ e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨γ, hz⟩ := hz
    exact lowered_mem H φ θ e (Lowered.step hα hneg hx hz)
  | zero => simp
  | add a b ha hb iha ihb => simpa only [lie_add] using
      (loweringSpan H φ θ e).add_mem iha ihb
  | smul c z hz ih => simpa only [lie_smul] using
      (loweringSpan H φ θ e).smul_mem c ih

private lemma loweringSpan_cartan (H : LieSubalgebra ℂ L)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L)
    (he : e ∈ rootSpace H θ) (h : H) {z : L} (hz : z ∈ loweringSpan H φ θ e) :
    ⁅(h : L), z⁆ ∈ loweringSpan H φ θ e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨γ, hz⟩ := hz
    rw [(mem_rootSpace H γ z).mp (lowered_weight H φ θ e he hz) h]
    exact (loweringSpan H φ θ e).smul_mem _ (lowered_mem H φ θ e hz)
  | zero => simp
  | add a b ha hb iha ihb => simpa only [lie_add] using
      (loweringSpan H φ θ e).add_mem iha ihb
  | smul c z hz ih => simpa only [lie_smul] using
      (loweringSpan H φ θ e).smul_mem c ih

/-- A root operator is positive, negative, Cartan, or zero. -/
private lemma root_action_mem [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H))
    (hφ : ∀ α ∈ rootSet H, φ α ≠ 0) (W : Submodule ℂ L) (z : L)
    (hcartan : ∀ h : H, ⁅(h : L), z⁆ ∈ W)
    (hpos : ∀ α ∈ positiveRoots H φ, ∀ x ∈ rootSpace H α, ⁅x, z⁆ ∈ W)
    (hneg : ∀ α ∈ rootSet H, φ α < 0 → ∀ x ∈ rootSpace H α, ⁅x, z⁆ ∈ W)
    (α : Module.Dual ℂ H) (x : L) (hx : x ∈ rootSpace H α) : ⁅x, z⁆ ∈ W := by
  by_cases hα : α = 0
  · subst α
    rw [rootSpace_zero hss H hH] at hx
    exact hcartan ⟨x, hx⟩
  by_cases ha : α ∈ rootSet H
  · rcases lt_or_gt_of_ne (hφ α ha) with hn | hp
    · exact hneg α ha hn x hx
    · exact hpos α ⟨ha, hp⟩ x hx
  · rw [rootSpace_eq_bot_of_not_mem H α hα ha] at hx
    have hx0 : x = 0 := hx
    simp only [hx0, zero_lie]
    exact W.zero_mem

private lemma loweringSpan_positive [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H))
    (hφ : ∀ α ∈ rootSet H, φ α ≠ 0)
    (θ : Module.Dual ℂ H) (e : L) (he : e ∈ rootSpace H θ)
    (hkill : ∀ α ∈ positiveRoots H φ, ∀ x ∈ rootSpace H α, ⁅x, e⁆ = 0)
    {γ : Module.Dual ℂ H} {z : L} (hz : Lowered H φ θ e γ z) :
    ∀ α ∈ positiveRoots H φ, ∀ x ∈ rootSpace H α,
      ⁅x, z⁆ ∈ loweringSpan H φ θ e := by
  induction hz with
  | base =>
    intro α hα x hx
    rw [hkill α hα x hx]
    exact (loweringSpan H φ θ e).zero_mem
  | @step β γ y z hβ hn hy hz ih =>
    intro α hα x hx
    have hfirst : ⁅⁅x, y⁆, z⁆ ∈ loweringSpan H φ θ e :=
      root_action_mem hss H hH φ hφ (loweringSpan H φ θ e) z
        (fun h => loweringSpan_cartan H φ θ e he h (lowered_mem H φ θ e hz))
        ih
        (fun δ hδ hδneg w hw => loweringSpan_negative H φ θ e hδ hδneg hw
          (lowered_mem H φ θ e hz))
        (α + β) ⁅x, y⁆ (rootSpace_bracket H α β x y hx hy)
    rw [leibniz_lie]
    exact (loweringSpan H φ θ e).add_mem hfirst
      (loweringSpan_negative H φ θ e hβ hn hy (ih α hα x hx))

private lemma loweringSpan_isIdeal [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H))
    (hφ : ∀ α ∈ rootSet H, φ α ≠ 0)
    (θ : Module.Dual ℂ H) (e : L) (he : e ∈ rootSpace H θ)
    (hkill : ∀ α ∈ positiveRoots H φ, ∀ x ∈ rootSpace H α, ⁅x, e⁆ = 0) :
    ∀ x z : L, z ∈ loweringSpan H φ θ e → ⁅x, z⁆ ∈ loweringSpan H φ θ e := by
  intro x z hz
  have hpos : ∀ α ∈ positiveRoots H φ, ∀ y ∈ rootSpace H α,
      ⁅y, z⁆ ∈ loweringSpan H φ θ e := by
    intro α hα y hy
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨γ, hz⟩ := hz
      exact loweringSpan_positive hss H hH φ hφ θ e he hkill hz α hα y hy
    | zero => simp
    | add a b ha hb iha ihb => simpa only [lie_add] using
        (loweringSpan H φ θ e).add_mem iha ihb
    | smul c z hz ih => simpa only [lie_smul] using
        (loweringSpan H φ θ e).smul_mem c ih
  have hx : x ∈ ⨆ α : Module.Dual ℂ H, rootSpace H α := by
    rw [iSup_rootSpace_eq_top H hH.1]; trivial
  refine Submodule.iSup_induction (rootSpace H) (motive := fun x =>
    ⁅x, z⁆ ∈ loweringSpan H φ θ e) hx (fun α x hx => ?_) ?_ ?_
  · exact root_action_mem hss H hH φ hφ _ z
      (fun h => loweringSpan_cartan H φ θ e he h hz) hpos
      (fun δ hδ hn y hy => loweringSpan_negative H φ θ e hδ hn hy hz) α x hx
  · simp
  · intro x y hx hy
    simpa only [add_lie] using (loweringSpan H φ θ e).add_mem hx hy

private lemma neg_mem_rootSet [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) : -α ∈ rootSet H := by
  refine ⟨neg_ne_zero.mpr hα.1, ?_⟩
  intro hbot
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  refine hx0 (congrArg Subtype.val ((rootPairing_perfect hss H hH α).separatingLeft
    ⟨x, hx⟩ ?_))
  intro y
  have hy : (y : L) = 0 := (rootSpace H (-α)).eq_bot_iff.mp hbot y y.property
  have hy' : y = 0 := Subtype.ext hy
  rw [hy', map_zero]

private lemma lowered_order [FiniteDimensional ℂ L] (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L)
    {γ : Module.Dual ℂ H} {z : L} (hz : Lowered H φ θ e γ z) :
    θ - γ ∈ positiveRootMonoid H φ := by
  induction hz with
  | base => rw [sub_self]; exact (positiveRootMonoid H φ).zero_mem
  | @step α γ x z hα hn hx hz ih =>
    have hneg : -α ∈ positiveRootMonoid H φ := positive_mem_monoid H hH.1 φ
      ⟨neg_mem_rootSet hss H hH hα, by simpa using neg_pos.mpr hn⟩
    convert (positiveRootMonoid H φ).add_mem ih hneg using 1
    abel

private lemma loweringSpan_eq_top [FiniteDimensional ℂ L] [LieAlgebra.IsSimple ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (hφ : ∀ α ∈ rootSet H, φ α ≠ 0)
    (θ : Module.Dual ℂ H) (e : L) (he : e ∈ rootSpace H θ) (he0 : e ≠ 0)
    (hkill : ∀ α ∈ positiveRoots H φ, ∀ x ∈ rootSpace H α, ⁅x, e⁆ = 0) :
    loweringSpan H φ θ e = ⊤ := by
  let I : LieIdeal ℂ L :=
    { loweringSpan H φ θ e with
      lie_mem := fun {x z} hz => loweringSpan_isIdeal hss H hH φ hφ θ e he hkill x z hz }
  have hI : I ≠ ⊥ := by
    intro hbot
    have hem : e ∈ I := lowered_mem H φ θ e Lowered.base
    rw [hbot] at hem
    exact he0 hem
  have htop := (LieAlgebra.IsSimple.eq_bot_or_eq_top I).resolve_left hI
  exact congrArg LieSubmodule.toSubmodule htop

private lemma root_below_of_loweringSpan_eq_top [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (θ : Module.Dual ℂ H) (e : L)
    (he : e ∈ rootSpace H θ) (htop : loweringSpan H φ θ e = ⊤)
    {β : Module.Dual ℂ H} (hβ : β ∈ rootSet H) : θ - β ∈ positiveRootMonoid H φ := by
  let S : Set (Module.Dual ℂ H) := {γ | θ - γ ∈ positiveRootMonoid H φ}
  have hle : loweringSpan H φ θ e ≤ ⨆ γ ∈ S, rootSpace H γ := by
    apply Submodule.span_le.mpr
    rintro z ⟨γ, hz⟩
    have hinc : rootSpace H γ ≤ ⨆ δ ∈ S, rootSpace H δ :=
      le_iSup_of_le γ (le_iSup_of_le
        (show γ ∈ S from lowered_order hss H hH φ θ e hz) le_rfl)
    exact hinc (lowered_weight H φ θ e he hz)
  by_contra hn
  have hd := (rootSpace_independent H hH.1).disjoint_biSup (x := β) (y := S) hn
  apply hβ.2
  apply hd.eq_bot_of_le
  rw [htop] at hle
  exact le_trans le_top hle

private lemma rootSet_nonempty [FiniteDimensional ℂ L] [LieAlgebra.IsSimple ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) :
    (rootSet H).Nonempty := by
  by_contra hn
  have hle : (⊤ : Submodule ℂ L) ≤ H.toSubmodule := by
    rw [← iSup_rootSpace_eq_top H hH.1]
    refine iSup_le fun α => ?_
    by_cases hα : α = 0
    · subst α
      rw [rootSpace_zero hss H hH]
    · rw [rootSpace_eq_bot_of_not_mem H α hα (fun ha => hn ⟨α, ha⟩)]
      exact bot_le
  apply LieAlgebra.IsSimple.non_abelian (R := ℂ) (L := L)
  let : IsLieAbelian H := hH.1.1
  constructor
  intro x y
  have hx : x ∈ H := hle (Submodule.mem_top)
  have hy : y ∈ H := hle (Submodule.mem_top)
  exact congrArg Subtype.val (trivial_lie_zero H H ⟨x, hx⟩ ⟨y, hy⟩)

private lemma positiveRoots_nonempty [FiniteDimensional ℂ L] [LieAlgebra.IsSimple ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (φ : Module.Dual ℝ (Module.Dual ℂ H)) (hφ : ∀ α ∈ rootSet H, φ α ≠ 0) :
    (positiveRoots H φ).Nonempty := by
  obtain ⟨α, hα⟩ := rootSet_nonempty hss H hH
  rcases lt_or_gt_of_ne (hφ α hα) with hn | hp
  · exact ⟨-α, neg_mem_rootSet hss H hH hα, by simpa using neg_pos.mpr hn⟩
  · exact ⟨α, hα, hp⟩

/-- A nonzero complex simple Lie algebra has a greatest root for the
simple-root order of the chosen positive system. -/
theorem highest_root :
    Specs.LieAlgebrasAndRepresentations.HighestRoot.highest_root_type.{u} := by
  intro L _ _ _ _ _ H hH φ hφ
  have hss : IsSemisimple ℂ L := LieAlgebra.radical_eq_bot
  obtain ⟨θ, hθ⟩ := ((rootSet_finite H hH.1).subset
    (show positiveRoots H φ ⊆ rootSet H from fun _ h => h.1)).exists_maximalFor
      φ (positiveRoots H φ) (positiveRoots_nonempty hss H hH φ hφ)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hθ.prop.1.2
  have hkill : ∀ α ∈ positiveRoots H φ, ∀ x ∈ rootSpace H α, ⁅x, e⁆ = 0 := by
    intro α hα x hx
    have hsum : 0 < φ (α + θ) := by
      rw [map_add]; exact add_pos hα.2 hθ.prop.2
    have hnroot : α + θ ∉ rootSet H := by
      intro hr
      have hmax := hθ.le_of_le (show α + θ ∈ positiveRoots H φ from ⟨hr, hsum⟩)
        (show φ θ ≤ φ (α + θ) by rw [map_add]; linarith [hα.2])
      rw [map_add] at hmax
      linarith [hα.2]
    have hnzero : α + θ ≠ 0 := by
      intro hz; rw [hz, map_zero] at hsum; exact lt_irrefl 0 hsum
    have hb := rootSpace_bracket H α θ x e hx he
    rw [rootSpace_eq_bot_of_not_mem H (α + θ) hnzero hnroot] at hb
    exact hb
  have htop := loweringSpan_eq_top hss H hH φ hφ θ e he he0 hkill
  have hgreat : ∀ β ∈ rootSet H, θ - β ∈ positiveRootMonoid H φ :=
    fun β hβ => root_below_of_loweringSpan_eq_top hss H hH φ θ e he htop hβ
  refine ⟨θ, ⟨hθ.prop, hgreat⟩, ?_⟩
  intro η hη
  exact monoid_antisymm H φ (hη.2 θ hθ.prop.1) (hgreat η hη.1.1)

/-- Transfer the highest root and its order to the chosen real root space. -/
theorem highest_root_regular_vector :
    Specs.LieAlgebrasAndRepresentations.HighestRoot.highest_root_regular_vector_type.{u,v} := by
  intro L _ _ _ _ _ H hH E _ _ j hj hR R w hw
  let φ : Module.Dual ℝ (Module.Dual ℂ H) := (innerₗ E w).comp j.leftInverse
  have hφj (a : E) : φ (j a) = inner ℝ w a := by
    change inner ℝ w (j.leftInverse (j a)) = _
    rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hj)]
  have hφ (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) : φ α ≠ 0 := by
    obtain ⟨a, rfl⟩ := hR hα
    rw [hφj]
    exact hw a hα
  have hpos (a : E) : j a ∈ positiveRoots H φ ↔
      a ∈ LieAlgebrasAndRepresentations.positiveRoots R w := by
    change (j a ∈ rootSet H ∧ 0 < φ (j a)) ↔ (j a ∈ rootSet H ∧ 0 < inner ℝ w a)
    rw [hφj]
  have hsimple : j '' LieAlgebrasAndRepresentations.simpleRoots R w = simpleRoots H φ := by
    ext α
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(hpos a).2 ha.1, ?_⟩
      intro β hβ γ hγ heq
      obtain ⟨b, rfl⟩ := hR hβ.1
      obtain ⟨c, rfl⟩ := hR hγ.1
      apply ha.2 b ((hpos b).1 hβ) c ((hpos c).1 hγ)
      exact hj (by simpa only [map_add] using heq)
    · intro hα
      obtain ⟨a, rfl⟩ := hR hα.1.1
      refine ⟨a, ⟨(hpos a).1 hα.1, ?_⟩, rfl⟩
      intro b hb c hc heq
      exact hα.2 (j b) ((hpos b).2 hb) (j c) ((hpos c).2 hc) (by rw [heq, map_add])
  have horder (a b : E) : j a - j b ∈ positiveRootMonoid H φ ↔
      a - b ∈ AddSubmonoid.closure (LieAlgebrasAndRepresentations.simpleRoots R w) := by
    rw [← map_sub]
    unfold positiveRootMonoid
    rw [← hsimple, ← AddMonoidHom.map_mclosure j]
    exact AddSubmonoid.mem_map_iff_mem (f := j) hj
  obtain ⟨θ, hθ, huniq⟩ := highest_root H hH φ hφ
  obtain ⟨t, rfl⟩ := hR hθ.1.1
  refine ⟨t, ⟨(hpos t).1 hθ.1, fun b hb => (horder t b).1 (hθ.2 (j b) hb)⟩, ?_⟩
  intro a ha
  apply hj (huniq (j a) ⟨(hpos a).2 ha.1, ?_⟩)
  intro β hβ
  obtain ⟨b, rfl⟩ := hR hβ
  exact (horder a b).2 (ha.2 b hβ)

end LieAlgebrasAndRepresentations.HighestRoot
