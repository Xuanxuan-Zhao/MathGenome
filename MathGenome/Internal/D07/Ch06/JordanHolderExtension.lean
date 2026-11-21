import MathGenome.Internal.Specs.D07.Ch06.JordanHolderExtension
import MathGenome.Internal.D07.Ch06.JordanHolderExtensionCompositionExistence
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.JordanHolder

/-!
Jordan–Hölder for the shared subgroup-chain representation.
We equip the subgroup lattice locally with maximal-normal steps. The
second isomorphism theorem supplies its diamond axiom and identifies
Mathlib's interval equivalence with actual quotient-group isomorphism.
-/
namespace D07.Ch06.JordanHolderExtension

open Specs.D07.Ch06.CompositionSeriesDefinition
universe u
variable {G : Type u} [Group G]

/-- A step is proper, normal in its successor, with simple quotient. -/
def SimpleStep (A B : Subgroup G) : Prop :=
  A < B ∧ ∃ hn : (A.subgroupOf B).Normal,
    let _ := hn
    IsSimpleGroup (B ⧸ A.subgroupOf B)

/-- Restriction of relative normality to a smaller overgroup. -/
theorem normal_restrict {N H K : Subgroup G} [(N.subgroupOf K).Normal]
    (hHK : H ≤ K) : (N.subgroupOf H).Normal := by
  have h := (inferInstance : (N.subgroupOf K).Normal).comap (Subgroup.inclusion hHK)
  simpa only [Subgroup.comap_inclusion_subgroupOf] using h

/-- Correspondence: a simple quotient has no intermediate normal subgroup. -/
theorem normal_intermediate {A B K : Subgroup G} (h : SimpleStep A B)
    (hAK : A ≤ K) (hKB : K ≤ B) [(K.subgroupOf B).Normal] :
    K = A ∨ K = B := by
  let _ := h.2.choose
  let _ := h.2.choose_spec
  let π := QuotientGroup.mk' (A.subgroupOf B)
  let M := (K.subgroupOf B).map π
  have : M.Normal := (inferInstance : (K.subgroupOf B).Normal).map π
    (QuotientGroup.mk'_surjective _)
  have hAM : A.subgroupOf B ≤ K.subgroupOf B := Subgroup.comap_mono hAK
  have hback : M.comap π = K.subgroupOf B :=
    D07.Ch04.CorrespondenceTheorem.inverse_image_image B _ _ hAM
  rcases Subgroup.Normal.eq_bot_or_eq_top M with hb | ht
  · left
    have heq : K.subgroupOf B = A.subgroupOf B := by
      rw [← hback, hb, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    have := congrArg (Subgroup.map B.subtype) heq
    simpa only [Subgroup.map_subgroupOf_eq_of_le hKB,
      Subgroup.map_subgroupOf_eq_of_le h.1.le] using this
  · right
    have heq : K.subgroupOf B = ⊤ := by rw [← hback, ht, Subgroup.comap_top]
    exact le_antisymm hKB (Subgroup.subgroupOf_eq_top.mp heq)

/-- Distinct maximal normal predecessors generate the whole successor. -/
theorem sup_eq_of_simpleSteps {A B C : Subgroup G} (hA : SimpleStep A C)
    (hB : SimpleStep B C) (hne : A ≠ B) : A ⊔ B = C := by
  let _ := hA.2.choose
  let _ := hB.2.choose
  have : ((A ⊔ B).subgroupOf C).Normal := by
    rw [Subgroup.subgroupOf_sup hA.1.le hB.1.le]
    infer_instance
  rcases normal_intermediate hA le_sup_left (sup_le hA.1.le hB.1.le) with heq | heq
  · have hBA : B ≤ A := heq ▸ le_sup_right
    rcases normal_intermediate hB hBA hA.1.le with h | h
    · exact (hne h).elim
    · exact (ne_of_lt hA.1 h).elim
  · exact heq

/-- The second isomorphism theorem with normality only in the join. -/
noncomputable def secondIso (A B : Subgroup G)
    [(A.subgroupOf (A ⊔ B)).Normal] [((A ⊓ B).subgroupOf B).Normal] :
    (A ⊔ B : Subgroup G) ⧸ A.subgroupOf (A ⊔ B) ≃*
      B ⧸ (A ⊓ B).subgroupOf B := by
  have hLE : B ≤ Subgroup.normalizer A := le_sup_right.trans
    (Subgroup.le_normalizer_of_normal_subgroupOf le_sup_left)
  let _ := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  let _ := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  exact ((QuotientGroup.equivQuotientSubgroupOfOfEq (A' := A) rfl (sup_comm B A)).symm.trans
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hLE).symm).trans
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.inf_subgroupOf_right A B).symm)

/-- The two simple quotients in a normal diamond are exchanged. -/
theorem simpleStep_inf {A B : Subgroup G}
    (_hA : SimpleStep A (A ⊔ B)) (hB : SimpleStep B (A ⊔ B)) :
    SimpleStep (A ⊓ B) A := by
  have hB' : SimpleStep B (B ⊔ A) := by rw [sup_comm]; exact hB
  let _ := hB.2.choose
  let _ := hB'.2.choose
  let _ := hB'.2.choose_spec
  have : ((B ⊓ A).subgroupOf A).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact normal_restrict (K := A ⊔ B) le_sup_left
  have hn : ((A ⊓ B).subgroupOf A).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact normal_restrict (K := A ⊔ B) le_sup_left
  let _ := hn
  let e := (secondIso B A).trans (QuotientGroup.quotientMulEquivOfEq
    (congrArg (fun H : Subgroup G => H.subgroupOf A) (inf_comm B A)))
  have := e.symm.isSimpleGroup
  refine ⟨lt_of_le_of_ne inf_le_left ?_, hn, inferInstance⟩
  intro heq
  have ht : (A ⊓ B).subgroupOf A = ⊤ :=
    Subgroup.subgroupOf_eq_top.mpr (by rw [heq])
  exact (QuotientGroup.nontrivial_iff.mp inferInstance) ht

/-- The abstract Jordan–Hölder interface, with maximal NORMAL steps. -/
@[instance_reducible] def subgroupJordanHolderLattice : JordanHolderLattice (Subgroup G) where
  IsMaximal := SimpleStep
  lt_of_isMaximal := And.left
  sup_eq_of_isMaximal := sup_eq_of_simpleSteps
  isMaximal_inf_left_of_isMaximal_sup := simpleStep_inf

attribute [local instance] subgroupJordanHolderLattice

/-- View the shared concrete series as an abstract maximal-normal chain. -/
def toAbstract (s : Series G) : _root_.CompositionSeries (Subgroup G) where
  length := s.length
  toFun := s.term
  step i := ⟨s.strictMono Fin.castSucc_lt_succ, s.normal i, s.simple i⟩

/-- Actual quotient-group isomorphism, allowing arbitrary normality witnesses. -/
def QuotientIso (x y : Subgroup G × Subgroup G) : Prop :=
  ((x.1.subgroupOf x.2).Normal ↔ (y.1.subgroupOf y.2).Normal) ∧
  ∀ (hx : (x.1.subgroupOf x.2).Normal) (hy : (y.1.subgroupOf y.2).Normal),
    let _ := hx
    let _ := hy
    Nonempty (x.2 ⧸ x.1.subgroupOf x.2 ≃* y.2 ⧸ y.1.subgroupOf y.2)

/-- Each generator of the abstract interval relation is a second-isomorphism map. -/
theorem quotientIso_second {A B : Subgroup G}
    (h : JordanHolderLattice.IsMaximal A (A ⊔ B)) :
    QuotientIso (A, A ⊔ B) (A ⊓ B, B) := by
  have hn : (A.subgroupOf (A ⊔ B)).Normal := h.2.choose
  let _ := hn
  have hm : ((A ⊓ B).subgroupOf B).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact normal_restrict (K := A ⊔ B) le_sup_right
  refine ⟨iff_of_true hn hm, ?_⟩
  intro hx hy
  let _ := hx
  let _ := hy
  exact ⟨secondIso A B⟩

/-- The abstract relation entails an isomorphism of the actual quotient groups. -/
theorem quotientIso_of_intervalIso {x y : Subgroup G × Subgroup G}
    (h : JordanHolderLattice.Iso x y) : QuotientIso x y := by
  apply JordanHolderLattice.Iso.rel QuotientIso (h_iso := h)
  · intro x
    exact ⟨Iff.rfl, fun _ _ => ⟨MulEquiv.refl _⟩⟩
  · intro x y h
    refine ⟨h.1.symm, fun hx hy => ?_⟩
    obtain ⟨e⟩ := h.2 hy hx
    exact ⟨e.symm⟩
  · intro x y z hxy hyz
    refine ⟨hxy.1.trans hyz.1, fun hx hz => ?_⟩
    have hy := hxy.1.mp hx
    obtain ⟨e₁⟩ := hxy.2 hx hy
    obtain ⟨e₂⟩ := hyz.2 hy hz
    exact ⟨e₁.trans e₂⟩
  · exact quotientIso_second

/-- Existence, supplied by the independently proved predecessor construction. -/
theorem composition_series_exists (G : Type u) [Group G] [Finite G] :
    Nonempty (Series G) :=
  D07.Ch06.JordanHolderExtensionCompositionExistence.composition_series_exists G

/-- Equal lengths and a bijection pairing all factors by group isomorphisms. -/
theorem jordan_holder (G : Type u) [Group G] [Finite G] (s t : Series G) :
    s.length = t.length ∧
      ∃ e : Fin s.length ≃ Fin t.length,
        ∀ i, Nonempty (factorValue s i ≃* factorValue t (e i)) := by
  have he := _root_.CompositionSeries.jordan_holder (toAbstract s) (toAbstract t)
    (s.first_eq_bot.trans t.first_eq_bot.symm)
    (s.last_eq_top.trans t.last_eq_top.symm)
  refine ⟨_root_.CompositionSeries.Equivalent.length_eq he, he.choose, fun i => ?_⟩
  exact (quotientIso_of_intervalIso (he.choose_spec i)).2 (s.normal i) (t.normal (he.choose i))

end D07.Ch06.JordanHolderExtension
