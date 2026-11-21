import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.ChainLongExactSequence

/-! Proof of paper.tex, Lemma `lem:p202-chain-les`.

We use the snake-lemma homology sequence in an arbitrary abelian category.
The concrete calculation verifies its sign and identifies it with the source's
boundary-of-a-lift construction. All quantifiers range over arbitrary complexes,
not only free or split complexes.
-/

open CategoryTheory HomologicalComplex
open P202Specs.ChainLES

universe u v w

namespace P202.ChainLES

theorem exactness : ExactnessType.{u,v,w} := by
  intro C _ _ ι shape S h
  let hs := HomologicalComplex.shortExact_of_degreewise_shortExact S h
  exact ⟨fun n => HomologicalComplex.HomologySequence.composableArrows₂_exact hs n,
    fun i j hij => HomologicalComplex.HomologySequence.composableArrows₅_exact hs i j hij⟩

theorem naturality : NaturalityType.{u,v,w} := by
  intro C _ _ ι shape S T φ hS hT
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₁₂]
  · intro n
    rw [← homologyMap_comp, ← homologyMap_comp, φ.comm₂₃]
  · intro i j hij
    exact HomologicalComplex.HomologySequence.δ_naturality φ
      (HomologicalComplex.shortExact_of_degreewise_shortExact S hS)
      (HomologicalComplex.shortExact_of_degreewise_shortExact T hT) i j hij

theorem ordinary_endpoint : OrdinaryEndpointType.{u,v} := by
  intro C _ _ S h
  have := (HomologicalComplex.shortExact_of_degreewise_shortExact S h).epi_g
  exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)

theorem integer_index : IntegerIndexType.{u,v} := by
  intro C _ _ S h n
  exact (exactness S h).2 (n + 1) n (by simp)

theorem natural_index : NaturalIndexType.{u,v} := by
  intro C _ _ S h n
  exact (exactness S h).2 (n + 1) n (by simp)

section Concrete
variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
  [HasForget₂ C Ab.{v}] [Abelian C] [(forget₂ C Ab).Additive]
  [(forget₂ C Ab).PreservesHomology] {ι : Type w} {shape : ComplexShape ι}
  (S : ShortComplex (HomologicalComplex C shape)) (h : DegreewiseShortExact S)

/-- Surjectivity gives a lift; exactness and injectivity give the unique preimage
of its boundary. The chain-map identities make that preimage a cycle. -/
theorem lifts_exist : LiftsExist S h := by
  intro i j hij z hz
  obtain ⟨c, hc⟩ := (h i).surjective_g z
  change (forget₂ C Ab).map (S.g.f i) c = z at hc
  have hboundary : (forget₂ C Ab).map (S.g.f j)
      ((forget₂ C Ab).map (S.X₂.d i j) c) = 0 := by
    rw [← ConcreteCategory.forget₂_comp_apply, ← S.g.comm,
      ConcreteCategory.forget₂_comp_apply, hc, hz]
  obtain ⟨x, hx⟩ := ((S.map (HomologicalComplex.eval C shape j)).exact_iff_of_hasForget.mp
    (h j).exact) _ hboundary
  refine ⟨c, hc, x, ⟨hx, ?_⟩, ?_⟩
  · intro k
    exact (HomologicalComplex.shortExact_of_degreewise_shortExact S h).d_eq_zero_of_f_eq_d_apply i j c x hx k
  · intro y hy
    exact (h j).injective_f (hy.1.trans hx.symm)

/-- This is Mathlib's concrete snake-lemma calculation, with the source's sign. -/
theorem lift_formula : LiftFormula S h := by
  intro i j hij z hz c hc x hx hxcycle
  exact (HomologicalComplex.shortExact_of_degreewise_shortExact S h).δ_apply i j hij z hz c hc x hx (shape.next j) rfl

/-- A formula through an actual homology morphism is independent of every choice. -/
theorem independence : Independence S h := by
  intro i j hij z z' hz hz' heq c c' hc hc' x x' hx hx' hxc hxc'
  rw [← lift_formula S h i j hij z hz c hc x hx hxc,
    ← lift_formula S h i j hij z' hz' c' hc' x' hx' hxc', heq]

end Concrete

theorem module_lift {R : Type u} [Ring R] {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape))
    (h : DegreewiseShortExact S) : LiftsExist S h ∧ LiftFormula S h ∧ Independence S h := by
  exact ⟨lifts_exist S h, lift_formula S h, independence S h⟩

theorem abelian_group_lift {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex Ab.{v} shape))
    (h : DegreewiseShortExact S) : LiftsExist S h ∧ LiftFormula S h ∧ Independence S h := by
  exact ⟨lifts_exist S h, lift_formula S h, independence S h⟩

theorem module_hypothesis {R : Type u} [Ring R] {ι : Type w} {shape : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) shape)) :
    DegreewiseShortExact S ↔ ∀ n,
      Function.Injective (S.f.f n) ∧
      (∀ y, S.g.f n y = 0 → ∃ x, S.f.f n x = y) ∧
      Function.Surjective (S.g.f n) := by
  constructor
  · intro h n
    exact ⟨(h n).moduleCat_injective_f,
      (ShortComplex.moduleCat_exact_iff _).mp (h n).exact,
      (h n).moduleCat_surjective_g⟩
  · intro h n
    exact {
      mono_f := (ModuleCat.mono_iff_injective _).mpr (h n).1
      exact := (ShortComplex.moduleCat_exact_iff _).mpr (h n).2.1
      epi_g := (ModuleCat.epi_iff_surjective _).mpr (h n).2.2 }

end P202.ChainLES
