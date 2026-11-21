import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Foundations

universe u v w x
noncomputable section
namespace FiniteCombinatorics.Graph.Coloring

abbrev ProperColoring : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.ProperColoringType :=
  fun {_} _ G α => G.Coloring α
abbrev KColoring : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.KColoringType :=
  fun {_} _ G k => G.Coloring (Fin k)
/-- The least natural number of colors, attained because the vertex set is finite. -/
def chromaticNumber : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumberType :=
  fun {_} _ G => sInf {k : ℕ | Nonempty (G.Coloring (Fin k))}
/-- Relabel an arbitrary palette by a bijection. -/
def recolor : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.recolorType :=
  fun {_} _ G {_} {_} e => G.recolorOfEquiv e
/-- Relabel vertices by a graph isomorphism; the coloring uses its inverse. -/
def transport : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.transportType :=
  fun {_} {_} _ _ {_} {_} e α => SimpleGraph.coloringCongr e (Equiv.refl α)

theorem coloring_valid : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.coloring_validType := by
  intro V _ G α c a b h
  exact c.valid h

theorem coloring_from_function : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.coloring_from_functionType := by
  intro V _ G α f h
  exact ⟨SimpleGraph.Coloring.mk f (fun {a b} => h a b), fun _ => rfl⟩

theorem kcoloring_iff : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.kcoloring_iffType := by
  intro V _ G k
  constructor
  · rintro ⟨c⟩
    exact ⟨c, fun _ _ => c.valid⟩
  · rintro ⟨f, h⟩
    exact ⟨SimpleGraph.Coloring.mk f (fun {a b} => h a b)⟩

theorem distinct_coloring : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.distinct_coloringType := by
  intro V _ G
  let := Fintype.ofFinite V
  let e : V ≃ Fin (Nat.card V) := Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)
  exact ⟨SimpleGraph.Coloring.mk e (fun h => e.injective.ne h.ne), e.injective⟩

theorem coloring_exists : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.coloring_existsType := by
  intro V _ G
  obtain ⟨c, _⟩ := distinct_coloring G
  exact ⟨Nat.card V, ⟨c⟩⟩

theorem chromaticNumber_minimum : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_minimumType := by
  intro V _ G
  have hne : {k : ℕ | Nonempty (G.Coloring (Fin k))}.Nonempty := coloring_exists G
  exact ⟨Nat.sInf_mem hne, fun k hk => csInf_le (OrderBot.bddBelow _) hk⟩

theorem chromaticNumber_eq_mathlib : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_eq_mathlibType := by
  intro V _ G
  obtain ⟨k, hk⟩ := coloring_exists G
  exact (SimpleGraph.Colorable.chromaticNumber_eq_sInf hk).symm

theorem chromaticNumber_eq_toNat : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_eq_toNatType := by
  intro V _ G
  rw [← chromaticNumber_eq_mathlib G]
  simp

theorem chromaticNumber_eq_zero_iff : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_eq_zero_iffType := by
  intro V _ G
  have h := SimpleGraph.chromaticNumber_eq_zero_iff (G := G)
  rw [← chromaticNumber_eq_mathlib G] at h
  simpa using h

theorem chromaticNumber_eq_one_iff : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_eq_one_iffType := by
  intro V _ G
  have h := SimpleGraph.chromaticNumber_eq_one_iff (G := G)
  rw [← chromaticNumber_eq_mathlib G] at h
  simpa using h

theorem chromaticNumber_edgeless : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_edgelessType := by
  intro V _ _
  exact (chromaticNumber_eq_one_iff (⊥ : SimpleGraph V)).mpr ⟨rfl, inferInstance⟩

theorem recolor_apply : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.recolor_applyType := by
  intro V _ G α β e c a
  rfl

theorem transport_apply : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.transport_applyType := by
  intro V W _ _ G H e α c b
  rfl

theorem colorable_iso_iff : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.colorable_iso_iffType := by
  intro V W _ _ G H e k
  exact SimpleGraph.colorable_congr e

theorem chromaticNumber_iso : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.chromaticNumber_isoType := by
  intro V W _ _ G H e
  apply ENat.natCast_inj.mp
  rw [chromaticNumber_eq_mathlib G, chromaticNumber_eq_mathlib H]
  exact SimpleGraph.chromaticNumber_congr e

theorem colorable_relabel_iff : Specs.FiniteCombinatorics.Graph.Coloring.Foundations.colorable_relabel_iffType := by
  intro V _ G α β e
  exact ⟨fun ⟨c⟩ => ⟨G.recolorOfEquiv e c⟩, fun ⟨c⟩ => ⟨G.recolorOfEquiv e.symm c⟩⟩

end FiniteCombinatorics.Graph.Coloring
