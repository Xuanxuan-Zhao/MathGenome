import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.CompactDirectMethod
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions

noncomputable section
open Set
universe u
namespace VariationalNotes.Existence

def ProperOn {X : Type u} (J : X → WithTop ℝ) (C : Set X) : Prop :=
  Specs.ProperOn J C

def IsLowerSemicontinuousOn {X : Type u} [TopologicalSpace X]
    (J : X → WithTop ℝ) (C : Set X) : Prop := Specs.IsLowerSemicontinuousOn J C

def CoerciveOn {X : Type u} [NormedAddCommGroup X]
    (J : X → WithTop ℝ) (C : Set X) : Prop := Specs.CoerciveOn J C

def AttainsFiniteMinimum {X : Type u} (J : X → WithTop ℝ) (C : Set X) : Prop :=
  Specs.AttainsFiniteMinimum J C

/-- The real-superlevel convention agrees with native semicontinuity on a set. -/
theorem lowerSemicontinuousOn_iff_native {X : Type u} [TopologicalSpace X]
    (J : X → WithTop ℝ) (C : Set X) :
    IsLowerSemicontinuousOn J C ↔ LowerSemicontinuousOn J C := by
  exact (ConvexAnalysis.lowerSemicontinuous_iff_native (fun x : C => J x)).trans
    lowerSemicontinuous_restrict_iff

private theorem finiteMinimum_of_isMinOn {X : Type u} (J : X → WithTop ℝ)
    (C : Set X) (hp : Specs.ProperOn J C) {x : X} (hx : x ∈ C)
    (hmin : IsMinOn J C x) : Specs.AttainsFiniteMinimum J C := by
  obtain ⟨y, hy⟩ := hp
  have hfinite : J x < ⊤ := (hmin y.property).trans_lt hy
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hfinite)
  refine ⟨x, hx, m, hm.symm, ?_⟩
  constructor
  · rintro z ⟨y, hy, rfl⟩
    rw [hm]
    exact hmin hy
  · intro b hb
    rw [hm]
    exact hb ⟨x, hx, rfl⟩

theorem compact_direct_method : Specs.compact_direct_method.{u} := by
  intro X _ J C hp hc hl
  have hl' : LowerSemicontinuousOn J C :=
    (lowerSemicontinuousOn_iff_native J C).mp hl
  obtain ⟨x, hx, hmin⟩ := hl'.exists_isMinOn (by
    obtain ⟨y, _⟩ := hp
    exact ⟨y, y.property⟩) hc
  exact finiteMinimum_of_isMinOn J C hp hx hmin

theorem compact_sublevel_direct_method : Specs.compact_sublevel_direct_method.{u} := by
  intro X _ J C x₀ hx₀ hfinite hk hl
  let K := {x ∈ C | J x ≤ J x₀}
  have hx₀K : x₀ ∈ K := ⟨hx₀, le_rfl⟩
  have hl' : LowerSemicontinuousOn J K :=
    (lowerSemicontinuousOn_iff_native J K).mp hl
  obtain ⟨x, hx, hmin⟩ := hl'.exists_isMinOn ⟨x₀, hx₀K⟩ hk
  apply finiteMinimum_of_isMinOn J C ⟨⟨x₀, hx₀⟩, hfinite⟩ hx.1
  intro y hy
  by_cases hyK : J y ≤ J x₀
  · exact hmin ⟨hy, hyK⟩
  · exact (hmin hx₀K).trans (le_of_lt (lt_of_not_ge hyK))

theorem finiteDimensional_direct_method : Specs.finiteDimensional_direct_method.{u} := by
  intro X _ _ _ J C hp hc hl hcoercive
  obtain ⟨x₀, hx₀⟩ := hp
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hx₀)
  change (a : WithTop ℝ) = J x₀ at ha
  have hl' : LowerSemicontinuousOn J C :=
    (lowerSemicontinuousOn_iff_native J C).mp hl
  obtain ⟨F, hF, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hl' (J x₀)
  have hclosed : IsClosed {x ∈ C | J x ≤ J x₀} := by
    change IsClosed (C ∩ J ⁻¹' Iic (J x₀))
    rw [heq]
    exact hc.inter hF
  have hbounded : Bornology.IsBounded {x ∈ C | J x ≤ J x₀} := by
    rw [← ha]
    exact hcoercive a
  apply compact_sublevel_direct_method J C x₀ x₀.property hx₀
    (Metric.isCompact_of_isClosed_isBounded hclosed hbounded)
  exact (lowerSemicontinuousOn_iff_native J _).mpr (hl'.mono (fun _ h => h.1))

end VariationalNotes.Existence
