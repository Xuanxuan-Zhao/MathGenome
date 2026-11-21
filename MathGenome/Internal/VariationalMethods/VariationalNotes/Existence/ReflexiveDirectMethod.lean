import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.ReflexiveDirectMethod
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.ReflexiveWeakCompactness
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.CompactDirectMethod
import Mathlib.Topology.Order.IsLUB
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter
open scoped Topology
universe u
namespace VariationalNotes.Existence
open private finiteMinimum_of_isMinOn from MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.CompactDirectMethod

def WeakSequentiallyClosed : Specs.WeakSequentiallyClosedType.{u} :=
  Specs.WeakSequentiallyClosed

def WeakSequentialLowerSemicontinuousOn : Specs.WeakSequentialLowerSemicontinuousOnType.{u} :=
  Specs.WeakSequentialLowerSemicontinuousOn

/-- Minimize inside a finite bounded sublevel, then extract a weakly convergent
subsequence. Only sequential closedness is used at its limit. -/
theorem reflexive_direct_method : Specs.reflexive_direct_method.{u} := by
  intro X _ _ _ hX J C _hne hclosed hp _hbelow hcoercive hlsc
  obtain ⟨x₀, hx₀⟩ := hp
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hx₀)
  let K : Set X := {x ∈ C | J x ≤ (r : WithTop ℝ)}
  have hx₀K : (x₀ : X) ∈ K := ⟨x₀.property, hr.symm.le⟩
  let V : Set EReal := (fun x => ConvexAnalysis.Specs.toEReal (J x)) '' K
  have hV : V.Nonempty := ⟨_, ⟨x₀, hx₀K, rfl⟩⟩
  obtain ⟨v, _hanti, _hbound, hvlim, hvmem⟩ :=
    (isGLB_sInf V).exists_seq_antitone_tendsto hV
  choose a ha hva using hvmem
  have habounded : Bornology.IsBounded (range a) :=
    (hcoercive r).subset (by rintro _ ⟨n, rfl⟩; exact ha n)
  obtain ⟨k, hk, x, hxlim⟩ := reflexive_weak_subsequence X hX a habounded
  have hac : ∀ n, a (k n) ∈ C := fun n => (ha (k n)).1
  have hxc : x ∈ C := hclosed _ x hac hxlim
  have hvsub : Tendsto (fun n => ConvexAnalysis.Specs.toEReal (J (a (k n))))
      atTop (𝓝 (sInf V)) := by
    simpa only [Function.comp_def, hva] using hvlim.comp hk.tendsto_atTop
  have hxinf : ConvexAnalysis.Specs.toEReal (J x) ≤ sInf V := by
    have h := hlsc (fun n => a (k n)) x hac hxc hxlim
    rwa [hvsub.liminf_eq] at h
  have hminK : ∀ y ∈ K, J x ≤ J y := by
    intro y hy
    exact (WithBot.coe_le_coe).mp (hxinf.trans (sInf_le ⟨y, hy, rfl⟩))
  apply finiteMinimum_of_isMinOn J C ⟨x₀, hx₀⟩ hxc
  intro y hy
  by_cases hyK : y ∈ K
  · exact hminK y hyK
  · have hry : (r : WithTop ℝ) < J y := lt_of_not_ge (fun h => hyK ⟨hy, h⟩)
    exact (hminK x₀ hx₀K).trans (hr.symm.le.trans hry.le)

theorem weaklyCompact_sublevel_direct_method :
    Specs.weaklyCompact_sublevel_direct_method.{u} := by
  intro X _ _ J C α hne hk hl
  letI : TopologicalSpace X := Specs.weakTopology X
  let K : Set X := {x ∈ C | J x ≤ (α : WithTop ℝ)}
  obtain ⟨x₀, hx₀⟩ := hne
  have hl' : LowerSemicontinuousOn J K :=
    (lowerSemicontinuousOn_iff_native J K).mp hl
  obtain ⟨x, hx, hmin⟩ := hl'.exists_isMinOn ⟨x₀, hx₀⟩ hk
  apply finiteMinimum_of_isMinOn J C
    ⟨⟨x₀, hx₀.1⟩, hx₀.2.trans_lt (WithTop.coe_lt_top α)⟩ hx.1
  intro y hy
  by_cases hyK : y ∈ K
  · exact hmin hyK
  · exact (hmin hx₀).trans (hx₀.2.trans (le_of_lt
      (lt_of_not_ge (fun h => hyK ⟨hy, h⟩))))

theorem three_forms_direct_method : Specs.three_forms_direct_method.{u} :=
  ⟨compact_direct_method, compact_sublevel_direct_method, finiteDimensional_direct_method,
    reflexive_direct_method, weaklyCompact_sublevel_direct_method⟩

end VariationalNotes.Existence
