import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.PrincipalBlockDefect
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.DefectGroups
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Modular.PrincipalBlockDefect

open RelativeTrace BrauerHomomorphism
open scoped BigOperators MonoidAlgebra

open private conjugationAction conjugationSMul smul_eq_conj fixedPoints_eq_centralizer
  coeff_conj_of_mem_fixed sum_eq_sum_fixedPoints from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.BrauerHomomorphism

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime] [CharP k p]

private theorem augmentation_projection {P : Subgroup G} (hP : IsPGroup p P)
    (a : fixedSubalgebra k P) :
    augmentation k (Subgroup.centralizer (P : Set G)) (projection k P a) =
      augmentation k G a.val := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (Subgroup.centralizer (P : Set G)) := Fintype.ofFinite _
  let : MulAction P G := conjugationAction P
  let : SMul P G := conjugationSMul P
  let : Fintype (MulAction.fixedPoints P G) := Fintype.ofFinite _
  rw [augmentation_eq_sum, augmentation_eq_sum]
  simp only [coeff_projection]
  symm
  have hinv (g : P) (x : G) : a.val.coeff (g • x) = a.val.coeff x :=
    (congrArg a.val.coeff (smul_eq_conj P g x)).trans
      (coeff_conj_of_mem_fixed k a g x)
  rw [sum_eq_sum_fixedPoints k hP a.val.coeff hinv]
  exact Fintype.sum_equiv (Set.equivOfEq (fixedPoints_eq_centralizer P)) _ _ (fun _ => rfl)

/-- Every Sylow subgroup at the characteristic is a defect group of the principal
block, and every defect group of that block is Sylow. -/
theorem principal_block_defect_iff : PrincipalBlockDefectSpec.principalBlockDefectType.{u, v} := by
  intro k _ G _ _ p _ _ b hprincipal P
  have haug := b.belongsTo_trivial_iff.mp hprincipal
  have hnonzero (Q : Subgroup G) (hQ : IsPGroup p Q) :
      DefectGroupsSpec.brauerImage b Q ≠ 0 := by
    let a : fixedSubalgebra k Q :=
      ⟨b.element, fun g => CentralTraceIdealsSpec.conjugation_center k (g : G) b.val⟩
    have h := (augmentation_projection hQ a).trans haug
    change projection k Q a ≠ 0
    intro hz
    rw [hz, map_zero] at h
    exact zero_ne_one h
  constructor
  · intro hP
    obtain ⟨S, hPS⟩ := hP.1.1.exists_le_sylow
    exact ⟨S, le_antisymm (hP.2 ⟨S.isPGroup', hnonzero S S.isPGroup'⟩ hPS) hPS⟩
  · rintro ⟨S, rfl⟩
    refine ⟨⟨S.isPGroup', hnonzero S S.isPGroup'⟩, ?_⟩
    intro Q hQ hSQ
    exact (S.is_maximal' hQ.1 hSQ).le

end RepTheorySurvey.Modular.PrincipalBlockDefect
