import MathGenome.Internal.D07.Ch01.AutomorphismGroups
import MathGenome.Internal.D07.Ch05.ActionDefinition
import MathGenome.Internal.Specs.D07.Ch05.ConjugationAction

/-!
The conjugation action, `K07.05.conjugation_action` (paper.tex:874–876).
The action uses the previously constructed conjugation automorphisms.
No global instance replaces the usual left multiplication action on `G`.
-/

namespace D07.Ch05.ConjugationAction

universe u

/-- The group acts on its underlying set by its conjugation automorphisms. -/
@[instance_reducible]
def conjugationAction (G : Type u) [Group G] : MulAction G G where
  smul g x := Ch01.AutomorphismGroups.conjugation G g x
  one_smul x := by
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  mul_smul g h x := by
    change (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹
    simp [mul_assoc]

theorem conjugation_formula (G : Type u) [Group G] (g x : G) :
    (conjugationAction G).smul g x = g * x * g⁻¹ :=
  Ch01.AutomorphismGroups.conjugation_formula G g x

theorem conjugation_laws (G : Type u) [Group G] :
    ActionDefinition.actionAxioms G G (conjugationAction G).smul :=
  ⟨(conjugationAction G).one_smul, (conjugationAction G).mul_smul⟩

theorem orbit_carrier (G : Type u) [Group G] (x : G) :
    @MulAction.orbit G G (conjugationAction G).toSMul x = {y : G | ∃ g : G, g * x * g⁻¹ = y} := by
  rfl

theorem orbit_eq_conjugacy_class (G : Type u) [Group G] (x : G) :
    @MulAction.orbit G G (conjugationAction G).toSMul x = (ConjClasses.mk x).carrier := by
  ext y
  change (∃ g : G, g * x * g⁻¹ = y) ↔ IsConj x y
  exact isConj_iff.symm

theorem stabilizer_carrier (G : Type u) [Group G] (x : G) :
    letI : MulAction G G := conjugationAction G
    (MulAction.stabilizer G x : Set G) = {g : G | g * x = x * g} := by
  ext g
  change g * x * g⁻¹ = x ↔ g * x = x * g
  exact mul_inv_eq_iff_eq_mul

theorem stabilizer_eq_centralizer (G : Type u) [Group G] (x : G) :
    letI : MulAction G G := conjugationAction G
    MulAction.stabilizer G x = Subgroup.centralizer {x} := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  change g * x * g⁻¹ = x ↔ g * x = x * g
  exact mul_inv_eq_iff_eq_mul

theorem fixed_points_carrier (G : Type u) [Group G] :
    letI : MulAction G G := conjugationAction G
    MulAction.fixedPoints G G = {x : G | ∀ g : G, g * x = x * g} := by
  ext x
  change (∀ g : G, g * x * g⁻¹ = x) ↔ ∀ g : G, g * x = x * g
  exact forall_congr' fun _ => mul_inv_eq_iff_eq_mul

theorem fixed_points_eq_center (G : Type u) [Group G] :
    letI : MulAction G G := conjugationAction G
    MulAction.fixedPoints G G = (Subgroup.center G : Set G) := by
  ext x
  change (∀ g : G, g * x * g⁻¹ = x) ↔ x ∈ Subgroup.center G
  rw [Subgroup.mem_center_iff]
  exact forall_congr' fun _ => mul_inv_eq_iff_eq_mul

end D07.Ch05.ConjugationAction
