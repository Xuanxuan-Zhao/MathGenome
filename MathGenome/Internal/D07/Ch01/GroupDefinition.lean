import MathGenome.Internal.Specs.D07.Ch01.GroupDefinition

/-!
# Groups and abelian groups

Formalization of `K07.01.group_definition`. A carrier is an arbitrary type
(equivalently, an underlying set); its multiplication has values in that same
type. No finiteness, commutativity, or nontriviality is required of a group.
-/

namespace D07.Ch01.GroupDefinition

universe u

/-- The canonical multiplicative group structure on a carrier. -/
abbrev GroupStructure (G : Type u) : Type u := Group G

/-- An abelian group is a group with commutative multiplication. -/
abbrev AbelianGroupStructure (G : Type u) : Type u := CommGroup G

/-- The five laws displayed in the source, for the specified operations. -/
def groupAxioms (G : Type u) (mul : G → G → G) (one : G) (inv : G → G) : Prop :=
  (∀ x y z : G, mul (mul x y) z = mul x (mul y z)) ∧
  (∀ x : G, mul one x = x) ∧
  (∀ x : G, mul x one = x) ∧
  (∀ x : G, mul x (inv x) = one) ∧
  (∀ x : G, mul (inv x) x = one)

/-- Abelian is a property of an existing group, rather than an implicit
requirement in the definition of a group. -/
def IsAbelian (G : Type u) [Group G] : Prop := ∀ x y : G, x * y = y * x

theorem group_laws (G : Type u) [Group G] :
    groupAxioms G (· * ·) 1 Inv.inv :=
  ⟨mul_assoc, one_mul, mul_one, mul_inv_cancel, inv_mul_cancel⟩

theorem axioms_realized (G : Type u) (mul : G → G → G) (one : G) (inv : G → G)
    (h : groupAxioms G mul one inv) :
    ∃ g : Group G, g.mul = mul ∧ g.one = one ∧ g.inv = inv := by
  let g : Group G := {
    mul := mul
    one := one
    inv := inv
    mul_assoc := h.1
    one_mul := h.2.1
    mul_one := h.2.2.1
    inv_mul_cancel := h.2.2.2.2
  }
  exact ⟨g, rfl, rfl, rfl⟩

theorem abelian_iff_commGroup (G : Type u) (g : Group G) :
    @IsAbelian G g ↔ ∃ c : CommGroup G, c.toGroup = g := by
  constructor
  · intro h
    exact ⟨{ g with mul_comm := h }, rfl⟩
  · intro h
    cases h with
    | intro c hc =>
      cases hc
      exact c.mul_comm

theorem group_nonempty (G : Type u) [Group G] : Nonempty G := ⟨1⟩

theorem empty_has_no_group (G : Type u) (h : IsEmpty G) : ¬ Nonempty (Group G) := by
  intro hg
  exact hg.elim (fun g => h.false g.one)

theorem trivial_group_allowed :
    Nonempty (CommGroup PUnit.{u + 1}) ∧ (∀ x y : PUnit.{u + 1}, x = y) :=
  ⟨⟨inferInstance⟩, fun _ _ => Subsingleton.elim _ _⟩

end D07.Ch01.GroupDefinition
