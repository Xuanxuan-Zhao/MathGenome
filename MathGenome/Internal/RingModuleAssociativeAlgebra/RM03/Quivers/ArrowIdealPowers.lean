import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Quivers.Relations
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Quivers.ArrowIdealPowers
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-! Powers of the arrow ideal are spanned by paths subject to a lower length bound. -/

universe u v w

namespace RM03.PathAlgebra

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

private noncomputable def lengthSpan (m : ℕ) : Submodule k (PathAlgebra k Q) :=
  Submodule.span k (ofPath k '' {p : Path Q | m ≤ p.length})

private theorem ofPath_mem_lengthSpan {m : ℕ} {p : Path Q} (hp : m ≤ p.length) :
    ofPath k p ∈ lengthSpan m :=
  Submodule.subset_span ⟨p, hp, rfl⟩

private theorem lengthSpan_zero : lengthSpan (k := k) (Q := Q) 0 = ⊤ := by
  have hall : {p : Path Q | 0 ≤ p.length} = Set.univ := by ext; simp
  have hb : ⇑(basis k Q) = ofPath k := funext basis_apply
  rw [lengthSpan, hall, Set.image_univ, ← hb, (basis k Q).span_eq]

private theorem mul_mem_lengthSpan {m n : ℕ} {x y : PathAlgebra k Q}
    (hx : x ∈ lengthSpan m) (hy : y ∈ lengthSpan n) : x * y ∈ lengthSpan (m + n) := by
  classical
  have h : Submodule.map₂ (mulBilinear k Q) (lengthSpan m) (lengthSpan n) ≤ lengthSpan (m + n) := by
    rw [lengthSpan, lengthSpan, Submodule.map₂_span_span, Submodule.span_le, Set.image2_subset_iff]
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [mulBilinear_apply, ofPath_mul_ofPath]
    by_cases h : p.source = q.target
    · rw [dite_eq_left h]
      apply ofPath_mem_lengthSpan
      rw [Path.length_concat, Nat.add_comm q.length]
      exact Nat.add_le_add hp hq
    · rw [dite_eq_right h]
      exact Submodule.zero_mem _
  exact h (Submodule.apply_mem_map₂ _ hx hy)

private noncomputable def lengthSpanIdeal (m : ℕ) : TwoSidedIdeal (PathAlgebra k Q) :=
  TwoSidedIdeal.mk' (lengthSpan m : Submodule k (PathAlgebra k Q))
    (Submodule.zero_mem _) (fun hx hy => Submodule.add_mem _ hx hy)
    (fun hx => Submodule.neg_mem _ hx)
    (fun {x y} hy => by
      have hx : x ∈ lengthSpan 0 := by rw [lengthSpan_zero]; trivial
      change x * y ∈ lengthSpan m
      simpa only [Nat.zero_add] using mul_mem_lengthSpan hx hy)
    (fun {x y} hx => by
      have hy : y ∈ lengthSpan 0 := by rw [lengthSpan_zero]; trivial
      change x * y ∈ lengthSpan m
      simpa only [Nat.add_zero] using mul_mem_lengthSpan hx hy)

private theorem coe_lengthSpanIdeal (m : ℕ) :
    (↑(lengthSpanIdeal (k := k) (Q := Q) m) : Set (PathAlgebra k Q)) =
      ↑(lengthSpan (k := k) (Q := Q) m) := by
  rw [lengthSpanIdeal, TwoSidedIdeal.coe_mk']

private theorem mem_lengthSpanIdeal {m : ℕ} {x : PathAlgebra k Q} :
    x ∈ lengthSpanIdeal m ↔ x ∈ lengthSpan m :=
  Set.ext_iff.mp (coe_lengthSpanIdeal m) x

private theorem lengthSpanIdeal_le {m : ℕ} {I : TwoSidedIdeal (PathAlgebra k Q)}
    (h : ∀ p : Path Q, m ≤ p.length → ofPath k p ∈ I) : lengthSpanIdeal m ≤ I := by
  have hspan : lengthSpan m ≤ I.asIdeal.restrictScalars k := by
    rw [lengthSpan, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp
  exact fun _ hx => hspan (mem_lengthSpanIdeal.mp hx)

private theorem arrow_mem_arrowIdeal {i j : Q} (a : Quiver.Hom i j) :
    arrow k a ∈ arrowIdeal k Q :=
  TwoSidedIdeal.subset_span ⟨⟨i, j, a⟩, rfl⟩

private theorem arrowIdeal_le_lengthSpanIdeal :
    arrowIdeal k Q ≤ lengthSpanIdeal (k := k) (Q := Q) 1 := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply mem_lengthSpanIdeal.mpr
  change arrow k a.2.2 ∈ lengthSpan 1
  rw [arrow_eq_ofPath]
  exact ofPath_mem_lengthSpan (Path.length_arrow a.2.2).ge

private theorem arrowIdeal_power_eq_lengthSpanIdeal (m : ℕ) :
    idealPower (arrowIdeal k Q) m = lengthSpanIdeal (k := k) (Q := Q) m := by
  induction m with
  | zero =>
    apply TwoSidedIdeal.ext
    intro x
    rw [mem_lengthSpanIdeal, lengthSpan_zero]
    change x ∈ (⊤ : TwoSidedIdeal (PathAlgebra k Q)) ↔ _
    simp
  | succ m ih =>
    change TwoSidedIdeal.span {z | ∃ x ∈ idealPower (arrowIdeal k Q) m,
      ∃ y ∈ arrowIdeal k Q, x * y = z} = _
    rw [ih]
    apply le_antisymm
    · apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact mem_lengthSpanIdeal.mpr
        (mul_mem_lengthSpan (mem_lengthSpanIdeal.mp hx)
          (mem_lengthSpanIdeal.mp (arrowIdeal_le_lengthSpanIdeal hy)))
    · apply lengthSpanIdeal_le
      rintro ⟨i, j, p⟩ hp
      change m + 1 ≤ p.length at hp
      obtain ⟨l, a, q, rfl, hlen⟩ := p.length_ne_zero_iff_eq_comp.mp (by omega)
      change ofPath k (Path.ofPath (a.toPath.comp q)) ∈ _
      rw [← ofPath_mul_comp q (Quiver.Hom.toPath a)]
      have hq : m ≤ q.length := by omega
      exact TwoSidedIdeal.subset_span
        ⟨ofPath k (Path.ofPath q), mem_lengthSpanIdeal.mpr (ofPath_mem_lengthSpan hq),
          arrow k a, arrow_mem_arrowIdeal a, rfl⟩

/-- The `m`-th power of the arrow ideal is the linear span of all paths of length at least `m`. -/
theorem arrowIdeal_power_eq_span (m : ℕ) (_hm : 1 ≤ m) :
    (idealPower (arrowIdeal k Q) m : Set (PathAlgebra k Q)) =
      (Submodule.span k (ofPath k '' {p : Path Q | m ≤ p.length}) : Set (PathAlgebra k Q)) := by
  rw [arrowIdeal_power_eq_lengthSpanIdeal]
  exact coe_lengthSpanIdeal m

end RM03.PathAlgebra
