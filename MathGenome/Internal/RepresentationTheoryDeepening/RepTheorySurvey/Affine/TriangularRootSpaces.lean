import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.TriangularRootSpaces
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples

/-! Triangular decomposition and ordinary root spaces of the untwisted affine algebra. -/

noncomputable section

universe u

namespace RepTheorySurvey.Affine

open LieAlgebra hiding rootSpace
open LieAlgebrasAndRepresentations
open Specs.RepTheorySurvey.Affine.TriangularRootSpaces
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular positive_value negative_value)
open private cartanMaximalToral from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.LoopAlgebra
open private negative_borel_isCompl borel_submodule cartan_positive_disjoint
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]

abbrev affineCartan := @affineCartan_value
abbrev affinePositive := @affinePositive_value
abbrev affineNegative := @affineNegative_value
abbrev delta := @delta_value
abbrev extendFiniteRoot := @extendFiniteRoot_value

section Coordinates

variable (B : InvariantForm G)

@[simp] private theorem coordinates_homogeneous (m : ℤ) (x : G) :
    coordinates B (homogeneous B m x) = ((Finsupp.single m x, 0), 0) := by
  change ((LoopAlgebra.toFinsupp ℂ ℤ G (loopVector m x), (0 : ℂ)), (0 : ℂ)) = _
  rw [loopVector_coefficients]

@[simp] private theorem coordinates_K :
    coordinates B (K B) = ((0, 1), 0) := rfl

@[simp] private theorem coordinates_d :
    coordinates B (d B) = ((0, 0), 1) := rfl

@[simp] private theorem homogeneousLinear_apply (m : ℤ) (x : G) :
    homogeneousLinear B m x = homogeneous B m x := rfl

@[simp] private theorem homogeneous_zero (m : ℤ) :
    homogeneous B m (0 : G) = 0 := (homogeneousLinear B m).map_zero

private theorem homogeneousLinear_injective (m : ℤ) :
    Function.Injective (homogeneousLinear B m) := by
  intro x y h
  have e := congrArg (fun z => (coordinates B z).1.1 m) h
  simpa using e

private theorem eq_homogeneous_add_lines {x : AffineAlgebra B} {m : ℤ} {a : G}
    (hf : (coordinates B x).1.1 = Finsupp.single m a) :
    x = homogeneous B m a + (coordinates B x).1.2 • K B + (coordinates B x).2 • d B := by
  apply (coordinates B).injective
  rw [map_add, map_add, map_smul, map_smul, coordinates_homogeneous, coordinates_K, coordinates_d]
  simpa using (Prod.ext (Prod.ext hf rfl) rfl :
    (coordinates B) x = ((Finsupp.single m a, (coordinates B x).1.2), (coordinates B x).2))

private theorem homogeneous_mem_components {P : ℤ → Submodule ℂ G}
    {C D : Submodule ℂ ℂ} {m : ℤ} {x : G} (hx : x ∈ P m) :
    homogeneous B m x ∈ components B P C D := by
  change (∀ n, (coordinates B (homogeneous B m x)).1.1 n ∈ P n) ∧ _ ∧ _
  rw [coordinates_homogeneous]
  refine ⟨fun n => ?_, C.zero_mem, D.zero_mem⟩
  by_cases h : m = n
  · subst n
    simpa using hx
  · simp [h]

private theorem components_induction {P : ℤ → Submodule ℂ G} {C D : Submodule ℂ ℂ}
    {p : AffineAlgebra B → Prop} {x : AffineAlgebra B} (hx : x ∈ components B P C D)
    (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (hom : ∀ m a, a ∈ P m → p (homogeneous B m a))
    (cent : ∀ a ∈ C, p (a • K B)) (deg : ∀ a ∈ D, p (a • d B)) :
    p x := by
  rcases hx with ⟨hx, hc, hd⟩
  let e := coordinates B
  have hf (f : ℤ →₀ G) (hf : ∀ m, f m ∈ P m) : p (e.symm ((f, 0), 0)) := by
    induction f using Finsupp.induction with
    | zero => change p (e.symm 0); rw [map_zero]; exact zero
    | single_add m a f hm _ ih =>
      have hm' := Finsupp.notMem_support_iff.mp hm
      have ha : a ∈ P m := by simpa [hm'] using hf m
      have hh : ∀ n, f n ∈ P n := by
        intro n
        by_cases h : m = n
        · subst n
          rw [hm']
          exact (P m).zero_mem
        · simpa [Finsupp.single_apply, h] using hf n
      have eq : e.symm ((Finsupp.single m a, 0), 0) = homogeneous B m a := by
        apply e.injective
        simp [e]
      have es : (((Finsupp.single m a + f, 0), 0) : ((ℤ →₀ G) × ℂ) × ℂ) =
          ((Finsupp.single m a, 0), 0) + ((f, 0), 0) := by simp
      rw [es, map_add, eq]
      exact add _ _ (hom m a ha) (ih hh)
  have ex : x = e.symm (((e x).1.1, 0), 0) + (e x).1.2 • K B + (e x).2 • d B := by
    apply e.injective
    simp only [map_add, map_smul, e, LinearEquiv.apply_symm_apply, coordinates_K, coordinates_d,
      Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [ex]
  exact add _ _ (add _ _ (hf _ hx) (cent _ hc)) (deg _ hd)

private theorem affine_induction {p : AffineAlgebra B → Prop} (x : AffineAlgebra B)
    (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (hom : ∀ m a, p (homogeneous B m a)) (cent : ∀ a : ℂ, p (a • K B))
    (deg : ∀ a : ℂ, p (a • d B)) : p x :=
  components_induction B (P := fun _ => ⊤) (C := ⊤) (D := ⊤)
    ⟨fun _ => trivial, trivial, trivial⟩ zero add
    (fun m a _ => hom m a) (fun a _ => cent a) (fun a _ => deg a)

end Coordinates

section Bracket

variable (B : InvariantForm G)

private theorem side_lie_mem (N : LieSubalgebra ℂ G) (s : ℤ) (hs : s = 1 ∨ s = -1)
    {x y : AffineAlgebra B}
    (hx : x ∈ components B (sideDegrees N s) ⊥ ⊥)
    (hy : y ∈ components B (sideDegrees N s) ⊥ ⊥) :
    ⁅x, y⁆ ∈ components B (sideDegrees N s) ⊥ ⊥ := by
  let P := components B (sideDegrees N s) ⊥ ⊥
  have singles (m n : ℤ) (a b : G) (ha : a ∈ sideDegrees N s m) (hb : b ∈ sideDegrees N s n) :
      ⁅homogeneous B m a, homogeneous B n b⁆ ∈ P := by
    by_cases ha' : a = 0
    · simpa only [ha', ← homogeneousLinear_apply B m, map_zero, zero_lie] using P.zero_mem
    by_cases hb' : b = 0
    · simpa only [hb', ← homogeneousLinear_apply B n, map_zero, lie_zero] using P.zero_mem
    have hm : m = 0 ∨ 0 < s * m := by
      by_contra! h
      exact ha' (by simpa [sideDegrees, h.1, not_lt.mpr h.2] using ha)
    have hn : n = 0 ∨ 0 < s * n := by
      by_contra! h
      exact hb' (by simpa [sideDegrees, h.1, not_lt.mpr h.2] using hb)
    have hmn : 0 < s * (m + n) ∨ (m = 0 ∧ n = 0) := by
      rcases hs with rfl | rfl <;> simp at hm hn ⊢ <;> omega
    rw [homogeneousBracket]
    rcases hmn with hpos | ⟨rfl, rfl⟩
    · have hne : m + n ≠ 0 := by
        intro h
        simp [h] at hpos
      have hc : m ≠ -n := by omega
      simp only [ite_eq_right hc, zero_smul, add_zero]
      apply homogeneous_mem_components
      simp [sideDegrees, hne, hpos]
    · simp only [Int.cast_zero, zero_mul, ite_self, zero_smul, add_zero]
      apply homogeneous_mem_components
      simpa [sideDegrees] using N.lie_mem
        (show a ∈ N by simpa [sideDegrees] using ha)
        (show b ∈ N by simpa [sideDegrees] using hb)
  have zeroLeft : ⁅(0 : AffineAlgebra B), y⁆ ∈ P := by rw [zero_lie]; exact P.zero_mem
  refine components_induction B (p := fun z => ⁅z, y⁆ ∈ P) hx zeroLeft
    (fun a b ha hb => by simpa only [add_lie] using P.add_mem ha hb) ?_ ?_ ?_
  · intro m a ha
    refine components_induction B (p := fun z => ⁅homogeneous B m a, z⁆ ∈ P) hy
      (by rw [lie_zero]; exact P.zero_mem)
      (fun b c hb hc => by simpa only [lie_add] using P.add_mem hb hc)
      (fun n b hb => singles m n a b ha hb) ?_ ?_
    all_goals
      intro b hb
      have : b = 0 := (Submodule.mem_bot ℂ).mp hb
      simp [this]
  · intro a ha
    have : a = 0 := (Submodule.mem_bot ℂ).mp ha
    simp [this]
  · intro a ha
    have : a = 0 := (Submodule.mem_bot ℂ).mp ha
    simp [this]

theorem sidesClosed (H : LieSubalgebra ℂ G) (φ : Direction H) :
    ClosedUnderBracket B (affinePositive B H φ) ∧
      ClosedUnderBracket B (affineNegative B H φ) :=
  ⟨fun {_ _} hx hy => side_lie_mem B (positive_value H φ) 1 (Or.inl rfl) hx hy,
    fun {_ _} hx hy => side_lie_mem B (negative_value H φ) (-1) (Or.inr rfl) hx hy⟩

def affinePositiveLie (H : LieSubalgebra ℂ G) (φ : Direction H) :
    LieSubalgebra ℂ (AffineAlgebra B) :=
  { affinePositive B H φ with lie_mem' := fun hx hy => (sidesClosed B H φ).1 hx hy }

def affineNegativeLie (H : LieSubalgebra ℂ G) (φ : Direction H) :
    LieSubalgebra ℂ (AffineAlgebra B) :=
  { affineNegative B H φ with lie_mem' := fun hx hy => (sidesClosed B H φ).2 hx hy }

end Bracket

section Triangular

variable (B : InvariantForm G)

private theorem central_mem_components {P : ℤ → Submodule ℂ G} {C D : Submodule ℂ ℂ}
    {c : ℂ} (hc : c ∈ C) : c • K B ∈ components B P C D := by
  change (∀ m, (coordinates B (c • K B)).1.1 m ∈ P m) ∧ _ ∧ _
  simpa [map_smul, coordinates_K] using hc

private theorem degree_mem_components {P : ℤ → Submodule ℂ G} {C D : Submodule ℂ ℂ}
    {a : ℂ} (ha : a ∈ D) : a • d B ∈ components B P C D := by
  change (∀ m, (coordinates B (a • d B)).1.1 m ∈ P m) ∧ _ ∧ _
  simpa [map_smul, coordinates_d] using ha

private theorem components_sup (P Q : ℤ → Submodule ℂ G) (C D E F : Submodule ℂ ℂ) :
    components B P C D ⊔ components B Q E F =
      components B (fun m => P m ⊔ Q m) (C ⊔ E) (D ⊔ F) := by
  apply le_antisymm
  · exact sup_le
      (fun _ hx => ⟨fun m => (le_sup_left : P m ≤ P m ⊔ Q m) (hx.1 m),
        (le_sup_left : C ≤ C ⊔ E) hx.2.1, (le_sup_left : D ≤ D ⊔ F) hx.2.2⟩)
      (fun _ hx => ⟨fun m => (le_sup_right : Q m ≤ P m ⊔ Q m) (hx.1 m),
        (le_sup_right : E ≤ C ⊔ E) hx.2.1, (le_sup_right : F ≤ D ⊔ F) hx.2.2⟩)
  · intro x hx
    let S := components B P C D ⊔ components B Q E F
    refine components_induction B (p := fun x => x ∈ S) hx S.zero_mem
      (fun _ _ => S.add_mem) ?_ ?_ ?_
    · intro m x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      rw [← homogeneousLinear_apply, map_add, homogeneousLinear_apply, homogeneousLinear_apply]
      exact Submodule.mem_sup.mpr ⟨_, homogeneous_mem_components B ha, _,
        homogeneous_mem_components B hb, rfl⟩
    · intro c hc
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
      rw [add_smul]
      exact Submodule.mem_sup.mpr ⟨_, central_mem_components B ha, _,
        central_mem_components B hb, rfl⟩
    · intro c hc
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
      rw [add_smul]
      exact Submodule.mem_sup.mpr ⟨_, degree_mem_components B ha, _,
        degree_mem_components B hb, rfl⟩

private theorem components_disjoint {P Q : ℤ → Submodule ℂ G} {C D E F : Submodule ℂ ℂ}
    (hP : ∀ m, Disjoint (P m) (Q m)) (hC : Disjoint C E) (hD : Disjoint D F) :
    Disjoint (components B P C D) (components B Q E F) := by
  refine Submodule.disjoint_def.mpr fun x hx hy => (coordinates B).injective ?_
  rw [map_zero]
  exact Prod.ext (Prod.ext (Finsupp.ext fun m => Submodule.disjoint_def.mp (hP m) _ (hx.1 m)
    (hy.1 m)) (Submodule.disjoint_def.mp hC _ hx.2.1 hy.2.1))
    (Submodule.disjoint_def.mp hD _ hx.2.2 hy.2.2)

private theorem semisimple [LieAlgebra.IsSimple ℂ G] :
    LieAlgebrasAndRepresentations.IsSemisimple ℂ G :=
  LieAlgebra.radical_eq_bot

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G]
variable (H : LieSubalgebra ℂ G) [H.IsCartanSubalgebra]

/-- The three summands form an internal direct sum of complex vector spaces. -/
theorem triangularDecomposition (φ : Direction H) (hφ : Regular H φ) :
    IsCompl (affineNegative B H φ) (affineCartan B H ⊔ affinePositive B H φ) ∧
      Disjoint (affineCartan B H) (affinePositive B H φ) := by
  let P := sideDegrees (positive_value H φ) 1
  let N := sideDegrees (negative_value H φ) (-1)
  let T := cartanDegrees H
  have hH := cartanMaximalToral H
  have hcomp : IsCompl (negative_value H φ).toSubmodule
      (H.toSubmodule ⊔ (positive_value H φ).toSubmodule) := by
    rw [← (borel_submodule H φ semisimple hH hφ).1]
    exact negative_borel_isCompl H φ semisimple hH hφ
  have hdisj := cartan_positive_disjoint H φ semisimple hH
  change IsCompl (components B N ⊥ ⊥) (components B T ⊤ ⊤ ⊔ components B P ⊥ ⊥) ∧
    Disjoint (components B T ⊤ ⊤) (components B P ⊥ ⊥)
  rw [components_sup]
  simp only [sup_bot_eq]
  refine ⟨⟨components_disjoint B ?_ disjoint_bot_left disjoint_bot_left, ?_⟩,
    components_disjoint B ?_ disjoint_bot_right disjoint_bot_right⟩
  · intro m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · simp [N, T, P, sideDegrees, cartanDegrees, hm.ne, hm, not_lt.mpr hm.le]
    · simpa [N, T, P, sideDegrees, cartanDegrees] using hcomp.disjoint
    · simp [N, T, P, sideDegrees, cartanDegrees, hm.ne', hm, not_lt.mpr hm.le]
  · rw [codisjoint_iff, components_sup]
    have he : (fun m => N m ⊔ (T m ⊔ P m)) = fun _ => ⊤ := by
      funext m
      rcases lt_trichotomy m 0 with hm | rfl | hm
      · simp [N, T, P, sideDegrees, cartanDegrees, hm.ne, hm, not_lt.mpr hm.le]
      · simpa [N, T, P, sideDegrees, cartanDegrees] using hcomp.sup_eq_top
      · simp [N, T, P, sideDegrees, cartanDegrees, hm.ne', hm, not_lt.mpr hm.le]
    rw [he]
    exact top_unique fun _ _ => ⟨fun _ => trivial, by simp, by simp⟩
  · intro m
    by_cases hm : m = 0
    · subst m
      simpa [T, P, sideDegrees, cartanDegrees] using hdisj
    · simp [T, cartanDegrees, hm]

end Triangular

section Cartan

variable (B : InvariantForm G) (H : LieSubalgebra ℂ G)

/-- The constant loops of the finite Cartan, inside the affine Cartan. -/
def cartanIncl : H →ₗ[ℂ] affineCartan B H :=
  ((homogeneousLinear B 0).comp H.toSubmodule.subtype).codRestrict _
    (fun h => homogeneous_mem_components B (by simp [cartanDegrees]))

/-- The central generator as an element of the affine Cartan. -/
def cartanK : affineCartan B H :=
  ⟨K B, by
    change K B ∈ components B (cartanDegrees H) ⊤ ⊤
    rw [← one_smul ℂ (K B)]
    exact central_mem_components B (by trivial)⟩

/-- The degree generator as an element of the affine Cartan. -/
def cartanD : affineCartan B H :=
  ⟨d B, by
    change d B ∈ components B (cartanDegrees H) ⊤ ⊤
    rw [← one_smul ℂ (d B)]
    exact degree_mem_components B (by trivial)⟩

private theorem cartanExpansion (h : affineCartan B H) :
    h = cartanIncl B H (cartanProjection B H h) +
      (coordinates B (h : AffineAlgebra B)).1.2 • cartanK B H + delta B H h • cartanD B H := by
  apply Subtype.ext
  change (h : AffineAlgebra B) = homogeneous B 0 (cartanProjection B H h : G) +
    (coordinates B (h : AffineAlgebra B)).1.2 • K B + delta B H h • d B
  apply eq_homogeneous_add_lines B
  ext m
  by_cases hm : m = 0
  · subst m
    simp
    rfl
  · have hz := h.property.1 m
    rw [cartanDegrees, ite_eq_right hm] at hz
    rw [Finsupp.single_eq_of_ne hm, (Submodule.mem_bot ℂ).mp hz]

@[simp] theorem delta_cartanIncl (h : H) : delta B H (cartanIncl B H h) = 0 := by
  change (coordinates B (homogeneous B 0 h)).2 = 0
  rw [coordinates_homogeneous]

@[simp] theorem delta_cartanK : delta B H (cartanK B H) = 0 := rfl
@[simp] theorem delta_cartanD : delta B H (cartanD B H) = 1 := rfl

@[simp] private theorem cartanProjection_cartanIncl (h : H) :
    cartanProjection B H (cartanIncl B H h) = h := by
  apply Subtype.ext
  change (coordinates B (homogeneous B 0 h)).1.1 0 = (h : G)
  rw [coordinates_homogeneous, Finsupp.single_eq_same]

@[simp] private theorem cartanProjection_cartanK : cartanProjection B H (cartanK B H) = 0 := by
  apply Subtype.ext
  rfl

@[simp] private theorem cartanProjection_cartanD : cartanProjection B H (cartanD B H) = 0 := by
  apply Subtype.ext
  rfl

@[simp] theorem extendFiniteRoot_cartanIncl (α : Module.Dual ℂ H) (h : H) :
    extendFiniteRoot B H α (cartanIncl B H h) = α h := by
  simp [extendFiniteRoot_value]

@[simp] theorem extendFiniteRoot_cartanK (α : Module.Dual ℂ H) :
    extendFiniteRoot B H α (cartanK B H) = 0 := by simp [extendFiniteRoot_value]

@[simp] theorem extendFiniteRoot_cartanD (α : Module.Dual ℂ H) :
    extendFiniteRoot B H α (cartanD B H) = 0 := by simp [extendFiniteRoot_value]

@[simp] private theorem lie_K_left (x : AffineAlgebra B) : ⁅K B, x⁆ = 0 :=
  centralGenerator B x

@[simp] private theorem lie_K_right (x : AffineAlgebra B) : ⁅x, K B⁆ = 0 := by
  rw [← lie_skew, lie_K_left, neg_zero]

private theorem lie_cartanIncl_homogeneous (h : H) (m : ℤ) (x : G) :
    ⁅(cartanIncl B H h : AffineAlgebra B), homogeneous B m x⁆ =
      homogeneous B m ⁅(h : G), x⁆ := by
  change ⁅homogeneous B 0 (h : G), homogeneous B m x⁆ = _
  rw [homogeneousBracket]
  simp

private theorem lie_cartan_homogeneous (h : affineCartan B H) (m : ℤ) (x : G) :
    ⁅(h : AffineAlgebra B), homogeneous B m x⁆ =
      homogeneous B m (⁅(cartanProjection B H h : G), x⁆ +
        (delta B H h * (m : ℂ)) • x) := by
  conv_lhs => rw [cartanExpansion B H h]
  change ⁅homogeneous B 0 (cartanProjection B H h : G) +
    (coordinates B (h : AffineAlgebra B)).1.2 • K B + delta B H h • d B,
    homogeneous B m x⁆ = _
  rw [add_lie, add_lie, smul_lie, smul_lie, lie_K_left, smul_zero, add_zero,
    degreeBracket, smul_smul]
  change _ = homogeneousLinear B m (⁅(cartanProjection B H h : G), x⁆ +
    (delta B H h * (m : ℂ)) • x)
  rw [map_add, map_smul]
  simp only [homogeneousLinear_apply]
  exact congrArg (fun y => y + (delta B H h * (m : ℂ)) • homogeneous B m x)
    (lie_cartanIncl_homogeneous B H (cartanProjection B H h) m x)

private theorem lie_cartan_degree (h : affineCartan B H) :
    ⁅(h : AffineAlgebra B), d B⁆ = 0 := by
  rw [← lie_skew]
  conv_lhs => rw [cartanExpansion B H h]
  change -⁅d B, homogeneous B 0 (cartanProjection B H h : G) +
    (coordinates B (h : AffineAlgebra B)).1.2 • K B + delta B H h • d B⁆ = 0
  simp [lie_add, lie_smul, degreeBracket]

private theorem lie_cartan_coordinates (h : affineCartan B H) (x : AffineAlgebra B) :
    let c := coordinates B ⁅(h : AffineAlgebra B), x⁆
    let f := (coordinates B x).1.1
    (∀ m : ℤ, c.1.1 m = ⁅(cartanProjection B H h : G), f m⁆ +
      (delta B H h * (m : ℂ)) • f m) ∧ c.1.2 = 0 ∧ c.2 = 0 := by
  induction x using affine_induction B with
  | zero => simp
  | add x y hx hy =>
    simp only [lie_add, map_add, Prod.fst_add, Prod.snd_add, Finsupp.add_apply]
    refine ⟨fun m => ?_, by rw [hx.2.1, hy.2.1, add_zero], by rw [hx.2.2, hy.2.2, add_zero]⟩
    rw [hx.1, hy.1, smul_add]
    abel
  | hom m x =>
    rw [lie_cartan_homogeneous, coordinates_homogeneous, coordinates_homogeneous]
    dsimp
    refine ⟨fun n => ?_, rfl, rfl⟩
    by_cases hmn : m = n
    · subst n
      simp
    · simp [hmn]
  | cent c => simp [lie_smul, lie_K_right, coordinates_K]
  | deg r => simp [lie_smul, lie_cartan_degree, coordinates_d]

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra]

theorem cartanAbelianBracket (x y : affineCartan B H) :
    ⁅(x : AffineAlgebra B), (y : AffineAlgebra B)⁆ = 0 := by
  conv_lhs => rw [cartanExpansion B H y]
  change ⁅(x : AffineAlgebra B), homogeneous B 0 (cartanProjection B H y : G) +
    (coordinates B (y : AffineAlgebra B)).1.2 • K B + delta B H y • d B⁆ = 0
  let : IsLieAbelian H := cartanAbelian H
  have hcomm : ⁅(cartanProjection B H x : G), (cartanProjection B H y : G)⁆ = 0 :=
    congrArg Subtype.val (trivial_lie_zero H H (cartanProjection B H x)
      (cartanProjection B H y))
  simp only [lie_add, lie_smul, lie_K_right, lie_cartan_homogeneous, lie_cartan_degree,
    hcomm, Int.cast_zero, mul_zero, zero_smul, add_zero, smul_zero, homogeneous_zero]

/-- The Cartan Lie subalgebra with the underlying vector space used for the weights. -/
def affineCartanLie : LieSubalgebra ℂ (AffineAlgebra B) :=
  { affineCartan B H with
    lie_mem' := fun hx hy => by
      rw [cartanAbelianBracket B H ⟨_, hx⟩ ⟨_, hy⟩]
      exact (affineCartan B H).zero_mem }

instance : IsLieAbelian (affineCartanLie B H) :=
  ⟨fun x y => Subtype.ext (cartanAbelianBracket B H x y)⟩

end Cartan

section Weights

variable (B : InvariantForm G) (H : LieSubalgebra ℂ G)

private abbrev coeff (x : AffineAlgebra B) (m : ℤ) : G :=
  (coordinates B x).1.1 m

private theorem weight_coefficient {χ : Module.Dual ℂ (affineCartan B H)} {x : AffineAlgebra B}
    (hx : IsAdjointWeightVector B H χ x) (h : affineCartan B H) (m : ℤ) :
    ⁅(cartanProjection B H h : G), coeff B x m⁆ +
      (delta B H h * (m : ℂ)) • coeff B x m = χ h • coeff B x m := by
  have eq := congrArg (fun z => coeff B z m) (hx h)
  change (coordinates B ⁅(h : AffineAlgebra B), x⁆).1.1 m = coeff B (χ h • x) m at eq
  rw [(lie_cartan_coordinates B H h x).1 m] at eq
  change _ = (coordinates B (χ h • x)).1.1 m at eq
  rw [map_smul] at eq
  exact eq

private theorem weight_degree {χ : Module.Dual ℂ (affineCartan B H)} {x : AffineAlgebra B}
    (hx : IsAdjointWeightVector B H χ x) {m : ℤ} (hm : coeff B x m ≠ 0) :
    χ (cartanD B H) = (m : ℂ) := by
  have eq := weight_coefficient B H hx (cartanD B H) m
  simp only [cartanProjection_cartanD, Submodule.coe_zero, zero_lie, zero_add,
    delta_cartanD, one_mul] at eq
  exact sub_eq_zero.mp ((smul_eq_zero.mp
    (show (χ (cartanD B H) - (m : ℂ)) • coeff B x m = 0 by rw [sub_smul, eq, sub_self])).resolve_right hm)

private theorem weight_restrict {χ : Module.Dual ℂ (affineCartan B H)} {x : AffineAlgebra B}
    (hx : IsAdjointWeightVector B H χ x) (m : ℤ) :
    coeff B x m ∈ rootSpace H (χ.comp (cartanIncl B H)) := by
  apply (mem_rootSpace H _ _).mpr
  intro h
  simpa only [cartanProjection_cartanIncl, delta_cartanIncl, zero_mul, zero_smul, add_zero,
    LinearMap.comp_apply] using weight_coefficient B H hx (cartanIncl B H h) m

private theorem weight_lines_zero {χ : Module.Dual ℂ (affineCartan B H)} {x : AffineAlgebra B}
    (hχ : χ ≠ 0) (hx : IsAdjointWeightVector B H χ x) :
    (coordinates B x).1.2 = 0 ∧ (coordinates B x).2 = 0 := by
  obtain ⟨h, hh⟩ : ∃ h, χ h ≠ 0 := by
    by_contra! h
    exact hχ (LinearMap.ext h)
  have eq := congrArg (coordinates B) (hx h)
  change coordinates B ⁅(h : AffineAlgebra B), x⁆ = coordinates B (χ h • x) at eq
  rw [map_smul] at eq
  have hc := congrArg (fun c => c.1.2) eq
  have hd := congrArg Prod.snd eq
  have hcoords := lie_cartan_coordinates B H h x
  change (coordinates B ⁅(h : AffineAlgebra B), x⁆).1.2 = χ h • (coordinates B x).1.2 at hc
  change (coordinates B ⁅(h : AffineAlgebra B), x⁆).2 = χ h • (coordinates B x).2 at hd
  rw [hcoords.2.1] at hc
  rw [hcoords.2.2] at hd
  exact ⟨(smul_eq_zero.mp hc.symm).resolve_left hh, (smul_eq_zero.mp hd.symm).resolve_left hh⟩

private theorem weight_eq_extend {χ : Module.Dual ℂ (affineCartan B H)} {x : AffineAlgebra B}
    (hx : IsAdjointWeightVector B H χ x) {m : ℤ} (hm : coeff B x m ≠ 0) :
    χ = extendFiniteRoot B H (χ.comp (cartanIncl B H)) + (m : ℂ) • delta B H := by
  have hk : χ (cartanK B H) = 0 := by
    have eq := weight_coefficient B H hx (cartanK B H) m
    simp only [cartanProjection_cartanK, Submodule.coe_zero, zero_lie, zero_add,
      delta_cartanK, zero_mul, zero_smul] at eq
    exact (smul_eq_zero.mp eq.symm).resolve_right hm
  have hd := weight_degree B H hx hm
  apply LinearMap.ext
  intro h
  conv_lhs => rw [cartanExpansion B H h]
  simp [hk, hd, extendFiniteRoot_value, mul_comm]

private theorem weight_supported {χ : Module.Dual ℂ (affineCartan B H)} {x : AffineAlgebra B}
    (hx : IsAdjointWeightVector B H χ x) {m : ℤ} (hm : χ (cartanD B H) = (m : ℂ)) :
    (coordinates B x).1.1 = Finsupp.single m (coeff B x m) := by
  ext n
  by_cases hn : n = m
  · subst n
    simp
  · rw [Finsupp.single_eq_of_ne hn]
    by_contra h
    exact hn (Int.cast_injective ((weight_degree B H hx h).symm.trans hm))

private theorem extended_weight_cartanD (α : Module.Dual ℂ H) (m : ℤ) :
    (extendFiniteRoot B H α + (m : ℂ) • delta B H) (cartanD B H) = (m : ℂ) := by
  simp

private theorem extended_weight_restrict (α : Module.Dual ℂ H) (m : ℤ) :
    (extendFiniteRoot B H α + (m : ℂ) • delta B H).comp (cartanIncl B H) = α := by
  ext h
  simp

private theorem homogeneous_weight (α : Module.Dual ℂ H) (m : ℤ) (a : G)
    (ha : a ∈ rootSpace H α) :
    IsAdjointWeightVector B H (extendFiniteRoot B H α + (m : ℂ) • delta B H)
      (homogeneous B m a) := by
  intro h
  change ⁅(h : AffineAlgebra B), homogeneous B m a⁆ =
    (extendFiniteRoot B H α + (m : ℂ) • delta B H) h • homogeneous B m a
  rw [lie_cartan_homogeneous, (mem_rootSpace H α a).mp ha (cartanProjection B H h),
    ← add_smul]
  change homogeneousLinear B m ((α (cartanProjection B H h) + delta B H h * (m : ℂ)) • a) = _
  rw [map_smul]
  simp [extendFiniteRoot_value, mul_comm]

private theorem mem_extended_weight (α : Module.Dual ℂ H) (m : ℤ)
    (hχ : extendFiniteRoot B H α + (m : ℂ) • delta B H ≠ 0) (x : AffineAlgebra B) :
    IsAdjointWeightVector B H (extendFiniteRoot B H α + (m : ℂ) • delta B H) x ↔
      x ∈ (rootSpace H α).map (homogeneousLinear B m) := by
  constructor
  · intro hx
    have ⟨hc, hd⟩ := weight_lines_zero B H hχ hx
    have hsupport := weight_supported B H hx (extended_weight_cartanD B H α m)
    have hroot := weight_restrict B H hx m
    rw [extended_weight_restrict] at hroot
    refine ⟨coeff B x m, hroot, ?_⟩
    simpa only [hc, hd, zero_smul, add_zero, homogeneousLinear_apply] using
      (eq_homogeneous_add_lines B hsupport).symm
  · rintro ⟨a, ha, rfl⟩
    exact homogeneous_weight B H α m a ha

private theorem extended_weight_ne_zero_of_root {α : Module.Dual ℂ H} (hα : α ≠ 0) (m : ℤ) :
    extendFiniteRoot B H α + (m : ℂ) • delta B H ≠ 0 := by
  intro h
  apply hα
  rw [← extended_weight_restrict B H α m, h]
  rfl

private theorem extended_zero (m : ℤ) :
    extendFiniteRoot B H 0 + (m : ℂ) • delta B H = (m : ℂ) • delta B H := by
  ext h
  simp [extendFiniteRoot_value]

private theorem imaginary_weight_ne_zero {m : ℤ} (hm : m ≠ 0) :
    (m : ℂ) • delta B H ≠ 0 := by
  intro h
  rw [← extended_zero B H m] at h
  have eq := congrArg (fun η : Module.Dual ℂ (affineCartan B H) => η (cartanD B H)) h
  exact hm (Int.cast_eq_zero.mp (by simpa only [extended_weight_cartanD, LinearMap.zero_apply] using eq))

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra]

theorem zeroWeightSpace (x : AffineAlgebra B) :
    IsAdjointWeightVector B H 0 x ↔ x ∈ affineCartan B H := by
  constructor
  · intro hx
    have hsupport := weight_supported B H hx (by simp : (0 : Module.Dual ℂ (affineCartan B H))
      (cartanD B H) = ((0 : ℤ) : ℂ))
    have hroot := weight_restrict B H hx 0
    change coeff B x 0 ∈ rootSpace H 0 at hroot
    rw [rootSpace_zero semisimple H (cartanMaximalToral H)] at hroot
    refine ⟨fun m => ?_, trivial, trivial⟩
    by_cases hm : m = 0
    · subst m
      simpa [cartanDegrees] using hroot
    · have hf : coeff B x m = 0 := by
        change (coordinates B x).1.1 m = 0
        rw [hsupport, Finsupp.single_eq_of_ne hm]
      simp [cartanDegrees, hm, hf]
  · intro hx h
    change ⁅(h : AffineAlgebra B), x⁆ = (0 : ℂ) • x
    rw [zero_smul]
    exact cartanAbelianBracket B H h ⟨x, hx⟩

theorem realWeightSpace (α : rootSet H) (m : ℤ) :
    (∀ x, IsAdjointWeightVector B H (extendFiniteRoot B H α.val +
      (m : ℂ) • delta B H) x ↔
      x ∈ (rootSpace H α.val).map (homogeneousLinear B m)) ∧
    Module.finrank ℂ ((rootSpace H α.val).map (homogeneousLinear B m)) = 1 := by
  refine ⟨mem_extended_weight B H α.val m (extended_weight_ne_zero_of_root B H α.property.1 m), ?_⟩
  rw [← ((rootSpace H α.val).equivMapOfInjective (homogeneousLinear B m)
    (homogeneousLinear_injective B m)).finrank_eq]
  exact finrank_rootSpace_eq_one semisimple H (cartanMaximalToral H) α.val α.property

theorem imaginaryWeightSpace (m : ℤ) (hm : m ≠ 0) :
    (∀ x, IsAdjointWeightVector B H ((m : ℂ) • delta B H) x ↔
      x ∈ H.toSubmodule.map (homogeneousLinear B m)) ∧
    Module.finrank ℂ (H.toSubmodule.map (homogeneousLinear B m)) = Module.finrank ℂ H := by
  constructor
  · intro x
    rw [← extended_zero B H m, ← rootSpace_zero semisimple H (cartanMaximalToral H)]
    exact mem_extended_weight B H 0 m (by rw [extended_zero]; exact imaginary_weight_ne_zero B H hm) x
  · exact (H.toSubmodule.equivMapOfInjective (homogeneousLinear B m)
      (homogeneousLinear_injective B m)).finrank_eq.symm

theorem nonzeroWeights (χ : Module.Dual ℂ (affineCartan B H)) :
    (χ ≠ 0 ∧ ∃ x : AffineAlgebra B, x ≠ 0 ∧ IsAdjointWeightVector B H χ x) ↔
      (∃ (α : rootSet H) (m : ℤ),
        χ = extendFiniteRoot B H α.val + (m : ℂ) • delta B H) ∨
      (∃ m : ℤ, m ≠ 0 ∧ χ = (m : ℂ) • delta B H) := by
  constructor
  · rintro ⟨hχ, x, hx0, hx⟩
    have ⟨hc, hd⟩ := weight_lines_zero B H hχ hx
    obtain ⟨m, hm⟩ : ∃ m, coeff B x m ≠ 0 := by
      by_contra! h
      apply hx0
      apply (coordinates B).injective
      rw [map_zero]
      exact Prod.ext (Prod.ext (Finsupp.ext h) hc) hd
    let α := χ.comp (cartanIncl B H)
    have he : χ = extendFiniteRoot B H α + (m : ℂ) • delta B H := weight_eq_extend B H hx hm
    by_cases hα : α = 0
    · rw [hα, extended_zero] at he
      refine Or.inr ⟨m, ?_, he⟩
      rintro rfl
      exact hχ (by simpa using he)
    · have ha : α ∈ rootSet H :=
        ⟨hα, (Submodule.ne_bot_iff _).mpr ⟨_, weight_restrict B H hx m, hm⟩⟩
      exact Or.inl ⟨⟨α, ha⟩, m, he⟩
  · rintro (⟨α, m, rfl⟩ | ⟨m, hm, rfl⟩)
    · obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp α.property.2
      refine ⟨extended_weight_ne_zero_of_root B H α.property.1 m,
        homogeneousLinear B m a, ?_, (realWeightSpace B H α m).1 _ |>.mpr ⟨a, ha, rfl⟩⟩
      simpa only [map_zero] using (homogeneousLinear_injective B m).ne ha0
    · let : Nontrivial H := cartanNontrivial H
      obtain ⟨a, ha⟩ := exists_ne (0 : H)
      have ha0 : (a : G) ≠ 0 := by
        intro eq
        exact ha (Subtype.ext eq)
      refine ⟨imaginary_weight_ne_zero B H hm,
        homogeneousLinear B m a, ?_, (imaginaryWeightSpace B H m hm).1 _ |>.mpr ⟨a, a.property, rfl⟩⟩
      simpa only [map_zero] using (homogeneousLinear_injective B m).ne ha0

/-- The ordinary simultaneous eigenspace of the restricted adjoint action. -/
abbrev affineWeightSpace := @affineWeightSpace_value

omit [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra] in
theorem mem_affineWeightSpace (χ : Module.Dual ℂ (affineCartan B H)) (x : AffineAlgebra B) :
    x ∈ affineWeightSpace B H χ ↔ IsAdjointWeightVector B H χ x := Iff.rfl

theorem affineWeightSpace_eq_native (χ : Module.Dual ℂ (affineCartan B H)) :
    affineWeightSpace B H χ =
      (LieModule.weightSpace (AffineAlgebra B) (L := affineCartanLie B H)
        (fun h : affineCartanLie B H => χ ⟨h.1, h.2⟩)).toSubmodule := by
  ext x
  exact (LieModule.mem_weightSpace (L := affineCartanLie B H)
    (fun h : affineCartanLie B H => χ ⟨h.1, h.2⟩) x).symm

theorem affineWeightSpace_zero :
    affineWeightSpace B H 0 = affineCartan B H :=
  Submodule.ext (zeroWeightSpace B H)

theorem affineWeightSpace_real (α : rootSet H) (m : ℤ) :
    affineWeightSpace B H (extendFiniteRoot B H α.val + (m : ℂ) • delta B H) =
      (rootSpace H α.val).map (homogeneousLinear B m) :=
  Submodule.ext (realWeightSpace B H α m).1

theorem affineWeightSpace_imaginary (m : ℤ) (hm : m ≠ 0) :
    affineWeightSpace B H ((m : ℂ) • delta B H) =
      H.toSubmodule.map (homogeneousLinear B m) :=
  Submodule.ext (imaginaryWeightSpace B H m hm).1

open scoped Classical in
/-- The ordinary affine adjoint eigenspaces give an internal direct sum. -/
theorem adjointWeightDecomposition : DirectSum.IsInternal (affineWeightSpace B H) := by
  classical
  let A := affineCartanLie B H
  let f : Module.Dual ℂ (affineCartan B H) → A → ℂ := fun χ h => χ ⟨h.1, h.2⟩
  have hf : Function.Injective f := fun a b h => LinearMap.ext fun x =>
    congrFun h (⟨x.1, x.2⟩ : A)
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · have hi := ((LieSubmodule.iSupIndep_toSubmodule).mpr
      (LieModule.iSupIndep_genWeightSpace ℂ A (AffineAlgebra B))).comp hf
    refine hi.mono fun χ => ?_
    rw [affineWeightSpace_eq_native]
    exact (LieSubmodule.toSubmodule_le_toSubmodule _ _).mpr
      (LieModule.weightSpace_le_genWeightSpace (AffineAlgebra B) (f χ))
  · let S := ⨆ χ, affineWeightSpace B H χ
    have hzero : affineCartan B H ≤ S := by
      rw [← affineWeightSpace_zero B H]
      exact le_iSup (affineWeightSpace B H) 0
    refine top_unique fun x _ => affine_induction B (p := fun x => x ∈ S) x S.zero_mem
      (fun _ _ => S.add_mem) ?_ ?_ ?_
    · intro m x
      have hx : x ∈ ⨆ α, rootSpace H α := by
        rw [iSup_rootSpace_eq_top H (cartanMaximalToral H).1]
        trivial
      refine Submodule.iSup_induction _ (motive := fun x => homogeneousLinear B m x ∈ S) hx
        (fun α a ha => ?_) (by simp) (fun a b ha hb => by rw [map_add]; exact S.add_mem ha hb)
      exact Submodule.mem_iSup_of_mem (extendFiniteRoot B H α + (m : ℂ) • delta B H)
        (homogeneous_weight B H α m a ha)
    · intro c
      exact hzero (central_mem_components B (P := cartanDegrees H) (C := ⊤) (D := ⊤)
        (c := c) trivial)
    · intro a
      exact hzero (degree_mem_components B (P := cartanDegrees H) (C := ⊤) (D := ⊤)
        (a := a) trivial)

end Weights

end RepTheorySurvey.Affine
