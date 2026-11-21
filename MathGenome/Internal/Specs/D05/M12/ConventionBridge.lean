import MathGenome.Internal.Specs.D05.M12.InnerProduct

/-!
Independent statements for K05.12.convention_bridge, paper.tex:1886–1893.
`Function.swap h` is exactly the map `(u,v) ↦ h(v,u)`. The algebraic
statements use only the prerequisite inner-product axioms on the given module;
they impose no topology, completeness, or dimension hypothesis. Induced norms
are written explicitly as square roots of real diagonal values. The final
statements identify this construction with the shared `D05.firstInner` and
Mathlib's inner product and norm.
-/

namespace Specs.D05.M12.ConventionBridge

universe u v w

def swap_eq_conjugate : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v : V,
    Function.swap h u v = starRingEnd F (h u v)

def swap_conjugate_linear_first : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h →
    ∀ (a b : F) (u v w : V),
    Function.swap h (a • u + b • v) w =
      starRingEnd F a * Function.swap h u w +
      starRingEnd F b * Function.swap h v w

def swap_linear_second : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h →
    ∀ (a b : F) (u v w : V),
    Function.swap h u (a • v + b • w) =
      a * Function.swap h u v + b * Function.swap h u w

def swap_hermitian : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v : V,
    Function.swap h v u = starRingEnd F (Function.swap h u v)

def swap_diagonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ v : V,
    Function.swap h v v = h v v ∧
    RCLike.im (Function.swap h v v) = 0 ∧
    (v ≠ 0 → 0 < RCLike.re (Function.swap h v v))

/-- Both directions of the change between the two sets of inner-product axioms. -/
def axioms_iff_swap : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h ↔
      (∀ (a b : F) (u v w : V),
        Function.swap h (a • u + b • v) w =
          starRingEnd F a * Function.swap h u w +
          starRingEnd F b * Function.swap h v w) ∧
      (∀ (a b : F) (u v w : V),
        Function.swap h u (a • v + b • w) =
          a * Function.swap h u v + b * Function.swap h u w) ∧
      (∀ u v : V, Function.swap h v u = starRingEnd F (Function.swap h u v)) ∧
      (∀ v : V, RCLike.im (Function.swap h v v) = 0) ∧
      (∀ v : V, v ≠ 0 → 0 < RCLike.re (Function.swap h v v))

def swap_involutive : Prop :=
  ∀ {F : Type u} {V : Type v} (h : V → V → F),
    Function.swap (Function.swap h) = h

/-- The same induced norm is obtained from either diagonal. -/
def norm_preserved : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] (h : V → V → F) (v : V),
    Real.sqrt (RCLike.re (Function.swap h v v)) = Real.sqrt (RCLike.re (h v v))

def orthogonality_preserved : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F), _root_.D05.IsFirstInnerProduct h → ∀ u v : V,
    (Function.swap h u v = 0 ↔ h u v = 0)

/-- In an expansion, the coefficient's argument order must also be swapped. -/
def coefficient_translation : Prop :=
  ∀ {F : Type u} {V : Type v} (h : V → V → F) (v e : V),
    h v e = Function.swap h e v

/-- Translation of a finite expansion; this identity applies to every family,
and in particular to an orthonormal family, including the empty family. -/
def finite_expansion_translation : Prop :=
  ∀ {F : Type u} {V : Type v} {ι : Type w}
    [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F) (s : Finset ι) (e : ι → V) (v : V),
    (v = ∑ i ∈ s, h v (e i) • e i) ↔
      (v = ∑ i ∈ s, Function.swap h (e i) v • e i)

def swap_firstInner_eq_inner : Prop :=
  ∀ {F : Type u} {V : Type v} [Inner F V],
    Function.swap (_root_.D05.firstInner (F := F) (V := V)) = inner F

/-- The diagonal formula really gives the existing norm of the same space. -/
def canonical_norm : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (v : V),
    Real.sqrt (RCLike.re (_root_.D05.firstInner (F := F) v v)) = ‖v‖ ∧
    Real.sqrt (RCLike.re
      (Function.swap (_root_.D05.firstInner (F := F) (V := V)) v v)) = ‖v‖

def canonical_orthogonality : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (u v : V),
    (_root_.D05.firstInner (F := F) u v = 0 ↔ inner F u v = 0)

end Specs.D05.M12.ConventionBridge
