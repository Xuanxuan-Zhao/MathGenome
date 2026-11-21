import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests
import Mathlib.Algebra.Module.Injective

/-!
Vanishing and flatness, paper.tex 2717–2723 and 2761–2766, with the
chapter conventions at 2577–2582. All rings are associative and unital,
including the zero ring. Homology is the shared explicit quotient.
Statements quantify over every projective resolution, so no particular
choice of a derived group is privileged. Positive degrees are `n+1`.
For injective coefficients an adequate universe `max u w` is used, as in
the upstream injective-resolution interface: the ring fits in this universe.
There is no finiteness hypothesis. The opposite-ring statements are included
explicitly. Flatness tests all modules in an arbitrary enlarged universe.
-/
namespace P103.Specs.Ch11.VanishingAndFlatness
open P103.Specs.Ch10.Comparison P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch02.FlatnessTests
universe u v w

def ext_projectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B],
    Module.Projective R A → ∀ (P : LeftResolution R A), P.IsProjective →
      ∀ n : ℕ, Subsingleton (ExtWith P B (n+1))

def ext_injectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type (max u w))
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B],
    Module.Injective R B → ∀ (P : LeftResolution R A), P.IsProjective →
      ∀ n : ℕ, Subsingleton (ExtWith P B (n+1))

def right_ext_projectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B],
    Module.Projective Rᵐᵒᵖ A → ∀ (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
      ∀ n : ℕ, Subsingleton (ExtWith P B (n+1))

def right_ext_injectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type (max u w))
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B],
    Module.Injective Rᵐᵒᵖ B → ∀ (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
      ∀ n : ℕ, Subsingleton (ExtWith P B (n+1))

def tor_left_flatType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B],
    Flat.{u,w,v} R B → ∀ (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
      ∀ n : ℕ, Subsingleton (TorWith P B (n+1))

def tor_right_flatType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module R B],
    RightFlat.{u,v,w} R A → ∀ (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
      ∀ n : ℕ, Subsingleton (TorWith P B (n+1))

def right_flat_iff_tor_oneType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    RightFlat.{u,v,w} R A ↔
      ∀ (B : Type (max u v w)) [AddCommGroup B] [Module R B]
        (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective → Subsingleton (TorWith P B 1)

def left_flat_iff_tor_oneType : Prop :=
  ∀ (R : Type u) [Ring R] (B : Type w) [AddCommGroup B] [Module R B],
    Flat.{u,w,v} R B ↔
      ∀ (A : Type (max u v w)) [AddCommGroup A] [Module Rᵐᵒᵖ A]
        (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective → Subsingleton (TorWith P B 1)

end P103.Specs.Ch11.VanishingAndFlatness
