/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! One declaration of each kind `api-lock` reports, plus ones it must leave out. -/

namespace Fixture

inductive Shape where
  | dot
  | line (length : Nat)
  deriving Repr, BEq

structure Point (α : Type) where
  x : α
  y : α

class HasArea (α : Type) where
  area : α → Nat

instance : HasArea Shape where
  area
    | .dot => 0
    | .line n => n

def total : List Shape → Nat
  | [] => 0
  | s :: ss => HasArea.area s + total ss

private def hidden (n : Nat) : Nat := n + 1

theorem total_nil : total [] = 0 := rfl

axiom fixtureAxiom : ∀ n : Nat, n = n

opaque secret : Nat

end Fixture
