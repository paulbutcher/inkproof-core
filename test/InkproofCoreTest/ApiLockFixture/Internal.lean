/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Public declarations in an `Internal` module, which `api-lock` must leave out. -/

namespace Fixture.Internal

def helper (n : Nat) : Nat := n * 2

theorem helper_zero : helper 0 = 0 := rfl

end Fixture.Internal
