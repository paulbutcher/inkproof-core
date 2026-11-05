/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Core

universe u v

/-- A mergeable aggregate: summaries of adjacent runs of data combine with `merge`, and `empty`
summarises no data. Merging keeps order: `merge a b` summarises a run followed by the run `b`
summarises, so the operation need not be commutative. -/
class Aggregate (M : Type u) where
  empty : M
  merge : M → M → M

/-- The laws that make aggregation exact, regardless of how the data is grouped: `merge` is
associative with `empty` as its identity, so the aggregate forms a monoid. A type can have an
`Aggregate` instance without this one, as float sums do, and then carries no exactness theorem. -/
class LawfulAggregate (M : Type u) [Aggregate M] : Prop extends
    Std.Associative (Aggregate.merge (M := M)),
    Std.LawfulIdentity (Aggregate.merge (M := M)) Aggregate.empty

namespace Aggregate

variable {M : Type u} [Aggregate M]

/-- Merges the measures of `xs` in order. -/
def fold {γ : Type v} (measure : γ → M) (xs : Array γ) : M :=
  xs.foldl (fun acc x => merge acc (measure x)) empty

end Aggregate

namespace LawfulAggregate

/-- Builds the instance from the three laws. -/
theorem of_laws {M : Type u} [Aggregate M]
    (assoc : ∀ a b c : M,
      Aggregate.merge (Aggregate.merge a b) c = Aggregate.merge a (Aggregate.merge b c))
    (empty_merge : ∀ a : M, Aggregate.merge Aggregate.empty a = a)
    (merge_empty : ∀ a : M, Aggregate.merge a Aggregate.empty = a) : LawfulAggregate M :=
  { assoc, left_id := empty_merge, right_id := merge_empty }

variable {M : Type u} [Aggregate M] [LawfulAggregate M]

theorem merge_assoc (a b c : M) :
    Aggregate.merge (Aggregate.merge a b) c = Aggregate.merge a (Aggregate.merge b c) :=
  Std.Associative.assoc a b c

@[simp] theorem empty_merge (a : M) : Aggregate.merge Aggregate.empty a = a :=
  Std.LawfulLeftIdentity.left_id a

@[simp] theorem merge_empty (a : M) : Aggregate.merge a Aggregate.empty = a :=
  Std.LawfulRightIdentity.right_id a

end LawfulAggregate

open Aggregate (empty merge)

/-- The smallest value; on ties, the earliest. -/
structure Minimum (α : Type u) where
  get : Option α
  deriving Repr, BEq

/-- The largest value; on ties, the earliest. -/
structure Maximum (α : Type u) where
  get : Option α
  deriving Repr, BEq

/-- The earliest value. -/
structure First (α : Type u) where
  get : Option α
  deriving Repr, BEq

/-- The latest value. -/
structure Last (α : Type u) where
  get : Option α
  deriving Repr, BEq

/-- The number of items. -/
structure Count where
  get : Nat
  deriving Repr, BEq

/-- The sum of the values. -/
structure Total (α : Type u) where
  get : α
  deriving Repr, BEq

/-- A set of pixel indices, such as the columns or cells some data falls in; merging takes the
union. Stored as a bitmask, so it suits sets of indices below a few thousand. -/
structure Occupancy where
  bits : Nat
  deriving Repr, BEq

/-- Picking the left argument of `r` when it holds, else the right, is associative when `r` is a
total preorder; minimum and maximum both reduce to this. -/
private theorem pick_assoc {α : Type u} (r : α → α → Prop) [DecidableRel r]
    (trans : ∀ a b c, r a b → r b c → r a c) (total : ∀ a b, r a b ∨ r b a) (a b c : α) :
    (if r (if r a b then a else b) c then (if r a b then a else b) else c) =
      (if r a (if r b c then b else c) then a else (if r b c then b else c)) := by
  have := trans a b c; have := trans a c b; have := trans b a c; have := trans b c a
  have := trans c a b; have := trans c b a
  have := total a b; have := total b c; have := total a c
  by_cases hab : r a b <;> by_cases hbc : r b c <;> by_cases hac : r a c <;> simp_all

section Order

variable {α : Type u} [LE α] [DecidableLE α]

instance : Aggregate (Minimum α) where
  empty := ⟨none⟩
  merge
    | ⟨some a⟩, ⟨some b⟩ => ⟨some (if a ≤ b then a else b)⟩
    | ⟨none⟩, b => b
    | a, ⟨none⟩ => a

instance : Aggregate (Maximum α) where
  empty := ⟨none⟩
  merge
    | ⟨some a⟩, ⟨some b⟩ => ⟨some (if b ≤ a then a else b)⟩
    | ⟨none⟩, b => b
    | a, ⟨none⟩ => a

variable [Std.IsLinearOrder α]

instance : LawfulAggregate (Minimum α) :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => by
      cases a <;> cases b <;> cases c <;> simp only [merge, Minimum.mk.injEq, Option.some.injEq]
      exact pick_assoc (· ≤ ·) Std.IsPreorder.le_trans Std.IsLinearPreorder.le_total _ _ _)
    (fun ⟨a⟩ => by cases a <;> rfl)
    (fun ⟨a⟩ => by cases a <;> rfl)

instance : LawfulAggregate (Maximum α) :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => by
      cases a <;> cases b <;> cases c <;> simp only [merge, Maximum.mk.injEq, Option.some.injEq]
      exact pick_assoc (fun x y => y ≤ x) (fun _ _ _ h₁ h₂ => Std.IsPreorder.le_trans _ _ _ h₂ h₁)
        (fun _ _ => Std.IsLinearPreorder.le_total _ _) _ _ _)
    (fun ⟨a⟩ => by cases a <;> rfl)
    (fun ⟨a⟩ => by cases a <;> rfl)

end Order

instance {α : Type u} : Aggregate (First α) where
  empty := ⟨none⟩
  merge a b := ⟨a.get <|> b.get⟩

instance {α : Type u} : LawfulAggregate (First α) :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => by cases a <;> rfl)
    (fun ⟨_⟩ => rfl)
    (fun ⟨a⟩ => by cases a <;> rfl)

instance {α : Type u} : Aggregate (Last α) where
  empty := ⟨none⟩
  merge a b := ⟨b.get <|> a.get⟩

instance {α : Type u} : LawfulAggregate (Last α) :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => by cases c <;> rfl)
    (fun ⟨a⟩ => by cases a <;> rfl)
    (fun ⟨_⟩ => rfl)

instance : Aggregate Count where
  empty := ⟨0⟩
  merge a b := ⟨a.get + b.get⟩

instance : LawfulAggregate Count :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Count.mk (Nat.add_assoc a b c))
    (fun ⟨a⟩ => congrArg Count.mk (Nat.zero_add a))
    (fun ⟨_⟩ => rfl)

instance {α : Type u} [Add α] [OfNat α 0] : Aggregate (Total α) where
  empty := ⟨0⟩
  merge a b := ⟨a.get + b.get⟩

/-- Sums are exact only where addition is associative with `0` as identity, as on `Nat` and `Int`
but not on floats. -/
instance {α : Type u} [Add α] [OfNat α 0] [Std.Associative (α := α) (· + ·)]
    [Std.LawfulIdentity (α := α) (· + ·) 0] : LawfulAggregate (Total α) :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Total.mk (Std.Associative.assoc (op := (· + ·)) a b c))
    (fun ⟨a⟩ => congrArg Total.mk (Std.LawfulLeftIdentity.left_id (op := (· + ·)) a))
    (fun ⟨a⟩ => congrArg Total.mk (Std.LawfulRightIdentity.right_id (op := (· + ·)) a))

instance : Aggregate Occupancy where
  empty := ⟨0⟩
  merge a b := ⟨a.bits ||| b.bits⟩

instance : LawfulAggregate Occupancy :=
  .of_laws
    (fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Occupancy.mk (Nat.or_assoc a b c))
    (fun ⟨a⟩ => congrArg Occupancy.mk (Nat.zero_or a))
    (fun ⟨a⟩ => congrArg Occupancy.mk (Nat.or_zero a))

namespace Occupancy

def singleton (i : Nat) : Occupancy := ⟨1 <<< i⟩

def contains (o : Occupancy) (i : Nat) : Bool := o.bits.testBit i

end Occupancy

/-- Aggregates both components side by side, such as first, maximum, minimum and last together. -/
instance {A : Type u} {B : Type v} [Aggregate A] [Aggregate B] : Aggregate (A × B) where
  empty := (empty, empty)
  merge a b := (merge a.1 b.1, merge a.2 b.2)

instance {A : Type u} {B : Type v} [Aggregate A] [Aggregate B] [LawfulAggregate A]
    [LawfulAggregate B] : LawfulAggregate (A × B) :=
  .of_laws
    (fun a b c => Prod.ext (LawfulAggregate.merge_assoc a.1 b.1 c.1)
      (LawfulAggregate.merge_assoc a.2 b.2 c.2))
    (fun a => Prod.ext (LawfulAggregate.empty_merge a.1) (LawfulAggregate.empty_merge a.2))
    (fun a => Prod.ext (LawfulAggregate.merge_empty a.1) (LawfulAggregate.merge_empty a.2))

end Inkproof.Core
