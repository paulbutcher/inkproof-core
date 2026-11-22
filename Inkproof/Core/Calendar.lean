/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Inkproof.Core.Decimal
import Std.Time.Date.PlainDate

open Std.Time

namespace Inkproof.Core.Calendar

/-- Whether `y` is a leap year of the proleptic Gregorian calendar. -/
def isLeap (y : Int) : Bool := (Year.Offset.ofInt y).isLeap

/-- The number of days in month `m` (1 for January) of year `y`; 31 for any `m` outside 1 to 12. -/
def daysInMonth (y : Int) (m : Nat) : Nat :=
  (Month.Ordinal.days (isLeap y) (Internal.Bounded.LE.clip (m : Int) (by decide))).val.toNat

/-- The date after `(y, m, d)`. -/
def nextDay : Int × Nat × Nat → Int × Nat × Nat
  | (y, m, d) =>
    if d < daysInMonth y m then (y, m, d + 1)
    else if m < 12 then (y, m + 1, 1)
    else (y + 1, 1, 1)

/-- The proleptic Gregorian date `(year, month, day)` that is `z` days after 1970-01-01 (before it when `z` is negative). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let date := PlainDate.ofEpochDay (Day.Offset.ofInt z)
  (date.year.toInt, date.month.val.toNat, date.day.val.toNat)

/-- The number of days from 1970-01-01 to the proleptic Gregorian date `(y, m, d)`; meaningful when `1 ≤ m ≤ 12` and `1 ≤ d ≤ daysInMonth y m`. -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  (PlainDate.ofYearMonthDayClip (Year.Offset.ofInt y) (Internal.Bounded.LE.clip (m : Int) (by decide))
    (Internal.Bounded.LE.clip (d : Int) (by decide))).toEpochDay.toInt

/-- The characters `YYYY-MM-DD` of the date `(y, m, d)`: the year padded to four digits, with a leading `'-'` when negative, and month and day padded to two. -/
def isoChars : Int × Nat × Nat → List Char
  | (y, m, d) =>
    (if y < 0 then ['-'] else []) ++ List.leftpad 4 '0' (Nat.toDigits 10 y.natAbs) ++ '-' :: List.leftpad 2 '0' (Nat.toDigits 10 m) ++ '-' :: List.leftpad 2 '0' (Nat.toDigits 10 d)

/-- The date `z` days after 1970-01-01 as `YYYY-MM-DD`. -/
def isoDate (z : Int) : String := String.ofList (isoChars (civilFromDays z))

end Inkproof.Core.Calendar
