/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Core.Calendar

/-- Whether `y` is a leap year of the proleptic Gregorian calendar. -/
def isLeap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- The number of days in month `m` (1 for January) of year `y`; 31 for any `m` outside 1 to 12. -/
def daysInMonth (y : Int) (m : Nat) : Nat :=
  if m = 2 then (if isLeap y then 29 else 28)
  else if m = 4 || m = 6 || m = 9 || m = 11 then 30
  else 31

/-- The date after `(y, m, d)`. -/
def nextDay : Int × Nat × Nat → Int × Nat × Nat
  | (y, m, d) =>
    if d < daysInMonth y m then (y, m, d + 1)
    else if m < 12 then (y, m + 1, 1)
    else (y + 1, 1, 1)

/-- The proleptic Gregorian date `(year, month, day)` that is `z` days after 1970-01-01 (before it when `z` is negative). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := z / 146097
  let doe := z % 146097
  -- The year of the era, counted from March: an estimate from the 365-day year, corrected down by one if it overshoots.
  let y := min (doe / 365) 399
  let yoe := if doe < 365 * y + y / 4 - y / 100 then y - 1 else y
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  -- Months count from March so that the leap day is the last day of the year.
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m.toNat, d.toNat)

/-- The number of days from 1970-01-01 to the proleptic Gregorian date `(y, m, d)`; meaningful when `1 ≤ m ≤ 12` and `1 ≤ d ≤ daysInMonth y m`. -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y % 400
  let doy := (153 * (if m > 2 then (m : Int) - 3 else (m : Int) + 9) + 2) / 5 + d - 1
  era * 146097 + (yoe * 365 + yoe / 4 - yoe / 100 + doy) - 719468

end Inkproof.Core.Calendar
