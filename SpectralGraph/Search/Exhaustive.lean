import Mathlib.Data.List.Basic

/-! # Exhaustive finite search

A finite family with proved coverage and sound checking.
-/

namespace SpectralGraph
namespace Search

variable {α : Type _}

/-- A finite list together with a mathematical proof that it contains every
admissible object. Duplicates are allowed; this is intentional for searches
such as the order-13 subcubic extension census. -/
structure Certificate (admissible : α → Prop) where
  candidates : List α
  exhaustive : ∀ x, admissible x → x ∈ candidates

namespace Certificate

variable {admissible : α → Prop}

/-- If every candidate in an exhaustive finite certificate avoids `bad`, then
no admissible object is bad. -/
theorem noCounterexample (C : Certificate admissible) (bad : α → Prop)
    (hcheck : ∀ x, x ∈ C.candidates → ¬ bad x) :
    ∀ x, admissible x → ¬ bad x := by
  intro x hx
  exact hcheck x (C.exhaustive x hx)

/-- Boolean-checker version of `noCounterexample`. The Boolean checker may be
fast executable code; only its proved specification is used by the theorem. -/
theorem noCounterexampleOfBool
    (C : Certificate admissible) (check : α → Bool) (bad : α → Prop)
    (hspec : ∀ x, check x = true ↔ ¬ bad x)
    (hall : ∀ x, x ∈ C.candidates → check x = true) :
    ∀ x, admissible x → ¬ bad x := by
  intro x hx
  exact (hspec x).mp (hall x (C.exhaustive x hx))

end Certificate
end Search
end SpectralGraph
