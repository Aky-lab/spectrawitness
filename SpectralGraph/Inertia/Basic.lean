/-!
# Inertia triples

Computable positive, zero, and negative indices, their order and signature.
-/

namespace SpectralGraph

/-- The three inertia indices `(n₊, n₀, n₋)`. -/
structure Inertia where
  pos : Nat
  zero : Nat
  neg : Nat
  deriving DecidableEq, Repr

namespace Inertia

/-- Total dimension represented by an inertia triple. -/
def order (ι : Inertia) : Nat := ι.pos + ι.zero + ι.neg

/-- Signature `n₊ - n₋`. -/
def signature (ι : Inertia) : Int := (ι.pos : Int) - (ι.neg : Int)

@[simp] theorem order_mk (p z n : Nat) :
    (Inertia.mk p z n).order = p + z + n := rfl

@[simp] theorem signature_mk (p z n : Nat) :
    (Inertia.mk p z n).signature = (p : Int) - (n : Int) := rfl

end Inertia
end SpectralGraph
