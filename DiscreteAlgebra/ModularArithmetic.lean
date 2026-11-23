import DiscreteAlgebra.DivisibilityGcd

namespace DiscreteAlgebra

/-- Modular congruence: `a ≡ b [MOD m]` holds when `a` and `b` share the same remainder modulo `m`. -/
def ModEq (m a b : Nat) : Prop := a % m = b % m

notation:50 a " ≡ " b " [MOD " m "]" => ModEq m a b

private theorem mul_mod_self_zero (m k : Nat) : (m * k) % m = 0 := by
  rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]

private theorem ModEq.add_mul_right (m a k : Nat) : a + k * m ≡ a [MOD m] := by
  unfold ModEq
  rw [Nat.add_mod, Nat.mul_comm k m, mul_mod_self_zero, Nat.add_zero, Nat.mod_mod]

/-- Modular congruence defines an equivalence relation on `Nat` for every modulus `m`. -/
theorem ModEq.equivalence (m : Nat) : Equivalence (ModEq m) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Modular congruence is compatible with addition. -/
theorem ModEq.add {m a b c d : Nat} (h1 : a ≡ b [MOD m]) (h2 : c ≡ d [MOD m]) :
    a + c ≡ b + d [MOD m] := by
  unfold ModEq at *
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]

/-- Modular congruence is compatible with multiplication. -/
theorem ModEq.mul {m a b c d : Nat} (h1 : a ≡ b [MOD m]) (h2 : c ≡ d [MOD m]) :
    a * c ≡ b * d [MOD m] := by
  unfold ModEq at *
  rw [Nat.mul_mod, h1, h2, ← Nat.mul_mod]

/-- Modular congruence is compatible with natural-number exponentiation. -/
theorem ModEq.pow {m a b : Nat} (k : Nat) (h : a ≡ b [MOD m]) :
    a ^ k ≡ b ^ k [MOD m] := by
  induction k with
  | zero => exact rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact ModEq.mul ih h

/-- Characterization of modular congruence via divisibility of differences when `b ≤ a`. -/
theorem ModEq.iff_dvd_sub {m a b : Nat} (hle : b ≤ a) :
    a ≡ b [MOD m] ↔ m ∣ a - b := by
  constructor
  · intro h
    unfold ModEq at h
    have ha : m * (a / m) + a % m = a := Nat.div_add_mod a m
    have hb : m * (b / m) + b % m = b := Nat.div_add_mod b m
    have hle' : m * (b / m) ≤ m * (a / m) := by omega
    have hsub : a - b = m * (a / m) - m * (b / m) := by omega
    rw [hsub]
    exact dvd_sub_of_dvd hle' ⟨a / m, rfl⟩ ⟨b / m, rfl⟩
  · intro hdvd
    cases hdvd with
    | intro k hk =>
      have heq : a = b + k * m := by
        rw [Nat.mul_comm] at hk
        omega
      rw [heq]
      exact ModEq.add_mul_right m b k

/-- Congruence modulo `m` projects to congruence modulo any divisor `n ∣ m`. -/
theorem ModEq.of_dvd {m n a b : Nat} (hdvd : n ∣ m) (h : a ≡ b [MOD m]) :
    a ≡ b [MOD n] := by
  have hmod : ∀ x : Nat, (x % m) % n = x % n := by
    intro x
    cases hdvd with
    | intro k hk =>
      have hdiv : m * (x / m) + x % m = x := Nat.div_add_mod x m
      have hx : x = x % m + (k * (x / m)) * n := by
        rw [hk, Nat.mul_assoc, Nat.mul_comm n (k * (x / m))] at hdiv
        omega
      have hshift : (x % m + (k * (x / m)) * n) % n = (x % m) % n :=
        ModEq.add_mul_right n (x % m) (k * (x / m))
      rw [← hx] at hshift
      exact hshift.symm
  unfold ModEq at *
  rw [← hmod a, ← hmod b, h]

end DiscreteAlgebra
