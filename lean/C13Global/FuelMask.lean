import C13Global.MaskKernel
namespace C13.Global
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pow2fuel : Nat → Nat → Nat
  | 0, _ => 1
  | k+1, n => let a := pow2fuel k (n / 2)
      if n % 2 = 0 then a * a else 2 * a * a

theorem pow2fuel_eq (k n : Nat) (h : n < 2 ^ k) : pow2fuel k n = 2 ^ n := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn,pow2fuel]
  | succ k ih =>
    have hn : n / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at h
      omega
    simp only [pow2fuel,ih _ hn]
    split
    · rename_i hm
      rw [← Nat.pow_add]
      congr 1
      omega
    · rename_i hm
      calc
        2 * 2 ^ (n / 2) * 2 ^ (n / 2) = 2 ^ (n / 2 + n / 2 + 1) := by
          simp only [Nat.pow_add,Nat.pow_one]
          ac_rfl
        _ = 2 ^ n := by congr 1; omega

def fuelListMask : List Code → Mask
  | [] => 0
  | b :: bs => pow2fuel 13 b.toNat ||| fuelListMask bs

theorem fuelListMask_eq (xs : List Code) : fuelListMask xs = listMask xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [fuelListMask,listMask,singletonMask,pow2fuel_eq 13 b.toNat b.isLt,ih]
end C13.Global
