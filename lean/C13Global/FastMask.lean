import C13Global.MaskKernel
namespace C13.Global
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pow2fast (n : Nat) : Nat :=
  if n = 0 then 1 else
    let a := pow2fast (n / 2)
    if n % 2 = 0 then a * a else 2 * a * a
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem pow2fast_eq (n : Nat) : pow2fast n = 2 ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [pow2fast]
    split
    · rename_i h
      simp [h]
    · rename_i h
      rw [ih (n / 2) (Nat.div_lt_self (by omega) (by decide))]
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

def fastListMask : List Code → Mask
  | [] => 0
  | b :: bs => pow2fast b.toNat ||| fastListMask bs

theorem fastListMask_eq (xs : List Code) : fastListMask xs = listMask xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [fastListMask,listMask,singletonMask,pow2fast_eq,ih]
end C13.Global
