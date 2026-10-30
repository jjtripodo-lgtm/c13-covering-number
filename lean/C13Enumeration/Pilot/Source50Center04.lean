import C13Enumeration.Pilot.Data
namespace C13.Enumeration.Pilot.Source50Center04
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def valuesA : Array Nat := #[5,2,2,2,0,3,2,2,3,1,2,1,0,2,4,2,2,0,2,1,1,1,3,1,1,0,2,2,4,2,0,2,1,1,1,1,3,1,0,2,2,2,4,0,2,1,1,1,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,2,2,2,0,5,1,1,2,2,3,2,0,2,1,1,1,0,1,3,1,1,1,2,1,0,2,1,1,1,0,1,1,3,1,1,2,1,0,3,1,1,1,0,2,1,1,4,2,2,2,0,1,3,1,1,0,2,1,1,2,4,2,2,0,2,1,3,1,0,3,2,2,2,2,5,2,0,1,1,1,3,0,2,1,1,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def A (a b : Point) : Nat := valuesA.getD (13*a.val+b.val) 0
theorem A_checked : ∀ a b, A a b = coDegree (link link50 4) a b := by decide +kernel
def step := matrixStep (List.finRange 13) A matrix
def finish := centerFinish link50 link01 hole 4 hole 0
def table0 : Point → Point := anchorTable hole hole 0
def table1 : Point → Point := put table0 6 2
def table2 : Point → Point := put table1 7 3
def table3 : Point → Point := put table2 0 4
def table4 : Point → Point := put table3 5 1
def table5 : Point → Point := put table2 0 5
def table6 : Point → Point := put table5 5 1
def table7 : Point → Point := put table0 6 3
def table8 : Point → Point := put table7 7 2
def table9 : Point → Point := put table8 0 4
def table10 : Point → Point := put table9 5 1
def table11 : Point → Point := put table8 0 5
def table12 : Point → Point := put table11 5 1

theorem bound12 : ∀ Q ∈ assignSearch step finish [10,1,2,3,8,9,11] [4,6,7,8,9,10,11] table12, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [1,2,3,8,9,11] [4,6,7,8,9,10,11] [] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound11 : ∀ Q ∈ assignSearch step finish [5,10,1,2,3,8,9,11] [1,4,6,7,8,9,10,11] table11, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [10,1,2,3,8,9,11] [1,4,6,7,8,9,10,11] [1] table11 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound12

theorem bound10 : ∀ Q ∈ assignSearch step finish [10,1,2,3,8,9,11] [5,6,7,8,9,10,11] table10, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [1,2,3,8,9,11] [5,6,7,8,9,10,11] [] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound9 : ∀ Q ∈ assignSearch step finish [5,10,1,2,3,8,9,11] [1,5,6,7,8,9,10,11] table9, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [10,1,2,3,8,9,11] [1,5,6,7,8,9,10,11] [1] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ Q ∈ assignSearch step finish [0,5,10,1,2,3,8,9,11] [1,4,5,6,7,8,9,10,11] table8, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 0 [5,10,1,2,3,8,9,11] [1,4,5,6,7,8,9,10,11] [4,5] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound9
    · exact bound11

theorem bound7 : ∀ Q ∈ assignSearch step finish [7,0,5,10,1,2,3,8,9,11] [1,2,4,5,6,7,8,9,10,11] table7, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [0,5,10,1,2,3,8,9,11] [1,2,4,5,6,7,8,9,10,11] [2] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ Q ∈ assignSearch step finish [10,1,2,3,8,9,11] [4,6,7,8,9,10,11] table6, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [1,2,3,8,9,11] [4,6,7,8,9,10,11] [] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound5 : ∀ Q ∈ assignSearch step finish [5,10,1,2,3,8,9,11] [1,4,6,7,8,9,10,11] table5, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [10,1,2,3,8,9,11] [1,4,6,7,8,9,10,11] [1] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ Q ∈ assignSearch step finish [10,1,2,3,8,9,11] [5,6,7,8,9,10,11] table4, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [1,2,3,8,9,11] [5,6,7,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ Q ∈ assignSearch step finish [5,10,1,2,3,8,9,11] [1,5,6,7,8,9,10,11] table3, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [10,1,2,3,8,9,11] [1,5,6,7,8,9,10,11] [1] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound4

theorem bound2 : ∀ Q ∈ assignSearch step finish [0,5,10,1,2,3,8,9,11] [1,4,5,6,7,8,9,10,11] table2, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 0 [5,10,1,2,3,8,9,11] [1,4,5,6,7,8,9,10,11] [4,5] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound5

theorem bound1 : ∀ Q ∈ assignSearch step finish [7,0,5,10,1,2,3,8,9,11] [1,3,4,5,6,7,8,9,10,11] table1, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [0,5,10,1,2,3,8,9,11] [1,3,4,5,6,7,8,9,10,11] [3] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ Q ∈ assignSearch step finish [6,7,0,5,10,1,2,3,8,9,11] [1,2,3,4,5,6,7,8,9,10,11] table0, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 6 [7,0,5,10,1,2,3,8,9,11] [1,2,3,4,5,6,7,8,9,10,11] [2,3] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound7

theorem complete (e : Equiv.Perm Point) (he : e hole = 0) (hc : e (4 : Point) = hole)
    (hs : transport e (link link50 4) = link link01 0) : emitPencil link50 4 0 e = expected := by
  apply pencil_eq_of_search_bound link50 link01 hole 4 hole 0 [6,7,0,5,10,1,2,3,8,9,11]
    (by decide +kernel) (by decide +kernel) A matrix A_checked matrix_checked expected
    bound0 e he hc hs
end C13.Enumeration.Pilot.Source50Center04
