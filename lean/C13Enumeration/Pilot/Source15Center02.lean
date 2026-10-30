import C13Enumeration.Pilot.Data
namespace C13.Enumeration.Pilot.Source15Center02
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def valuesA : Array Nat := #[5,1,0,1,3,3,2,2,2,2,2,2,0,1,3,0,1,2,2,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,3,2,2,1,1,1,1,1,1,0,3,2,0,2,5,3,2,2,1,1,3,1,0,3,2,0,2,3,5,2,2,1,1,1,3,0,2,1,0,1,2,2,4,2,3,1,1,1,0,2,1,0,1,2,2,2,4,1,3,1,1,0,2,1,0,1,1,1,3,1,4,2,2,2,0,2,1,0,1,1,1,1,3,2,4,2,2,0,2,1,0,1,3,1,1,1,2,2,4,2,0,2,1,0,1,1,3,1,1,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def A (a b : Point) : Nat := valuesA.getD (13*a.val+b.val) 0
theorem A_checked : ∀ a b, A a b = coDegree (link link15 2) a b := by decide +kernel
def step := matrixStep (List.finRange 13) A matrix
def finish := centerFinish link15 link01 hole 2 hole 0
def table0 : Point → Point := anchorTable hole hole 0
def table1 : Point → Point := put table0 1 2
def table2 : Point → Point := put table1 3 3
def table3 : Point → Point := put table2 0 1
def table4 : Point → Point := put table3 4 4
def table5 : Point → Point := put table4 5 5
def table6 : Point → Point := put table5 6 6
def table7 : Point → Point := put table6 7 7
def table8 : Point → Point := put table7 8 10
def table9 : Point → Point := put table8 9 11
def table10 : Point → Point := put table9 10 8
def table11 : Point → Point := put table10 11 9
def table12 : Point → Point := put table5 6 7
def table13 : Point → Point := put table12 7 6
def table14 : Point → Point := put table13 8 11
def table15 : Point → Point := put table14 9 10
def table16 : Point → Point := put table15 10 8
def table17 : Point → Point := put table16 11 9
def table18 : Point → Point := put table3 4 5
def table19 : Point → Point := put table18 5 4
def table20 : Point → Point := put table19 6 6
def table21 : Point → Point := put table20 7 7
def table22 : Point → Point := put table21 8 10
def table23 : Point → Point := put table22 9 11
def table24 : Point → Point := put table23 10 9
def table25 : Point → Point := put table24 11 8
def table26 : Point → Point := put table19 6 7
def table27 : Point → Point := put table26 7 6
def table28 : Point → Point := put table27 8 11
def table29 : Point → Point := put table28 9 10
def table30 : Point → Point := put table29 10 9
def table31 : Point → Point := put table30 11 8
def table32 : Point → Point := put table0 1 3
def table33 : Point → Point := put table32 3 2
def table34 : Point → Point := put table33 0 1
def table35 : Point → Point := put table34 4 4
def table36 : Point → Point := put table35 5 5
def table37 : Point → Point := put table36 6 6
def table38 : Point → Point := put table37 7 7
def table39 : Point → Point := put table38 8 10
def table40 : Point → Point := put table39 9 11
def table41 : Point → Point := put table40 10 8
def table42 : Point → Point := put table41 11 9
def table43 : Point → Point := put table36 6 7
def table44 : Point → Point := put table43 7 6
def table45 : Point → Point := put table44 8 11
def table46 : Point → Point := put table45 9 10
def table47 : Point → Point := put table46 10 8
def table48 : Point → Point := put table47 11 9
def table49 : Point → Point := put table34 4 5
def table50 : Point → Point := put table49 5 4
def table51 : Point → Point := put table50 6 6
def table52 : Point → Point := put table51 7 7
def table53 : Point → Point := put table52 8 10
def table54 : Point → Point := put table53 9 11
def table55 : Point → Point := put table54 10 9
def table56 : Point → Point := put table55 11 8
def table57 : Point → Point := put table50 6 7
def table58 : Point → Point := put table57 7 6
def table59 : Point → Point := put table58 8 11
def table60 : Point → Point := put table59 9 10
def table61 : Point → Point := put table60 10 9
def table62 : Point → Point := put table61 11 8

theorem bound62 : ∀ Q ∈ assignSearch step finish [] [] table62, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound61 : ∀ Q ∈ assignSearch step finish [11] [8] table61, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [8] [8] table61 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound62

theorem bound60 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table60, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [9] table60 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound61

theorem bound59 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,10] table59, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,10] [10] table59 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound60

theorem bound58 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table58, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [11] table58 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound59

theorem bound57 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table57, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table57 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound58

theorem bound56 : ∀ Q ∈ assignSearch step finish [] [] table56, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound55 : ∀ Q ∈ assignSearch step finish [11] [8] table55, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [8] [8] table55 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound56

theorem bound54 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table54, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [9] table54 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound55

theorem bound53 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,11] table53, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,11] [11] table53 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound54

theorem bound52 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table52, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [10] table52 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound53

theorem bound51 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [7,8,9,10,11] table51, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [7,8,9,10,11] [7] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound52

theorem bound50 : ∀ Q ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table50, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [6,7] table50 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound51
    · exact bound57

theorem bound49 : ∀ Q ∈ assignSearch step finish [5,6,7,8,9,10,11] [4,6,7,8,9,10,11] table49, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [6,7,8,9,10,11] [4,6,7,8,9,10,11] [4] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound50

theorem bound48 : ∀ Q ∈ assignSearch step finish [] [] table48, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound47 : ∀ Q ∈ assignSearch step finish [11] [9] table47, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [9] [9] table47 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound48

theorem bound46 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table46, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [8] table46 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound47

theorem bound45 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,10] table45, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,10] [10] table45 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound46

theorem bound44 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table44, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [11] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound45

theorem bound43 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table43, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table43 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound44

theorem bound42 : ∀ Q ∈ assignSearch step finish [] [] table42, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound41 : ∀ Q ∈ assignSearch step finish [11] [9] table41, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [9] [9] table41 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound42

theorem bound40 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table40, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [8] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound41

theorem bound39 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,11] table39, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,11] [11] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound40

theorem bound38 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table38, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [10] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound39

theorem bound37 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [7,8,9,10,11] table37, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [7,8,9,10,11] [7] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound38

theorem bound36 : ∀ Q ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table36, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [6,7] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound37
    · exact bound43

theorem bound35 : ∀ Q ∈ assignSearch step finish [5,6,7,8,9,10,11] [5,6,7,8,9,10,11] table35, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [6,7,8,9,10,11] [5,6,7,8,9,10,11] [5] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound36

theorem bound34 : ∀ Q ∈ assignSearch step finish [4,5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] table34, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 4 [5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] [4,5] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound35
    · exact bound49

theorem bound33 : ∀ Q ∈ assignSearch step finish [0,4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] table33, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 0 [4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] [1] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ Q ∈ assignSearch step finish [3,0,4,5,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] table32, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 3 [0,4,5,6,7,8,9,10,11] [1,2,4,5,6,7,8,9,10,11] [2] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound33

theorem bound31 : ∀ Q ∈ assignSearch step finish [] [] table31, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound30 : ∀ Q ∈ assignSearch step finish [11] [8] table30, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [8] [8] table30 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound31

theorem bound29 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table29, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [9] table29 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound30

theorem bound28 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,10] table28, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,10] [10] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound29

theorem bound27 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table27, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [11] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table26, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ Q ∈ assignSearch step finish [] [] table25, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound24 : ∀ Q ∈ assignSearch step finish [11] [8] table24, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [8] [8] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table23, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [9] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,11] table22, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,11] [11] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound23

theorem bound21 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table21, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [10] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound22

theorem bound20 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [7,8,9,10,11] table20, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [7,8,9,10,11] [7] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound21

theorem bound19 : ∀ Q ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table19, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [6,7] table19 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound20
    · exact bound26

theorem bound18 : ∀ Q ∈ assignSearch step finish [5,6,7,8,9,10,11] [4,6,7,8,9,10,11] table18, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [6,7,8,9,10,11] [4,6,7,8,9,10,11] [4] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ Q ∈ assignSearch step finish [] [] table17, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound16 : ∀ Q ∈ assignSearch step finish [11] [9] table16, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [9] [9] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table15, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [8] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,10] table14, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,10] [10] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table13, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [11] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [6,8,9,10,11] table12, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [6,8,9,10,11] [6] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ Q ∈ assignSearch step finish [] [] table11, Q = expected := by
  apply list_all_eq_bound
  decide +kernel

theorem bound10 : ∀ Q ∈ assignSearch step finish [11] [9] table10, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 11 [] [9] [9] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ Q ∈ assignSearch step finish [10,11] [8,9] table9, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 10 [11] [8,9] [8] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ Q ∈ assignSearch step finish [9,10,11] [8,9,11] table8, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 9 [10,11] [8,9,11] [11] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ Q ∈ assignSearch step finish [8,9,10,11] [8,9,10,11] table7, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 8 [9,10,11] [8,9,10,11] [10] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ Q ∈ assignSearch step finish [7,8,9,10,11] [7,8,9,10,11] table6, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 7 [8,9,10,11] [7,8,9,10,11] [7] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ Q ∈ assignSearch step finish [6,7,8,9,10,11] [6,7,8,9,10,11] table5, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 6 [7,8,9,10,11] [6,7,8,9,10,11] [6,7] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound6
    · exact bound12

theorem bound4 : ∀ Q ∈ assignSearch step finish [5,6,7,8,9,10,11] [5,6,7,8,9,10,11] table4, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 5 [6,7,8,9,10,11] [5,6,7,8,9,10,11] [5] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ Q ∈ assignSearch step finish [4,5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] table3, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 4 [5,6,7,8,9,10,11] [4,5,6,7,8,9,10,11] [4,5] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound18

theorem bound2 : ∀ Q ∈ assignSearch step finish [0,4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] table2, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 0 [4,5,6,7,8,9,10,11] [1,4,5,6,7,8,9,10,11] [1] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound3

theorem bound1 : ∀ Q ∈ assignSearch step finish [3,0,4,5,6,7,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] table1, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 3 [0,4,5,6,7,8,9,10,11] [1,3,4,5,6,7,8,9,10,11] [3] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ Q ∈ assignSearch step finish [1,3,0,4,5,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] table0, Q = expected := by
  refine assignSearch_bound_cons (R := fun Q => Q = expected) step finish 1 [3,0,4,5,6,7,8,9,10,11] [1,2,3,4,5,6,7,8,9,10,11] [2,3] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound32

theorem complete (e : Equiv.Perm Point) (he : e hole = 0) (hc : e (2 : Point) = hole)
    (hs : transport e (link link15 2) = link link01 0) : emitPencil link15 2 0 e = expected := by
  apply pencil_eq_of_search_bound link15 link01 hole 2 hole 0 [1,3,0,4,5,6,7,8,9,10,11]
    (by decide +kernel) (by decide +kernel) A matrix A_checked matrix_checked expected
    bound0 e he hc hs
end C13.Enumeration.Pilot.Source15Center02
