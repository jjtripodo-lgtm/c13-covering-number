import C13Enumeration.Canonical.Atlas
namespace C13.Enumeration.Canonical.Pair56_56
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def maps : List (Point → Point) := [![0,1,2,3,12,5,6,7,8,9,10,11,4],![0,1,3,2,12,5,7,6,8,9,11,10,4],![9,8,11,10,12,5,6,7,1,0,3,2,4],![9,8,10,11,12,5,7,6,1,0,2,3,4]]
def step := starStep (link link57 4) (link link57 4) Data56.matrix Data56.matrix
def finish := crossMapFinish link57 link57 hole 4 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 5 5
def table2 : Point → Point := put table1 6 6
def table3 : Point → Point := put table2 7 7
def table4 : Point → Point := put table3 0 0
def table5 : Point → Point := put table4 1 1
def table6 : Point → Point := put table5 8 8
def table7 : Point → Point := put table6 9 9
def table8 : Point → Point := put table7 2 2
def table9 : Point → Point := put table8 3 3
def table10 : Point → Point := put table9 10 10
def table11 : Point → Point := put table10 11 11
def table12 : Point → Point := put table3 0 9
def table13 : Point → Point := put table12 1 8
def table14 : Point → Point := put table13 8 1
def table15 : Point → Point := put table14 9 0
def table16 : Point → Point := put table15 2 11
def table17 : Point → Point := put table16 3 10
def table18 : Point → Point := put table17 10 3
def table19 : Point → Point := put table18 11 2
def table20 : Point → Point := put table1 6 7
def table21 : Point → Point := put table20 7 6
def table22 : Point → Point := put table21 0 0
def table23 : Point → Point := put table22 1 1
def table24 : Point → Point := put table23 8 8
def table25 : Point → Point := put table24 9 9
def table26 : Point → Point := put table25 2 3
def table27 : Point → Point := put table26 3 2
def table28 : Point → Point := put table27 10 11
def table29 : Point → Point := put table28 11 10
def table30 : Point → Point := put table21 0 9
def table31 : Point → Point := put table30 1 8
def table32 : Point → Point := put table31 8 1
def table33 : Point → Point := put table32 9 0
def table34 : Point → Point := put table33 2 10
def table35 : Point → Point := put table34 3 11
def table36 : Point → Point := put table35 10 2
def table37 : Point → Point := put table36 11 3
def table38 : Point → Point := put table0 5 6
def table39 : Point → Point := put table38 6 5
def table40 : Point → Point := put table39 7 7
def table41 : Point → Point := put table40 0 0
def table42 : Point → Point := put table40 0 9
def table43 : Point → Point := put table38 6 7
def table44 : Point → Point := put table43 7 5
def table45 : Point → Point := put table44 0 0
def table46 : Point → Point := put table44 0 9
def table47 : Point → Point := put table0 5 7
def table48 : Point → Point := put table47 6 5
def table49 : Point → Point := put table48 7 6
def table50 : Point → Point := put table49 0 0
def table51 : Point → Point := put table49 0 9
def table52 : Point → Point := put table47 6 6
def table53 : Point → Point := put table52 7 5
def table54 : Point → Point := put table53 0 0
def table55 : Point → Point := put table53 0 9

theorem bound55 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [0,1,2,3,8,10,11] table55, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [0,1,2,3,8,10,11] [] table55 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound54 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [1,2,3,8,9,10,11] table54, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [1,2,3,8,9,10,11] [] table54 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound53 : ∀ f ∈ assignSearch step finish [0,1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] table53, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] [0,9] table53 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound54
    · exact bound55

theorem bound52 : ∀ f ∈ assignSearch step finish [7,0,1,8,9,2,3,10,11] [0,1,2,3,5,8,9,10,11] table52, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,8,9,2,3,10,11] [0,1,2,3,5,8,9,10,11] [5] table52 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound53

theorem bound51 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [0,1,2,3,8,10,11] table51, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [0,1,2,3,8,10,11] [] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound50 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [1,2,3,8,9,10,11] table50, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [1,2,3,8,9,10,11] [] table50 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound49 : ∀ f ∈ assignSearch step finish [0,1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] table49, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] [0,9] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound50
    · exact bound51

theorem bound48 : ∀ f ∈ assignSearch step finish [7,0,1,8,9,2,3,10,11] [0,1,2,3,6,8,9,10,11] table48, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,8,9,2,3,10,11] [0,1,2,3,6,8,9,10,11] [6] table48 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound49

theorem bound47 : ∀ f ∈ assignSearch step finish [6,7,0,1,8,9,2,3,10,11] [0,1,2,3,5,6,8,9,10,11] table47, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,1,8,9,2,3,10,11] [0,1,2,3,5,6,8,9,10,11] [5,6] table47 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound48
    · exact bound52

theorem bound46 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [0,1,2,3,8,10,11] table46, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [0,1,2,3,8,10,11] [] table46 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound45 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [1,2,3,8,9,10,11] table45, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [1,2,3,8,9,10,11] [] table45 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound44 : ∀ f ∈ assignSearch step finish [0,1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] table44, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] [0,9] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound45
    · exact bound46

theorem bound43 : ∀ f ∈ assignSearch step finish [7,0,1,8,9,2,3,10,11] [0,1,2,3,5,8,9,10,11] table43, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,8,9,2,3,10,11] [0,1,2,3,5,8,9,10,11] [5] table43 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound44

theorem bound42 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [0,1,2,3,8,10,11] table42, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [0,1,2,3,8,10,11] [] table42 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound41 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [1,2,3,8,9,10,11] table41, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [1,2,3,8,9,10,11] [] table41 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound40 : ∀ f ∈ assignSearch step finish [0,1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] [0,9] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound41
    · exact bound42

theorem bound39 : ∀ f ∈ assignSearch step finish [7,0,1,8,9,2,3,10,11] [0,1,2,3,7,8,9,10,11] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,8,9,2,3,10,11] [0,1,2,3,7,8,9,10,11] [7] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound40

theorem bound38 : ∀ f ∈ assignSearch step finish [6,7,0,1,8,9,2,3,10,11] [0,1,2,3,5,7,8,9,10,11] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,1,8,9,2,3,10,11] [0,1,2,3,5,7,8,9,10,11] [5,7] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound39
    · exact bound43

theorem bound37 : ∀ f ∈ assignSearch step finish [] [] table37, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound36 : ∀ f ∈ assignSearch step finish [11] [3] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound37

theorem bound35 : ∀ f ∈ assignSearch step finish [10,11] [2,3] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,3] [2] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound36

theorem bound34 : ∀ f ∈ assignSearch step finish [3,10,11] [2,3,11] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [10,11] [2,3,11] [11] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound35

theorem bound33 : ∀ f ∈ assignSearch step finish [2,3,10,11] [2,3,10,11] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,10,11] [2,3,10,11] [10] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [9,2,3,10,11] [0,2,3,10,11] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [2,3,10,11] [0,2,3,10,11] [0] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound33

theorem bound31 : ∀ f ∈ assignSearch step finish [8,9,2,3,10,11] [0,1,2,3,10,11] table31, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,2,3,10,11] [0,1,2,3,10,11] [1] table31 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound32

theorem bound30 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [0,1,2,3,8,10,11] table30, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [0,1,2,3,8,10,11] [8] table30 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound31

theorem bound29 : ∀ f ∈ assignSearch step finish [] [] table29, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound28 : ∀ f ∈ assignSearch step finish [11] [10] table28, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table28 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound29

theorem bound27 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table27, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table27 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound28

theorem bound26 : ∀ f ∈ assignSearch step finish [3,10,11] [2,10,11] table26, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [10,11] [2,10,11] [2] table26 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound27

theorem bound25 : ∀ f ∈ assignSearch step finish [2,3,10,11] [2,3,10,11] table25, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,10,11] [2,3,10,11] [3] table25 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound26

theorem bound24 : ∀ f ∈ assignSearch step finish [9,2,3,10,11] [2,3,9,10,11] table24, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [2,3,10,11] [2,3,9,10,11] [9] table24 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound25

theorem bound23 : ∀ f ∈ assignSearch step finish [8,9,2,3,10,11] [2,3,8,9,10,11] table23, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,2,3,10,11] [2,3,8,9,10,11] [8] table23 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound24

theorem bound22 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [1,2,3,8,9,10,11] table22, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [1,2,3,8,9,10,11] [1] table22 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound23

theorem bound21 : ∀ f ∈ assignSearch step finish [0,1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] table21, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] [0,9] table21 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound22
    · exact bound30

theorem bound20 : ∀ f ∈ assignSearch step finish [7,0,1,8,9,2,3,10,11] [0,1,2,3,6,8,9,10,11] table20, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,8,9,2,3,10,11] [0,1,2,3,6,8,9,10,11] [6] table20 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound21

theorem bound19 : ∀ f ∈ assignSearch step finish [] [] table19, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound18 : ∀ f ∈ assignSearch step finish [11] [2] table18, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table18 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound19

theorem bound17 : ∀ f ∈ assignSearch step finish [10,11] [2,3] table17, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,3] [3] table17 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound18

theorem bound16 : ∀ f ∈ assignSearch step finish [3,10,11] [2,3,10] table16, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [10,11] [2,3,10] [10] table16 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound17

theorem bound15 : ∀ f ∈ assignSearch step finish [2,3,10,11] [2,3,10,11] table15, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,10,11] [2,3,10,11] [11] table15 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound16

theorem bound14 : ∀ f ∈ assignSearch step finish [9,2,3,10,11] [0,2,3,10,11] table14, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [2,3,10,11] [0,2,3,10,11] [0] table14 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound15

theorem bound13 : ∀ f ∈ assignSearch step finish [8,9,2,3,10,11] [0,1,2,3,10,11] table13, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,2,3,10,11] [0,1,2,3,10,11] [1] table13 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound14

theorem bound12 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [0,1,2,3,8,10,11] table12, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [0,1,2,3,8,10,11] [8] table12 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound13

theorem bound11 : ∀ f ∈ assignSearch step finish [] [] table11, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound10 : ∀ f ∈ assignSearch step finish [11] [11] table10, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table10 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound11

theorem bound9 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table9, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table9 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound10

theorem bound8 : ∀ f ∈ assignSearch step finish [3,10,11] [3,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [10,11] [3,10,11] [3] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound9

theorem bound7 : ∀ f ∈ assignSearch step finish [2,3,10,11] [2,3,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,10,11] [2,3,10,11] [2] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound8

theorem bound6 : ∀ f ∈ assignSearch step finish [9,2,3,10,11] [2,3,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [2,3,10,11] [2,3,9,10,11] [9] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound7

theorem bound5 : ∀ f ∈ assignSearch step finish [8,9,2,3,10,11] [2,3,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,2,3,10,11] [2,3,8,9,10,11] [8] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [1,8,9,2,3,10,11] [1,2,3,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [8,9,2,3,10,11] [1,2,3,8,9,10,11] [1] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound5

theorem bound3 : ∀ f ∈ assignSearch step finish [0,1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,8,9,2,3,10,11] [0,1,2,3,8,9,10,11] [0,9] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound4
    · exact bound12

theorem bound2 : ∀ f ∈ assignSearch step finish [7,0,1,8,9,2,3,10,11] [0,1,2,3,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [0,1,8,9,2,3,10,11] [0,1,2,3,7,8,9,10,11] [7] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound3

theorem bound1 : ∀ f ∈ assignSearch step finish [6,7,0,1,8,9,2,3,10,11] [0,1,2,3,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,0,1,8,9,2,3,10,11] [0,1,2,3,6,7,8,9,10,11] [6,7] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound2
    · exact bound20

theorem bound0 : ∀ f ∈ assignSearch step finish [5,6,7,0,1,8,9,2,3,10,11] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,0,1,8,9,2,3,10,11] [0,1,2,3,5,6,7,8,9,10,11] [5,6,7] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound1
    · exact bound38
    · exact bound47

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (4 : Point) = hole)
    (hs : transport e (link link57 4) = link link57 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link57 link57 hole 4 4 [5,6,7,0,1,8,9,2,3,10,11]
    (by decide +kernel) (by decide +kernel) Data56.matrix Data56.matrix
    Data56.matrix_checked Data56.matrix_checked maps bound0 e he hc hs

def validMap (f : Point → Point) : Bool := decide (GoodMap link57 link57 hole 4 hole 4 f)
theorem valid0 : (((maps.drop 0).take 16).all validMap) = true := by decide +kernel
theorem all_valid : maps.all validMap = true := by
  have hsplit : maps = ((maps.drop 0).take 16) := by rfl
  rw [hsplit]
  exact valid0
theorem every_listed_map_valid : ∀ f ∈ maps, GoodMap link57 link57 hole 4 hole 4 f := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp all_valid) f hf)
end C13.Enumeration.Canonical.Pair56_56
