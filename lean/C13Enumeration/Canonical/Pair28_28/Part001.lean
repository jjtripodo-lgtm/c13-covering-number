import C13Enumeration.Canonical.Pair28_28.Part002
namespace C13.Enumeration.Canonical.Pair28_28
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound63 : ∀ f ∈ assignSearch step finish [11] [11] table63, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table63 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound64

theorem bound62 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table62, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table62 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound63

theorem bound61 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table61, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table61 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound62

theorem bound60 : ∀ f ∈ assignSearch step finish [3,9,10,11] [3,9,10,11] table60, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [3,9,10,11] [3] table60 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound61

theorem bound59 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [2,3,9,10,11] table59, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [2,3,9,10,11] [2] table59 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound60

theorem bound58 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table58, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [1] table58 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound59

theorem bound57 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,7,9,10,11] table57, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,7,9,10,11] [7] table57 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound58

theorem bound56 : ∀ f ∈ assignSearch step finish [6,7,1,2,3,9,10,11] [1,2,3,6,7,9,10,11] table56, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,1,2,3,9,10,11] [1,2,3,6,7,9,10,11] [6,7] table56 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound57
    · exact bound65

theorem bound55 : ∀ f ∈ assignSearch step finish [5,6,7,1,2,3,9,10,11] [1,2,3,5,6,7,9,10,11] table55, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [6,7,1,2,3,9,10,11] [1,2,3,5,6,7,9,10,11] [5,6,7] table55 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact bound56
    · exact bound73
    · exact bound90

theorem bound54 : ∀ f ∈ assignSearch step finish [4,5,6,7,1,2,3,9,10,11] [0,1,2,3,5,6,7,9,10,11] table54, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,6,7,1,2,3,9,10,11] [0,1,2,3,5,6,7,9,10,11] [0] table54 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound55

theorem bound53 : ∀ f ∈ assignSearch step finish [] [] table53, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound52 : ∀ f ∈ assignSearch step finish [11] [9] table52, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table52 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound53

theorem bound51 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table51, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [10] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound52

theorem bound50 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table50, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table50 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound51

theorem bound49 : ∀ f ∈ assignSearch step finish [3,9,10,11] [1,9,10,11] table49, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [1,9,10,11] [1] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound50

theorem bound48 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [1,2,9,10,11] table48, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [1,2,9,10,11] [2] table48 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound49

theorem bound47 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table47, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [3] table47 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound48

theorem bound46 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,5,9,10,11] table46, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,5,9,10,11] [5] table46 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound47

theorem bound45 : ∀ f ∈ assignSearch step finish [] [] table45, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound44 : ∀ f ∈ assignSearch step finish [11] [10] table44, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound45

theorem bound43 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table43, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [9] table43 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound44

theorem bound42 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table42, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table42 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound43

theorem bound41 : ∀ f ∈ assignSearch step finish [3,9,10,11] [2,9,10,11] table41, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [2,9,10,11] [2] table41 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound42

theorem bound40 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [1,2,9,10,11] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [1,2,9,10,11] [1] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound41

theorem bound39 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [3] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound40

theorem bound38 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,6,9,10,11] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,6,9,10,11] [6] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound39

theorem bound37 : ∀ f ∈ assignSearch step finish [6,7,1,2,3,9,10,11] [1,2,3,5,6,9,10,11] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,1,2,3,9,10,11] [1,2,3,5,6,9,10,11] [5,6] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound38
    · exact bound46

theorem bound36 : ∀ f ∈ assignSearch step finish [] [] table36, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound35 : ∀ f ∈ assignSearch step finish [11] [9] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound36

theorem bound34 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [11] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound35

theorem bound33 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [3,9,10,11] [1,9,10,11] table32, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [1,9,10,11] [1] table32 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound33
end C13.Enumeration.Canonical.Pair28_28
