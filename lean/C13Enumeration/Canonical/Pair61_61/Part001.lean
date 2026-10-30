import C13Enumeration.Canonical.Pair61_61.Part002
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound63 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,7,8,9,11] table63, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,7,8,9,11] [11] table63 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound64

theorem bound62 : ∀ f ∈ assignSearch step finish [] [] table62, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound61 : ∀ f ∈ assignSearch step finish [11] [11] table61, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table61 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound62

theorem bound60 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table60, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [10] table60 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound61

theorem bound59 : ∀ f ∈ assignSearch step finish [9,10,11] [3,10,11] table59, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,10,11] [3] table59 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound60

theorem bound58 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,10,11] table58, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,10,11] [1] table58 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound59

theorem bound57 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,10,11] table57, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,10,11] [2] table57 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound58

theorem bound56 : ∀ f ∈ assignSearch step finish [] [] table56, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound55 : ∀ f ∈ assignSearch step finish [11] [1] table55, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table55 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound56

theorem bound54 : ∀ f ∈ assignSearch step finish [10,11] [1,2] table54, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,2] [2] table54 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound55

theorem bound53 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,6] table53, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,6] [6] table53 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound54

theorem bound52 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,6,11] table52, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,6,11] [11] table52 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound53

theorem bound51 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,6,10,11] table51, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,6,10,11] [10] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound52

theorem bound50 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,6,10,11] table50, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,6,10,11] [3,6] table50 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound51
    · exact bound57

theorem bound49 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,9,10,11] table49, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,9,10,11] [9] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound50

theorem bound48 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,7,9,10,11] table48, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,7,9,10,11] [7] table48 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound49

theorem bound47 : ∀ f ∈ assignSearch step finish [] [] table47, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound46 : ∀ f ∈ assignSearch step finish [11] [10] table46, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table46 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound47

theorem bound45 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table45, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table45 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound46

theorem bound44 : ∀ f ∈ assignSearch step finish [9,10,11] [3,10,11] table44, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,10,11] [3] table44 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound45

theorem bound43 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,10,11] table43, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,10,11] [2] table43 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound44

theorem bound42 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,10,11] table42, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,10,11] [1] table42 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound43

theorem bound41 : ∀ f ∈ assignSearch step finish [] [] table41, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound40 : ∀ f ∈ assignSearch step finish [11] [2] table40, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table40 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound41

theorem bound39 : ∀ f ∈ assignSearch step finish [10,11] [1,2] table39, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,2] [1] table39 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound40

theorem bound38 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,6] table38, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,6] [6] table38 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound39

theorem bound37 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,6,10] table37, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,6,10] [10] table37 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound38

theorem bound36 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,6,10,11] table36, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,6,10,11] [11] table36 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound37

theorem bound35 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,6,10,11] table35, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,6,10,11] [3,6] table35 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound36
    · exact bound42

theorem bound34 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,9,10,11] table34, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,9,10,11] [9] table34 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound35

theorem bound33 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,8,9,10,11] table33, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,8,9,10,11] [8] table33 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound34

theorem bound32 : ∀ f ∈ assignSearch step finish [] [] table32, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Canonical.Pair61_61
