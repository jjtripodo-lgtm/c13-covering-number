import C13Enumeration.Template6.Part004
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound63 : ∀ f ∈ assignSearch step finish [] [] table63, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound62 : ∀ f ∈ assignSearch step finish [11] [11] table62, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table62 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound63

theorem bound61 : ∀ f ∈ assignSearch step finish [9,11] [2,11] table61, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,11] [2] table61 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound62

theorem bound60 : ∀ f ∈ assignSearch step finish [8,9,11] [2,3,11] table60, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,3,11] [3] table60 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound61

theorem bound59 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,3,7,11] table59, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,3,7,11] [7] table59 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound60

theorem bound58 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,3,4,7,11] table58, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,3,4,7,11] [4] table58 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound59

theorem bound57 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,3,4,5,7,11] table57, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,3,4,5,7,11] [5] table57 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound58

theorem bound56 : ∀ f ∈ assignSearch step finish [] [] table56, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound55 : ∀ f ∈ assignSearch step finish [11] [11] table55, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table55 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound56

theorem bound54 : ∀ f ∈ assignSearch step finish [9,11] [8,11] table54, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,11] [8] table54 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound55

theorem bound53 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table53, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [3] table53 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound54

theorem bound52 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,7,8,11] table52, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,7,8,11] [7] table52 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound53

theorem bound51 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,4,7,8,11] table51, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,4,7,8,11] [4] table51 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound52

theorem bound50 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table50, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [5] table50 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound51

theorem bound49 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [2,3,4,5,7,8,11] table49, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [2,3,4,5,7,8,11] [2,8] table49 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound50
    · exact bound57

theorem bound48 : ∀ f ∈ assignSearch step finish [] [] table48, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Template6
