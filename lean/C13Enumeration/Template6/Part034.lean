import C13Enumeration.Template6.Part035
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound559 : ∀ f ∈ assignSearch step finish [8,9,11] [2,9,11] table559, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,9,11] [11] table559 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound560

theorem bound558 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,4,9,11] table558, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,4,9,11] [4] table558 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound559

theorem bound557 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,4,5,9,11] table557, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,4,5,9,11] [5] table557 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound558

theorem bound556 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,4,5,7,9,11] table556, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,4,5,7,9,11] [7] table556 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound557

theorem bound555 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [2,3,4,5,7,9,11] table555, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [2,3,4,5,7,9,11] [3,9] table555 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound556
    · exact bound563

theorem bound554 : ∀ f ∈ assignSearch step finish [2,3,4,5,7,8,9,11] [1,2,3,4,5,7,9,11] table554, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7,8,9,11] [1,2,3,4,5,7,9,11] [1,3,9,11] table554 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound555
    · exact bound570
    · exact bound585
    · exact bound600

theorem bound553 : ∀ f ∈ assignSearch step finish [] [] table553, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound552 : ∀ f ∈ assignSearch step finish [11] [9] table552, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table552 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound553

theorem bound551 : ∀ f ∈ assignSearch step finish [9,11] [2,9] table551, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,9] [2] table551 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound552

theorem bound550 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table550, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [1] table550 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound551

theorem bound549 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,5,9] table549, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,5,9] [5] table549 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound550

theorem bound548 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,4,5,9] table548, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,4,5,9] [4] table548 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound549

theorem bound547 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table547, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [7] table547 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound548

theorem bound546 : ∀ f ∈ assignSearch step finish [] [] table546, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound545 : ∀ f ∈ assignSearch step finish [11] [9] table545, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table545 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound546

theorem bound544 : ∀ f ∈ assignSearch step finish [9,11] [8,9] table544, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,9] [8] table544 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound545
end C13.Enumeration.Template6
