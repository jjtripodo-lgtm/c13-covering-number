import C13Enumeration.Template6.Part038
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound607 : ∀ f ∈ assignSearch step finish [] [] table607, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound606 : ∀ f ∈ assignSearch step finish [11] [2] table606, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table606 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound607

theorem bound605 : ∀ f ∈ assignSearch step finish [9,11] [2,9] table605, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,9] [9] table605 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound606

theorem bound604 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table604, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [1] table604 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound605

theorem bound603 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,4,9] table603, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,4,9] [4] table603 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound604

theorem bound602 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,4,5,9] table602, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,4,5,9] [5] table602 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound603

theorem bound601 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table601, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [7] table601 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound602

theorem bound600 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,3,4,5,7,9] table600, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,3,4,5,7,9] [3,9] table600 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound601
    · exact bound608

theorem bound599 : ∀ f ∈ assignSearch step finish [] [] table599, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound598 : ∀ f ∈ assignSearch step finish [11] [2] table598, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table598 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound599

theorem bound597 : ∀ f ∈ assignSearch step finish [9,11] [1,2] table597, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,2] [1] table597 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound598

theorem bound596 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,3] table596, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,3] [3] table596 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound597

theorem bound595 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,3,4] table595, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,3,4] [4] table595 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound596

theorem bound594 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,3,4,7] table594, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,3,4,7] [7] table594 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound595

theorem bound593 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,3,4,5,7] table593, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,3,4,5,7] [5] table593 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound594

theorem bound592 : ∀ f ∈ assignSearch step finish [] [] table592, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Template6
