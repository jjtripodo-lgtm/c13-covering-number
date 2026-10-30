import C13Enumeration.Template6.Part034
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound543 : ∀ f ∈ assignSearch step finish [8,9,11] [1,8,9] table543, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,8,9] [1] table543 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound544

theorem bound542 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,5,8,9] table542, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,5,8,9] [5] table542 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound543

theorem bound541 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,4,5,8,9] table541, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,4,5,8,9] [4] table541 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound542

theorem bound540 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,4,5,7,8,9] table540, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,4,5,7,8,9] [7] table540 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound541

theorem bound539 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,4,5,7,8,9] table539, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,4,5,7,8,9] [2,8] table539 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound540
    · exact bound547

theorem bound538 : ∀ f ∈ assignSearch step finish [] [] table538, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound537 : ∀ f ∈ assignSearch step finish [11] [9] table537, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table537 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound538

theorem bound536 : ∀ f ∈ assignSearch step finish [9,11] [1,9] table536, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,9] [1] table536 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound537

theorem bound535 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table535, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [2] table535 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound536

theorem bound534 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,5,9] table534, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,5,9] [5] table534 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound535

theorem bound533 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,5,7,9] table533, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,5,7,9] [7] table533 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound534

theorem bound532 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table532, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [4] table532 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound533

theorem bound531 : ∀ f ∈ assignSearch step finish [] [] table531, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound530 : ∀ f ∈ assignSearch step finish [11] [9] table530, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table530 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound531

theorem bound529 : ∀ f ∈ assignSearch step finish [9,11] [9,11] table529, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [9,11] [11] table529 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound530

theorem bound528 : ∀ f ∈ assignSearch step finish [8,9,11] [2,9,11] table528, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,9,11] [2] table528 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound529
end C13.Enumeration.Template6
