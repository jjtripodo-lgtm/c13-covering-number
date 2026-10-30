import C13Enumeration.Template6.Part044
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound703 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table703, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [9] table703 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound704

theorem bound702 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,7,9] table702, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,7,9] [7] table702 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound703

theorem bound701 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,4,7,9] table701, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,4,7,9] [4] table701 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound702

theorem bound700 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table700, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [5] table700 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound701

theorem bound699 : ∀ f ∈ assignSearch step finish [] [] table699, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound698 : ∀ f ∈ assignSearch step finish [11] [1] table698, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table698 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound699

theorem bound697 : ∀ f ∈ assignSearch step finish [9,11] [1,8] table697, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,8] [8] table697 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound698

theorem bound696 : ∀ f ∈ assignSearch step finish [8,9,11] [1,8,9] table696, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,8,9] [9] table696 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound697

theorem bound695 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,7,8,9] table695, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,7,8,9] [7] table695 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound696

theorem bound694 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,4,7,8,9] table694, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,4,7,8,9] [4] table694 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound695

theorem bound693 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,4,5,7,8,9] table693, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,4,5,7,8,9] [5] table693 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound694

theorem bound692 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,4,5,7,8,9] table692, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,4,5,7,8,9] [2,8] table692 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound693
    · exact bound700

theorem bound691 : ∀ f ∈ assignSearch step finish [] [] table691, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound690 : ∀ f ∈ assignSearch step finish [11] [1] table690, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table690 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound691

theorem bound689 : ∀ f ∈ assignSearch step finish [9,11] [1,3] table689, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,3] [3] table689 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound690

theorem bound688 : ∀ f ∈ assignSearch step finish [8,9,11] [1,3,8] table688, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,3,8] [8] table688 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound689
end C13.Enumeration.Template6
