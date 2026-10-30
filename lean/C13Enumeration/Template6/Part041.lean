import C13Enumeration.Template6.Part042
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound671 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,3,5] table671, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,3,5] [5] table671 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound672

theorem bound670 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,3,4,5] table670, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,3,4,5] [4] table670 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound671

theorem bound669 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,3,4,5,7] table669, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,3,4,5,7] [7] table669 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound670

theorem bound668 : ∀ f ∈ assignSearch step finish [] [] table668, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound667 : ∀ f ∈ assignSearch step finish [11] [3] table667, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table667 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound668

theorem bound666 : ∀ f ∈ assignSearch step finish [9,11] [3,8] table666, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,8] [8] table666 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound667

theorem bound665 : ∀ f ∈ assignSearch step finish [8,9,11] [1,3,8] table665, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,3,8] [1] table665 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound666

theorem bound664 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,3,5,8] table664, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,3,5,8] [5] table664 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound665

theorem bound663 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,3,4,5,8] table663, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,3,4,5,8] [4] table663 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound664

theorem bound662 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,3,4,5,7,8] table662, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,3,4,5,7,8] [7] table662 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound663

theorem bound661 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,3,4,5,7,8] table661, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,3,4,5,7,8] [2,8] table661 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound662
    · exact bound669

theorem bound660 : ∀ f ∈ assignSearch step finish [] [] table660, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound659 : ∀ f ∈ assignSearch step finish [11] [3] table659, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table659 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound660

theorem bound658 : ∀ f ∈ assignSearch step finish [9,11] [1,3] table658, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,3] [1] table658 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound659

theorem bound657 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,3] table657, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,3] [2] table657 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound658

theorem bound656 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,3,5] table656, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,3,5] [5] table656 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound657
end C13.Enumeration.Template6
