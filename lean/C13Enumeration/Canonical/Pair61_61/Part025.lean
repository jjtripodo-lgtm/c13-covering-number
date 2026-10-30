import C13Enumeration.Canonical.Pair61_61.Part026
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound831 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,8,9] table831, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,8,9] [3] table831 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound832

theorem bound830 : ∀ f ∈ assignSearch step finish [] [] table830, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound829 : ∀ f ∈ assignSearch step finish [11] [8] table829, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table829 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound830

theorem bound828 : ∀ f ∈ assignSearch step finish [10,11] [3,8] table828, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,8] [3] table828 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound829

theorem bound827 : ∀ f ∈ assignSearch step finish [9,10,11] [3,7,8] table827, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,7,8] [7] table827 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound828

theorem bound826 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,7,8] table826, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,7,8] [1] table826 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound827

theorem bound825 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,7,8,9] table825, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,7,8,9] [9] table825 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound826

theorem bound824 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,7,8,9] table824, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,7,8,9] [2,7] table824 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound825
    · exact bound831

theorem bound823 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,7,8,9] table823, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,7,8,9] [6] table823 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound824

theorem bound822 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,7,8,9,10] table822, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,7,8,9,10] [10] table822 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound823

theorem bound821 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9,10] table821, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9,10] [0,1,3,8,9,10] table821 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound822
    · exact bound837
    · exact bound852
    · exact bound867
    · exact bound882
    · exact bound897

theorem bound820 : ∀ f ∈ assignSearch step finish [] [] table820, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound819 : ∀ f ∈ assignSearch step finish [11] [9] table819, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table819 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound820

theorem bound818 : ∀ f ∈ assignSearch step finish [10,11] [2,9] table818, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,9] [2] table818 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound819

theorem bound817 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,9] table817, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,9] [1] table817 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound818

theorem bound816 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,3,9] table816, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,3,9] [3] table816 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound817

theorem bound815 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,7,9] table815, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,7,9] [7] table815 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound816

theorem bound814 : ∀ f ∈ assignSearch step finish [] [] table814, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound813 : ∀ f ∈ assignSearch step finish [11] [3] table813, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table813 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound814

theorem bound812 : ∀ f ∈ assignSearch step finish [10,11] [3,7] table812, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,7] [7] table812 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound813

theorem bound811 : ∀ f ∈ assignSearch step finish [9,10,11] [3,7,8] table811, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,7,8] [8] table811 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound812

theorem bound810 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,7,8,9] table810, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,7,8,9] [9] table810 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound811

theorem bound809 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,7,8,9] table809, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,7,8,9] [2] table809 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound810

theorem bound808 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,7,8,9] table808, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,7,8,9] [1,8] table808 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound809
    · exact bound815

theorem bound807 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,7,8,9] table807, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,7,8,9] [6] table807 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound808

theorem bound806 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9] table806, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,7,8,9] [0] table806 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound807

theorem bound805 : ∀ f ∈ assignSearch step finish [] [] table805, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound804 : ∀ f ∈ assignSearch step finish [11] [11] table804, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table804 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound805

theorem bound803 : ∀ f ∈ assignSearch step finish [10,11] [0,11] table803, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,11] [0] table803 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound804

theorem bound802 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,11] table802, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,11] [1] table802 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound803

theorem bound801 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,3,11] table801, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,3,11] [3] table801 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound802

theorem bound800 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,7,11] table800, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,7,11] [7] table800 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound801
end C13.Enumeration.Canonical.Pair61_61
