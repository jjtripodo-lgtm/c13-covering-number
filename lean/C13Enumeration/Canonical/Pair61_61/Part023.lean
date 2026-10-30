import C13Enumeration.Canonical.Pair61_61.Part024
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound767 : ∀ f ∈ assignSearch step finish [10,11] [0,11] table767, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,11] [0] table767 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound768

theorem bound766 : ∀ f ∈ assignSearch step finish [9,10,11] [0,8,11] table766, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,8,11] [8] table766 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound767

theorem bound765 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,8,9,11] table765, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,8,9,11] [9] table765 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound766

theorem bound764 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,8,9,11] table764, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,8,9,11] [2] table764 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound765

theorem bound763 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,6,8,9,11] table763, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,6,8,9,11] [6,8] table763 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound764
    · exact bound770

theorem bound762 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,8,9,11] table762, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,8,9,11] [1] table762 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound763

theorem bound761 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,9,11] table761, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,8,9,11] [7] table761 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound762

theorem bound760 : ∀ f ∈ assignSearch step finish [] [] table760, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound759 : ∀ f ∈ assignSearch step finish [11] [0] table759, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table759 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound760

theorem bound758 : ∀ f ∈ assignSearch step finish [10,11] [0,11] table758, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,11] [11] table758 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound759

theorem bound757 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,11] table757, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,11] [1] table757 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound758

theorem bound756 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,7,11] table756, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,7,11] [7] table756 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound757

theorem bound755 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,7,11] table755, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,7,11] [3] table755 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound756

theorem bound754 : ∀ f ∈ assignSearch step finish [] [] table754, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound753 : ∀ f ∈ assignSearch step finish [11] [7] table753, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table753 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound754

theorem bound752 : ∀ f ∈ assignSearch step finish [10,11] [3,7] table752, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,7] [3] table752 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound753

theorem bound751 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,7] table751, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,7] [6] table751 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound752

theorem bound750 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,6,7] table750, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,6,7] [0] table750 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound751

theorem bound749 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,6,7,11] table749, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,6,7,11] [11] table749 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound750

theorem bound748 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,6,7,11] table748, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,6,7,11] [1,6] table748 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound749
    · exact bound755

theorem bound747 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,6,7,8,11] table747, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,6,7,8,11] [8] table747 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound748

theorem bound746 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,6,7,8,9,11] table746, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,6,7,8,9,11] [9] table746 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound747

theorem bound745 : ∀ f ∈ assignSearch step finish [] [] table745, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound744 : ∀ f ∈ assignSearch step finish [11] [2] table744, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table744 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound745

theorem bound743 : ∀ f ∈ assignSearch step finish [10,11] [2,9] table743, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,9] [9] table743 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound744

theorem bound742 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,9] table742, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,9] [1] table742 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound743

theorem bound741 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,7,9] table741, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,7,9] [7] table741 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound742

theorem bound740 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,7,9] table740, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,7,9] [3] table740 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound741

theorem bound739 : ∀ f ∈ assignSearch step finish [] [] table739, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound738 : ∀ f ∈ assignSearch step finish [11] [7] table738, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table738 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound739

theorem bound737 : ∀ f ∈ assignSearch step finish [10,11] [3,7] table737, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,7] [3] table737 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound738

theorem bound736 : ∀ f ∈ assignSearch step finish [9,10,11] [3,7,8] table736, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,7,8] [8] table736 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound737
end C13.Enumeration.Canonical.Pair61_61
