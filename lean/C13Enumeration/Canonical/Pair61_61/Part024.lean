import C13Enumeration.Canonical.Pair61_61.Part025
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound799 : ∀ f ∈ assignSearch step finish [] [] table799, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound798 : ∀ f ∈ assignSearch step finish [11] [3] table798, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table798 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound799

theorem bound797 : ∀ f ∈ assignSearch step finish [10,11] [3,7] table797, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,7] [7] table797 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound798

theorem bound796 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,7] table796, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,7] [6] table796 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound797

theorem bound795 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,6,7,11] table795, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,6,7,11] [11] table795 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound796

theorem bound794 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,6,7,11] table794, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,6,7,11] [0] table794 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound795

theorem bound793 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,6,7,11] table793, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,6,7,11] [1,6] table793 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound794
    · exact bound800

theorem bound792 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,6,7,8,11] table792, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,6,7,8,11] [8] table792 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound793

theorem bound791 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,7,8,11] table791, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,7,8,11] [2] table791 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound792

theorem bound790 : ∀ f ∈ assignSearch step finish [] [] table790, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound789 : ∀ f ∈ assignSearch step finish [11] [2] table789, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table789 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound790

theorem bound788 : ∀ f ∈ assignSearch step finish [10,11] [2,9] table788, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,9] [9] table788 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound789

theorem bound787 : ∀ f ∈ assignSearch step finish [9,10,11] [2,6,9] table787, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,6,9] [6] table787 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound788

theorem bound786 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,6,9] table786, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,6,9] [0] table786 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound787

theorem bound785 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,6,9,11] table785, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,6,9,11] [11] table785 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound786

theorem bound784 : ∀ f ∈ assignSearch step finish [] [] table784, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound783 : ∀ f ∈ assignSearch step finish [11] [0] table783, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table783 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound784

theorem bound782 : ∀ f ∈ assignSearch step finish [10,11] [0,11] table782, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,11] [11] table782 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound783

theorem bound781 : ∀ f ∈ assignSearch step finish [9,10,11] [0,8,11] table781, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,8,11] [8] table781 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound782

theorem bound780 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,8,11] table780, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,8,11] [2] table780 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound781

theorem bound779 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,8,9,11] table779, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,8,9,11] [9] table779 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound780

theorem bound778 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,6,8,9,11] table778, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,6,8,9,11] [6,8] table778 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound779
    · exact bound785

theorem bound777 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,8,9,11] table777, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,8,9,11] [1] table777 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound778

theorem bound776 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,6,8,9,11] table776, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,6,8,9,11] [3] table776 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound777

theorem bound775 : ∀ f ∈ assignSearch step finish [] [] table775, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound774 : ∀ f ∈ assignSearch step finish [11] [9] table774, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table774 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound775

theorem bound773 : ∀ f ∈ assignSearch step finish [10,11] [2,9] table773, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,9] [2] table773 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound774

theorem bound772 : ∀ f ∈ assignSearch step finish [9,10,11] [2,6,9] table772, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,6,9] [6] table772 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound773

theorem bound771 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,6,9,11] table771, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,6,9,11] [11] table771 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound772

theorem bound770 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,6,9,11] table770, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,6,9,11] [0] table770 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound771

theorem bound769 : ∀ f ∈ assignSearch step finish [] [] table769, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound768 : ∀ f ∈ assignSearch step finish [11] [11] table768, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table768 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound769
end C13.Enumeration.Canonical.Pair61_61
