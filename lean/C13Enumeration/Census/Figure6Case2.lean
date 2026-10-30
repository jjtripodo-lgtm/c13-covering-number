import C13Enumeration.Census.Figure6Case2Leaf2
import C13Enumeration.Census.Figure6Case2Leaf3
import C13Enumeration.Census.Figure6Case2Leaf4
namespace C13.Enumeration.Census.Figure6Case2
set_option Elab.async false
set_option maxRecDepth 10000
theorem tree_checked : tree.check columns C13.SourceData.figure6 points [] = true := by
  simp only [tree,CoverTree.check,valid2,cert2,valid3,cert3,valid4,cert4,Bool.and_self]
end C13.Enumeration.Census.Figure6Case2
