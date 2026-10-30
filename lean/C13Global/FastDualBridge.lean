import C13Global.DualBridge
import C13Global.FastDual
namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem fast_dual_actual_obstruction (K : Family Point) (root : List Code)
    (binding : decodeSource root = K) (alphabets : List Mask)
    (halph : AlphabetComplete K alphabets) (hnon : NonincidentComplete alphabets)
    (points : List Point) (columns : List Code) (rows : List LinearRow) (bound : Int)
    (hpoints : ∀ q ∈ points, q ≠ hole)
    (column_mask : listMask columns = restrictMask universeMask alphabets points)
    (checked : fastLeafCheck columns root K points.toFinset rows bound = true)
    (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (hmin : ∀ q ∈ points.toFinset, degree F q = 15)
    (hcard : (outside F hole).card ≤ 14) : False :=
  dual_actual_obstruction K alphabets halph hnon points columns rows bound hpoints column_mask
    (fastLeafCheck_sound columns root K binding points.toFinset rows bound checked)
    hclass F hcover hroot hmin hcard
end C13.Global
