import C13Enumeration.Census.CoverRows
namespace C13.Enumeration.Census.Figure6Alphabets
open C13.Checker.RawSupport C13.SourceData C13.Enumeration.Canonical
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def alphabet00 : List Code := [1243, 1691, 1747, 1739, 1183, 1239, 1245, 1687, 1693, 1749, 1741, 3227, 3283, 2267, 3731, 2715, 2771, 2763, 3223, 2207, 3229, 2263, 3285, 2269, 2711, 3733, 2717, 2773, 2765, 1211, 1267, 1259, 1715, 1707, 1763, 1207, 1213, 1199, 1269, 1255, 1261, 1717, 1703, 1709, 1765, 3251, 2235, 3243, 2291, 3299, 2283, 2739, 3747, 2731, 2787, 2231, 3253, 3239, 2237, 2223, 3245, 2293, 2279, 3301, 2285, 2741, 2727, 3749, 2733, 2789, 1435, 1491, 1371, 1939, 1819, 1875, 1867, 1431, 1437, 1311, 1493, 1367, 1373, 1941, 1815, 1821, 1877, 1869, 3475, 2459, 3355, 2515, 3411, 2395, 2963, 3859, 2843, 2899, 2891, 2455, 3477, 3351, 2461, 2335, 3357, 2517, 2391, 3413, 2397, 2965, 2839, 3861, 2845, 2901, 2893, 1459, 1339, 1451, 1395, 1507, 1387, 1843, 1955, 1835, 1891, 1461, 1335, 1447, 1341, 1453, 1327, 1397, 1509, 1383, 1389, 1845, 1957, 1831, 1837, 1893, 2483, 3379, 3491, 2363, 2475, 3371, 2419, 2531, 3427, 2411, 2867, 2979, 3875, 2859, 2915, 2485, 2359, 2471, 3381, 3493, 3367, 2365, 2477, 2351, 3373, 2421, 2533, 2407, 3429, 2413, 2869, 2981, 2855, 3877, 2861, 2917]
theorem checked00 : (relabelDomain (domains 6) Normalizers.Source68.normalizer00.symm 0).alphabet = alphabet00 := by decide +kernel
def alphabet01 : List Code := [731, 1627, 1747, 1739, 607, 727, 734, 1623, 1630, 1750, 1742, 2651, 2771, 2267, 3667, 3163, 3283, 3275, 2647, 2143, 2654, 2263, 2774, 2270, 3159, 3670, 3166, 3286, 3278, 635, 755, 747, 1651, 1643, 1763, 631, 638, 623, 758, 743, 750, 1654, 1639, 1646, 1766, 2675, 2171, 2667, 2291, 2787, 2283, 3187, 3683, 3179, 3299, 2167, 2678, 2663, 2174, 2159, 2670, 2294, 2279, 2790, 2286, 3190, 3175, 3686, 3182, 3302, 859, 979, 923, 1875, 1819, 1939, 1931, 855, 862, 799, 982, 919, 926, 1878, 1815, 1822, 1942, 1934, 2899, 2395, 2843, 2515, 2963, 2459, 3411, 3859, 3355, 3475, 3467, 2391, 2902, 2839, 2398, 2335, 2846, 2518, 2455, 2966, 2462, 3414, 3351, 3862, 3358, 3478, 3470, 883, 827, 875, 947, 995, 939, 1843, 1891, 1835, 1955, 886, 823, 871, 830, 878, 815, 950, 998, 935, 942, 1846, 1894, 1831, 1838, 1958, 2419, 2867, 2915, 2363, 2411, 2859, 2483, 2531, 2979, 2475, 3379, 3427, 3875, 3371, 3491, 2422, 2359, 2407, 2870, 2918, 2855, 2366, 2414, 2351, 2862, 2486, 2534, 2471, 2982, 2478, 3382, 3430, 3367, 3878, 3374, 3494]
theorem checked01 : (relabelDomain (domains 6) Normalizers.Source68.normalizer01.symm 1).alphabet = alphabet01 := by decide +kernel
def alphabet02 : List Code := [861, 2653, 2901, 2893, 607, 855, 862, 2647, 2654, 2902, 2894, 1629, 1877, 1373, 3669, 3165, 3413, 3405, 1623, 1119, 1630, 1367, 1878, 1374, 3159, 3670, 3166, 3414, 3406, 637, 885, 877, 2677, 2669, 2917, 631, 638, 623, 886, 871, 878, 2678, 2663, 2670, 2918, 1653, 1149, 1645, 1397, 1893, 1389, 3189, 3685, 3181, 3429, 1143, 1654, 1639, 1150, 1135, 1646, 1398, 1383, 1894, 1390, 3190, 3175, 3686, 3182, 3430, 733, 981, 925, 2773, 2717, 2965, 2957, 727, 734, 671, 982, 919, 926, 2774, 2711, 2718, 2966, 2958, 1749, 1245, 1693, 1493, 1941, 1437, 3285, 3733, 3229, 3477, 3469, 1239, 1750, 1687, 1246, 1183, 1694, 1494, 1431, 1942, 1438, 3286, 3223, 3734, 3230, 3478, 3470, 757, 701, 749, 949, 997, 941, 2741, 2789, 2733, 2981, 758, 695, 743, 702, 750, 687, 950, 998, 935, 942, 2742, 2790, 2727, 2734, 2982, 1269, 1717, 1765, 1213, 1261, 1709, 1461, 1509, 1957, 1453, 3253, 3301, 3749, 3245, 3493, 1270, 1207, 1255, 1718, 1766, 1703, 1214, 1262, 1199, 1710, 1462, 1510, 1447, 1958, 1454, 3254, 3302, 3239, 3750, 3246, 3494]
theorem checked02 : (relabelDomain (domains 6) Normalizers.Source68.normalizer02.symm 2).alphabet = alphabet02 := by decide +kernel
def alphabet03 : List Code := [475, 477, 478, 463, 985, 986, 923, 988, 925, 926, 911, 1497, 1498, 1371, 1500, 1373, 1374, 1359, 2008, 1881, 1945, 1882, 1946, 1819, 1884, 1948, 1821, 1822, 1807, 505, 506, 491, 508, 493, 494, 1016, 953, 1001, 954, 1002, 939, 956, 1004, 941, 942, 1528, 1401, 1513, 1402, 1514, 1387, 1404, 1516, 1389, 1390, 1912, 1976, 2024, 1849, 1897, 1961, 1850, 1898, 1962, 1835, 1852, 1900, 1964, 1837, 1838, 2521, 2522, 2267, 2524, 2269, 2270, 2255, 3032, 2969, 2777, 2970, 2778, 2715, 2972, 2780, 2717, 2718, 2703, 3544, 3417, 3289, 3418, 3290, 3163, 3420, 3292, 3165, 3166, 3151, 3928, 3992, 3800, 3865, 3673, 3737, 3866, 3674, 3738, 3611, 3868, 3676, 3740, 3613, 3614, 3599, 2552, 2297, 2537, 2298, 2538, 2283, 2300, 2540, 2285, 2286, 3000, 2808, 3048, 2745, 2985, 2793, 2746, 2986, 2794, 2731, 2748, 2988, 2796, 2733, 2734, 3448, 3320, 3560, 3193, 3433, 3305, 3194, 3434, 3306, 3179, 3196, 3436, 3308, 3181, 3182, 3896, 3704, 3944, 3768, 4008, 3816, 3641, 3881, 3689, 3753, 3642, 3882, 3690, 3754, 3627, 3644, 3884, 3692, 3756, 3629, 3630]
theorem checked03 : (relabelDomain (domains 6) Normalizers.Source68.normalizer03.symm 3).alphabet = alphabet03 := by decide +kernel
def alphabet04 : List Code := [471, 1756, 2906, 3481, 3607]
theorem checked04 : (relabelDomain (domains 61) Normalizers.Source68.normalizer04.symm 4).alphabet = alphabet04 := by decide +kernel
def alphabet05 : List Code := [487, 1772, 2922, 3497, 3623]
theorem checked05 : (relabelDomain (domains 61) Normalizers.Source68.normalizer05.symm 5).alphabet = alphabet05 := by decide +kernel
def alphabet06 : List Code := [1119, 2143, 3166, 3151, 607, 1630, 1623, 2654, 2647, 3670, 3655, 351, 1374, 1373, 2398, 2397, 3420, 3405, 862, 861, 855, 1884, 1878, 1877, 2908, 2902, 2901, 3924, 3909, 127, 1150, 1135, 2174, 2159, 3182, 638, 631, 623, 1654, 1646, 1639, 2678, 2670, 2663, 3686, 382, 381, 367, 1404, 1390, 1389, 2428, 2414, 2413, 3436, 892, 886, 878, 885, 877, 871, 1908, 1900, 1894, 1893, 2932, 2924, 2918, 2917, 3940, 223, 1246, 1243, 2270, 2267, 3290, 3275, 734, 727, 731, 1750, 1754, 1747, 2774, 2778, 2771, 3794, 3779, 478, 477, 475, 1500, 1498, 1497, 2524, 2522, 2521, 3544, 3529, 988, 982, 986, 981, 985, 979, 2004, 2008, 2002, 2001, 3028, 3032, 3026, 3025, 4048, 4033, 254, 251, 239, 1274, 1262, 1259, 2298, 2286, 2283, 3306, 758, 762, 750, 755, 743, 747, 1778, 1766, 1770, 1763, 2802, 2790, 2794, 2787, 3810, 508, 506, 494, 505, 493, 491, 1528, 1516, 1514, 1513, 2552, 2540, 2538, 2537, 3560, 1012, 1016, 1004, 1010, 998, 1002, 1009, 997, 1001, 995, 2032, 2020, 2024, 2018, 2017, 3056, 3044, 3048, 3042, 3041, 4064]
theorem checked06 : (relabelDomain (domains 6) Normalizers.Source68.normalizer06.symm 6).alphabet = alphabet06 := by decide +kernel
def alphabet07 : List Code := [671, 2207, 2717, 2703, 1183, 1693, 1687, 3229, 3223, 3733, 3719, 415, 925, 926, 2461, 2462, 2972, 2958, 1437, 1438, 1431, 1948, 1941, 1942, 3484, 3477, 3478, 3988, 3974, 191, 701, 687, 2237, 2223, 2733, 1213, 1207, 1199, 1717, 1709, 1703, 3253, 3245, 3239, 3749, 445, 446, 431, 956, 941, 942, 2492, 2477, 2478, 2988, 1468, 1461, 1453, 1462, 1454, 1447, 1972, 1964, 1957, 1958, 3508, 3500, 3493, 3494, 4004, 223, 733, 731, 2269, 2267, 2777, 2763, 1245, 1239, 1243, 1749, 1753, 1747, 3285, 3289, 3283, 3793, 3779, 477, 478, 475, 988, 985, 986, 2524, 2521, 2522, 3032, 3018, 1500, 1493, 1497, 1494, 1498, 1491, 2004, 2008, 2001, 2002, 3540, 3544, 3537, 3538, 4048, 4034, 253, 251, 239, 761, 749, 747, 2297, 2285, 2283, 2793, 1269, 1273, 1261, 1267, 1255, 1259, 1777, 1765, 1769, 1763, 3313, 3301, 3305, 3299, 3809, 508, 505, 493, 506, 494, 491, 1016, 1004, 1001, 1002, 2552, 2540, 2537, 2538, 3048, 1524, 1528, 1516, 1521, 1509, 1513, 1522, 1510, 1514, 1507, 2032, 2020, 2024, 2017, 2018, 3568, 3556, 3560, 3553, 3554, 4064]
theorem checked07 : (relabelDomain (domains 6) Normalizers.Source68.normalizer07.symm 7).alphabet = alphabet07 := by decide +kernel
def alphabet08 : List Code := [799, 1311, 1819, 1807, 2335, 2843, 2839, 3355, 3351, 3859, 3847, 415, 923, 926, 1435, 1438, 1946, 1934, 2459, 2462, 2455, 2970, 2963, 2966, 3482, 3475, 3478, 3986, 3974, 319, 827, 815, 1339, 1327, 1835, 2363, 2359, 2351, 2867, 2859, 2855, 3379, 3371, 3367, 3875, 443, 446, 431, 954, 939, 942, 1466, 1451, 1454, 1962, 2490, 2483, 2475, 2486, 2478, 2471, 2994, 2986, 2979, 2982, 3506, 3498, 3491, 3494, 4002, 351, 859, 861, 1371, 1373, 1881, 1869, 2395, 2391, 2397, 2899, 2905, 2901, 3411, 3417, 3413, 3921, 3909, 475, 478, 477, 986, 985, 988, 1498, 1497, 1500, 2008, 1996, 2522, 2515, 2521, 2518, 2524, 2517, 3026, 3032, 3025, 3028, 3538, 3544, 3537, 3540, 4048, 4036, 379, 381, 367, 889, 875, 877, 1401, 1387, 1389, 1897, 2419, 2425, 2411, 2421, 2407, 2413, 2929, 2915, 2921, 2917, 3441, 3427, 3433, 3429, 3937, 506, 505, 491, 508, 494, 493, 1016, 1002, 1001, 1004, 1528, 1514, 1513, 1516, 2024, 2546, 2552, 2538, 2545, 2531, 2537, 2548, 2534, 2540, 2533, 3056, 3042, 3048, 3041, 3044, 3568, 3554, 3560, 3553, 3556, 4064]
theorem checked08 : (relabelDomain (domains 6) Normalizers.Source68.normalizer08.symm 8).alphabet = alphabet08 := by decide +kernel
def alphabet09 : List Code := [671, 799, 926, 911, 607, 734, 727, 862, 855, 982, 967, 2591, 2718, 2717, 2846, 2845, 2972, 2957, 2654, 2653, 2647, 2780, 2774, 2773, 2908, 2902, 2901, 3028, 3013, 575, 702, 687, 830, 815, 942, 638, 631, 623, 758, 750, 743, 886, 878, 871, 998, 2622, 2621, 2607, 2748, 2734, 2733, 2876, 2862, 2861, 2988, 2684, 2678, 2670, 2677, 2669, 2663, 2804, 2796, 2790, 2789, 2932, 2924, 2918, 2917, 3044, 1567, 1694, 1691, 1822, 1819, 1946, 1931, 1630, 1623, 1627, 1750, 1754, 1747, 1878, 1882, 1875, 2002, 1987, 3614, 3613, 3611, 3740, 3738, 3737, 3868, 3866, 3865, 3992, 3977, 3676, 3670, 3674, 3669, 3673, 3667, 3796, 3800, 3794, 3793, 3924, 3928, 3922, 3921, 4048, 4033, 1598, 1595, 1583, 1722, 1710, 1707, 1850, 1838, 1835, 1962, 1654, 1658, 1646, 1651, 1639, 1643, 1778, 1766, 1770, 1763, 1906, 1894, 1898, 1891, 2018, 3644, 3642, 3630, 3641, 3629, 3627, 3768, 3756, 3754, 3753, 3896, 3884, 3882, 3881, 4008, 3700, 3704, 3692, 3698, 3686, 3690, 3697, 3685, 3689, 3683, 3824, 3812, 3816, 3810, 3809, 3952, 3940, 3944, 3938, 3937, 4064]
theorem checked09 : (relabelDomain (domains 6) Normalizers.Source68.normalizer09.symm 9).alphabet = alphabet09 := by decide +kernel
def alphabet10 : List Code := [1119, 1311, 1373, 1359, 1183, 1245, 1239, 1437, 1431, 1493, 1479, 3103, 3165, 3166, 3357, 3358, 3420, 3406, 3229, 3230, 3223, 3292, 3285, 3286, 3484, 3477, 3478, 3540, 3526, 1087, 1149, 1135, 1341, 1327, 1389, 1213, 1207, 1199, 1269, 1261, 1255, 1461, 1453, 1447, 1509, 3133, 3134, 3119, 3196, 3181, 3182, 3388, 3373, 3374, 3436, 3260, 3253, 3245, 3254, 3246, 3239, 3316, 3308, 3301, 3302, 3508, 3500, 3493, 3494, 3556, 1567, 1629, 1627, 1821, 1819, 1881, 1867, 1693, 1687, 1691, 1749, 1753, 1747, 1941, 1945, 1939, 2001, 1987, 3613, 3614, 3611, 3676, 3673, 3674, 3868, 3865, 3866, 3928, 3914, 3740, 3733, 3737, 3734, 3738, 3731, 3796, 3800, 3793, 3794, 3988, 3992, 3985, 3986, 4048, 4034, 1597, 1595, 1583, 1657, 1645, 1643, 1849, 1837, 1835, 1897, 1717, 1721, 1709, 1715, 1703, 1707, 1777, 1765, 1769, 1763, 1969, 1957, 1961, 1955, 2017, 3644, 3641, 3629, 3642, 3630, 3627, 3704, 3692, 3689, 3690, 3896, 3884, 3881, 3882, 3944, 3764, 3768, 3756, 3761, 3749, 3753, 3762, 3750, 3754, 3747, 3824, 3812, 3816, 3809, 3810, 4016, 4004, 4008, 4001, 4002, 4064]
theorem checked10 : (relabelDomain (domains 6) Normalizers.Source68.normalizer10.symm 10).alphabet = alphabet10 := by decide +kernel
def alphabet11 : List Code := [2143, 2207, 2267, 2255, 2335, 2395, 2391, 2459, 2455, 2515, 2503, 3103, 3163, 3166, 3227, 3230, 3290, 3278, 3355, 3358, 3351, 3418, 3411, 3414, 3482, 3475, 3478, 3538, 3526, 2111, 2171, 2159, 2235, 2223, 2283, 2363, 2359, 2351, 2419, 2411, 2407, 2483, 2475, 2471, 2531, 3131, 3134, 3119, 3194, 3179, 3182, 3258, 3243, 3246, 3306, 3386, 3379, 3371, 3382, 3374, 3367, 3442, 3434, 3427, 3430, 3506, 3498, 3491, 3494, 3554, 2591, 2651, 2653, 2715, 2717, 2777, 2765, 2843, 2839, 2845, 2899, 2905, 2901, 2963, 2969, 2965, 3025, 3013, 3611, 3614, 3613, 3674, 3673, 3676, 3738, 3737, 3740, 3800, 3788, 3866, 3859, 3865, 3862, 3868, 3861, 3922, 3928, 3921, 3924, 3986, 3992, 3985, 3988, 4048, 4036, 2619, 2621, 2607, 2681, 2667, 2669, 2745, 2731, 2733, 2793, 2867, 2873, 2859, 2869, 2855, 2861, 2929, 2915, 2921, 2917, 2993, 2979, 2985, 2981, 3041, 3642, 3641, 3627, 3644, 3630, 3629, 3704, 3690, 3689, 3692, 3768, 3754, 3753, 3756, 3816, 3890, 3896, 3882, 3889, 3875, 3881, 3892, 3878, 3884, 3877, 3952, 3938, 3944, 3937, 3940, 4016, 4002, 4008, 4001, 4004, 4064]
theorem checked11 : (relabelDomain (domains 6) Normalizers.Source68.normalizer11.symm 11).alphabet = alphabet11 := by decide +kernel


def alphabet : C13.Point → List Code := ![alphabet00,alphabet01,alphabet02,alphabet03,alphabet04,alphabet05,alphabet06,alphabet07,alphabet08,alphabet09,alphabet10,alphabet11,[]]

theorem represented_record (r : Record templates) (P : C13.Family C13.Point)
    (hP : P ∈ C13.completeDomain catalog hole r.family hole r.center) :
    ∃ p ∈ (relabelDomain (domains r.template) r.normalizer.symm r.center).supported.domain.2,
      C13.RepresentsPencil p P := by
  exact (complete_relabelled_domain catalog hole r.family (templates r.template).family
    r.center (templates r.template).center r.center_ne r.avoids (domains r.template)
    r.normalizer r.hole_fixed r.center_image r.star_image (canonical_complete r.template)).2 P hP

theorem alphabet_complete (q : C13.Point) (hq : q ≠ hole)
    (P : C13.Family C13.Point) (hP : P ∈ C13.completeDomain catalog hole figure6 hole q)
    (B : Finset C13.Point) (hB : B ∈ P) : encodeTyped B ∈ alphabet q := by
  fin_cases q
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record00.template)
        Normalizers.Source68.normalizer00.symm 0) P
      (represented_record Normalizers.Source68.record00 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer00.symm 0).alphabet at hh
    change encodeTyped B ∈ alphabet00
    rw [checked00] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record01.template)
        Normalizers.Source68.normalizer01.symm 1) P
      (represented_record Normalizers.Source68.record01 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer01.symm 1).alphabet at hh
    change encodeTyped B ∈ alphabet01
    rw [checked01] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record02.template)
        Normalizers.Source68.normalizer02.symm 2) P
      (represented_record Normalizers.Source68.record02 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer02.symm 2).alphabet at hh
    change encodeTyped B ∈ alphabet02
    rw [checked02] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record03.template)
        Normalizers.Source68.normalizer03.symm 3) P
      (represented_record Normalizers.Source68.record03 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer03.symm 3).alphabet at hh
    change encodeTyped B ∈ alphabet03
    rw [checked03] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record04.template)
        Normalizers.Source68.normalizer04.symm 4) P
      (represented_record Normalizers.Source68.record04 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 61) Normalizers.Source68.normalizer04.symm 4).alphabet at hh
    change encodeTyped B ∈ alphabet04
    rw [checked04] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record05.template)
        Normalizers.Source68.normalizer05.symm 5) P
      (represented_record Normalizers.Source68.record05 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 61) Normalizers.Source68.normalizer05.symm 5).alphabet at hh
    change encodeTyped B ∈ alphabet05
    rw [checked05] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record06.template)
        Normalizers.Source68.normalizer06.symm 6) P
      (represented_record Normalizers.Source68.record06 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer06.symm 6).alphabet at hh
    change encodeTyped B ∈ alphabet06
    rw [checked06] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record07.template)
        Normalizers.Source68.normalizer07.symm 7) P
      (represented_record Normalizers.Source68.record07 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer07.symm 7).alphabet at hh
    change encodeTyped B ∈ alphabet07
    rw [checked07] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record08.template)
        Normalizers.Source68.normalizer08.symm 8) P
      (represented_record Normalizers.Source68.record08 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer08.symm 8).alphabet at hh
    change encodeTyped B ∈ alphabet08
    rw [checked08] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record09.template)
        Normalizers.Source68.normalizer09.symm 9) P
      (represented_record Normalizers.Source68.record09 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer09.symm 9).alphabet at hh
    change encodeTyped B ∈ alphabet09
    rw [checked09] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record10.template)
        Normalizers.Source68.normalizer10.symm 10) P
      (represented_record Normalizers.Source68.record10 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer10.symm 10).alphabet at hh
    change encodeTyped B ∈ alphabet10
    rw [checked10] at hh
    exact hh
  · have hh := represented_block_in_alphabet
      (relabelDomain (domains Normalizers.Source68.record11.template)
        Normalizers.Source68.normalizer11.symm 11) P
      (represented_record Normalizers.Source68.record11 P hP) B hB
    change encodeTyped B ∈ (relabelDomain (domains 6) Normalizers.Source68.normalizer11.symm 11).alphabet at hh
    change encodeTyped B ∈ alphabet11
    rw [checked11] at hh
    exact hh
  · exact (hq rfl).elim
end C13.Enumeration.Census.Figure6Alphabets
