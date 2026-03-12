
# Problem Progress

This document details progress over all and each of the TIP
problems.

## Overview

 Problem file                 | File   | Additional lemmas | Verification time / Notes
------------------------------|--------|-------------------|---------------------------
 PairUnpair.smt2              | p4.rs  | 12                | 2.29s
 Select.smt2                  | p5.rs  | 0                 | 0.11s
 append_inj_1.smt2            | p8.rs  | 5                 | 0.37s
 append_inj_2.smt2            | p9.rs  | 0                 | 0.09s
 assoc.smt2                   | p10.rs |                   | Type issues
 concat_map_bind.smt2         | p11.rs | 0                 | 0.13s
 elem.smt2                    | p14.rs | 0                 | 0.07s
 elem_map.smt2                | p15.rs |                   | Sort cycles in main VC
 nat_PairUnpair.smt2          | p21.rs |                   | Type issues
 nat_Select.smt2              | p22.rs | 0                 | 0.10s
 nat_elem.smt2                | p29.rs |                   |
 nat_elem_map.smt2            | p30.rs |                   | Sort cycles in main VC
 return_1.smt2                | p43.rs | 1                 | 0.06s
 return_2.smt2                | p44.rs | 0                 | 0.04s
 weird_concat_map_bind.smt2   | p45.rs |                   | Type issues
 weird_is_normal.smt2         | p46.rs |                   |

## Problems ignored

The following files have unsupported features.

 Problem file                 | File
------------------------------|--------
 Interleave.smt2              | p1.rs
 PairEvens.smt2               | p2.rs
 PairOdds.smt2                | p3.rs
 nat_Interleave.smt2          | p18.rs
 nat_PairEvens.smt2           | p19.rs
 nat_PairOdds.smt2            | p20.rs
 nat_SelectPermutations'.smt2 | p23.rs
 SelectPermutations'.smt2     | p6.rs
 SelectPermutations.smt2      | p7.rs

Note: Right now, functions that return functions are not
allowed in ravencheck. These actually comprise the bulk of the
problems for linked lists, so I'm wary of ignoring them. For
now, I'll put them on the back burner but not write them off.
The following are those problems.

 Problem file                 | File
------------------------------|--------
 count_nub.smt2               | p12.rs
 deleteAll_count.smt2         | p13.rs
 elem_nub_l.smt2              | p16.rs
 elem_nub_r.smt2              | p17.rs
 nat_SelectPermutations.smt2  | p24.rs
 nat_count_nub.smt2           | p27.rs
 nat_deleteAll_count.smt2     | p28.rs
 nat_elem_nub_l.smt2          | p31.rs
 nat_elem_nub_r.smt2          | p32.rs
 nat_nub_nub.smt2             | p33.rs
 nat_perm_elem.smt2           | p34.rs
 nat_perm_refl.smt2           | p35.rs
 nat_perm_symm.smt2           | p36.rs
 nat_perm_trans.smt2          | p37.rs
 nub_nub.smt2                 | p38.rs
 perm_elem.smt2               | p39.rs
 perm_refl.smt2               | p40.rs
 perm_symm.smt2               | p41.rs
 perm_trans.smt2              | p42.rs

These could probably be fixed by un-Currying them. There are
other problems which have mutually recursive functions which
could probably be fixed by unrolling them to become regular
recursive.
