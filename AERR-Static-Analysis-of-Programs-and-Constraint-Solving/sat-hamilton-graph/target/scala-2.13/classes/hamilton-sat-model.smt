(declare-const s10 Bool)
(declare-const s11 Bool)
(declare-const s12 Bool)
(declare-const s13 Bool)
(declare-const s14 Bool)
(declare-const s20 Bool)
(declare-const s21 Bool)
(declare-const s22 Bool)
(declare-const s23 Bool)
(declare-const s24 Bool)
(declare-const s30 Bool)
(declare-const s31 Bool)
(declare-const s32 Bool)
(declare-const s33 Bool)
(declare-const s34 Bool)
(declare-const s40 Bool)
(declare-const s41 Bool)
(declare-const s42 Bool)
(declare-const s43 Bool)
(declare-const s44 Bool)
(declare-const s50 Bool)
(declare-const s51 Bool)
(declare-const s52 Bool)
(declare-const s53 Bool)
(declare-const s54 Bool)
(assert (or s10 s11 s12 s13 s14))
(assert (or s20 s21 s22 s23 s24))
(assert (or s30 s31 s32 s33 s34))
(assert (or s40 s41 s42 s43 s44))
(assert (or s50 s51 s52 s53 s54))
(assert (=> s10 (and (not s11) (not s12) (not s13) (not s14))))
(assert (=> s11 (and (not s10) (not s12) (not s13) (not s14))))
(assert (=> s12 (and (not s10) (not s11) (not s13) (not s14))))
(assert (=> s13 (and (not s10) (not s11) (not s12) (not s14))))
(assert (=> s14 (and (not s10) (not s11) (not s12) (not s13))))
(assert (=> s20 (and (not s21) (not s22) (not s23) (not s24))))
(assert (=> s21 (and (not s20) (not s22) (not s23) (not s24))))
(assert (=> s22 (and (not s20) (not s21) (not s23) (not s24))))
(assert (=> s23 (and (not s20) (not s21) (not s22) (not s24))))
(assert (=> s24 (and (not s20) (not s21) (not s22) (not s23))))
(assert (=> s30 (and (not s31) (not s32) (not s33) (not s34))))
(assert (=> s31 (and (not s30) (not s32) (not s33) (not s34))))
(assert (=> s32 (and (not s30) (not s31) (not s33) (not s34))))
(assert (=> s33 (and (not s30) (not s31) (not s32) (not s34))))
(assert (=> s34 (and (not s30) (not s31) (not s32) (not s33))))
(assert (=> s40 (and (not s41) (not s42) (not s43) (not s44))))
(assert (=> s41 (and (not s40) (not s42) (not s43) (not s44))))
(assert (=> s42 (and (not s40) (not s41) (not s43) (not s44))))
(assert (=> s43 (and (not s40) (not s41) (not s42) (not s44))))
(assert (=> s44 (and (not s40) (not s41) (not s42) (not s43))))
(assert (=> s50 (and (not s51) (not s52) (not s53) (not s54))))
(assert (=> s51 (and (not s50) (not s52) (not s53) (not s54))))
(assert (=> s52 (and (not s50) (not s51) (not s53) (not s54))))
(assert (=> s53 (and (not s50) (not s51) (not s52) (not s54))))
(assert (=> s54 (and (not s50) (not s51) (not s52) (not s53))))
(assert (or s10 s20 s30 s40 s50))
(assert (or s11 s21 s31 s41 s51))
(assert (or s12 s22 s32 s42 s52))
(assert (or s13 s23 s33 s43 s53))
(assert (or s14 s24 s34 s44 s54))
(assert (=> s10 (and (not s20) (not s30) (not s40) (not s50))))
(assert (=> s20 (and (not s10) (not s30) (not s40) (not s50))))
(assert (=> s30 (and (not s10) (not s20) (not s40) (not s50))))
(assert (=> s40 (and (not s10) (not s20) (not s30) (not s50))))
(assert (=> s50 (and (not s10) (not s20) (not s30) (not s40))))
(assert (=> s11 (and (not s21) (not s31) (not s41) (not s51))))
(assert (=> s21 (and (not s11) (not s31) (not s41) (not s51))))
(assert (=> s31 (and (not s11) (not s21) (not s41) (not s51))))
(assert (=> s41 (and (not s11) (not s21) (not s31) (not s51))))
(assert (=> s51 (and (not s11) (not s21) (not s31) (not s41))))
(assert (=> s12 (and (not s22) (not s32) (not s42) (not s52))))
(assert (=> s22 (and (not s12) (not s32) (not s42) (not s52))))
(assert (=> s32 (and (not s12) (not s22) (not s42) (not s52))))
(assert (=> s42 (and (not s12) (not s22) (not s32) (not s52))))
(assert (=> s52 (and (not s12) (not s22) (not s32) (not s42))))
(assert (=> s13 (and (not s23) (not s33) (not s43) (not s53))))
(assert (=> s23 (and (not s13) (not s33) (not s43) (not s53))))
(assert (=> s33 (and (not s13) (not s23) (not s43) (not s53))))
(assert (=> s43 (and (not s13) (not s23) (not s33) (not s53))))
(assert (=> s53 (and (not s13) (not s23) (not s33) (not s43))))
(assert (=> s14 (and (not s24) (not s34) (not s44) (not s54))))
(assert (=> s24 (and (not s14) (not s34) (not s44) (not s54))))
(assert (=> s34 (and (not s14) (not s24) (not s44) (not s54))))
(assert (=> s44 (and (not s14) (not s24) (not s34) (not s54))))
(assert (=> s54 (and (not s14) (not s24) (not s34) (not s44))))
(assert (=> s10 (and (not s31) (not s41))))
(assert (=> s20 (and (not s41) (not s51))))
(assert (=> s30 (not s11)))
(assert (=> s40 (and (not s11) (not s21))))
(assert (=> s50 (not s21)))
(assert (=> s11 (and (not s32) (not s42))))
(assert (=> s21 (and (not s42) (not s52))))
(assert (=> s31 (not s12)))
(assert (=> s41 (and (not s12) (not s22))))
(assert (=> s51 (not s22)))
(assert (=> s12 (and (not s33) (not s43))))
(assert (=> s22 (and (not s43) (not s53))))
(assert (=> s32 (not s13)))
(assert (=> s42 (and (not s13) (not s23))))
(assert (=> s52 (not s23)))
(assert (=> s13 (and (not s34) (not s44))))
(assert (=> s23 (and (not s44) (not s54))))
(assert (=> s33 (not s14)))
(assert (=> s43 (and (not s14) (not s24))))
(assert (=> s53 (not s24)))
(check-sat)
(get-model)