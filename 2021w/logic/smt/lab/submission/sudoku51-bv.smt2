(set-logic QF_BV)

; set up cells as variables of the form c{row}{column}
(declare-fun c11 () (_ BitVec 3))
(declare-fun c12 () (_ BitVec 3))
(declare-fun c13 () (_ BitVec 3))
(declare-fun c14 () (_ BitVec 3))

(declare-fun c21 () (_ BitVec 3))
(declare-fun c22 () (_ BitVec 3))
(declare-fun c23 () (_ BitVec 3))
(declare-fun c24 () (_ BitVec 3))

(declare-fun c31 () (_ BitVec 3))
(declare-fun c32 () (_ BitVec 3))
(declare-fun c33 () (_ BitVec 3))
(declare-fun c34 () (_ BitVec 3))

(declare-fun c41 () (_ BitVec 3))
(declare-fun c42 () (_ BitVec 3))
(declare-fun c43 () (_ BitVec 3))
(declare-fun c44 () (_ BitVec 3))

; set up values from sudoku 51
(assert (= c13 #b100))
(assert (= c22 #b001))
(assert (= c24 #b011))
(assert (= c32 #b010))

; ensure cells have values in [1, 4]
(assert (and (bvuge c11 #b001) (bvule c11 #b111) (bvuge c12 #b001) (bvule c12 #b111)
             (bvuge c13 #b001) (bvule c13 #b111) (bvuge c14 #b001) (bvule c14 #b111)))
(assert (and (bvuge c21 #b001) (bvule c21 #b111) (bvuge c22 #b001) (bvule c22 #b111)
             (bvuge c23 #b001) (bvule c23 #b111) (bvuge c24 #b001) (bvule c24 #b111)))
(assert (and (bvuge c31 #b001) (bvule c31 #b111) (bvuge c32 #b001) (bvule c32 #b111)
             (bvuge c33 #b001) (bvule c33 #b111) (bvuge c34 #b001) (bvule c34 #b111)))
(assert (and (bvuge c41 #b001) (bvule c41 #b111) (bvuge c42 #b001) (bvule c42 #b111)
             (bvuge c43 #b001) (bvule c43 #b111) (bvuge c44 #b001) (bvule c44 #b111)))

; ensure rows have distinct values
(assert (distinct c11 c12 c13 c14))
(assert (distinct c21 c22 c23 c24))
(assert (distinct c31 c32 c33 c34))
(assert (distinct c41 c42 c43 c44))

; ensure columns have distinct values
(assert (distinct c11 c21 c31 c41))
(assert (distinct c12 c22 c32 c42))
(assert (distinct c13 c23 c33 c43))
(assert (distinct c14 c24 c34 c44))

; ensure grids have distinct values
(assert (distinct c11 c12 c21 c22))
(assert (distinct c13 c14 c23 c24))
(assert (distinct c31 c32 c41 c42))
(assert (distinct c33 c34 c43 c44))

(check-sat)
(get-model)
