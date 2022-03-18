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

; ensure cells have values in [1, 4]
(assert (or (= c11 #b001) (= c11 #b010) (= c11 #b011) (= c11 #b100)))
(assert (or (= c12 #b001) (= c12 #b010) (= c12 #b011) (= c12 #b100)))
(assert (or (= c13 #b001) (= c13 #b010) (= c13 #b011) (= c13 #b100)))
(assert (or (= c14 #b001) (= c14 #b010) (= c14 #b011) (= c14 #b100)))

(assert (or (= c21 #b001) (= c21 #b010) (= c21 #b011) (= c21 #b100)))
(assert (or (= c22 #b001) (= c22 #b010) (= c22 #b011) (= c22 #b100)))
(assert (or (= c23 #b001) (= c23 #b010) (= c23 #b011) (= c23 #b100)))
(assert (or (= c24 #b001) (= c24 #b010) (= c24 #b011) (= c24 #b100)))

(assert (or (= c31 #b001) (= c31 #b010) (= c31 #b011) (= c31 #b100)))
(assert (or (= c32 #b001) (= c32 #b010) (= c32 #b011) (= c32 #b100)))
(assert (or (= c33 #b001) (= c33 #b010) (= c33 #b011) (= c33 #b100)))
(assert (or (= c34 #b001) (= c34 #b010) (= c34 #b011) (= c34 #b100)))

(assert (or (= c41 #b001) (= c41 #b010) (= c41 #b011) (= c41 #b100)))
(assert (or (= c42 #b001) (= c42 #b010) (= c42 #b011) (= c42 #b100)))
(assert (or (= c43 #b001) (= c43 #b010) (= c43 #b011) (= c43 #b100)))
(assert (or (= c44 #b001) (= c44 #b010) (= c44 #b011) (= c44 #b100)))

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
