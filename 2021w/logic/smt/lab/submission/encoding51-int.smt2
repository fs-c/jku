(set-logic QF_LIA)

; set up cells as variables of the form c{row}{column}
(declare-fun c11 () Int)
(declare-fun c12 () Int)
(declare-fun c13 () Int)
(declare-fun c14 () Int)

(declare-fun c21 () Int)
(declare-fun c22 () Int)
(declare-fun c23 () Int)
(declare-fun c24 () Int)

(declare-fun c31 () Int)
(declare-fun c32 () Int)
(declare-fun c33 () Int)
(declare-fun c34 () Int)

(declare-fun c41 () Int)
(declare-fun c42 () Int)
(declare-fun c43 () Int)
(declare-fun c44 () Int)

; ensure cells have values in [1, 4]
(assert (and (> c11 0) (< c11 5) (> c12 0) (< c12 5) (> c13 0) (< c13 5) (> c14 0) (< c14 5)))
(assert (and (> c21 0) (< c21 5) (> c22 0) (< c22 5) (> c23 0) (< c23 5) (> c24 0) (< c24 5)))
(assert (and (> c31 0) (< c31 5) (> c32 0) (< c32 5) (> c33 0) (< c33 5) (> c34 0) (< c34 5)))
(assert (and (> c41 0) (< c41 5) (> c42 0) (< c42 5) (> c43 0) (< c43 5) (> c44 0) (< c44 5)))

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
