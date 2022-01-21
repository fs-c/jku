; t = 1, s = 2, c = 5

(declare-fun c () Int) ; Circle
(declare-fun s () Int) ; Square
(declare-fun t () Int) ; Triangle

(assert (= (+ c c) 10))
(assert (= (+ (* c s) s) 12))
(assert (= (- (* c s) (* t c)) c))

(check-sat)
(get-model)