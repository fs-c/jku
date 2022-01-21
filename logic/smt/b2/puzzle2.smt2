; t = -2, c = -52, s = -1

(declare-fun c () Int) ; Circle
(declare-fun s () Int) ; Square
(declare-fun t () Int) ; Triangle

; changed (+ c c) to (- s c)
(assert (= (- s c) 51))
(assert (= (+ (* c s) s) 51))
(assert (= (- (* c s) (* t c)) c))

(check-sat)
(get-model)