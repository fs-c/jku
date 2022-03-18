; t = 10, s = 11, c = 5

(set-logic QF_BV)

(declare-fun c () (_ BitVec 4)) ; Circle
(declare-fun s () (_ BitVec 4)) ; Square
(declare-fun t () (_ BitVec 4)) ; Triangle

(assert (= (bvadd c c) #xA))
(assert (= (bvadd (bvmul c s) c) #xC))
(assert (= (bvsub (bvmul c s) (bvmul t c)) c))

(check-sat)
(get-model)
