; s = 0x40, c = 0x73, t = 0x3f

(set-logic QF_BV)

(declare-fun c () (_ BitVec 8)) ; Circle
(declare-fun s () (_ BitVec 8)) ; Square
(declare-fun t () (_ BitVec 8)) ; Triangle

; changed (bvadd c c) to (bvsub c s)
(assert (= (bvsub c s) #x33))
(assert (= (bvadd (bvmul c s) c) #x33))
(assert (= (bvsub (bvmul c s) (bvmul t c)) c))

(check-sat)
(get-model)
