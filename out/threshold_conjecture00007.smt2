(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall B_c:B. C(B_c)

(declare-fun n () Int)
(declare-fun t () Int)

(declare-fun EMPTYSET () (Set Int))
(declare-fun UNIVERSALSET () (Set Int))
(declare-fun f () (Set Int))

(assert (> n 0))
(assert (> n (* 3 t)))
(assert (subset EMPTYSET UNIVERSALSET))
(assert (= (card EMPTYSET) 0))
(assert (subset UNIVERSALSET UNIVERSALSET))
(assert (= (card UNIVERSALSET) n))
(assert (subset f UNIVERSALSET))
(assert (= (card f) t))

(declare-fun B_C () (Set Int))
(assert (subset B_C UNIVERSALSET))
(assert (> (* 2 (card B_C)) (+ n (* 3 t))))


(assert (not (> (* 2 (card B_C)) (- n t))))

(check-sat)
(get-model)
