(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall C_d:C. C(C_d)

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

(declare-fun C_D () (Set Int))
(assert (subset C_D UNIVERSALSET))
(assert (> (* 2 (card C_D)) (- n t)))


(assert (not (> (* 2 (card C_D)) (- n t))))

(check-sat)
(get-model)
