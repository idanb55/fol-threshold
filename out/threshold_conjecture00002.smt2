(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_b:A. A_b != EMPTYSET

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

(declare-fun A_B () (Set Int))
(assert (subset A_B UNIVERSALSET))
(assert (>= (card A_B) (- n t)))


(assert (= A_B EMPTYSET))

(check-sat)
(get-model)
