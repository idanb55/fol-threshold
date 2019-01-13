(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_m:A. forall C_l:C. C_l & A_m != EMPTYSET

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

(declare-fun A_M () (Set Int))
(assert (subset A_M UNIVERSALSET))
(assert (>= (card A_M) (- n t)))

(declare-fun C_L () (Set Int))
(assert (subset C_L UNIVERSALSET))
(assert (> (* 2 (card C_L)) (- n t)))


(assert (= (intersection C_L A_M) EMPTYSET))

(check-sat)
(get-model)
