(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall B_o:B. forall B_n:B. B_n & B_o != EMPTYSET

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

(declare-fun B_O () (Set Int))
(assert (subset B_O UNIVERSALSET))
(assert (> (* 2 (card B_O)) (+ n (* 3 t))))

(declare-fun B_N () (Set Int))
(assert (subset B_N UNIVERSALSET))
(assert (> (* 2 (card B_N)) (+ n (* 3 t))))


(assert (= (intersection B_N B_O) EMPTYSET))

(check-sat)
(get-model)
