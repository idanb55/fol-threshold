(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_bq:A. forall B_bp:B. forall B_bo:B. B_bo & B_bp & A_bq != EMPTYSET

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

(declare-fun A_BQ () (Set Int))
(assert (subset A_BQ UNIVERSALSET))
(assert (>= (card A_BQ) (- n t)))

(declare-fun B_BP () (Set Int))
(assert (subset B_BP UNIVERSALSET))
(assert (> (* 2 (card B_BP)) (+ n (* 3 t))))

(declare-fun B_BO () (Set Int))
(assert (subset B_BO UNIVERSALSET))
(assert (> (* 2 (card B_BO)) (+ n (* 3 t))))


(assert (= (intersection B_BO (intersection B_BP A_BQ)) EMPTYSET))

(check-sat)
(get-model)
