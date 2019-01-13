(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_bk:A. forall A_bj:A. forall B_bi:B. B_bi & A_bj & A_bk != EMPTYSET

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

(declare-fun A_BK () (Set Int))
(assert (subset A_BK UNIVERSALSET))
(assert (>= (card A_BK) (- n t)))

(declare-fun A_BJ () (Set Int))
(assert (subset A_BJ UNIVERSALSET))
(assert (>= (card A_BJ) (- n t)))

(declare-fun B_BI () (Set Int))
(assert (subset B_BI UNIVERSALSET))
(assert (> (* 2 (card B_BI)) (+ n (* 3 t))))


(assert (= (intersection B_BI (intersection A_BJ A_BK)) EMPTYSET))

(check-sat)
(get-model)
