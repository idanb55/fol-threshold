(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_bt:A. forall B_bs:B. forall C_br:C. C_br & B_bs & A_bt != EMPTYSET

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

(declare-fun A_BT () (Set Int))
(assert (subset A_BT UNIVERSALSET))
(assert (>= (card A_BT) (- n t)))

(declare-fun B_BS () (Set Int))
(assert (subset B_BS UNIVERSALSET))
(assert (> (* 2 (card B_BS)) (+ n (* 3 t))))

(declare-fun C_BR () (Set Int))
(assert (subset C_BR UNIVERSALSET))
(assert (> (* 2 (card C_BR)) (- n t)))


(assert (= (intersection (intersection C_BR B_BS) A_BT) EMPTYSET))

(check-sat)
(get-model)
