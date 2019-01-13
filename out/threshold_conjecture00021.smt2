(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_bh:A. forall A_bg:A. forall A_bf:A. A_bf & A_bg & A_bh != EMPTYSET

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

(declare-fun A_BH () (Set Int))
(assert (subset A_BH UNIVERSALSET))
(assert (>= (card A_BH) (- n t)))

(declare-fun A_BG () (Set Int))
(assert (subset A_BG UNIVERSALSET))
(assert (>= (card A_BG) (- n t)))

(declare-fun A_BF () (Set Int))
(assert (subset A_BF UNIVERSALSET))
(assert (>= (card A_BF) (- n t)))


(assert (= (intersection A_BF (intersection A_BG A_BH)) EMPTYSET))

(check-sat)
(get-model)
