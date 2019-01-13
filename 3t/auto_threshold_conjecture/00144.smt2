(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall B_q:B. forall C_p:C. C_p & B_q != EMPTYSET

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

(declare-fun B_Q () (Set Int))
(assert (subset B_Q UNIVERSALSET))
(assert (> (* 2 (card B_Q)) (+ n (* 3 t))))

(declare-fun C_P () (Set Int))
(assert (subset C_P UNIVERSALSET))
(assert (> (* 2 (card C_P)) (- n t)))


(assert (= (intersection C_P B_Q) EMPTYSET))

(check-sat)
(get-model)
