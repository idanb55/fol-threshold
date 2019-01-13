(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall B_f:B. C(B_f & ~f)

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

(declare-fun B_F () (Set Int))
(assert (subset B_F UNIVERSALSET))
(assert (> (* 2 (card B_F)) (+ n (* 3 t))))


(assert (not (> (* 2 (card (intersection B_F (setminus UNIVERSALSET f)))) (- n t))))

(check-sat)
(get-model)
