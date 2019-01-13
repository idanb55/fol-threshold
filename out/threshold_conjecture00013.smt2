(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_i:A. forall A_h:A. C(A_h & A_i)

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

(declare-fun A_I () (Set Int))
(assert (subset A_I UNIVERSALSET))
(assert (>= (card A_I) (- n t)))

(declare-fun A_H () (Set Int))
(assert (subset A_H UNIVERSALSET))
(assert (>= (card A_H) (- n t)))


(assert (not (> (* 2 (card (intersection A_H A_I))) (- n t))))

(check-sat)
(get-model)
