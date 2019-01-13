(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_e:A. C(A_e & ~f)

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

(declare-fun A_E () (Set Int))
(assert (subset A_E UNIVERSALSET))
(assert (>= (card A_E) (- n t)))


(assert (not (> (* 2 (card (intersection A_E (setminus UNIVERSALSET f)))) (- n t))))

(check-sat)
(get-model)
