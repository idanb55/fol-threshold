(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_u:A. forall A_t:A. A_t & A_u & ~f != EMPTYSET

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

(declare-fun A_U () (Set Int))
(assert (subset A_U UNIVERSALSET))
(assert (>= (card A_U) (- n t)))

(declare-fun A_T () (Set Int))
(assert (subset A_T UNIVERSALSET))
(assert (>= (card A_T) (- n t)))


(assert (= (intersection A_T (intersection A_U (setminus UNIVERSALSET f))) EMPTYSET))

(check-sat)
(get-model)
