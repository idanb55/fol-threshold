(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall A_k:A. forall B_j:B. B_j & A_k != EMPTYSET

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

(declare-fun A_K () (Set Int))
(assert (subset A_K UNIVERSALSET))
(assert (>= (card A_K) (- n t)))

(declare-fun B_J () (Set Int))
(assert (subset B_J UNIVERSALSET))
(assert (> (* 2 (card B_J)) (+ n (* 3 t))))


(assert (= (intersection B_J A_K) EMPTYSET))

(check-sat)
(get-model)
