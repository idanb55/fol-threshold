(set-logic ALL_SUPPORTED)
(set-info :status unsat)

; conjecture set forall C_g:C. C_g & ~f != EMPTYSET

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

(declare-fun C_G () (Set Int))
(assert (subset C_G UNIVERSALSET))
(assert (> (* 2 (card C_G)) (- n t)))


(assert (= (intersection C_G (setminus UNIVERSALSET f)) EMPTYSET))

(check-sat)
(get-model)
