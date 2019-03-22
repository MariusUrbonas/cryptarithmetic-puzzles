; crypto program

(defmodule MAIN
	(export deftemplate ?ALL))

(deftemplate MAIN::var
	(slot lit)
	(slot value)
	(slot stage)
	(slot nonzero)
	(slot zero-nine)
	(slot rank))

(deftemplate MAIN::carry
	(slot value)
	(slot pos)
	(slot fixed))

(deftemplate MAIN::column
	(slot op1)
	(slot op2)
	(slot ans)
	(slot pos))

(deftemplate MAIN::triplet
	(slot v1)
	(slot v2)
	(slot v3))

(deftemplate MAIN::domain
		(multislot dom)
		(slot stage))

(deftemplate MAIN::current-stage
	(slot stage)
	(multislot local-frame)
	(multislot frame)
	(slot current-branch-choise))

(deftemplate MAIN::carry-counter
	(slot count))

(deftemplate MAIN::ans-len
	(slot len))

(deftemplate MAIN::status
	(slot phase))

(deftemplate MAIN::num-base
	(slot base))

(deffacts MAIN::initial-facts
	(domain (dom ) (stage 1))
	(status (phase SETUP))
	(carry-counter (count 0))
	(var (lit nil) (value 0) (stage 1) (nonzero FALSE) (rank 0))
	)

;###############################################################################
;#																MAIN RULES																   #
;###############################################################################

(defrule MAIN::start
	?st<-(status (phase SETUP))
	=>
	(modify ?st (phase SOLVE))
	(focus GET_INPUT SETUP UPDATE_DOMAIN PROPAGATE))

(defrule MAIN::solve
	?st <- (status (phase ?ph&~FINISHED))
	?cs <- (current-stage (stage ?stage) (current-branch-choise ?b) (frame $?f))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
 =>
 (duplicate ?cs (stage (+ ?stage 1)) (local-frame nil) (frame $?f ?b) (current-branch-choise nil))
 (modify ?st (phase SOLVE))
 (focus BRANCH UPDATE_DOMAIN PROPAGATE))

(defrule MAIN::backtrack
 	(declare (salience 10))
 	?st <- (status (phase BLOCKED|GO-BACK))
 	=>
 	(modify ?st (phase SOLVE))
 	(focus BACKTRACK BRANCH UPDATE_DOMAIN PROPAGATE))

(defrule MAIN::solution-found
	(declare (salience 20))
	?st <- (status (phase ?s&~FINISHED&~BLOCKED&~GO-BACK))
	(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	(not (var (lit ?l) (value ?val&:(eq ?val nil)) (stage ?s2&:(eq ?s2 (+ 1 ?stage)))))
	=>
	(modify ?st (phase SOLVE))
	(focus PRINT_ANSWER BACKTRACK BRANCH UPDATE_DOMAIN PROPAGATE)
	(refresh PRINT_ANSWER::message)
	(refresh PRINT_ANSWER::print))

(defrule MAIN::change-carry
	(declare (salience 40))
	?st <- (status (phase GO-BACK))
	?cs <- (current-stage (stage ?stage&0))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	(carry (value 0) (fixed FALSE))
	?cc <-(carry-counter (count ?count))
	=>
	(modify ?cc (count (+ ?count 1)))
	(focus NEW_CARRY_PERMUTATION)
	(modify ?st (phase SOLVE))
	(retract ?cs)
	(assert (current-stage (stage 0))))
		;(refresh BRANCH::branch-triplet))

(defrule MAIN::finish-search
	(declare (salience 30))
	?st <- (status (phase GO-BACK))
	(current-stage (stage ?stage&0))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	=>
	(modify ?st (phase FINISHED)))

;###############################################################################
;#																GET INPUT																		 #
;###############################################################################
(defmodule GET_INPUT
	(import MAIN deftemplate ?ALL))

(defrule GET_INPUT::get-input
		=>
		(printout t "Enter number base for the problem" crlf)
		(assert (num-base (base (read))))
		(printout t "Enter first crypto-number with spaces between letters:" crlf)
		(assert (op1 (explode$ (upcase(readline)))))
		(printout t "+ " crlf)
		(assert (op2 (explode$ (upcase(readline)))))
		(printout t "= " crlf)
		(assert (ans (explode$ (upcase(readline))))
		))

(defrule GET_INPUT::set-domain
		(declare (salience -10))
	  (num-base (base ?base))
		?domain <- (domain (dom $?dom))
		=>
		(bind $?bill $?dom)
		(loop-for-count (?num 0 (- ?base 1)) do
				(bind $?bill (create$ $?bill ?num))
			)
		(modify ?domain (dom $?dom ?bill))
		(return))

(defrule GET_INPUT::switch-up
	(declare (salience 40))
	?o1<-(op1 $?op1)
	?o2<-(op2 $?op2)
	(test (> (length$ $?op1) (length$ $?op2)))
	=>
	(retract ?o1)
	(retract ?o2)
	(assert (op1 $?op2))
	(assert (op2 $?op1)))

(defrule GET_INPUT::get-ans-len
	(ans $?ans)
	=>
	(assert (ans-len (len (length$ $?ans)))))

(defrule GET_INPUT::prepate-input
	(op1 $?op1)
	(op2 $?op2)
	(ans $?ans)
	=>
	(loop-for-count (?column 1 (length$ $?ans) ) do
			(assert (column (op1 (nth$ (- (length$ $?op1) (- ?column 1)) $?op1)) (op2 (nth$ (- (length$ $?op2) (- ?column 1)) $?op2)) (ans (nth$ (- (length$ $?ans) (- ?column 1)) $?ans)) (pos ?column)))))

(defrule GET_INPUT::prepate-vars1
	(declare (salience 20))
	(op1 $? ?var $?)
	=>
	(assert (var (lit ?var) (value nil) (stage 1) (nonzero FALSE) (rank 0) (zero-nine FALSE))))

(defrule GET_INPUT::prepate-vars2
	(declare (salience 20))
	(op2 $? ?var $?)
	=>
	(assert (var (lit ?var) (value nil) (stage 1) (nonzero FALSE) (rank 0) (zero-nine FALSE))))

(defrule GET_INPUT::prepate-vars3
	(declare (salience 20))
	(ans $? ?var $?)
	=>
	(assert (var (lit ?var) (value nil) (stage 1) (nonzero FALSE) (rank 0) (zero-nine FALSE))))

(defrule GET_INPUT::prepare-rank
	?col <- (column (op1 ?op1) (op2 ?op2) (ans ?ans) (pos ?pos))
	(not (processed-col ?pos))
	?var1 <- (var (lit ?op1) (rank ?rank1))
	?var2 <- (var (lit ?op2) (rank ?rank2))
	?var3 <- (var (lit ?ans) (rank ?rank3))
	=>
	(modify ?var1 (rank (+ ?rank1 1)))
	(modify ?var2 (rank (+ ?rank2 1)))
	(modify ?var3 (rank (+ ?rank3 1)))
	(assert (processed-col ?pos)))

(defrule GET_INPUT::prepate-nonzeros1
	(op1 $?op1)
	?var1 <-(var (lit ?l1&:(eq ?l1 (nth$ 1 $?op1)))(nonzero FALSE))
	=>
	(modify ?var1 (nonzero TRUE)))

(defrule GET_INPUT::prepate-nonzeros2
	(op2 $?op2)
	?var2 <-(var (lit ?l2&:(eq ?l2 (nth$ 1 $?op2)))(nonzero FALSE))
	=>
	(modify ?var2 (nonzero TRUE)))

(defrule GET_INPUT::prepate-nonzeros3
	(ans $?ans)
	?var3 <-(var (lit ?l3&:(eq ?l3 (nth$ 1 $?ans)))(nonzero FALSE))
	=>
	(modify ?var3 (nonzero TRUE)))

;###############################################################################
;#																SETUP																				 #
;###############################################################################
(defmodule SETUP
	(import MAIN deftemplate ?ALL))

(defrule SETUP::gen-carries1
	(declare (salience 20))
	(column (op1 ?op1) (op2 ?op2) (ans ?ans) (pos ?pos))
	=>
	(if (eq ?pos 1)
		then (assert (carry (pos ?pos) (value 0) (fixed TRUE)))
		else (assert (carry (pos ?pos) (value 0) (fixed FALSE)))))

(defrule SETUP::gen-carries2
	(declare (salience 15))
	(column (op1 nil) (op2 nil) (ans ?ans) (pos ?pos))
	?var <- (var (lit ?ans))
	?c <- (carry (pos ?pos))
	=>
	(modify ?c (value 1) (fixed TRUE))
	(modify ?var (value 1)))

(defrule SETUP::gen-carries3
	(declare (salience 20))
	(ans-len (len ?len))
	=>
	(assert (carry (pos (+ ?len 1)) (value 0) (fixed TRUE))))

(defrule SETUP::setup-stage
	(declare (salience 20))
	=>
	(assert (current-stage (stage 0))))

(defrule SETUP::setup-zero-nines1
	(declare (salience 17))
	(column (op1 ?op1) (op2 ?op2) (ans ?op2))
	?var <- (var (lit ?op1))
	=>
	(modify ?var (zero-nine TRUE)))

(defrule SETUP::setup-zero-nines2
	(declare (salience 17))
	(column (op1 ?op2) (op2 ?op1) (ans ?op2))
	?var <- (var (lit ?op1) (zero-nine FALSE))
	=>
	(modify ?var (zero-nine TRUE)))

(defrule SETUP::early-halt
	(declare (salience 15))
  (var (lit ?op1) (nonzero TRUE) (zero-nine TRUE))
	(var (lit ?op2&~?op1) (nonzero TRUE) (zero-nine TRUE))
	=>
	(halt))

(defrule SETUP::setup-zero-nines3
	(declare (salience 10))
	?var <- (var (lit ?op1) (nonzero TRUE) (zero-nine TRUE))
	=>
	(modify ?var (value 9)))

(defrule SETUP::gen-pairs
	(domain (dom  $? ?n1 $?) (stage 1))
	(domain (dom  $? ?n2 $?) (stage 1))
	(num-base (base ?base))
	=>
	(assert (triplet (v1 ?n1) (v2 ?n2) (v3 (mod (+ ?n1 ?n2) ?base))))
	(assert (triplet (v1 ?n1) (v2 ?n2) (v3 (mod (+ ?n1 ?n2 1) ?base)))))


;###############################################################################
;#																BRANCH																			 #
;###############################################################################
(defmodule BRANCH
	(import MAIN deftemplate ?ALL))

(deftemplate MAIN::max-rank
	(slot rank)
	(slot col-pos)
	(slot stage))

(defrule BRANCH::set-max-rank-to-zero
	(declare (salience 40))
	?cs <- (current-stage (stage ?stage) (local-frame $?fr) (frame $?f) (current-branch-choise nil))
	(forall (current-stage (stage ?s))
					(current-stage (stage ?s&:(<= ?s ?stage))))
	=>
	(assert(max-rank (rank 0) (col-pos nil) (stage ?stage))))

(defrule BRANCH::calculate-col-ranks
	(declare (salience 30))
	?cs <- (current-stage (stage ?stage) (local-frame $?fr) (frame $?f))
	(forall (current-stage (stage ?s))
					(current-stage (stage ?s&:(<= ?s ?stage))))
	(column (op1 ?op1) (op2 ?op2) (ans ?op3) (pos ?pos&:(not (member$ ?pos $?f))))
	(var (lit ?op1) (value ?val1) (stage ?stage) (nonzero ?nz1) (rank ?rank1))
	(var (lit ?op2) (value ?val2) (stage ?stage) (nonzero ?nz2) (rank ?rank2))
	(var (lit ?op3) (value ?val3) (stage ?stage) (nonzero ?nz3) (rank ?rank3))
	?mr<-(max-rank (rank ?r) (col-pos ?cp))
	(test (< ?r (+ ?rank1 ?rank2 ?rank3)))
	=>
	(modify ?mr (rank (+ ?rank1 ?rank2 ?rank3)) (col-pos ?pos)))

(defrule BRANCH::branch-triplet
	(declare (salience 20))
	?cs <- (current-stage (stage ?stage) (local-frame $?fr))
	(forall (current-stage (stage ?s))
					(current-stage (stage ?s&:(<= ?s ?stage))))
	?domain <-(domain (dom $?dom) (stage ?stage))
	?max<-(max-rank (col-pos ?pos) (stage ?stage))
	(column (op1 ?op1) (op2 ?op2) (ans ?op3) (pos ?pos))
	(carry  (pos ?pos) (value ?c))
	(carry  (pos ?pos2&:(= ?pos2 (+ 1 ?pos))) (value ?c2))
	(num-base (base ?base))
	?var1 <- (var (lit ?op1) (value ?val1) (stage ?stage) (nonzero ?nz1) (zero-nine ?zenine1) (rank ?rank1))
	?var2 <- (var (lit ?op2) (value ?val2) (stage ?stage) (nonzero ?nz2) (zero-nine ?zenine2) (rank ?rank2))
	?var3 <- (var (lit ?op3) (value ?val3) (stage ?stage) (nonzero ?nz3) (zero-nine ?zenine3) (rank ?rank3))
	?trip <- (triplet (v1 ?v1&:(or (and (eq ?val1 nil) (member$ ?v1 $?dom))
												(eq ?v1 ?val1)))
  				 (v2 ?v2&:(or (and (eq ?op1 ?op2) (eq ?v1 ?v2))
						 						(and (neq ?op1 ?op2) (neq ?v1 ?v2))))
					 (v3 ?v3&:(and (or (and (eq ?op3 ?op2) (eq ?v3 ?v2))
						 						     (and (neq ?op3 ?op2) (neq ?v3 ?v2)))
												 (or (and (eq ?op3 ?op1) (eq ?v3 ?v1))
													   (and (neq ?op3 ?op1) (neq ?v3 ?v1))))))
	(test (not(member$ ?trip $?fr)))
	(test (eq (- (+ ?v1 ?v2) (* ?base ?c2)) (- ?v3 ?c)))
	(test (or (and (eq ?nz1 TRUE) (neq ?v1 0)) (neq ?nz1 TRUE)))
	(test (or (and (eq ?nz2 TRUE) (neq ?v2 0)) (neq ?nz2 TRUE)))
	(test (or (and (eq ?nz3 TRUE) (neq ?v3 0)) (neq ?nz3 TRUE)))
	(test (or (and (eq ?zenine1 TRUE) (or (eq ?v1 0) (eq ?v1 (- ?base 1)))) (neq ?zenine1 TRUE)))
	(test (or (and (eq ?zenine2 TRUE) (or (eq ?v2 0) (eq ?v2 (- ?base 1)))) (neq ?zenine2 TRUE)))
	(test (or (and (eq ?zenine3 TRUE) (or (eq ?v3 0) (eq ?v3 (- ?base 1)))) (neq ?zenine3 TRUE)))
  (test (or (and (eq ?val2 nil) (member$ ?v2 $?dom))
						 (eq ?v2 ?val2)))
	(test (or (and (eq ?val3 nil) (member$ ?v3 $?dom))
						 (eq ?v3 ?val3)))
	=>
	(duplicate ?var1 (value ?v1) (stage (+ ?stage 1))(rank (- ?rank1 1)))
	(duplicate ?var2 (value ?v2) (stage (+ ?stage 1))(rank (- ?rank2 1)))
	(duplicate ?var3 (value ?v3) (stage (+ ?stage 1))(rank (- ?rank3 1)))
	(duplicate ?domain (stage (+ ?stage 1)))
	(modify ?cs (local-frame $?fr ?trip) (current-branch-choise ?pos))
	(return))

(defrule BRANCH::no-branches-left
	?st <- (status (phase ?ph))
	?cs <-(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	=>
	(modify ?st (phase GO-BACK))
	(retract ?cs)
	(return))

;###############################################################################
;#																UPDATE_DOMAIN																 #
;###############################################################################
(defmodule UPDATE_DOMAIN
	(import MAIN deftemplate ?ALL))


(defrule UPDATE_DOMAIN:update-domain
	(declare (salience 10))
	(status (phase SOLVE))
	(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?d <- (domain (dom $?dom) (stage ?st&:(eq ?st (+ ?stage 1))))
	(var (lit ?op1&:(neq ?op1 nil)) (value ?val1&:(and (neq ?val1 nil) (member$ ?val1 $?dom))) (stage ?s&:(eq (+ ?stage 1) ?s)))
	=>
	;(duplicate ?d (stage (+ ?stage 1)) (dom (delete-member$ (delete-member$ (delete-member$ $?dom ?val3 ) ?val2 ) ?val1)))
	(modify ?d (dom (delete-member$ $?dom ?val1))))

;###############################################################################
;#																PROPAGATE																		 #
;###############################################################################

(defmodule PROPAGATE
	(import MAIN deftemplate ?ALL))

(defrule PROPAGATE::prop-assigned
	(declare (salience 20))
	(status (phase SOLVE))
	(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?var1 <- (var (lit ?op1) (value ?val1&:(neq nil ?val1)) (stage ?s1&:(= ?s1 ?stage)) (rank ?r))
	(not (var (lit ?op1) (value ?val4&:(neq ?val4 nil)) (stage ?s4&:(= ?s4 (+ ?stage 1)))))
  =>
	(duplicate ?var1 (value ?val1) (stage (+ ?stage 1))))

(defrule PROPAGATE::prop-unassigned
	(status (phase SOLVE))
	(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?var1 <- (var (lit ?op1) (value ?val1&:(eq nil ?val1)) (stage ?s1&:(= ?s1 ?stage)))
	(not (var (lit ?op1) (value ?val4&:(neq ?val4 nil)) (stage ?s4&:(= ?s4 (+ ?stage 1)))))
  =>
	(duplicate ?var1 (value nil) (stage (+ ?stage 1))))

(defrule PROPAGATE::check-conflict
	(declare (salience 15))
	?st <- (status (phase SOLVE))
	(current-stage (stage ?stage))
	(num-base (base ?base))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	(column (op1 ?op1) (op2 ?op2) (ans ?ans) (pos ?pos))
	(carry  (pos ?pos) (value ?c))
	(carry  (pos ?pos2&:(= ?pos2 (+ 1 ?pos))) (value ?c2))
	(var (lit ?op1) (value ?val1&:(neq ?val1 nil)) (stage ?s1&:(= ?s1 (+ 1 ?stage))))
	(var (lit ?op2) (value ?val2&:(neq ?val2 nil)) (stage ?s1&:(= ?s1 (+ 1 ?stage))))
	(var (lit ?ans) (value ?val3&:(neq ?val3 nil)) (stage ?s1&:(= ?s1 (+ 1 ?stage))))
	(test (neq (- (+ ?val1 ?val2 ?c) (* ?c2 ?base)) ?val3))
  =>
	(modify ?st (phase BLOCKED))
	(return))

(defrule PROPAGATE::propag1
	(declare (salience 10))
	?st <- (status (phase SOLVE))
	(current-stage (stage ?stage))
	(num-base (base ?base))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?domain <-(domain (dom $?dom) (stage ?s&:(eq (+ ?stage 1) ?s)))
	(column (op1 ?op1) (op2 ?op2) (ans ?op3) (pos ?pos))
	(carry  (pos ?pos) (value ?c))
	(carry  (pos ?pos2&:(= ?pos2 (+ 1 ?pos))) (value ?c2))
	?var1 <- (var (lit ?op1) (value ?val1&:(neq ?val1 nil)) (stage ?s1&:(= ?s1 (+ 1 ?stage))))
	?var2 <- (var (lit ?op2) (value ?val2&:(neq ?val2 nil)) (stage ?s2&:(= ?s2 (+ 1 ?stage))))
	?var3 <- (var (lit ?op3) (value ?val3&:(eq ?val3 nil)) (stage ?s3&:(= ?s3 ?stage)) (nonzero ?nz) (zero-nine ?zenine))
	(not (var (lit ?op3) (value ?val4&:(neq ?val4 nil)) (stage ?s4&:(= ?s4 (+ ?stage 1)))))
	(triplet (v1 ?val1) (v2 ?val2) (v3 ?v3))
	(test (eq (mod (+ ?val1 ?val2 ?c) ?base) ?v3))
	=>
	(if (and (member$ ?v3 $?dom) (eq (- (+ ?val1 ?val2 ?c) (* ?base ?c2)) ?v3) (and (or (and (eq ?nz TRUE) (neq ?v3 0)) (neq ?nz TRUE))
																																									(or (and (eq ?zenine TRUE) (or (eq ?v3 0) (eq ?v3 (- ?base 1))))  (neq ?zenine TRUE))))
			then (duplicate ?var3 (value ?v3) (stage (+ ?stage 1)))
					 (modify ?domain (dom (delete-member$ $?dom ?v3)))
			else (modify ?st (phase BLOCKED))
					 (return)))

(defrule PROPAGATE::propag2
	(declare (salience 10))
	?st <- (status (phase SOLVE))
	(current-stage (stage ?stage))
	(num-base (base ?base))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?domain <-(domain (dom $?dom) (stage ?s&:(eq (+ ?stage 1) ?s)))
	(column (op1 ?op1) (op2 ?op2) (ans ?op3) (pos ?pos))
	(carry  (pos ?pos) (value ?c))
	(carry  (pos ?pos2&:(= ?pos2 (+ 1 ?pos))) (value ?c2))
	?var1 <- (var (lit ?op1) (value ?val1&:(neq ?val1 nil)) (stage ?s1&:(= ?s1 (+ 1 ?stage))))
	?var2 <- (var (lit ?op2) (value ?val2&:(eq ?val2 nil)) (stage ?s2&:(= ?s2 ?stage))(nonzero ?nz)(zero-nine ?zenine))
	?var3 <- (var (lit ?op3) (value ?val3&:(neq ?val3 nil)) (stage ?s3&:(= ?s3 (+ 1 ?stage))))
	(not (var (lit ?op2) (value ?val4&:(neq ?val4 nil)) (stage ?s4&:(= ?s4 (+ ?stage 1)))))
	(triplet (v1 ?val1) (v2 ?v2) (v3 ?val3))
	(test (eq (mod (+ ?val1 ?v2 ?c) ?base) ?val3))
	=>
	(if (and (member$ ?v2 $?dom) (eq (- (+ ?val1 ?v2 ?c) (* ?base ?c2)) ?val3) (and (or (and (eq ?nz TRUE) (neq ?v2 0)) (neq ?nz TRUE))
																																						      (or (and (eq ?zenine TRUE) (or (eq ?v2 0) (eq ?v2 (- ?base 1))))  (neq ?zenine TRUE))))
			then (duplicate ?var2 (value ?v2) (stage (+ ?stage 1)))
					 (modify ?domain (dom (delete-member$ $?dom ?v2)))
			else (modify ?st (phase BLOCKED))
					 (return)))

(defrule PROPAGATE::propag3
 	(declare (salience 10))
 	?st <- (status (phase SOLVE))
 	(current-stage (stage ?stage))
	(num-base (base ?base))
 	(not (current-stage (stage ?s&:(> ?s ?stage))))
 	?domain <-(domain (dom $?dom) (stage ?s&:(eq (+ ?stage 1) ?s)))
 	(column (op1 ?op1) (op2 ?op2) (ans ?op3) (pos ?pos))
 	(carry  (pos ?pos) (value ?c))
 	(carry  (pos ?pos2&:(= ?pos2 (+ 1 ?pos))) (value ?c2))
 	?var1 <- (var (lit ?op1) (value ?val1&:(eq ?val1 nil)) (stage ?s1&:(= ?s1 ?stage))(nonzero ?nz) (zero-nine ?zenine))
 	?var2 <- (var (lit ?op2) (value ?val2&:(neq ?val2 nil)) (stage ?s2&:(= ?s2 (+ 1 ?stage))))
 	?var3 <- (var (lit ?op3) (value ?val3&:(neq ?val3 nil)) (stage ?s3&:(= ?s3 (+ 1 ?stage))))
 	(not (var (lit ?op1) (value ?val4&:(neq ?val4 nil)) (stage ?s4&:(= ?s4 (+ ?stage 1)))))
 	(triplet (v1 ?v1) (v2 ?val2) (v3 ?val3))
 	(test (eq (mod (+ ?v1 ?val2 ?c) ?base) ?val3))
 	=>
 	(if (and (member$ ?v1 $?dom) (eq (- (+ ?v1 ?val2 ?c) (* ?base ?c2)) ?val3) (and (or (and (eq ?nz TRUE) (neq ?v1 0)) (neq ?nz TRUE))
																																							    (or (and (eq ?zenine TRUE) (or (eq ?v1 0) (eq ?v1 (- ?base 1))))  (neq ?zenine TRUE))))
 			then (duplicate ?var1 (value ?v1) (stage (+ ?stage 1)))
 					 (modify ?domain (dom (delete-member$ $?dom ?v1)))
 			else (modify ?st (phase BLOCKED))
 					 (return)))

(defrule PROPAGATE::propag4
 	(declare (salience 10))
 	?st <- (status (phase SOLVE))
 	(current-stage (stage ?stage))
	(num-base (base ?base))
 	(not (current-stage (stage ?s&:(> ?s ?stage))))
 	?domain <-(domain (dom $?dom) (stage ?s&:(eq (+ ?stage 1) ?s)))
 	(column (op1 ?op1) (op2 ?op1) (ans ?op3) (pos ?pos))
 	(carry  (pos ?pos) (value ?c))
 	(carry  (pos ?pos2&:(= ?pos2 (+ 1 ?pos))) (value ?c2))
 	?var1 <- (var (lit ?op1) (value ?val1&:(eq ?val1 nil)) (stage ?s1&:(= ?s1 ?stage))(nonzero ?nz)(zero-nine ?zenine))
 	?var3 <- (var (lit ?op3) (value ?val3&:(neq ?val3 nil)) (stage ?s3&:(= ?s3 (+ 1 ?stage))))
 	(not (var (lit ?op1) (value ?val4&:(neq ?val4 nil)) (stage ?s4&:(= ?s4 (+ ?stage 1)))))
 	(triplet (v1 ?v1) (v2 ?v1) (v3 ?val3))
 	(test (eq (mod (+ ?v1 ?v1 ?c) ?base) ?val3))
	(test (eq (div (+ ?v1 ?v1 ?c) ?base) ?c2))
 	=>
 	(if (and (member$ ?v1 $?dom) (eq (- (+ ?v1 ?v1 ?c) (* ?base ?c2)) ?val3) (and (or (and (eq ?nz TRUE) (neq ?v1 0)) (neq ?nz TRUE))
																																								(or (and (eq ?zenine TRUE) (or (eq ?v1 0) (eq ?v1 (- ?base 1))))  (neq ?zenine TRUE))))
 			then (duplicate ?var1 (value ?v1) (stage (+ ?stage 1)))
 					 (modify ?domain (dom (delete-member$ $?dom ?v1)))
 			else (modify ?st (phase BLOCKED))
 					 (return)))


;###############################################################################
;#																BACKTRACK																		 #
;###############################################################################

(defmodule BACKTRACK
	(import MAIN deftemplate ?ALL))

(defrule BACKTRACK::backtrack-vars
	(declare (salience 10))
	(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?var <- (var (stage ?s&:(> ?s ?stage)))
	=>
	(retract ?var))

(defrule BACKTRACK::backtrack-domain
	?cs <- (current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?domain <- (domain (stage ?s&:(> ?s ?stage)))
	=>
	(retract ?domain))

(defrule BACKTRACK::backtrack-max-col-pos
	?cs <- (current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	?max <- (max-rank (stage ?s&:(> ?s ?stage)))
	=>
	(retract ?max))

;###############################################################################
;#													 			PRINT ANSWER												    	   #
;###############################################################################

(defmodule PRINT_ANSWER
(import MAIN deftemplate ?ALL))

(defrule PRINT_ANSWER::message
	(declare (salience 10))
	=>
	(printout t "Solution found:" crlf))

(defrule PRINT_ANSWER::print
	(current-stage (stage ?stage))
	(not (current-stage (stage ?s&:(> ?s ?stage))))
	(var (lit ?l&:(neq nil ?l)) (value ?val) (stage ?s&:(eq ?s (+ ?stage 1))))
	=>
	(printout t  ?l " = " ?val crlf))

;###############################################################################
;#													 			NEW CARRY PERMUTATION								    	   #
;###############################################################################

(defmodule NEW_CARRY_PERMUTATION
 (import MAIN deftemplate ?ALL))


(defrule NEW_CARRY_PERMUTATION::generate-new-carries
	(carry-counter (count ?count))
	?carry <- (carry (pos ?p) (value ?c) (fixed FALSE))
	=>
	(modify ?carry (value (mod (div ?count (** 2 (- ?p 2))) 2))))





;
