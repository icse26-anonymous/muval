;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_tree_set$ 0 )
(declare-sort Num$ 0)
(declare-sort A_tree$ 0)
(declare-fun one$ ()Num$)
(declare-fun select$ (Num$)Num$)
(declare-fun bit0$ (Num$ )Num$)
(declare-fun selecta$ (Num$)Num$)
(declare-fun bit1$ (Num$ )Num$)
(declare-fun leaf$ ()A_tree$)
(declare-fun left$ (A_tree$)A_tree$)
(declare-fun val$ (A_tree$)A$)
(declare-fun right$ (A_tree$)A_tree$)
(declare-fun node$ (A_tree$ A$ A_tree$ )A_tree$)
(declare-fun a$ (A$ A_tree$ )Real )
(declare-fun b$ ()A$ )
(declare-fun c$ ()A$ )
(declare-fun l$ ()A_tree$ )
(declare-fun r$ ()A_tree$ )
(declare-fun u$ ()A$ )
(declare-fun aa$ ()A$ )
(declare-fun l$a ()A_tree$ )
(declare-fun la$ ()A_tree$ )
(declare-fun r$a ()A_tree$ )
(declare-fun ra$ ()A_tree$ )
(declare-fun rl$ ()A_tree$ )
(declare-fun rr$ ()A_tree$ )
(declare-fun bst$ (A_tree$ )Bool )
(declare-fun log$ (Real Real )Real )
(declare-fun less$ (A$ A$ )Bool )
(declare-fun real$ (Nat$ )Real )
(declare-fun size1$ (A_tree$ )Nat$ )
(declare-fun splay$ (A$ A_tree$ )A_tree$ )
(declare-fun member$ (A_tree$ A_tree_set$ )Bool )
(declare-fun subtrees$ (A_tree$ )A_tree_set$ )
(assert (! (not (<= (+ (- (+ (log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a ))))(* 2.0 (log$ 2.0 (real$ (size1$ (node$ l$ c$ r$ ))))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))1.0 )(+ (- (* 3.0 (log$ 2.0 (real$ (size1$ (node$ l$ c$ r$ )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))1.0 ))):named a0 ))
(assert (! (not (= aa$ c$ )):named a1 ))
(assert (! (not (= aa$ b$ )):named a2 ))
(assert (! (=> (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A_tree$ ))(=> (= r$ (node$ ?v0 ?v1 ?v2 ))false ))false ):named a3 ))
(assert (! (= (splay$ aa$ rr$ )(node$ l$a u$ r$a )):named a4 ))
(assert (! (less$ c$ aa$ ):named a5 ))
(assert (! (less$ b$ aa$ ):named a6 ))
(assert (! (=> (forall ((?v0 A_tree$ )(?v1 A$ )(?v2 A_tree$ ))(=> (= (splay$ aa$ rr$ )(node$ ?v0 ?v1 ?v2 ))false ))false ):named a7 ))
(assert (! (member$ (node$ la$ aa$ ra$ )(subtrees$ (node$ l$ c$ r$ ))):named a8 ))
(assert (! (bst$ (node$ l$ c$ r$ )):named a9 ))
(assert (! (<= (+ (- (- (+ (+ (* 2.0 (log$ 2.0 (real$ (size1$ rr$ ))))(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(log$ 2.0 (real$ (size1$ (node$ rl$ b$ rr$ )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))2.0 )(+ (- (+ (+ (log$ 2.0 (real$ (size1$ rr$ )))(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))2.0 )):named a10 ))
(assert (! (<= (+ (- (+ (+ (log$ 2.0 (real$ (size1$ rr$ )))(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))2.0 )(+ (- (+ (log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a ))))(* 2.0 (log$ 2.0 (real$ (size1$ (node$ l$ c$ r$ ))))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))1.0 )):named a11 ))
(assert (! (= (+ (- (- (- (+ (+ (* 3.0 (log$ 2.0 (real$ (size1$ rr$ ))))(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(log$ 2.0 (real$ (size1$ (node$ rl$ b$ rr$ )))))(log$ 2.0 (real$ (size1$ (node$ l$a u$ r$a )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))2.0 )(+ (- (- (+ (+ (* 2.0 (log$ 2.0 (real$ (size1$ rr$ ))))(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(log$ 2.0 (real$ (size1$ (node$ rl$ b$ rr$ )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))2.0 )):named a12 ))
(assert (! (<= (a$ aa$ (node$ l$ c$ r$ ))(+ (- (+ (log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a ))))(* 2.0 (log$ 2.0 (real$ (size1$ (node$ l$ c$ r$ ))))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))1.0 )):named a13 ))
(assert (! (= r$ (node$ rl$ b$ rr$ )):named a14 ))
(assert (! (<= (+ (- (- (+ (+ (a$ aa$ rr$ )(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(log$ 2.0 (real$ (size1$ (node$ rl$ b$ rr$ )))))(log$ 2.0 (real$ (size1$ (node$ l$a u$ r$a )))))1.0 )(+ (- (- (- (+ (+ (* 3.0 (log$ 2.0 (real$ (size1$ rr$ ))))(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(log$ 2.0 (real$ (size1$ (node$ rl$ b$ rr$ )))))(log$ 2.0 (real$ (size1$ (node$ l$a u$ r$a )))))(* 3.0 (log$ 2.0 (real$ (size1$ (node$ la$ aa$ ra$ ))))))2.0 )):named a15 ))
(assert (! (= (+ 1.0 1.0 )2.0 ):named a16 ))
(assert (! (= (a$ aa$ (node$ l$ c$ r$ ))(+ (- (- (+ (+ (a$ aa$ rr$ )(log$ 2.0 (real$ (size1$ (node$ (node$ l$ c$ rl$ )b$ l$a )))))(log$ 2.0 (real$ (size1$ (node$ l$ c$ rl$ )))))(log$ 2.0 (real$ (size1$ (node$ rl$ b$ rr$ )))))(log$ 2.0 (real$ (size1$ (node$ l$a u$ r$a )))))1.0 )):named a17 ))
(check-sat )
;(get-unsat-core )
