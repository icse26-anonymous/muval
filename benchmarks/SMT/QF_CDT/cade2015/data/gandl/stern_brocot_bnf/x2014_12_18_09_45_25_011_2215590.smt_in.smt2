;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_tree$ 0)
(declare-fun root$ (A_tree$)A$)
(declare-fun left$ (A_tree$)A_tree$)
(declare-fun right$ (A_tree$)A_tree$)
(declare-fun node$ (A$ A_tree$ A_tree$ )A_tree$)
(declare-fun a$ ()A_tree$ )
(declare-fun b$ ()A_tree$ )
(declare-fun c$ ()A_tree$ )
(declare-fun plus$ (A_tree$ A_tree$ )A_tree$ )
(declare-fun times$ (A_tree$ A_tree$ )A_tree$ )
(assert (! (not (= (times$ a$ (plus$ b$ c$ ))(plus$ (times$ a$ b$ )(times$ a$ c$ )))):named a0 ))
(assert (! (= (times$ (plus$ a$ b$ )c$ )(plus$ (times$ a$ c$ )(times$ b$ c$ ))):named a1 ))
(check-sat )
;(get-unsat-core )
