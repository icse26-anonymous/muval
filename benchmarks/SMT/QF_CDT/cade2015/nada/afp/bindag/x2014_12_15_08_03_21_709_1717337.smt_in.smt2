;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Ref$ 0 )
(declare-sort Dag$ 0)
(declare-fun tip$ ()Dag$)
(declare-fun select$ (Dag$)Dag$)
(declare-fun selecta$ (Dag$)Ref$)
(declare-fun selectb$ (Dag$)Dag$)
(declare-fun node$ (Dag$ Ref$ Dag$ )Dag$)
(declare-fun a$ ()Ref$ )
(declare-fun lt$ ()Dag$ )
(declare-fun rt$ ()Dag$ )
(assert (! (not (not (= (node$ lt$ a$ rt$ )rt$ ))):named a0 ))
(check-sat )
;(get-unsat-core )
