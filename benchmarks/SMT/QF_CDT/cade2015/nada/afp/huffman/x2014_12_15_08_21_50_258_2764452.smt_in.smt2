;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_nat_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-fun select$ (A_tree$)Nat$)
(declare-fun selecta$ (A_tree$)A$)
(declare-fun leaf$ (Nat$ A$ )A_tree$)
(declare-fun selectb$ (A_tree$)Nat$)
(declare-fun selectc$ (A_tree$)A_tree$)
(declare-fun selectd$ (A_tree$)A_tree$)
(declare-fun innerNode$ (Nat$ A_tree$ A_tree$ )A_tree$)
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun c$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun u$ ()A_tree$ )
(declare-fun w_a$ ()Nat$ )
(declare-fun w_b$ ()Nat$ )
(declare-fun cost$ (A_tree$ )Nat$ )
(declare-fun freq$ (A_tree$ )A_nat_fun$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_nat_fun$ A$ )Nat$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun optimum$ (A_tree$ )Bool )
(declare-fun sibling$ (A_tree$ A$ )A$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun consistent$ (A_tree$ )Bool )
(declare-fun mergeSibling$ (A_tree$ A$ )A_tree$ )
(declare-fun swapFourSyms$ (A_tree$ A$ A$ A$ A$ )A_tree$ )
(assert (! (not (less_eq$ (plus$ (plus$ (cost$ t$ )w_a$ )w_b$ )(plus$ (plus$ (cost$ (mergeSibling$ (swapFourSyms$ u$ a$ b$ c$ (sibling$ u$ c$ ))a$ ))w_a$ )w_b$ ))):named a0 ))
(assert (! (optimum$ t$ ):named a1 ))
(assert (! (consistent$ u$ ):named a2 ))
(assert (! (consistent$ t$ ):named a3 ))
(assert (! (member$ c$ (alphabet$ u$ )):named a4 ))
(assert (! (member$ a$ (alphabet$ t$ )):named a5 ))
(assert (! (not (member$ b$ (alphabet$ t$ ))):named a6 ))
(assert (! (less_eq$ w_a$ w_b$ ):named a7 ))
(assert (! (not (= a$ b$ )):named a8 ))
(assert (! (not (= (sibling$ u$ c$ )c$ )):named a9 ))
(assert (! (consistent$ (mergeSibling$ (swapFourSyms$ u$ a$ b$ c$ (sibling$ u$ c$ ))a$ )):named a10 ))
(assert (! (= (freq$ (mergeSibling$ (swapFourSyms$ u$ a$ b$ c$ (sibling$ u$ c$ ))a$ ))(freq$ t$ )):named a11 ))
(assert (! (= (alphabet$ (mergeSibling$ (swapFourSyms$ u$ a$ b$ c$ (sibling$ u$ c$ ))a$ ))(alphabet$ t$ )):named a12 ))
(assert (! (= (fun_app$ (freq$ t$ )a$ )(plus$ w_a$ w_b$ )):named a13 ))
(assert (! (member$ a$ (alphabet$ u$ )):named a14 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 (alphabet$ t$ ))(and (less_eq$ w_a$ (fun_app$ (freq$ t$ )?v0 ))(less_eq$ w_b$ (fun_app$ (freq$ t$ )?v0 ))))):named a15 ))
(assert (! (member$ b$ (alphabet$ u$ )):named a16 ))
(assert (! (member$ (sibling$ u$ c$ )(alphabet$ u$ )):named a17 ))
(check-sat )
;(get-unsat-core )
