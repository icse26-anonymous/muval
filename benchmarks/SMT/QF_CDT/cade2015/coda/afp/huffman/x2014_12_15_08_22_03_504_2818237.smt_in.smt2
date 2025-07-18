;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_tree_list_a_tree_list_fun$ 0 )
(declare-sort A_tree$ 0)
(declare-sort A_tree_list$ 0)
(declare-fun select$ (A_tree$)Nat$)
(declare-fun selecta$ (A_tree$)A$)
(declare-fun leaf$ (Nat$ A$ )A_tree$)
(declare-fun selectb$ (A_tree$)Nat$)
(declare-fun selectc$ (A_tree$)A_tree$)
(declare-fun selectd$ (A_tree$)A_tree$)
(declare-fun innerNode$ (Nat$ A_tree$ A_tree$ )A_tree$)
(declare-fun nil$ ()A_tree_list$)
(declare-fun hd$ (A_tree_list$)A_tree$)
(declare-fun tl$ (A_tree_list$)A_tree_list$)
(declare-fun cons$ (A_tree$ A_tree_list$ )A_tree_list$)
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun u$ ()A_tree$ )
(declare-fun us$ ()A_tree_list$ )
(declare-fun w_a$ ()Nat$ )
(declare-fun w_b$ ()Nat$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun freq_F$ (A_tree_list$ A$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_tree_list_a_tree_list_fun$ A_tree_list$ )A_tree_list$ )
(declare-fun huffman$ (A_tree_list$ )A_tree$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun splitLeaf$ (A_tree$ Nat$ A$ Nat$ A$ )A_tree$ )
(declare-fun alphabet_F$ (A_tree_list$ )A_set$ )
(declare-fun insortTree$ (A_tree$ )A_tree_list_a_tree_list_fun$ )
(declare-fun uniteTrees$ (A_tree$ A_tree$ )A_tree$ )
(declare-fun splitLeaf_F$ (A_tree_list$ Nat$ A$ Nat$ A$ )A_tree_list$ )
(declare-fun consistent_F$ (A_tree_list$ )Bool )
(declare-fun sortedByWeight$ (A_tree_list$ )Bool )
(assert (! (not (= (splitLeaf_F$ (fun_app$ (insortTree$ t$ )(cons$ u$ us$ ))w_a$ a$ w_b$ b$ )(fun_app$ (insortTree$ t$ )(splitLeaf_F$ (cons$ u$ us$ )w_a$ a$ w_b$ b$ )))):named a0 ))
(assert (! (not (member$ a$ (alphabet_F$ us$ ))):named a1 ))
(assert (! (member$ a$ (alphabet$ u$ )):named a2 ))
(assert (! (not (member$ a$ (alphabet$ t$ ))):named a3 ))
(assert (! (consistent_F$ (cons$ u$ us$ )):named a4 ))
(assert (! (member$ a$ (alphabet_F$ (cons$ u$ us$ ))):named a5 ))
(assert (! (= (freq_F$ (cons$ u$ us$ )a$ )(plus$ w_a$ w_b$ )):named a6 ))
(assert (! (=> (and (member$ a$ (alphabet_F$ us$ ))(and (consistent_F$ us$ )(and (not (member$ a$ (alphabet$ t$ )))(= (freq_F$ us$ a$ )(plus$ w_a$ w_b$ )))))(= (splitLeaf_F$ (fun_app$ (insortTree$ t$ )us$ )w_a$ a$ w_b$ b$ )(fun_app$ (insortTree$ t$ )(splitLeaf_F$ us$ w_a$ a$ w_b$ b$ )))):named a7 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ ))(= (consistent_F$ (fun_app$ (insortTree$ ?v0 )?v1 ))(consistent_F$ (cons$ ?v0 ?v1 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree_list$ )(?v2 Nat$ )(?v3 Nat$ )(?v4 A$ ))(! (=> (not (member$ ?v0 (alphabet_F$ ?v1 )))(= (splitLeaf_F$ ?v1 ?v2 ?v0 ?v3 ?v4 )?v1 )):pattern ((splitLeaf_F$ ?v1 ?v2 ?v0 ?v3 ?v4 )))):named a9 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(= (= (cons$ ?v0 ?v1 )(cons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a10 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ )(?v2 Nat$ )(?v3 A$ )(?v4 Nat$ )(?v5 A$ ))(! (= (splitLeaf_F$ (cons$ ?v0 ?v1 )?v2 ?v3 ?v4 ?v5 )(cons$ (splitLeaf$ ?v0 ?v2 ?v3 ?v4 ?v5 )(splitLeaf_F$ ?v1 ?v2 ?v3 ?v4 ?v5 ))):pattern ((splitLeaf_F$ (cons$ ?v0 ?v1 )?v2 ?v3 ?v4 ?v5 )))):named a11 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ ))(not (= (cons$ ?v0 ?v1 )?v1 ))):named a12 ))
(assert (! (forall ((?v0 A_tree$ ))(! (= (fun_app$ (insortTree$ ?v0 )nil$ )(cons$ ?v0 nil$ )):pattern ((insortTree$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree$ )(?v2 A_tree_list$ ))(! (= (huffman$ (cons$ ?v0 (cons$ ?v1 ?v2 )))(huffman$ (fun_app$ (insortTree$ (uniteTrees$ ?v0 ?v1 ))?v2 ))):pattern ((cons$ ?v0 (cons$ ?v1 ?v2 ))))):named a14 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ ))(=> (sortedByWeight$ (cons$ ?v0 ?v1 ))(sortedByWeight$ ?v1 ))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 Nat$ )(?v3 A$ ))(! (= (splitLeaf_F$ nil$ ?v0 ?v1 ?v2 ?v3 )nil$ ):pattern ((splitLeaf_F$ nil$ ?v0 ?v1 ?v2 ?v3 )))):named a16 ))
(check-sat )
;(get-unsat-core )
