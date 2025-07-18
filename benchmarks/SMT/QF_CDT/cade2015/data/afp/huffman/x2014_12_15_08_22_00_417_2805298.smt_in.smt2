;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_tree_bool_fun$ 0 )
(declare-sort A_tree_list_bool_fun$ 0 )
(declare-sort A_tree_a_tree_list_fun$ 0 )
(declare-sort A_tree_list_a_tree_list_fun$ 0 )
(declare-datatypes ()((A_tree$ (leaf$ (select$ Nat$ )(selecta$ A$ ))(innerNode$ (selectb$ Nat$ )(selectc$ A_tree$ )(selectd$ A_tree$ )))(A_tree_list$ (nil$ )(cons$ (hd$ A_tree$ )(tl$ A_tree_list$ )))))
(declare-fun a$ ()A$ )
(declare-fun b$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun w_a$ ()Nat$ )
(declare-fun w_b$ ()Nat$ )
(declare-fun bind$ (A_tree_list$ A_tree_a_tree_list_fun$ )A_tree_list$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun freq_F$ (A_tree_list$ A$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_tree_list_a_tree_list_fun$ A_tree_list$ )A_tree_list$ )
(declare-fun huffman$ (A_tree_list$ )A_tree$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun fun_app$a (A_tree_list_bool_fun$ A_tree_list$ )Bool )
(declare-fun list_ex1$ (A_tree_bool_fun$ )A_tree_list_bool_fun$ )
(declare-fun alphabet_F$ (A_tree_list$ )A_set$ )
(declare-fun insortTree$ (A_tree$ )A_tree_list_a_tree_list_fun$ )
(declare-fun splitLeaf_F$ (A_tree_list$ Nat$ A$ Nat$ A$ )A_tree_list$ )
(declare-fun consistent_F$ (A_tree_list$ )Bool )
(declare-fun sortedByWeight$ (A_tree_list$ )Bool )
(assert (! (not (= (splitLeaf_F$ (fun_app$ (insortTree$ t$ )nil$ )w_a$ a$ w_b$ b$ )(fun_app$ (insortTree$ t$ )(splitLeaf_F$ nil$ w_a$ a$ w_b$ b$ )))):named a0 ))
(assert (! (consistent_F$ nil$ ):named a1 ))
(assert (! (member$ a$ (alphabet_F$ nil$ )):named a2 ))
(assert (! (not (member$ a$ (alphabet$ t$ ))):named a3 ))
(assert (! (= (freq_F$ nil$ a$ )(plus$ w_a$ w_b$ )):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree_list$ )(?v2 Nat$ )(?v3 Nat$ )(?v4 A$ ))(! (=> (not (member$ ?v0 (alphabet_F$ ?v1 )))(= (splitLeaf_F$ ?v1 ?v2 ?v0 ?v3 ?v4 )?v1 )):pattern ((splitLeaf_F$ ?v1 ?v2 ?v0 ?v3 ?v4 )))):named a5 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 Nat$ )(?v3 A$ ))(! (= (splitLeaf_F$ nil$ ?v0 ?v1 ?v2 ?v3 )nil$ ):pattern ((splitLeaf_F$ nil$ ?v0 ?v1 ?v2 ?v3 )))):named a6 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ ))(not (= (fun_app$ (insortTree$ ?v0 )?v1 )nil$ ))):named a7 ))
(assert (! (= (consistent_F$ nil$ )true ):named a8 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (=> (= ?v0 nil$ )false )(=> (not (= ?v0 nil$ ))false ))false )):named a9 ))
(assert (! (forall ((?v0 A_tree$ ))(! (= (fun_app$ (insortTree$ ?v0 )nil$ )(cons$ ?v0 nil$ )):pattern ((insortTree$ ?v0 )))):named a10 ))
(assert (! (= (sortedByWeight$ nil$ )true ):named a11 ))
(assert (! (forall ((?v0 A_tree_a_tree_list_fun$ ))(! (= (bind$ nil$ ?v0 )nil$ ):pattern ((bind$ nil$ ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (not (= ?v0 nil$ ))(= (alphabet$ (huffman$ ?v0 ))(alphabet_F$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_tree_bool_fun$ ))(! (= (fun_app$a (list_ex1$ ?v0 )nil$ )false ):pattern ((list_ex1$ ?v0 )))):named a14 ))
(assert (! (forall ((?v0 A_tree$ )(?v1 A_tree_list$ ))(= (consistent_F$ (fun_app$ (insortTree$ ?v0 )?v1 ))(consistent_F$ (cons$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (=> (= ?v0 nil$ )false )(and (forall ((?v1 A_tree$ ))(=> (= ?v0 (cons$ ?v1 nil$ ))false ))(forall ((?v1 A_tree$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 (cons$ ?v2 ?v3 )))false ))))false )):named a16 ))
(assert (! (forall ((?v0 A_tree_list$ ))(=> (and (forall ((?v1 A_tree$ ))(=> (= ?v0 (cons$ ?v1 nil$ ))false ))(and (forall ((?v1 A_tree$ )(?v2 A_tree$ )(?v3 A_tree_list$ ))(=> (= ?v0 (cons$ ?v1 (cons$ ?v2 ?v3 )))false ))(=> (= ?v0 nil$ )false )))false )):named a17 ))
(check-sat )
;(get-unsat-core )
