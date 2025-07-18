;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-datatypes ()((A_tree$ (leaf$ (select$ Nat$ )(selecta$ A$ ))(innerNode$ (selectb$ Nat$ )(selectc$ A_tree$ )(selectd$ A_tree$ )))(Nibble$ (nibble0$ )(nibble1$ )(nibble2$ )(nibble3$ )(nibble4$ )(nibble5$ )(nibble6$ )(nibble7$ )(nibble8$ )(nibble9$ )(nibbleA$ )(nibbleB$ )(nibbleC$ )(nibbleD$ )(nibbleE$ )(nibbleF$ ))(Char$ (char$ (selecte$ Nibble$ )(selectf$ Nibble$ )))))
(declare-fun a$ ()A$ )
(declare-fun t$ ()A_tree$ )
(declare-fun cost$ (A_tree$ )Nat$ )
(declare-fun zero$ ()Nat$ )
(declare-fun height$ (A_tree$ )Nat$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun weight$ (A_tree$ )Nat$ )
(declare-fun sibling$ (A_tree$ A$ )A$ )
(declare-fun alphabet$ (A_tree$ )A_set$ )
(declare-fun size_bool$ (Bool )Nat$ )
(declare-fun size_char$ (Char$ )Nat$ )
(declare-fun cachedWeight$ (A_tree$ )Nat$ )
(assert (! (not (= (sibling$ t$ a$ )a$ )):named a0 ))
(assert (! (= (height$ t$ )zero$ ):named a1 ))
(assert (! (forall ((?v0 A_tree$ ))(! (=> (= (height$ ?v0 )zero$ )(= (cost$ ?v0 )zero$ )):pattern ((cost$ ?v0 )))):named a2 ))
(assert (! (= zero$ zero$ ):named a3 ))
(assert (! (forall ((?v0 Nat$ ))(=> (and (=> (= ?v0 zero$ )false )(=> (not (= ?v0 zero$ ))false ))false )):named a4 ))
(assert (! (forall ((?v0 Nat$ ))(= (= zero$ ?v0 )(= ?v0 zero$ ))):named a5 ))
(assert (! (forall ((?v0 A_tree$ ))(! (=> (= (height$ ?v0 )zero$ )(= (cachedWeight$ ?v0 )(weight$ ?v0 ))):pattern ((cachedWeight$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ ))(! (= (height$ (leaf$ ?v0 ?v1 ))zero$ ):pattern ((leaf$ ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 Char$ ))(! (= (size_char$ ?v0 )zero$ ):pattern ((size_char$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_tree$ ))(! (=> (not (member$ ?v0 (alphabet$ ?v1 )))(= (sibling$ ?v1 ?v0 )?v0 )):pattern ((sibling$ ?v1 ?v0 )))):named a9 ))
(assert (! (= (size_bool$ true )zero$ ):named a10 ))
(assert (! (= (size_bool$ false )zero$ ):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ )(?v2 Nat$ )(?v3 A$ ))(= (= (leaf$ ?v0 ?v1 )(leaf$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a12 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ ))(! (= (weight$ (leaf$ ?v0 ?v1 ))?v0 ):pattern ((leaf$ ?v0 ?v1 )))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ ))(! (= (cachedWeight$ (leaf$ ?v0 ?v1 ))?v0 ):pattern ((leaf$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_tree$ ))(exists ((?v1 A$ ))(member$ ?v1 (alphabet$ ?v0 )))):named a15 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A$ ))(! (= (cost$ (leaf$ ?v0 ?v1 ))zero$ ):pattern ((leaf$ ?v0 ?v1 )))):named a16 ))
(check-sat )
;(get-unsat-core )
