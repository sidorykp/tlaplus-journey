---- MODULE FiniteSetsExt_theorems_ext ----
EXTENDS FiniteSetsExt_theorems_proofs

LEMMA CardSumEqual ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op1(_), NEW op2(_),
           \A e \in S: op1(e) = op2(e),
           \A e \in S: op1(e) \in Nat,
           \A e \in S: op2(e) \in Nat
    PROVE CardSum(S, op1) = CardSum(S, op2)
<1> DEFINE P(s) == s \subseteq S => CardSum(s, op1) = CardSum(s, op2)
<1> HIDE DEF P
<1>1 IsFiniteSet(S) OBVIOUS
<1>2 P({}) BY CardSumEmpty DEF P
<1>3 ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T PROVE P(T \cup {x})
    <2> SUFFICES ASSUME T \subseteq S, x \in S PROVE P(T \cup {x}) BY DEF P
    <2>1 CardSum(T, op1) = CardSum(T, op2) BY <1>3 DEF P
    <2>2 T \cup {x} \subseteq S OBVIOUS
    <2>3 IsFiniteSet(T) BY FS_Subset
    <2>4 x \notin T BY <1>3
    <2>5 CardSum(T \cup {x}, op1) = CardSum(T, op1) + op1(x)
        <3> \A s \in T : op1(s) \in Nat OBVIOUS       
        <3> QED BY CardSumAddElem, <2>3, <2>4
    <2>6 CardSum(T \cup {x}, op2) = CardSum(T, op2) + op2(x)
        <3> \A s \in T : op2(s) \in Nat OBVIOUS
        <3> QED BY CardSumAddElem, <2>3, <2>4
    <2>7 op1(x) = op2(x) OBVIOUS
    <2>8 CardSum(T \cup {x}, op1) = CardSum(T \cup {x}, op2)
        <3>1 IsFiniteSet(T \cup {x}) BY <1>3, FS_Union, FS_Singleton
        <3>2 \A s \in T \cup {x} : op1(s) \in Nat OBVIOUS
        <3>3 CardSum(T \cup {x}, op1) \in Nat BY <3>1, <3>2, CardSumType
        <3>4 \A s \in T \cup {x} : op2(s) \in Nat OBVIOUS
        <3>5 CardSum(T \cup {x}, op2) \in Nat BY <3>1, <3>4, CardSumType
        <3> QED BY ONLY <2>1, <2>5, <2>6, <2>7, <3>3, <3>5
    <2> QED BY <2>8 DEF P
<1>4 P(S) BY ONLY <1>1, <1>2, <1>3, FS_Induction
<1> QED BY <1>4 DEF P


LEMMA MapThenSumSetEqual ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW op1(_), NEW op2(_),
           \A e \in S: op1(e) = op2(e),
           \A e \in S: op1(e) \in Nat,
           \A e \in S: op2(e) \in Nat
    PROVE MapThenSumSet(op1, S) = MapThenSumSet(op2, S)
<1>1 MapThenSumSet(op1, S) = CardSum(S, op1) BY MapThenSumSetDefined
<1>2 MapThenSumSet(op2, S) = CardSum(S, op2) BY MapThenSumSetDefined
<1> QED BY <1>1, <1>2, CardSumEqual

====
